"""Entry point for running OpenEvolve-based evolutionary search.

This script connects to a LiteLLM-compatible proxy and uses OpenEvolve
to evolve the ``generate_candidates`` function in
``evolve/seed_solution.py``.  It does **not** evolve individual polynomial
pairs -- it evolves the *strategy* for generating them.

Prerequisites
-------------
* A running LiteLLM proxy (or any OpenAI-compatible endpoint).  Pass the
  URL via ``--api-base``, ``$OPENAI_API_BASE``, ``$LITELLM_API_BASE``, or
  let it default to ``http://localhost:4000/v1``.
* The ``evolve`` dependency group: ``uv sync --group dev --group evolve``.

How it works
------------
1. Loads ``evolve/config.yaml`` and applies CLI overrides (model list,
   temperature, api_base, iterations).
2. Passes ``evolve/seed_solution.py`` (initial program) and
   ``evolve/openevolve_evaluator.py`` (fitness function) to OpenEvolve.
3. OpenEvolve mutates the code between ``# EVOLVE-BLOCK-START`` and
   ``# EVOLVE-BLOCK-END`` markers using LLM-generated diffs.
4. Each mutation is evaluated via the two-stage cascade in
   ``openevolve_evaluator.py`` (see that module's docstring for details).
5. Opted-in ansatz configs use 5 algebraic-mechanism islands and MAP-Elites
   across fixed mechanism, support-split, and cover-orbit cells.
6. The LLM receives structured evaluation artifacts (best code found,
   per-lattice breakdown, errors) as feedback for the next mutation.

W&B integration
---------------
Pass ``--wandb`` to enable live dashboards.  A background ``WandbSyncer``
thread tails the metrics JSONL file written by evaluator subprocesses
(where ``wandb.run`` is ``None``) and forwards each record to W&B with
running-best tracking.

Output
------
* Best evolved program: ``best_generate_candidates.py`` for Python genomes or
  ``best_coset_policy.json`` for the typed coset DSL.
* OpenEvolve checkpoints: ``results/evolution/<run_name>/checkpoints/``
* Metrics JSONL: ``results/evolution_metrics.jsonl``
* Discovered codes: ``results/discovered_codes.json``

Usage::

    # Single model
    uv run python evolve/run_evolution.py \\
        --model anthropic/claude-sonnet-4-5-20250514 --iterations 100

    # Ensemble of models
    uv run python evolve/run_evolution.py \\
        --models gemini/gemini-2.5-flash anthropic/claude-sonnet-4-5-20250514 \\
        --iterations 200 --run-name ensemble_v1

    # Resume from checkpoint
    uv run python evolve/run_evolution.py \\
        --resume results/evolution/run_20260218/checkpoints/checkpoint_100 \\
        --iterations 200

    # With W&B tracking
    uv run python evolve/run_evolution.py \\
        --model anthropic/claude-sonnet-4-5-20250514 --iterations 100 --wandb
"""

from __future__ import annotations

import argparse
import asyncio
import copy
import concurrent.futures
import fcntl
import hashlib
import json
import math
import os
import platform as platform_module
import re
import signal
import shutil
import stat
import subprocess
import sys
import tempfile
import threading
import time
from datetime import datetime
from contextlib import contextmanager, nullcontext
from dataclasses import dataclass, field
from pathlib import Path
from typing import Any

import yaml

# Ensure project root is on path
PROJECT_ROOT = str(Path(__file__).resolve().parent.parent)
if PROJECT_ROOT not in sys.path:
    sys.path.insert(0, PROJECT_ROOT)

from evolve.dependency_contract import (
    COSET_EVALUATOR_DEPENDENCIES,
    LOCAL_EVALUATOR_DEPENDENCIES,
)
from evaluation.search_contract import (
    ACTIVE_GEOMETRY_CONTRACT,
    ACTIVE_STAGE2_DEEP_LATTICES,
    EVOLUTION_LATTICES,
    LEGACY_GEOMETRY_CONTRACT,
    SEARCH_GEOMETRY_CONTRACT_ENV,
    TWISTED_TORUS_GEOMETRY_CONTRACT,
)

SEED_SOLUTION = str(Path(__file__).parent / "seed_solution.py")
SEED_SOLUTION_MILP = str(Path(__file__).parent / "seed_solution_milp.py")
SEED_SOLUTION_NONCSS = str(Path(__file__).parent / "seed_solution_noncss.py")
SEED_SOLUTION_COSET_TWO_BLOCK_V2 = str(
    Path(__file__).parent / "coset_seed_solution_v2.py"
)
SEED_SOLUTION_COSET_TWO_BLOCK_V3 = str(
    Path(__file__).parent / "coset_seed_solution_v3.py"
)
# New coset launches use renderer v3.  The v2 paths remain explicit replay
# inputs and are selected only by a v2 config/checkpoint contract.
SEED_SOLUTION_COSET_TWO_BLOCK = SEED_SOLUTION_COSET_TWO_BLOCK_V3
EVALUATOR = str(Path(__file__).parent / "openevolve_evaluator.py")
EVALUATOR_NONCSS = str(Path(__file__).parent / "openevolve_evaluator_noncss.py")
EVALUATOR_COSET_TWO_BLOCK = str(
    Path(__file__).parent / "coset_openevolve_evaluator.py"
)
DEFAULT_CONFIG = str(Path(__file__).parent / "config.yaml")
DEFAULT_CONFIG_NONCSS = str(Path(__file__).parent / "config_noncss.yaml")
DEFAULT_CONFIG_COSET_TWO_BLOCK_V2 = str(
    Path(__file__).parent / "coset_config_v2.yaml"
)
DEFAULT_CONFIG_COSET_TWO_BLOCK_V3 = str(
    Path(__file__).parent / "coset_config_v3.yaml"
)
DEFAULT_CONFIG_COSET_TWO_BLOCK = DEFAULT_CONFIG_COSET_TWO_BLOCK_V3
EVOLUTION_BASE = str(Path(PROJECT_ROOT) / "results" / "evolution")
METRICS_FILE = str(Path(PROJECT_ROOT) / "results" / "evolution_metrics.jsonl")

EVALUATOR_KIND_DEFAULT = "default"
EVALUATOR_KIND_COSET_TWO_BLOCK = "coset-two-block"
EVALUATOR_KIND_BINDING_FIELD = "qcode_evaluator_kind"
EVALUATOR_KIND_ID_METRIC = "qcode_evaluator_kind_id"
ACTION_CATALOG_SHA256_BINDING_FIELD = "qcode_action_catalog_sha256"
COSET_RENDERER_ACTIVATION_SHA256_BINDING_FIELD = (
    "qcode_coset_renderer_activation_sha256"
)
COSET_RENDERER_ACTIVATION_JSON_ENV = (
    "QCODE_COSET_RENDERER_ACTIVATION_JSON"
)
COSET_NEGATIVE_FEEDBACK_INVOCATION_FIELDS = frozenset({
    "qcode_negative_feedback_live_archive_path",
    "qcode_negative_feedback_snapshot_path",
    "qcode_negative_feedback_snapshot_sha256",
    "qcode_negative_feedback_archive_sha256",
    "qcode_negative_feedback_manifest_path",
    "qcode_negative_feedback_manifest_sha256",
    "qcode_negative_feedback_epoch",
})
NEGATIVE_ARCHIVE_PATH_ENV = "QCODE_COSET_NEGATIVE_ARCHIVE_PATH"
NEGATIVE_ARCHIVE_SNAPSHOT_PATH_ENV = (
    "QCODE_COSET_NEGATIVE_ARCHIVE_SNAPSHOT_PATH"
)
ACTION_CATALOG_ID_METRIC = "qcode_action_catalog_id"
EVALUATOR_KIND_IDS = {
    EVALUATOR_KIND_DEFAULT: 0,
    EVALUATOR_KIND_COSET_TWO_BLOCK: 1,
}
EVALUATOR_KINDS = (
    EVALUATOR_KIND_DEFAULT,
    EVALUATOR_KIND_COSET_TWO_BLOCK,
)
# Schema 5 binds the mechanism-portfolio semantics (relation-first MAP cells,
# lineage islands, and the recorded search regime).  Schema 6 additionally
# binds the pinned OpenEvolve evaluator source whose outer Stage-1 failure
# envelope is interpreted by this launcher.  Schema 7 binds the data-only
# coset policy renderer and its killable mutation preflight.  Older artifacts
# remain frozen replay inputs for Humanize; this launcher emits only current
# schema artifacts.
EVOLUTION_LEGACY_COMPLETION_SCHEMA_VERSION = 4
EVOLUTION_LEGACY_SLICE_WITNESS_SCHEMA_VERSION = 4
EVOLUTION_COMPLETION_SCHEMA_VERSION = 7
EVOLUTION_SLICE_WITNESS_SCHEMA_VERSION = 7
WINNER_PREFLIGHT_CONTRACT_VERSION = 2
WINNER_PREFLIGHT_CONTRACT_ID_ENV = "QCODE_WINNER_PREFLIGHT_CONTRACT_ID"
CANDIDATE_LOG_PATH_ENV = "QCODE_CANDIDATE_LOG_PATH"
STAGE1_PREFLIGHT_JOURNAL_SCHEMA_VERSION = 1
STAGE1_PREFLIGHT_JOURNAL_DIRECTORY = ".stage1-preflight"
STAGE1_PREFLIGHT_MAX_EPOCH_ATTEMPTS = 2
STAGE1_PREFLIGHT_WORKER_ATTEMPTS = 2
STAGE1_PREFLIGHT_LOCK_WAIT_INTERVALS = 2
STAGE1_PREFLIGHT_OUTER_MARGIN_S = 120.0
STAGE2_DEEP_CONTRACT_VERSION = 3
STAGE2_DEEP_LATTICE_COUNT = len(ACTIVE_STAGE2_DEEP_LATTICES)
STAGE2_CONTRACT_VERSION_METRIC = "stage2_contract_version"
STAGE2_CONTRACT_ID_METRIC = "stage2_contract_id"
STAGE2_COMPLETE_METRIC = "stage2_complete"
STAGE2_INCOMPLETE_METRIC = "stage2_incomplete"
STAGE2_LATTICES_METRIC = "stage2_lattices"
STAGE2_HARD_TIMEOUT_METRIC = "stage2_hard_timeout"
STAGE2_SUBPROCESS_FAILED_METRIC = "stage2_subprocess_failed"
STAGE2_MARKER_FIELDS = (
    STAGE2_CONTRACT_VERSION_METRIC,
    STAGE2_CONTRACT_ID_METRIC,
    STAGE2_COMPLETE_METRIC,
    STAGE2_INCOMPLETE_METRIC,
    STAGE2_LATTICES_METRIC,
    STAGE2_HARD_TIMEOUT_METRIC,
    STAGE2_SUBPROCESS_FAILED_METRIC,
)
LEGACY_STAGE2_DEEP_METRIC_FIELDS = (
    "best_fom",
    "best_bp_fom_upper_bound",
    "fitness_distance_credit",
    "mean_fom",
    "num_above_6",
    "num_above_12",
    "target_preflight_lattices",
    "unique_candidates",
    "evaluated_candidate_definitions",
    "duplicate_candidate_occurrences",
    "winner_capable_unresolved_top_persisted",
    "distance_backend_error_count",
)
WINNER_PREFLIGHT_CONTRACT_VERSION_METRIC = (
    "winner_preflight_contract_version"
)
WINNER_PREFLIGHT_CONTRACT_ID_METRIC = "winner_preflight_contract_id"
WINNER_PREFLIGHT_COMPLETE_METRIC = "winner_preflight_complete"
WINNER_PREFLIGHT_INCOMPLETE_METRIC = "winner_preflight_incomplete"
WINNER_PREFLIGHT_LATTICES_METRIC = "winner_preflight_lattices"
WINNER_PREFLIGHT_UNIT_KIND_ID_METRIC = "winner_preflight_unit_kind_id"
WINNER_PREFLIGHT_UNITS_METRIC = "winner_preflight_units"
WINNER_PREFLIGHT_ACTION_STRATA_METRIC = (
    "winner_preflight_action_strata"
)
WINNER_PREFLIGHT_UNIT_KIND_ACTION_STRATA = 1
WINNER_PREFLIGHT_EVALUATED_METRIC = (
    "winner_preflight_candidate_definitions_evaluated"
)
WINNER_PREFLIGHT_ELIGIBLE_METRIC = (
    "winner_preflight_winner_capable_eligible"
)
WINNER_PREFLIGHT_PERSISTED_METRIC = (
    "winner_preflight_winner_capable_persisted"
)
WINNER_PREFLIGHT_OMITTED_METRIC = "winner_preflight_winner_capable_omitted"
WINNER_PREFLIGHT_HARD_TIMEOUT_METRIC = "winner_preflight_hard_timeout"
WINNER_PREFLIGHT_SUBPROCESS_FAILED_METRIC = (
    "winner_preflight_subprocess_failed"
)
# Keep this value synchronized with openevolve_evaluator.py.  Version 4 makes
# the algebraic relation and cover-orbit span first-class archive coordinates.
# Older feature maps describe a different search geometry and are deliberately
# not resumable under this portfolio schema.
MAP_DESCRIPTOR_VERSION = 4
MAP_DESCRIPTOR_VERSION_METRIC = "map_descriptor_version"
MAP_DESCRIPTOR_POOL_SIZE_METRIC = "map_descriptor_pool_size"
MAP_DESCRIPTOR_DOMINANT_SHARE_METRIC = (
    "map_descriptor_dominant_pattern_share"
)
MAP_DESCRIPTOR_SUPPORT_SPLIT_METRIC = "support_split_type"
MAP_DESCRIPTOR_STRUCTURAL_ENTROPY_METRIC = "search_structural_entropy"
MAP_DESCRIPTOR_ALGEBRAIC_RELATION_METRIC = "algebraic_relation_type"
MAP_DESCRIPTOR_ORBIT_SPAN_METRIC = "orbit_span_bin"
MAP_DESCRIPTOR_DIFFERENCE_SPECTRUM_METRIC = "difference_spectrum_bin"
SEARCH_PORTFOLIO_SCHEMA_VERSION = 2
SEARCH_PORTFOLIO_CONFIG_KEY = "qcode_search_portfolio"
SEARCH_PORTFOLIO_ISLAND_COUNT = 5
COSET_SEARCH_PORTFOLIO_CONFIG_KEY = "qcode_coset_search_portfolio"
COSET_SEARCH_PORTFOLIO_COMPATIBILITY_GROUP = (
    "coset-two-block-catalog-v2-dsl-map-v3-proof-ladder-v3"
)
COSET_SEARCH_PORTFOLIO_ISLAND_COUNT = 4
COSET_MUTATION_REJECTION_PREFIX = "QCODE_COSET_MUTATION_REJECTED_V1="
COSET_MUTATION_REJECTION_SCHEMA_VERSION = 1
COSET_MUTATION_REJECTION_KINDS = {
    "ambiguous_search": "invalid_mutation",
    "dsl_invalid": "invalid_mutation",
    "dsl_noncanonical": "invalid_mutation",
    "empty_search": "invalid_mutation",
    "no_diff_blocks": "invalid_mutation",
    "semantic_noop": "no_effect_mutation",
    "textual_noop": "no_effect_mutation",
    "unmatched_search": "no_effect_mutation",
}
SEARCH_PORTFOLIO_V2_FEATURE_DIMENSIONS = (
    MAP_DESCRIPTOR_ALGEBRAIC_RELATION_METRIC,
    MAP_DESCRIPTOR_SUPPORT_SPLIT_METRIC,
    MAP_DESCRIPTOR_ORBIT_SPAN_METRIC,
)
SEARCH_PORTFOLIO_V2_FEATURE_BINS = {
    MAP_DESCRIPTOR_ALGEBRAIC_RELATION_METRIC: 5,
    MAP_DESCRIPTOR_SUPPORT_SPLIT_METRIC: 6,
    MAP_DESCRIPTOR_ORBIT_SPAN_METRIC: 3,
}
SEARCH_PORTFOLIO_V3_SCHEMA_VERSION = 3
SEARCH_PORTFOLIO_V3_GEOMETRY_METRIC = "geometry_twist_class"
SEARCH_PORTFOLIO_V3_FEATURE_DIMENSIONS = (
    MAP_DESCRIPTOR_ALGEBRAIC_RELATION_METRIC,
    MAP_DESCRIPTOR_SUPPORT_SPLIT_METRIC,
    SEARCH_PORTFOLIO_V3_GEOMETRY_METRIC,
)
SEARCH_PORTFOLIO_V3_FEATURE_BINS = {
    MAP_DESCRIPTOR_ALGEBRAIC_RELATION_METRIC: 5,
    MAP_DESCRIPTOR_SUPPORT_SPLIT_METRIC: 6,
    SEARCH_PORTFOLIO_V3_GEOMETRY_METRIC: 3,
}
SEARCH_PORTFOLIO_SPECS = {
    SEARCH_PORTFOLIO_SCHEMA_VERSION: (
        SEARCH_PORTFOLIO_V2_FEATURE_DIMENSIONS,
        SEARCH_PORTFOLIO_V2_FEATURE_BINS,
    ),
    SEARCH_PORTFOLIO_V3_SCHEMA_VERSION: (
        SEARCH_PORTFOLIO_V3_FEATURE_DIMENSIONS,
        SEARCH_PORTFOLIO_V3_FEATURE_BINS,
    ),
}
SEARCH_GEOMETRY_CONTRACT_FIELD = "search_geometry_contract"
# Compatibility aliases for schema-v2 callers and tests.
SEARCH_PORTFOLIO_FEATURE_DIMENSIONS = SEARCH_PORTFOLIO_V2_FEATURE_DIMENSIONS
SEARCH_PORTFOLIO_FEATURE_BINS = SEARCH_PORTFOLIO_V2_FEATURE_BINS
SEARCH_PORTFOLIO_ROLES = (
    "affine_automorphism_cover",
    "shared_anchor_coset_cover",
    "complementary_diagonal_cover",
    "asymmetric_anchor_cover",
    "failure_repair_restart",
)
SEARCH_PORTFOLIO_SUPPORT_TARGETS = (
    ((2, 3), (3, 2), (3, 3)),
    ((2, 2), (2, 3), (3, 2), (3, 3)),
    ((2, 2), (2, 3), (3, 2), (3, 3)),
    ((2, 4), (4, 2), (2, 3), (3, 2)),
    ((2, 2), (2, 3), (3, 2), (2, 4), (4, 2), (3, 3)),
)
# Exact indices of evaluation.algebraic_mechanisms.RELATION_TYPES.  Unlike the
# v1 support-split islands, every v2 island owns a distinct generative
# mechanism. Support split remains an orthogonal MAP/quota coordinate.
SEARCH_PORTFOLIO_RELATION_CATEGORIES = (
    (0,),
    (1,),
    (2,),
    (3,),
    (4,),
)


def _mechanism_island_for_relation(category: int) -> int:
    matches = [
        island
        for island, categories in enumerate(
            SEARCH_PORTFOLIO_RELATION_CATEGORIES
        )
        if category in categories
    ]
    if len(matches) != 1:
        raise RuntimeError(
            "algebraic relation category does not map to one mechanism island"
        )
    return matches[0]
SEARCH_PORTFOLIO_DIRECTIVES = (
    "Construct nontrivial cyclic covers/lifts where B is an affine torus "
    "automorphism or translated orbit of A; vary lift index and orbit span, "
    "not merely individual exponents.",
    "Construct shared-anchor or shared-difference coset mechanisms whose A/B "
    "supports arise from a common subgroup/ideal but are not identical.",
    "Construct complementary diagonal cover mechanisms with distinct primitive "
    "directions and controlled intersections across the lifted torus.",
    "Construct asymmetric anchored mechanisms, especially legal 2+4/4+2 "
    "extensions, while preserving positive k and avoiding self-duality.",
    "Perform mechanism-changing restarts and witness-guided repair; escape "
    "occupied mechanism/support/orbit cells instead of coefficient jitter.",
)
ADAPTIVE_MUTATION_POLICY_PREFIX = "QCODE_ADAPTIVE_MUTATION_POLICY_V1="
ADAPTIVE_MUTATION_TACTICS = (
    "novel_structure_exploration",
    "repair_x_low_weight",
    "repair_z_low_weight",
    "repair_dual_balance",
)
ADAPTIVE_MUTATION_DIRECTIVES = {
    "novel_structure_exploration": (
        "Change the generator's structural template, not just coefficients; "
        "avoid definitions and MAP cells already represented in the prompt."
    ),
    "repair_x_low_weight": (
        "Disrupt the concrete X-logical supports in the parent's "
        "low_weight_oracle_failures artifact (and matching Humanize evidence) "
        "by changing the responsible algebraic/cover mechanism while preserving "
        "commutation, positive k, and structural novelty."
    ),
    "repair_z_low_weight": (
        "Disrupt the concrete Z-logical supports in the parent's "
        "low_weight_oracle_failures artifact (and matching Humanize evidence) "
        "by changing the responsible algebraic/cover mechanism while preserving "
        "commutation, positive k, and structural novelty."
    ),
    "repair_dual_balance": (
        "Change the A/B relationship using the concrete X/Z supports in the "
        "parent's low_weight_oracle_failures artifact so neither logical "
        "sector retains or recreates an easy low-weight failure mode."
    ),
}
DEFAULT_ADAPTIVE_MUTATION_POLICY = {
    "novel_structure_exploration": 1000,
    "repair_x_low_weight": 0,
    "repair_z_low_weight": 0,
    "repair_dual_balance": 0,
}
ADAPTIVE_MUTATION_TOTAL_WEIGHT = 1000
ADAPTIVE_MUTATION_EXPLORATION_FLOOR = 250
SEARCH_REGIME_POLICY_PREFIX = "QCODE_SEARCH_REGIME_V1="
SEARCH_REGIME_POLICY_V2_PREFIX = "QCODE_SEARCH_REGIME_V2="
SEARCH_REGIME_POLICY_V3_PREFIX = "QCODE_SEARCH_REGIME_V3="
SEARCH_REGIME_POLICY_V4_PREFIX = "QCODE_SEARCH_REGIME_V4="
SEARCH_REGIME_PREFIX_BY_POLICY_VERSION = {
    1: SEARCH_REGIME_POLICY_PREFIX,
    2: SEARCH_REGIME_POLICY_V2_PREFIX,
    3: SEARCH_REGIME_POLICY_V3_PREFIX,
    4: SEARCH_REGIME_POLICY_V4_PREFIX,
}
SEARCH_REGIME_V1_STATUSES = (
    "normal",
    "expand_required",
    "exploit",
)
SEARCH_REGIME_V2_STATUSES = (
    *SEARCH_REGIME_V1_STATUSES,
    "representation_change_required",
)
SEARCH_REGIME_STATUSES = SEARCH_REGIME_V2_STATUSES
DEFAULT_SEARCH_REGIME = {"schema_version": 1, "status": "normal"}
SEARCH_REGIME_DIRECTIVES = {
    "normal": (
        "Machine search-regime directive: preserve broad mechanism coverage "
        "and prefer structurally novel candidates over coefficient jitter."
    ),
    "expand_required": (
        "Machine search-regime directive: expand the BB mechanism family, "
        "support shapes, orbit spans, and cover constructions; do not merely "
        "retune coefficients in an occupied family."
    ),
    "representation_change_required": (
        "Machine search-regime directive: change the generator representation "
        "or structural genotype and use the restart lane for representation-"
        "changing proposals; coefficient-only mutation is insufficient."
    ),
    "exploit": (
        "Machine search-regime directive: exploit the trusted exact-distance "
        "mechanism while retaining cross-mechanism coverage."
    ),
}
SEARCH_PORTFOLIO_ARTIFACT_KEY = "qcode_search_portfolio_v2"
WINNER_PREFLIGHT_NUMERIC_THREAD_ENV = (
    "OMP_NUM_THREADS",
    "OPENBLAS_NUM_THREADS",
    "MKL_NUM_THREADS",
    "NUMEXPR_NUM_THREADS",
    "VECLIB_MAXIMUM_THREADS",
    "BLIS_NUM_THREADS",
)


class _WinnerPreflightTimeout(RuntimeError):
    """One checkpoint preflight child made no durable lattice progress."""


class _WinnerPreflightChildFailure(RuntimeError):
    """One checkpoint preflight child ended without a completed payload."""


def _file_identity(path: str | Path, label: str) -> dict[str, object]:
    original = Path(path)
    if original.is_symlink():
        raise RuntimeError(f"{label} may not be a symlink: {original}")
    try:
        resolved = original.resolve(strict=True)
    except OSError as exc:
        raise RuntimeError(f"{label} is missing: {original}") from exc
    if not resolved.is_file():
        raise RuntimeError(f"{label} is not a regular file: {resolved}")
    digest = hashlib.sha256()
    with resolved.open("rb") as stream:
        for chunk in iter(lambda: stream.read(1024 * 1024), b""):
            digest.update(chunk)
    return {
        "path": str(resolved),
        "sha256": digest.hexdigest(),
        "bytes": resolved.stat().st_size,
    }


def _read_text_snapshot(
    path_value: str | Path,
    label: str,
) -> tuple[str, dict[str, Any]]:
    path = Path(path_value)
    if not path.is_absolute() or path.is_symlink():
        raise RuntimeError(f"{label} path must be absolute and symlink-free")
    try:
        resolved = path.resolve(strict=True)
    except OSError as exc:
        raise RuntimeError(f"{label} is missing: {path}") from exc
    if resolved != path:
        raise RuntimeError(f"{label} path must be canonical: {path}")
    nofollow = getattr(os, "O_NOFOLLOW", None)
    if nofollow is None:
        raise RuntimeError(f"O_NOFOLLOW is required to read {label}")
    fd = os.open(path, os.O_RDONLY | nofollow | getattr(os, "O_CLOEXEC", 0))
    try:
        before = os.fstat(fd)
        path_before = os.stat(path, follow_symlinks=False)
        if (
            not stat.S_ISREG(before.st_mode)
            or not stat.S_ISREG(path_before.st_mode)
            or (before.st_dev, before.st_ino)
            != (path_before.st_dev, path_before.st_ino)
        ):
            raise RuntimeError(f"{label} must be one stable regular file")
        chunks: list[bytes] = []
        while True:
            chunk = os.read(fd, 1024 * 1024)
            if not chunk:
                break
            chunks.append(chunk)
        after = os.fstat(fd)
        path_after = os.stat(path, follow_symlinks=False)
        if (
            (before.st_dev, before.st_ino)
            != (after.st_dev, after.st_ino)
            or (after.st_dev, after.st_ino)
            != (path_after.st_dev, path_after.st_ino)
        ):
            raise RuntimeError(f"{label} changed identity while being read")
    finally:
        os.close(fd)
    encoded = b"".join(chunks)
    try:
        text = encoded.decode("utf-8")
    except UnicodeDecodeError as exc:
        raise RuntimeError(f"{label} is not UTF-8 text") from exc
    return text, {
        "path": str(path),
        "sha256": hashlib.sha256(encoded).hexdigest(),
        "bytes": len(encoded),
    }


def _file_sha256(path: Path) -> str:
    return str(_file_identity(path, "checkpoint file")["sha256"])


def _read_json_object(path: Path, label: str) -> dict[str, Any]:
    if path.is_symlink() or not path.is_file():
        raise RuntimeError(f"{label} must be a regular file: {path}")
    try:
        value = json.loads(path.read_text())
    except (OSError, json.JSONDecodeError) as exc:
        raise RuntimeError(f"cannot read {label}: {path}: {exc}") from exc
    if not isinstance(value, dict):
        raise RuntimeError(f"{label} must contain a JSON object: {path}")
    return value


SUPPORTED_OPENEVOLVE_VERSION = "0.2.26"
SUPPORTED_OPENEVOLVE_SHA256 = {
    "controller": "4508dfc844e26cd6da7cf48240e8acf0a42d8a927610b41e0ebb0f283d6e88f9",
    "process_parallel": "66f6fa57e7afb5db54cf7bc02130f30d4040175d9cdfdf53faf668787eec2371",
    "database": "4ae70c309d7c33a3f92ad181437ec71f9ca77575d57bd673249791ecf38d754b",
    "api": "c85fcafe18f288148a5dea918b6af5c2312717f39de2a416d26e158b84924eae",
    "evaluator": "f1deed6c378cc1e57bfb86548375ca7775de6857d829169015999d269f46bc5b",
}
STAGE1_EXCEPTION_PROVENANCE_FIELD = "qcode_exception_provenance"
STAGE1_EXCEPTION_PROVENANCE_SCHEMA_VERSION = 1

def _active_evaluator_dependencies(
    evaluator_kind: str = EVALUATOR_KIND_DEFAULT,
) -> dict[str, str]:
    _validated_evaluator_kind(evaluator_kind, noncss=False, milp=False)
    dependencies = dict(LOCAL_EVALUATOR_DEPENDENCIES)
    if evaluator_kind == EVALUATOR_KIND_COSET_TWO_BLOCK:
        dependencies.update(COSET_EVALUATOR_DEPENDENCIES)
    return dependencies


def _evaluator_dependency_identities(
    evaluator_kind: str = EVALUATOR_KIND_DEFAULT,
) -> dict[str, dict[str, Any]]:
    project_root = Path(PROJECT_ROOT)
    return {
        name: _file_identity(
            project_root / relative_path,
            f"evolution evaluator dependency {name}",
        )
        for name, relative_path in _active_evaluator_dependencies(
            evaluator_kind
        ).items()
    }


def _winner_preflight_contract_id(
    evaluator_path: str | Path,
    dependency_identities: dict[str, dict[str, Any]],
    *,
    candidate_log_path: str | Path,
    evaluator_kind: str = EVALUATOR_KIND_DEFAULT,
) -> int:
    """Bind checkpoint markers to code, lattices, and their durable run sink."""

    evaluator = _file_identity(
        evaluator_path, "winner preflight evaluator"
    )
    dependency_hashes: dict[str, str] = {}
    active_dependencies = _active_evaluator_dependencies(evaluator_kind)
    if set(dependency_identities) != set(active_dependencies):
        raise RuntimeError(
            "winner preflight evaluator dependency set is invalid"
        )
    for name in sorted(active_dependencies):
        identity = dependency_identities.get(name)
        digest = identity.get("sha256") if isinstance(identity, dict) else None
        if (
            not isinstance(digest, str)
            or len(digest) != 64
            or any(character not in "0123456789abcdef" for character in digest)
        ):
            raise RuntimeError(
                f"winner preflight dependency identity is invalid: {name}"
            )
        dependency_hashes[name] = digest
    candidate_log = Path(candidate_log_path).expanduser()
    if not candidate_log.is_absolute():
        raise RuntimeError(
            "winner preflight candidate log path must be absolute"
        )
    candidate_log = candidate_log.resolve(strict=False)
    output_dir = candidate_log.parent
    payload = {
        "contract_version": WINNER_PREFLIGHT_CONTRACT_VERSION,
        "evaluator_sha256": evaluator["sha256"],
        "dependency_sha256": dependency_hashes,
        "lattices": [list(lattice) for lattice in EVOLUTION_LATTICES],
        "candidate_log_path": str(candidate_log),
        "run_identity": {
            "output_dir": str(output_dir),
            "run_name": output_dir.name,
        },
    }
    if evaluator_kind == EVALUATOR_KIND_COSET_TWO_BLOCK:
        payload["preflight_unit_contract"] = {
            "kind": "action_strata",
            "kind_id": WINNER_PREFLIGHT_UNIT_KIND_ACTION_STRATA,
            "count": _coset_action_strata_count(),
        }
    if ACTIVE_GEOMETRY_CONTRACT == TWISTED_TORUS_GEOMETRY_CONTRACT:
        payload[SEARCH_GEOMETRY_CONTRACT_FIELD] = ACTIVE_GEOMETRY_CONTRACT
    digest = hashlib.sha256(
        json.dumps(
            payload,
            sort_keys=True,
            separators=(",", ":"),
        ).encode("utf-8")
    ).hexdigest()
    # OpenEvolve treats metrics as JSON numbers and converts cascade metrics
    # to float.  Thirteen hexadecimal digits stay below 2**53, so the id is
    # exactly representable and survives every checkpoint round trip.
    return int(digest[:13], 16)


_WINNER_PREFLIGHT_COMMON_MARKER_FIELDS = (
    WINNER_PREFLIGHT_CONTRACT_VERSION_METRIC,
    WINNER_PREFLIGHT_CONTRACT_ID_METRIC,
    WINNER_PREFLIGHT_COMPLETE_METRIC,
    WINNER_PREFLIGHT_INCOMPLETE_METRIC,
    WINNER_PREFLIGHT_EVALUATED_METRIC,
    WINNER_PREFLIGHT_ELIGIBLE_METRIC,
    WINNER_PREFLIGHT_PERSISTED_METRIC,
    WINNER_PREFLIGHT_OMITTED_METRIC,
    WINNER_PREFLIGHT_HARD_TIMEOUT_METRIC,
    WINNER_PREFLIGHT_SUBPROCESS_FAILED_METRIC,
)
_WINNER_PREFLIGHT_MARKER_FIELDS = (
    *_WINNER_PREFLIGHT_COMMON_MARKER_FIELDS,
    WINNER_PREFLIGHT_LATTICES_METRIC,
)
_COSET_WINNER_PREFLIGHT_MARKER_FIELDS = (
    *_WINNER_PREFLIGHT_COMMON_MARKER_FIELDS,
    WINNER_PREFLIGHT_UNIT_KIND_ID_METRIC,
    WINNER_PREFLIGHT_UNITS_METRIC,
    WINNER_PREFLIGHT_ACTION_STRATA_METRIC,
)


def _coset_action_strata_count() -> int:
    from evolve.coset_search_contract import action_search_views

    count = len(action_search_views())
    if count < 1:
        raise RuntimeError("coset preflight has no action strata")
    return count


def _validated_coset_activation_document(
    document: dict[str, Any],
):
    """Rehydrate one canonical, source-registered renderer activation."""

    if not isinstance(document, dict):
        raise RuntimeError("coset renderer activation is not an object")
    try:
        from evolve.coset_search_contract import (
            coset_renderer_activation_document,
            trusted_coset_renderer_activation_from_document,
        )

        activation = trusted_coset_renderer_activation_from_document(document)
        if coset_renderer_activation_document(activation) != document:
            raise ValueError("activation did not round-trip canonically")
    except (TypeError, ValueError) as exc:
        raise RuntimeError("coset renderer activation is invalid") from exc
    return activation


def _coset_mutation_bounds_prompt(
    activation_document: dict[str, Any] | None = None,
) -> str:
    """Build exact activation- and catalog-derived bounds for the LLM."""

    from evolve.coset_search_contract import action_search_views

    support_splits = (
        ((3, 3),)
        if activation_document is None
        else _validated_coset_activation_document(
            activation_document
        ).approved_support_splits
    )

    rows = [
        "Trusted catalog-derived mutation bounds (inclusive):",
        "Use these exact values; do not infer index sizes from block length.",
    ]
    rendered_splits = ", ".join(
        f"[{left},{right}]" for left, right in support_splits
    )
    rows.append(
        "The sealed activation for this slice permits exactly these "
        f"support_split values: {rendered_splits}."
    )
    if len(support_splits) == 1:
        rows.append(
            f"Keep support_split exactly {rendered_splits} in this slice; "
            "do not mutate it to another registry value."
        )
    for split in support_splits:
        rows.append(
            f"Bounds for support_split=[{split[0]},{split[1]}] "
            f"(explicit left/right lengths {split[0] - 1}/{split[1] - 1}):"
        )
        for view in action_search_views():
            left_count = sum(
                element != view.left_identity_id
                for element in view.left_element_ids
            )
            right_count = sum(
                element != view.right_identity_id
                for element in view.right_element_ids
            )
            left_choose = split[0] - 1
            right_choose = split[1] - 1
            if left_count < left_choose or right_count < right_choose:
                raise RuntimeError(
                    f"coset action {view.action_id} has no "
                    f"{split[0]}+{split[1]} support space"
                )
            combination_space = (
                math.comb(left_count, left_choose)
                * math.comb(right_count, right_choose)
            )
            if combination_space < 2:
                raise RuntimeError(
                    f"coset action {view.action_id} has a degenerate "
                    f"{split[0]}+{split[1]} support space"
                )
            rows.append(
                f"- action_id={view.action_id}: left indices "
                f"0..{left_count - 1}; right indices 0..{right_count - 1}; "
                f"walk offset 0..{combination_space - 1}; walk stride "
                f"1..{combination_space - 1}, "
                f"gcd(stride,{combination_space})=1."
            )
    rows.extend([
        "Policy arrays must already be canonical: keep actions in ascending "
        "action_id order; within every explicit support, left and right "
        "indices must be strictly increasing; within each supports list, "
        "entries must be strictly lexicographically increasing by "
        "(left,right). The worker rejects noncanonical ordering instead of "
        "repairing it.",
        "Every SEARCH value must be copied exactly from the current JSON and "
        "must occur exactly once. Every block must change the policy.",
        "Do not repeat the immutable published support in explicit supports.",
    ])
    return "\n".join(rows)


def _winner_preflight_marker_fields(
    evaluator_kind: str = EVALUATOR_KIND_DEFAULT,
) -> tuple[str, ...]:
    _validated_evaluator_kind(evaluator_kind, noncss=False, milp=False)
    if evaluator_kind == EVALUATOR_KIND_COSET_TWO_BLOCK:
        return _COSET_WINNER_PREFLIGHT_MARKER_FIELDS
    return _WINNER_PREFLIGHT_MARKER_FIELDS

_WINNER_PREFLIGHT_FAILURE_BASE_FIELDS = frozenset({
    "combined_score",
    "error",
    "lattices_with_high_k",
    MAP_DESCRIPTOR_DOMINANT_SHARE_METRIC,
    MAP_DESCRIPTOR_POOL_SIZE_METRIC,
    MAP_DESCRIPTOR_SUPPORT_SPLIT_METRIC,
    MAP_DESCRIPTOR_STRUCTURAL_ENTROPY_METRIC,
    MAP_DESCRIPTOR_ALGEBRAIC_RELATION_METRIC,
    MAP_DESCRIPTOR_ORBIT_SPAN_METRIC,
    MAP_DESCRIPTOR_DIFFERENCE_SPECTRUM_METRIC,
    MAP_DESCRIPTOR_VERSION_METRIC,
    "num_high_k",
    "term_count",
    "pattern_type",
    *({SEARCH_PORTFOLIO_V3_GEOMETRY_METRIC}
      if ACTIVE_GEOMETRY_CONTRACT == TWISTED_TORUS_GEOMETRY_CONTRACT
      else set()),
})


def _exact_nonnegative_metric(
    metrics: dict[str, Any],
    name: str,
) -> int:
    value = metrics.get(name)
    if (
        isinstance(value, bool)
        or not isinstance(value, (int, float))
        or not math.isfinite(float(value))
        or float(value) < 0
        or not float(value).is_integer()
    ):
        raise RuntimeError(f"winner preflight marker is invalid: {name}")
    return int(value)


def _validated_map_descriptor_version(
    metrics: Any,
    *,
    label: str,
) -> int:
    if not isinstance(metrics, dict):
        raise RuntimeError(f"{label} metrics are not an object")
    value = metrics.get(MAP_DESCRIPTOR_VERSION_METRIC)
    if (
        isinstance(value, bool)
        or not isinstance(value, (int, float))
        or not math.isfinite(float(value))
        or not float(value).is_integer()
        or int(value) != MAP_DESCRIPTOR_VERSION
    ):
        raise RuntimeError(
            f"{label} uses an incompatible MAP descriptor schema "
            f"({value!r}); start a fresh campaign instead of resuming this "
            "checkpoint"
        )
    return int(value)


def _validated_winner_preflight_markers(
    metrics: Any,
    *,
    expected_contract_id: int,
    evaluator_kind: str = EVALUATOR_KIND_DEFAULT,
) -> dict[str, float]:
    if not isinstance(metrics, dict):
        raise RuntimeError("winner preflight metrics are not an object")
    marker_fields = _winner_preflight_marker_fields(evaluator_kind)
    values = {
        name: _exact_nonnegative_metric(metrics, name)
        for name in marker_fields
    }
    common_valid = (
        values[WINNER_PREFLIGHT_CONTRACT_VERSION_METRIC]
        == WINNER_PREFLIGHT_CONTRACT_VERSION
        and values[WINNER_PREFLIGHT_CONTRACT_ID_METRIC]
        == expected_contract_id
        and values[WINNER_PREFLIGHT_COMPLETE_METRIC] == 1
        and values[WINNER_PREFLIGHT_INCOMPLETE_METRIC] == 0
        and values[WINNER_PREFLIGHT_OMITTED_METRIC] == 0
        and values[WINNER_PREFLIGHT_HARD_TIMEOUT_METRIC] == 0
        and values[WINNER_PREFLIGHT_SUBPROCESS_FAILED_METRIC] == 0
        and values[WINNER_PREFLIGHT_PERSISTED_METRIC]
        == values[WINNER_PREFLIGHT_ELIGIBLE_METRIC]
        and values[WINNER_PREFLIGHT_EVALUATED_METRIC]
        >= values[WINNER_PREFLIGHT_ELIGIBLE_METRIC]
    )
    if evaluator_kind == EVALUATOR_KIND_COSET_TWO_BLOCK:
        expected_units = _coset_action_strata_count()
        unit_valid = (
            values[WINNER_PREFLIGHT_UNIT_KIND_ID_METRIC]
            == WINNER_PREFLIGHT_UNIT_KIND_ACTION_STRATA
            and values[WINNER_PREFLIGHT_UNITS_METRIC] == expected_units
            and values[WINNER_PREFLIGHT_ACTION_STRATA_METRIC]
            == expected_units
            and WINNER_PREFLIGHT_LATTICES_METRIC not in metrics
        )
    else:
        unit_valid = (
            values[WINNER_PREFLIGHT_LATTICES_METRIC]
            == len(EVOLUTION_LATTICES)
            and not any(
                name in metrics
                for name in (
                    WINNER_PREFLIGHT_UNIT_KIND_ID_METRIC,
                    WINNER_PREFLIGHT_UNITS_METRIC,
                    WINNER_PREFLIGHT_ACTION_STRATA_METRIC,
                )
            )
        )
    if not common_valid or not unit_valid:
        raise RuntimeError(
            "winner preflight markers do not prove complete persistence"
        )
    return {name: float(values[name]) for name in values}


def _exact_incomplete_winner_preflight_markers(
    metrics: Any,
    *,
    expected_contract_id: int,
    evaluator_kind: str = EVALUATOR_KIND_DEFAULT,
) -> dict[str, float] | None:
    """Recognize only the evaluator's canonical incomplete-preflight envelope.

    A child with this envelope is a fully observed *failed attempt*, not a
    checkpointable program.  Returning ``None`` is deliberately fail-closed:
    malformed markers, a wrong contract, or an inconsistent claim continue
    through the normal database-add observer and make the whole slice fail.
    """

    marker_fields = _winner_preflight_marker_fields(evaluator_kind)
    expected_fields = _WINNER_PREFLIGHT_FAILURE_BASE_FIELDS.union(
        marker_fields
    )
    if evaluator_kind == EVALUATOR_KIND_COSET_TWO_BLOCK:
        from evolve.coset_search_contract import (
            COSET_PROOF_LADDER_VERSION_METRIC,
        )

        expected_fields = expected_fields.union(
            {COSET_PROOF_LADDER_VERSION_METRIC}
        )
    if (
        not isinstance(metrics, dict)
        or set(metrics) != expected_fields
        or not isinstance(metrics.get("error"), str)
        or not metrics["error"]
    ):
        return None
    for name in (
        "combined_score",
        "lattices_with_high_k",
        MAP_DESCRIPTOR_DOMINANT_SHARE_METRIC,
        MAP_DESCRIPTOR_POOL_SIZE_METRIC,
        MAP_DESCRIPTOR_SUPPORT_SPLIT_METRIC,
        MAP_DESCRIPTOR_STRUCTURAL_ENTROPY_METRIC,
        MAP_DESCRIPTOR_ALGEBRAIC_RELATION_METRIC,
        MAP_DESCRIPTOR_ORBIT_SPAN_METRIC,
        MAP_DESCRIPTOR_DIFFERENCE_SPECTRUM_METRIC,
        "num_high_k",
        "term_count",
        "pattern_type",
        *((SEARCH_PORTFOLIO_V3_GEOMETRY_METRIC,)
          if ACTIVE_GEOMETRY_CONTRACT == TWISTED_TORUS_GEOMETRY_CONTRACT
          else ()),
    ):
        value = metrics.get(name)
        if (
            isinstance(value, bool)
            or not isinstance(value, (int, float))
            or not math.isfinite(float(value))
            or float(value) != 0.0
        ):
            return None
    try:
        _validated_map_descriptor_version(
            metrics,
            label="incomplete winner preflight",
        )
    except RuntimeError:
        return None
    if evaluator_kind == EVALUATOR_KIND_COSET_TWO_BLOCK:
        from evolve.coset_search_contract import (
            COSET_PROOF_LADDER_SCHEMA_VERSION,
            COSET_PROOF_LADDER_VERSION_METRIC,
        )

        proof_marker = metrics.get(COSET_PROOF_LADDER_VERSION_METRIC)
        if (
            isinstance(proof_marker, bool)
            or not isinstance(proof_marker, (int, float))
            or not math.isfinite(float(proof_marker))
            or not float(proof_marker).is_integer()
            or int(proof_marker) != COSET_PROOF_LADDER_SCHEMA_VERSION
        ):
            return None
    try:
        values = {
            name: _exact_nonnegative_metric(metrics, name)
            for name in marker_fields
        }
    except RuntimeError:
        return None
    common_valid = (
        values[WINNER_PREFLIGHT_CONTRACT_VERSION_METRIC]
        == WINNER_PREFLIGHT_CONTRACT_VERSION
        and values[WINNER_PREFLIGHT_CONTRACT_ID_METRIC]
        == expected_contract_id
        and values[WINNER_PREFLIGHT_COMPLETE_METRIC] == 0
        and values[WINNER_PREFLIGHT_INCOMPLETE_METRIC] == 1
        and values[WINNER_PREFLIGHT_EVALUATED_METRIC] == 0
        and values[WINNER_PREFLIGHT_ELIGIBLE_METRIC] == 0
        and values[WINNER_PREFLIGHT_PERSISTED_METRIC] == 0
        and values[WINNER_PREFLIGHT_OMITTED_METRIC] == 0
        and values[WINNER_PREFLIGHT_HARD_TIMEOUT_METRIC] in (0, 1)
        and values[WINNER_PREFLIGHT_SUBPROCESS_FAILED_METRIC] == 1
    )
    if evaluator_kind == EVALUATOR_KIND_COSET_TWO_BLOCK:
        unit_valid = (
            values[WINNER_PREFLIGHT_UNIT_KIND_ID_METRIC]
            == WINNER_PREFLIGHT_UNIT_KIND_ACTION_STRATA
            and values[WINNER_PREFLIGHT_UNITS_METRIC] == 0
            and values[WINNER_PREFLIGHT_ACTION_STRATA_METRIC] == 0
            and WINNER_PREFLIGHT_LATTICES_METRIC not in metrics
        )
    else:
        unit_valid = values[WINNER_PREFLIGHT_LATTICES_METRIC] == 0
    if not common_valid or not unit_valid:
        return None
    return {name: float(values[name]) for name in values}


def _exact_coset_invalid_mutation_evidence(
    metrics: Any,
    artifacts: Any,
    *,
    expected_contract_id: int,
) -> dict[str, Any] | None:
    """Recognize only the typed evaluator's canonical bad-DSL envelope."""

    markers = _exact_incomplete_winner_preflight_markers(
        metrics,
        expected_contract_id=expected_contract_id,
        evaluator_kind=EVALUATOR_KIND_COSET_TWO_BLOCK,
    )
    if (
        markers is None
        or markers[WINNER_PREFLIGHT_HARD_TIMEOUT_METRIC] != 0.0
        or not isinstance(artifacts, dict)
        or set(artifacts) != {"failure_stage", "invalid_mutation"}
        or artifacts.get("failure_stage") != "mutation_preflight"
        or not isinstance(artifacts.get("invalid_mutation"), dict)
    ):
        return None
    invalid = artifacts["invalid_mutation"]
    if set(invalid) != {
        "reason",
        "program_sha256",
        "program_bytes",
        "detail_sha256",
        "error_type",
    }:
        return None
    reason = invalid.get("reason")
    program_sha256 = invalid.get("program_sha256")
    program_bytes = invalid.get("program_bytes")
    detail_sha256 = invalid.get("detail_sha256")
    error_type = invalid.get("error_type")
    valid_program_sha256 = (
        isinstance(program_sha256, str)
        and re.fullmatch(r"[0-9a-f]{64}", program_sha256) is not None
    ) or (program_sha256 is None and reason == "source_too_large")
    if (
        reason not in {"dsl_invalid", "source_too_large"}
        or not valid_program_sha256
        or isinstance(program_bytes, bool)
        or not isinstance(program_bytes, int)
        or program_bytes < 0
        or not isinstance(detail_sha256, str)
        or re.fullmatch(r"[0-9a-f]{64}", detail_sha256) is None
        or error_type != "CosetPolicyError"
    ):
        return None
    try:
        safe_error = json.loads(metrics["error"])
    except (KeyError, TypeError, json.JSONDecodeError):
        return None
    expected_error = {
        "detail_sha256": detail_sha256,
        "error_type": error_type,
        "kind": "qcode-coset-invalid-mutation",
        "program_bytes": program_bytes,
        "program_sha256": program_sha256,
        "reason": reason,
    }
    if (
        safe_error != expected_error
        or metrics["error"]
        != json.dumps(
            expected_error,
            sort_keys=True,
            separators=(",", ":"),
            allow_nan=False,
        )
    ):
        return None
    return dict(invalid)


def _validated_stage2_completion_markers(
    metrics: Any,
    *,
    expected_contract_id: int,
) -> dict[str, float]:
    if not isinstance(metrics, dict):
        raise RuntimeError("Stage 2 metrics are not an object")
    values = {
        name: _exact_nonnegative_metric(metrics, name)
        for name in STAGE2_MARKER_FIELDS
    }
    if (
        values[STAGE2_CONTRACT_VERSION_METRIC]
        != STAGE2_DEEP_CONTRACT_VERSION
        or values[STAGE2_CONTRACT_ID_METRIC] != expected_contract_id
        or values[STAGE2_COMPLETE_METRIC] != 1
        or values[STAGE2_INCOMPLETE_METRIC] != 0
        or values[STAGE2_LATTICES_METRIC]
        != STAGE2_DEEP_LATTICE_COUNT
        or values[STAGE2_HARD_TIMEOUT_METRIC] != 0
        or values[STAGE2_SUBPROCESS_FAILED_METRIC] != 0
    ):
        raise RuntimeError(
            "Stage 2 markers do not prove a complete deep evaluation"
        )
    return {name: float(values[name]) for name in STAGE2_MARKER_FIELDS}


def _exact_incomplete_stage2_markers(
    metrics: Any,
    artifacts: Any,
    *,
    expected_contract_id: int,
    evaluator_kind: str = EVALUATOR_KIND_DEFAULT,
) -> dict[str, float] | None:
    """Recognize only the evaluator's bound Stage 2 failure envelope."""

    if not isinstance(metrics, dict) or not isinstance(artifacts, dict):
        return None
    try:
        _validated_winner_preflight_markers(
            metrics,
            expected_contract_id=expected_contract_id,
            evaluator_kind=evaluator_kind,
        )
        values = {
            name: _exact_nonnegative_metric(metrics, name)
            for name in STAGE2_MARKER_FIELDS
        }
    except RuntimeError:
        return None
    subprocess_error = artifacts.get("stage2_subprocess_error")
    stderr = artifacts.get("stage2_stderr")
    if (
        values[STAGE2_CONTRACT_VERSION_METRIC]
        != STAGE2_DEEP_CONTRACT_VERSION
        or values[STAGE2_CONTRACT_ID_METRIC] != expected_contract_id
        or values[STAGE2_COMPLETE_METRIC] != 0
        or values[STAGE2_INCOMPLETE_METRIC] != 1
        or not (
            0
            <= values[STAGE2_LATTICES_METRIC]
            <= STAGE2_DEEP_LATTICE_COUNT
        )
        or values[STAGE2_HARD_TIMEOUT_METRIC] not in (0, 1)
        or values[STAGE2_SUBPROCESS_FAILED_METRIC] != 1
        or artifacts.get("failure_stage") != "stage2"
        or not isinstance(subprocess_error, str)
        or not subprocess_error
        or stderr is not None and not isinstance(stderr, str)
    ):
        return None
    return {name: float(values[name]) for name in STAGE2_MARKER_FIELDS}


def _validated_managed_stage2_state(
    metrics: Any,
    artifacts: Any = None,
    *,
    expected_contract_id: int,
    cascade_threshold: float | None = None,
) -> str:
    """Validate Stage 2 markers when the cascade emitted them."""

    if not isinstance(metrics, dict):
        raise RuntimeError("managed program metrics are not an object")
    present = {
        name for name in STAGE2_MARKER_FIELDS if name in metrics
    }
    if not present:
        if _pre_marker_stage2_failure_evidence(metrics, artifacts) is not None:
            raise RuntimeError(
                "Stage 2 failed in the OpenEvolve cascade before emitting "
                "the managed completion markers"
            )
        if (
            cascade_threshold is not None
            and any(
                name in metrics
                for name in LEGACY_STAGE2_DEEP_METRIC_FIELDS
            )
        ):
            raise RuntimeError(
                "legacy Stage 2 output has no managed completion markers"
            )
        if _cascade_selects_stage2(metrics, cascade_threshold):
            raise RuntimeError(
                "Stage 2 was selected by the cascade but emitted no managed "
                "completion markers"
            )
        return "not_observed"
    if present != set(STAGE2_MARKER_FIELDS):
        raise RuntimeError("Stage 2 markers are only partially present")
    _validated_stage2_completion_markers(
        metrics,
        expected_contract_id=expected_contract_id,
    )
    return "completed"


def _cascade_selects_stage2(
    metrics: Any,
    threshold: float | None,
) -> bool:
    """Mirror pinned OpenEvolve's Stage 1 cascade decision."""

    if threshold is None:
        return False
    if (
        isinstance(threshold, bool)
        or not isinstance(threshold, (int, float))
        or not math.isfinite(float(threshold))
    ):
        raise RuntimeError("Stage 2 cascade threshold is invalid")
    if not isinstance(metrics, dict) or not metrics:
        return False
    if "combined_score" in metrics:
        score = metrics.get("combined_score")
        if isinstance(score, (int, float)):
            return float(score) >= float(threshold)
    values = [
        float(value)
        for name, value in metrics.items()
        if name != "error" and isinstance(value, (int, float))
    ]
    return bool(values) and sum(values) / len(values) >= float(threshold)


def _exact_pre_marker_stage1_failure_metrics(metrics: Any) -> bool:
    if not isinstance(metrics, dict) or set(metrics) != {
        "stage1_passed",
        "error",
    }:
        return False
    return all(
        not isinstance(metrics.get(name), bool)
        and isinstance(metrics.get(name), (int, float))
        and math.isfinite(float(metrics[name]))
        and float(metrics[name]) == 0.0
        for name in ("stage1_passed", "error")
    )


def _pre_marker_stage1_failure_evidence(
    metrics: Any,
    artifacts: Any,
) -> dict[str, Any] | None:
    """Recognize a coset mutation exception before project markers exist.

    Pinned OpenEvolve catches every exception raised by ``evaluate_stage1``.
    The managed worker records the live exception traceback before it is
    stringified. Only failures whose deepest structured frame is the
    ephemeral evolved program are safe to isolate as a bad mutation. Trusted
    evaluator faults, unauthenticated text-only envelopes, and
    undifferentiated timeouts remain fatal to slice accounting.
    """

    if (
        not _exact_pre_marker_stage1_failure_metrics(metrics)
        or not isinstance(artifacts, dict)
    ):
        return None

    expected_artifact_fields = {
        "cascade_config",
        "cascade_thresholds",
        "error_message",
        "error_type",
        "evaluation_file",
        "failure_stage",
        "stderr",
        "timeout_config",
        "timestamp",
        "traceback",
        STAGE1_EXCEPTION_PROVENANCE_FIELD,
    }
    if set(artifacts) != expected_artifact_fields:
        return None
    error_type = artifacts.get("error_type")
    error_message = artifacts.get("error_message")
    stderr = artifacts.get("stderr")
    traceback_text = artifacts.get("traceback")
    evaluation_file = artifacts.get("evaluation_file")
    timestamp = artifacts.get("timestamp")
    timeout_config = artifacts.get("timeout_config")
    thresholds = artifacts.get("cascade_thresholds")
    provenance = artifacts.get(STAGE1_EXCEPTION_PROVENANCE_FIELD)
    unsafe_message_characters = frozenset(
        "\x00\n\r\v\f\x1c\x1d\x1e\x85\u2028\u2029"
    )
    if (
        artifacts.get("failure_stage") != "stage1"
        or not isinstance(error_type, str)
        or not error_type
        or len(error_type) > 256
        or not error_type.isascii()
        or not error_type.isidentifier()
        or not isinstance(error_message, str)
        or len(error_message) > 4096
        or not isinstance(stderr, str)
        or error_message != stderr
        or any(
            character in unsafe_message_characters
            for character in error_message
        )
        or not isinstance(traceback_text, str)
        or not traceback_text
        or len(traceback_text) > 1_000_000
        or not isinstance(evaluation_file, str)
        or not evaluation_file
        or Path(evaluation_file).resolve()
        != Path(EVALUATOR_COSET_TWO_BLOCK).resolve()
        or artifacts.get("cascade_config") is not True
        or isinstance(timestamp, bool)
        or not isinstance(timestamp, (int, float))
        or not math.isfinite(float(timestamp))
        or float(timestamp) <= 0.0
        or isinstance(timeout_config, bool)
        or not isinstance(timeout_config, (int, float))
        or not math.isfinite(float(timeout_config))
        or float(timeout_config) <= 0.0
        or not isinstance(thresholds, (list, tuple))
        or not thresholds
        or any(
            isinstance(value, bool)
            or not isinstance(value, (int, float))
            or not math.isfinite(float(value))
            for value in thresholds
        )
        or not isinstance(provenance, dict)
        or set(provenance) != {"schema_version", "stage", "frames"}
        or provenance.get("schema_version")
        != STAGE1_EXCEPTION_PROVENANCE_SCHEMA_VERSION
        or provenance.get("stage") != "stage1"
    ):
        return None

    traceback_lines = traceback_text.rstrip().splitlines()
    expected_terminal_error = (
        error_type
        if not error_message
        else f"{error_type}: {error_message}"
    )
    traceback_header_count = traceback_lines.count(
        "Traceback (most recent call last):"
    )
    if (
        not traceback_lines
        or not 1 <= traceback_header_count <= 64
        or traceback_lines[-1] != expected_terminal_error
        or traceback_lines.count(expected_terminal_error) != 1
    ):
        return None
    raw_frames = provenance.get("frames")
    if not isinstance(raw_frames, list) or not 2 <= len(raw_frames) <= 256:
        return None
    frames: list[tuple[Path, str]] = []
    for frame in raw_frames:
        if (
            not isinstance(frame, dict)
            or set(frame) != {"path", "function"}
            or not isinstance(frame.get("path"), str)
            or not frame["path"]
            or len(frame["path"]) > 4096
            or "\x00" in frame["path"]
            or not isinstance(frame.get("function"), str)
            or not frame["function"]
            or len(frame["function"]) > 1024
            or "\x00" in frame["function"]
        ):
            return None
        frames.append((Path(frame["path"]), frame["function"]))
    trusted_evaluator = Path(EVALUATOR_COSET_TWO_BLOCK).resolve()
    last_trusted_frame = max(
        (
            index
            for index, (path, function) in enumerate(frames)
            if path.resolve() == trusted_evaluator and function == "_evaluate"
        ),
        default=-1,
    )
    program_path = frames[-1][0]
    if (
        last_trusted_frame < 0
        or last_trusted_frame >= len(frames) - 1
        or program_path.resolve().parent
        != Path(tempfile.gettempdir()).resolve()
        or program_path.suffix != ".py"
        or not program_path.name.startswith("tmp")
    ):
        return None
    return {"error_type": error_type, "timeout": False}


def _pre_marker_stage2_failure_evidence(
    metrics: Any,
    artifacts: Any = None,
) -> dict[str, bool] | None:
    """Recognize OpenEvolve's own Stage 2 exception/timeout envelope.

    OpenEvolve 0.2.26 catches an exception or its outer ``wait_for`` timeout
    around ``evaluate_stage2``.  In that path it returns the trusted Stage 1
    metrics without our managed Stage 2 markers, then adds
    ``stage2_passed=0`` and/or a Stage 2 failure artifact.  Treating marker
    absence as "Stage 2 was not selected by the cascade" would therefore
    archive a known-incomplete evaluation.
    """

    if not isinstance(metrics, dict):
        return None
    if any(name in metrics for name in STAGE2_MARKER_FIELDS):
        return None
    stage2_passed = metrics.get("stage2_passed")
    stage2_passed_zero = (
        not isinstance(stage2_passed, bool)
        and isinstance(stage2_passed, (int, float))
        and math.isfinite(float(stage2_passed))
        and float(stage2_passed) == 0.0
    )
    timeout = metrics.get("timeout") is True
    artifact_stage2 = (
        isinstance(artifacts, dict)
        and artifacts.get("failure_stage") == "stage2"
    )
    if not (stage2_passed_zero or timeout or artifact_stage2):
        return None
    return {
        "artifact_stage2": artifact_stage2,
        "stage2_passed_zero": stage2_passed_zero,
        "timeout": timeout,
    }


def _checkpoint_preflight_summary(
    checkpoint_path: str | Path,
    *,
    expected_contract_id: int,
    cascade_threshold: float | None = None,
    evaluator_kind: str = EVALUATOR_KIND_DEFAULT,
    coset_map_schema_version: int | None = None,
) -> dict[str, int]:
    programs_dir = Path(checkpoint_path) / "programs"
    if programs_dir.is_symlink() or not programs_dir.is_dir():
        raise RuntimeError(
            f"checkpoint programs directory is missing: {programs_dir}"
        )
    codes: set[str] = set()
    programs = 0
    for path in sorted(programs_dir.glob("*.json")):
        program = _read_json_object(path, "checkpoint program")
        code = program.get("code")
        if not isinstance(code, str) or not code:
            raise RuntimeError(f"checkpoint program has invalid code: {path}")
        if evaluator_kind == EVALUATOR_KIND_COSET_TWO_BLOCK:
            from evolve.coset_policy_dispatch import (
                parse_and_render_registered_policy,
            )

            try:
                rendered = parse_and_render_registered_policy(code)
            except Exception as exc:
                raise RuntimeError(
                    f"result checkpoint contains a non-DSL coset program: {path}"
                ) from exc
            map_schema = rendered.descriptor.map_schema_version
            if (
                coset_map_schema_version is not None
                and map_schema != coset_map_schema_version
            ):
                raise RuntimeError(
                    "result checkpoint renderer epoch is incompatible with "
                    "the selected config"
                )
            expected_genome_format = _coset_genome_format_id_for_schema(
                map_schema
            )
            genome_format = program.get("metrics", {}).get(
                COSET_GENOME_FORMAT_ID_METRIC
            )
            if (
                isinstance(genome_format, bool)
                or not isinstance(genome_format, (int, float))
                or not math.isfinite(float(genome_format))
                or float(genome_format) != expected_genome_format
            ):
                raise RuntimeError(
                    "result checkpoint contains an unmarked coset DSL program: "
                    f"{path}"
                )
            _fixed_coset_feature_coords(
                argparse.Namespace(
                    id=program.get("id", path.stem),
                    metrics=program.get("metrics"),
                ),
                schema_version=map_schema,
            )
        _validated_winner_preflight_markers(
            program.get("metrics"),
            expected_contract_id=expected_contract_id,
            evaluator_kind=evaluator_kind,
        )
        _validated_managed_stage2_state(
            program.get("metrics"),
            expected_contract_id=expected_contract_id,
            cascade_threshold=cascade_threshold,
        )
        _validated_map_descriptor_version(
            program.get("metrics"),
            label=f"checkpoint program {path.name}",
        )
        programs += 1
        codes.add(hashlib.sha256(code.encode("utf-8")).hexdigest())
    if programs < 1:
        raise RuntimeError("result checkpoint contains no preflighted programs")
    return {"programs": programs, "unique_program_codes": len(codes)}


def _validate_managed_initial_evaluation(
    metrics: Any,
    artifacts: Any,
    *,
    expected_contract_id: int,
    cascade_threshold: float | None = None,
    evaluator_kind: str = EVALUATOR_KIND_DEFAULT,
) -> None:
    """Fail before a fresh seed with incomplete evaluation enters the DB."""

    _validated_winner_preflight_markers(
        metrics,
        expected_contract_id=expected_contract_id,
        evaluator_kind=evaluator_kind,
    )
    _validated_map_descriptor_version(
        metrics,
        label="fresh initial program",
    )
    _validated_managed_stage2_state(
        metrics,
        artifacts,
        expected_contract_id=expected_contract_id,
        cascade_threshold=cascade_threshold,
    )


def _validate_loaded_checkpoint_database(
    database: Any,
    checkpoint_path: str | Path,
) -> None:
    """Ensure OpenEvolve did not silently skip a checkpoint Program."""

    programs = getattr(database, "programs", None)
    if not isinstance(programs, dict):
        raise RuntimeError("loaded checkpoint program database is invalid")
    expected: dict[str, str] = {}
    programs_dir = Path(checkpoint_path) / "programs"
    for path in sorted(programs_dir.glob("*.json")):
        row = _read_json_object(path, "checkpoint program")
        program_id = row.get("id")
        code = row.get("code")
        if (
            not isinstance(program_id, str)
            or not program_id
            or program_id in expected
            or not isinstance(code, str)
            or not code
        ):
            raise RuntimeError(
                f"checkpoint program identity is invalid: {path}"
            )
        expected[program_id] = code
    if set(programs) != set(expected):
        raise RuntimeError(
            "OpenEvolve did not load the exact checkpoint program set"
        )
    for program_id, code in expected.items():
        if getattr(programs[program_id], "code", None) != code:
            raise RuntimeError(
                f"OpenEvolve changed checkpoint program code: {program_id}"
            )


def _validate_loaded_checkpoint_stage2_contract(
    database: Any,
    *,
    expected_contract_id: int,
    cascade_threshold: float | None,
) -> None:
    """Reject a pre-managed Stage 2 checkpoint before costly backfill."""

    programs = getattr(database, "programs", None)
    if not isinstance(programs, dict) or not programs:
        raise RuntimeError("loaded checkpoint contains no program database")
    try:
        for program_id in sorted(programs):
            _validated_managed_stage2_state(
                getattr(programs[program_id], "metrics", None),
                expected_contract_id=expected_contract_id,
                cascade_threshold=cascade_threshold,
            )
    except RuntimeError as exc:
        raise RuntimeError(
            "checkpoint predates or violates the managed Stage 2 contract; "
            "start a fresh campaign"
        ) from exc


def _winner_preflight_wall_timeout(configured_timeout: float) -> float:
    if (
        isinstance(configured_timeout, bool)
        or not isinstance(configured_timeout, (int, float))
        or not math.isfinite(float(configured_timeout))
        or configured_timeout <= 60
    ):
        raise RuntimeError(
            "evaluator timeout leaves no winner-preflight wall margin"
        )
    return min(1050.0, float(configured_timeout) - 60.0)


def _winner_preflight_outer_timeout(configured_timeout: float) -> float:
    """Leave OpenEvolve enough total time for progress-bounded lattices."""

    inactivity_timeout = _winner_preflight_wall_timeout(
        configured_timeout
    )
    attempt_timeout = _winner_preflight_attempt_timeout(
        inactivity_timeout
    )
    progress_bounded_total = (
        attempt_timeout * STAGE1_PREFLIGHT_WORKER_ATTEMPTS
        + inactivity_timeout * STAGE1_PREFLIGHT_LOCK_WAIT_INTERVALS
        + STAGE1_PREFLIGHT_OUTER_MARGIN_S
    )
    return max(float(configured_timeout), progress_bounded_total)


def _winner_preflight_attempt_timeout(
    inactivity_timeout: float,
) -> float:
    """Absolute non-resettable wall for one checkpoint preflight child."""

    return (
        inactivity_timeout
        * (
            len(EVOLUTION_LATTICES)
            * STAGE1_PREFLIGHT_MAX_EPOCH_ATTEMPTS
            + 1
        )
    )


def _winner_preflight_progress_path(
    code: str,
    *,
    expected_contract_id: int,
) -> Path | None:
    raw_candidate_log = os.environ.get(CANDIDATE_LOG_PATH_ENV)
    if raw_candidate_log in (None, ""):
        return None
    candidate_log = Path(raw_candidate_log)
    if not candidate_log.is_absolute() or "\x00" in raw_candidate_log:
        raise RuntimeError(
            "winner preflight candidate log binding is invalid"
        )
    source_sha256 = hashlib.sha256(code.encode("utf-8")).hexdigest()
    return (
        candidate_log.resolve(strict=False).parent
        / STAGE1_PREFLIGHT_JOURNAL_DIRECTORY
        / f"{expected_contract_id}-{source_sha256}.json"
    )


def _winner_preflight_progress_snapshot(
    path: Path | None,
    *,
    code: str,
    expected_contract_id: int,
) -> tuple[str, int, int, int, str]:
    if path is None:
        return ("", 0, 0, 0, "unbound")
    if not path.exists():
        return ("", 0, 0, 0, "missing")
    payload = _read_json_object(path, "winner preflight progress journal")
    expected_source = hashlib.sha256(code.encode("utf-8")).hexdigest()
    completed = payload.get("completed_lattices")
    progress = payload.get("progress_sequence")
    status = payload.get("status")
    epoch_id = payload.get("epoch_id")
    restart_count = payload.get("restart_count")
    raw_candidate_log = os.environ.get(CANDIDATE_LOG_PATH_ENV)
    if raw_candidate_log in (None, ""):
        raise RuntimeError(
            "winner preflight candidate log binding disappeared"
        )
    expected_candidate_log = str(
        Path(raw_candidate_log).resolve(strict=False)
    )
    if (
        payload.get("schema_version")
        != STAGE1_PREFLIGHT_JOURNAL_SCHEMA_VERSION
        or payload.get("contract_id") != expected_contract_id
        or payload.get("program_sha256") != expected_source
        or payload.get("candidate_log_path") != expected_candidate_log
        or not isinstance(epoch_id, str)
        or len(epoch_id) != 64
        or any(
            character not in "0123456789abcdef"
            for character in epoch_id
        )
        or type(restart_count) is not int
        or restart_count < 0
        or payload.get("lattices")
        != [list(lattice) for lattice in EVOLUTION_LATTICES]
        or not isinstance(completed, list)
        or len(completed) > len(EVOLUTION_LATTICES)
        or type(progress) is not int
        or progress < len(completed)
        or status not in {"in_progress", "completed"}
        or status == "completed"
        and len(completed) != len(EVOLUTION_LATTICES)
    ):
        raise RuntimeError("winner preflight progress journal is invalid")
    return (epoch_id, restart_count, progress, len(completed), status)


@contextmanager
def _acquire_winner_preflight_lock(
    progress_path: Path | None,
    *,
    code: str,
    expected_contract_id: int,
    wall_timeout: float,
    cancel_event: threading.Event,
):
    """Serialize checkpoint and live preflights with a cancellable wait."""

    if progress_path is None:
        yield
        return
    lock_root = progress_path.parent
    lock_root.mkdir(parents=True, exist_ok=True)
    if lock_root.is_symlink() or not lock_root.is_dir():
        raise RuntimeError(
            f"winner preflight lock root is unsafe: {lock_root}"
        )
    lock_path = progress_path.with_suffix(".lock")
    flags = os.O_RDWR | os.O_CREAT | os.O_CLOEXEC
    if hasattr(os, "O_NOFOLLOW"):
        flags |= os.O_NOFOLLOW
    descriptor = os.open(lock_path, flags, 0o600)
    try:
        if not stat.S_ISREG(os.fstat(descriptor).st_mode):
            raise RuntimeError(
                f"winner preflight lock is not regular: {lock_path}"
            )
        observed = _winner_preflight_progress_snapshot(
            progress_path,
            code=code,
            expected_contract_id=expected_contract_id,
        )
        started = time.monotonic()
        deadline = started + wall_timeout
        absolute_deadline = (
            started
            + wall_timeout * STAGE1_PREFLIGHT_LOCK_WAIT_INTERVALS
        )
        while True:
            if cancel_event.is_set():
                raise RuntimeError(
                    "winner preflight lock wait cancelled after peer failure"
                )
            try:
                fcntl.flock(
                    descriptor,
                    fcntl.LOCK_EX | fcntl.LOCK_NB,
                )
                break
            except BlockingIOError:
                remaining = min(
                    deadline,
                    absolute_deadline,
                ) - time.monotonic()
                if remaining <= 0:
                    raise RuntimeError(
                        "winner preflight lock owner made no durable "
                        "progress before its wall timeout"
                    )
                time.sleep(min(0.25, remaining))
                progress = _winner_preflight_progress_snapshot(
                    progress_path,
                    code=code,
                    expected_contract_id=expected_contract_id,
                )
                if (
                    progress[0] != observed[0]
                    or progress[1] != observed[1]
                    or progress[2] > observed[2]
                    or progress[3] > observed[3]
                    or progress[4] != observed[4]
                ):
                    observed = progress
                    deadline = min(
                        time.monotonic() + wall_timeout,
                        absolute_deadline,
                    )
        yield
    finally:
        try:
            fcntl.flock(descriptor, fcntl.LOCK_UN)
        finally:
            os.close(descriptor)


def _terminate_private_worker_group(process: subprocess.Popen) -> None:
    leader_reaped = False
    try:
        os.killpg(process.pid, signal.SIGTERM)
    except ProcessLookupError:
        process.wait()
        return
    try:
        process.wait(timeout=5)
        leader_reaped = True
    except subprocess.TimeoutExpired:
        pass
    try:
        os.killpg(process.pid, signal.SIGKILL)
    except ProcessLookupError:
        pass
    if not leader_reaped:
        process.wait()


def _preflight_stderr_tail(path: Path, limit: int = 8192) -> str:
    try:
        return path.read_bytes()[-limit:].decode("utf-8", errors="replace")
    except OSError:
        return ""


def _execute_winner_preflight_owned(
    evaluator_path: str | Path,
    code: str,
    *,
    expected_contract_id: int,
    wall_timeout: float,
    cancel_event: threading.Event,
    progress_path: Path | None,
    evaluator_kind: str = EVALUATOR_KIND_DEFAULT,
) -> dict[str, float]:
    """Evaluate one unique checkpoint program behind a progress hard wall."""

    observed_progress = _winner_preflight_progress_snapshot(
        progress_path,
        code=code,
        expected_contract_id=expected_contract_id,
    )
    with tempfile.TemporaryDirectory(prefix="qcode-checkpoint-preflight-") as root:
        temp_root = Path(root)
        program_path = temp_root / "program.py"
        result_path = temp_root / "result.json"
        stdout_path = temp_root / "stdout.log"
        stderr_path = temp_root / "stderr.log"
        program_path.write_text(code)
        lifecycle_read_fd, lifecycle_write_fd = os.pipe()
        command = [
            sys.executable,
            str(Path(evaluator_path).resolve()),
            "--preflight-worker",
            str(program_path.resolve()),
            str(result_path.resolve()),
            str(os.getpid()),
            str(lifecycle_read_fd),
        ]
        environment = os.environ.copy()
        environment[WINNER_PREFLIGHT_CONTRACT_ID_ENV] = str(
            expected_contract_id
        )
        environment.pop("QCODE_WINNER_PREFLIGHT_REUSE", None)
        for variable in WINNER_PREFLIGHT_NUMERIC_THREAD_ENV:
            environment[variable] = "1"
        try:
            with stdout_path.open("wb") as stdout, stderr_path.open(
                "wb"
            ) as stderr:
                try:
                    process = subprocess.Popen(
                        command,
                        stdin=subprocess.DEVNULL,
                        stdout=stdout,
                        stderr=stderr,
                        close_fds=True,
                        env=environment,
                        pass_fds=(lifecycle_read_fd,),
                        start_new_session=True,
                    )
                finally:
                    os.close(lifecycle_read_fd)
                started = time.monotonic()
                deadline = started + wall_timeout
                absolute_deadline = (
                    started
                    + _winner_preflight_attempt_timeout(wall_timeout)
                )
                try:
                    while True:
                        if cancel_event.is_set():
                            _terminate_private_worker_group(process)
                            raise RuntimeError(
                                "winner preflight cancelled after peer failure"
                            )
                        now = time.monotonic()
                        remaining = min(
                            deadline,
                            absolute_deadline,
                        ) - now
                        if remaining <= 0:
                            _terminate_private_worker_group(process)
                            raise _WinnerPreflightTimeout(
                                "winner preflight exceeded its killable "
                                + (
                                    "absolute wall timeout"
                                    if now >= absolute_deadline
                                    else "wall timeout without durable "
                                    "lattice progress"
                                )
                            )
                        try:
                            return_code = process.wait(
                                timeout=min(0.25, remaining)
                            )
                            break
                        except subprocess.TimeoutExpired:
                            progress = _winner_preflight_progress_snapshot(
                                progress_path,
                                code=code,
                                expected_contract_id=expected_contract_id,
                            )
                            if (
                                progress[0] != observed_progress[0]
                                or progress[1] != observed_progress[1]
                                or progress[2] > observed_progress[2]
                                or progress[3] > observed_progress[3]
                                or progress[4] != observed_progress[4]
                            ):
                                observed_progress = progress
                                deadline = min(
                                    time.monotonic() + wall_timeout,
                                    absolute_deadline,
                                )
                            continue
                except BaseException:
                    if process.poll() is None:
                        _terminate_private_worker_group(process)
                    raise
        finally:
            os.close(lifecycle_write_fd)

        if return_code != 0:
            tail = _preflight_stderr_tail(stderr_path)
            suffix = f": {tail}" if tail else ""
            raise _WinnerPreflightChildFailure(
                f"winner preflight subprocess exited with status "
                f"{return_code}{suffix}"
            )
        try:
            payload = json.loads(result_path.read_text())
        except (OSError, UnicodeDecodeError, json.JSONDecodeError) as exc:
            raise _WinnerPreflightChildFailure(
                "winner preflight result is unreadable"
            ) from exc
        expected_payload_fields = (
            {"schema_version", "status", "metrics", "artifacts"}
            if evaluator_kind == EVALUATOR_KIND_COSET_TWO_BLOCK
            else {"schema_version", "status", "metrics"}
        )
        if (
            not isinstance(payload, dict)
            or set(payload) != expected_payload_fields
            or payload.get("schema_version") != 1
            or payload.get("status") != "completed"
            or not isinstance(payload.get("metrics"), dict)
            or (
                evaluator_kind != EVALUATOR_KIND_COSET_TWO_BLOCK
                and set(payload["metrics"])
                != set(_winner_preflight_marker_fields(evaluator_kind))
            )
            or (
                evaluator_kind == EVALUATOR_KIND_COSET_TWO_BLOCK
                and not isinstance(payload.get("artifacts"), dict)
            )
        ):
            raise _WinnerPreflightChildFailure(
                "winner preflight result schema is invalid"
            )
        return _validated_winner_preflight_markers(
            payload["metrics"],
            expected_contract_id=expected_contract_id,
            evaluator_kind=evaluator_kind,
        )


def _execute_winner_preflight(
    evaluator_path: str | Path,
    code: str,
    *,
    expected_contract_id: int,
    wall_timeout: float,
    cancel_event: threading.Event,
    evaluator_kind: str = EVALUATOR_KIND_DEFAULT,
) -> dict[str, float]:
    progress_path = _winner_preflight_progress_path(
        code,
        expected_contract_id=expected_contract_id,
    )
    with _acquire_winner_preflight_lock(
        progress_path,
        code=code,
        expected_contract_id=expected_contract_id,
        wall_timeout=wall_timeout,
        cancel_event=cancel_event,
    ):
        for attempt in range(1, STAGE1_PREFLIGHT_WORKER_ATTEMPTS + 1):
            try:
                return _execute_winner_preflight_owned(
                    evaluator_path,
                    code,
                    expected_contract_id=expected_contract_id,
                    wall_timeout=wall_timeout,
                    cancel_event=cancel_event,
                    progress_path=progress_path,
                    evaluator_kind=evaluator_kind,
                )
            except (
                _WinnerPreflightTimeout,
                _WinnerPreflightChildFailure,
                OSError,
            ):
                if attempt >= STAGE1_PREFLIGHT_WORKER_ATTEMPTS:
                    raise
        raise AssertionError("winner preflight retry loop did not return")


COSET_GENOME_FORMAT_ID_METRIC = "qcode_coset_genome_format_id"
COSET_TYPED_DSL_GENOME_FORMAT_ID = 1.0
COSET_TYPED_DSL_GENOME_FORMAT_ID_V3 = 2.0
COSET_CHECKPOINT_MIGRATION_SCHEMA_VERSION = 1
COSET_ACTIVATION_BRIDGE_LEGACY_SCHEMA_VERSION = 1
COSET_ACTIVATION_BRIDGE_SCHEMA_VERSION = 2


def _coset_portfolio_contract_for_schema(
    schema_version: int,
) -> dict[str, Any]:
    """Resolve a MAP schema through the immutable renderer registry."""

    from evolve.coset_search_contract import (
        coset_renderer_portfolio_contract,
        trusted_coset_renderer_descriptors,
    )

    matches = [
        coset_renderer_portfolio_contract(item.representation_id)
        for item in trusted_coset_renderer_descriptors()
        if item.map_schema_version == schema_version
    ]
    if len(matches) != 1:
        raise RuntimeError(f"unsupported coset MAP schema: {schema_version!r}")
    return matches[0]


def _coset_genome_format_id_for_schema(schema_version: int) -> float:
    if schema_version == 3:
        return COSET_TYPED_DSL_GENOME_FORMAT_ID
    if schema_version == 4:
        return COSET_TYPED_DSL_GENOME_FORMAT_ID_V3
    raise RuntimeError(f"unsupported coset MAP schema: {schema_version!r}")


def _strict_coset_checkpoint_genome_kind(
    database: Any,
    *,
    expected_map_schema_version: int | None = None,
) -> str:
    """Classify a loaded coset population without executing any program.

    A mixed archive is never a legitimate epoch boundary.  In particular, a
    JSON-looking child must not allow neighboring legacy Python to survive the
    one-time migration and later become a sampled parent.
    """

    from evolve.coset_policy_dispatch import (
        CosetPolicyDispatchError,
        parse_and_render_registered_policy,
    )

    programs = getattr(database, "programs", None)
    if not isinstance(programs, dict) or not programs:
        raise RuntimeError("loaded checkpoint contains no coset genomes")
    kinds: set[str] = set()
    for program_id in sorted(programs):
        program = programs[program_id]
        code = getattr(program, "code", None)
        if not isinstance(code, str) or not code:
            raise RuntimeError(
                f"loaded checkpoint program has invalid code: {program_id}"
            )
        marker = getattr(program, "metrics", {}).get(
            COSET_GENOME_FORMAT_ID_METRIC
        )
        marker_is_absent = marker is None
        try:
            rendered = parse_and_render_registered_policy(code)
        except CosetPolicyDispatchError:
            if not marker_is_absent:
                raise RuntimeError(
                    "coset checkpoint has a marked but invalid typed DSL "
                    f"program: {program_id}"
                )
            kinds.add("legacy-python")
        else:
            map_schema = rendered.descriptor.map_schema_version
            expected_marker = _coset_genome_format_id_for_schema(map_schema)
            marker_is_typed = (
                not isinstance(marker, bool)
                and isinstance(marker, (int, float))
                and math.isfinite(float(marker))
                and float(marker) == expected_marker
            )
            if not marker_is_typed:
                raise RuntimeError(
                    "coset checkpoint has an unmarked typed DSL program: "
                    f"{program_id}"
                )
            if (
                expected_map_schema_version is not None
                and map_schema != expected_map_schema_version
            ):
                raise RuntimeError(
                    "coset checkpoint renderer epoch is incompatible with "
                    "the selected config; start a fresh checkpoint"
                )
            kinds.add(f"typed-json-dsl-map-v{map_schema}")
    if len(kinds) != 1:
        raise RuntimeError(
            "coset checkpoint mixes legacy Python or renderer epochs"
        )
    kind = next(iter(kinds))
    return "typed-json-dsl" if kind.startswith("typed-json-dsl-") else kind


def _validate_typed_coset_checkpoint_programs(
    database: Any,
    *,
    expected_map_schema_version: int | None = None,
) -> None:
    """Require every post-migration checkpoint row to be parseable current DSL."""

    from evolve.coset_policy_dispatch import parse_and_render_registered_policy

    programs = getattr(database, "programs", None)
    if not isinstance(programs, dict) or not programs:
        raise RuntimeError("typed coset checkpoint has no programs")
    policy_owners: dict[str, str] = {}
    for program_id in sorted(programs):
        program = programs[program_id]
        try:
            rendered = parse_and_render_registered_policy(program.code)
            digest = rendered.policy_sha256
        except Exception as exc:
            raise RuntimeError(
                f"typed coset checkpoint program is invalid: {program_id}"
            ) from exc
        map_schema = rendered.descriptor.map_schema_version
        if (
            expected_map_schema_version is not None
            and map_schema != expected_map_schema_version
        ):
            raise RuntimeError(
                "typed coset checkpoint renderer epoch is incompatible with "
                "the selected config; start a fresh checkpoint"
            )
        expected_marker = _coset_genome_format_id_for_schema(map_schema)
        value = getattr(program, "metrics", {}).get(
            COSET_GENOME_FORMAT_ID_METRIC
        )
        if (
            isinstance(value, bool)
            or not isinstance(value, (int, float))
            or not math.isfinite(float(value))
            or float(value) != expected_marker
        ):
            raise RuntimeError(
                f"typed coset checkpoint program lacks its genome marker: "
                f"{program_id}"
            )
        previous = policy_owners.get(digest)
        if previous is not None:
            raise RuntimeError(
                "typed coset checkpoint contains duplicate policy genomes: "
                f"{previous}, {program_id}"
            )
        policy_owners[digest] = program_id
        if expected_map_schema_version is not None:
            _fixed_coset_feature_coords(
                program,
                schema_version=expected_map_schema_version,
            )


def _coset_checkpoint_program_set_sha256(database: Any) -> str:
    programs = getattr(database, "programs", None)
    if not isinstance(programs, dict) or not programs:
        raise RuntimeError("coset checkpoint program set is empty")
    rows = []
    for program_id in sorted(programs):
        code = getattr(programs[program_id], "code", None)
        if not isinstance(code, str):
            raise RuntimeError("coset checkpoint program code is invalid")
        rows.append({
            "id": program_id,
            "code_sha256": hashlib.sha256(code.encode("utf-8")).hexdigest(),
        })
    return hashlib.sha256(json.dumps(
        rows,
        sort_keys=True,
        separators=(",", ":"),
        allow_nan=False,
    ).encode("utf-8")).hexdigest()


def _execute_coset_checkpoint_root_evaluation(
    evaluator_path: str | Path,
    code: str,
    *,
    expected_contract_id: int,
    wall_timeout: float,
    expected_map_schema_version: int,
) -> tuple[dict[str, Any], dict[str, Any], dict[str, Any]]:
    """Fully evaluate the canonical DSL root in one killable process group."""

    from evolve.openevolve_evaluator import candidate_log_range_identity

    raw_candidate_log = os.environ.get(CANDIDATE_LOG_PATH_ENV)
    if not isinstance(raw_candidate_log, str) or not raw_candidate_log:
        raise RuntimeError("coset migration has no candidate log binding")
    candidate_log = Path(raw_candidate_log).resolve(strict=False)
    before = candidate_log_range_identity(candidate_log, start_offset=0)
    with tempfile.TemporaryDirectory(prefix="qcode-coset-dsl-root-") as root:
        temp_root = Path(root)
        program_path = temp_root / "policy.json"
        result_path = temp_root / "result.json"
        stdout_path = temp_root / "stdout.log"
        stderr_path = temp_root / "stderr.log"
        program_path.write_text(code, encoding="utf-8")
        lifecycle_read_fd, lifecycle_write_fd = os.pipe()
        command = [
            sys.executable,
            str(Path(evaluator_path).resolve()),
            "--preflight-worker",
            str(program_path.resolve()),
            str(result_path.resolve()),
            str(os.getpid()),
            str(lifecycle_read_fd),
        ]
        environment = os.environ.copy()
        environment[WINNER_PREFLIGHT_CONTRACT_ID_ENV] = str(
            expected_contract_id
        )
        for variable in WINNER_PREFLIGHT_NUMERIC_THREAD_ENV:
            environment[variable] = "1"
        try:
            with stdout_path.open("wb") as stdout, stderr_path.open("wb") as stderr:
                try:
                    process = subprocess.Popen(
                        command,
                        stdin=subprocess.DEVNULL,
                        stdout=stdout,
                        stderr=stderr,
                        close_fds=True,
                        env=environment,
                        pass_fds=(lifecycle_read_fd,),
                        start_new_session=True,
                    )
                finally:
                    os.close(lifecycle_read_fd)
                try:
                    return_code = process.wait(timeout=wall_timeout)
                except subprocess.TimeoutExpired as exc:
                    _terminate_private_worker_group(process)
                    raise RuntimeError(
                        "coset DSL checkpoint root exceeded its hard wall timeout"
                    ) from exc
                except BaseException:
                    if process.poll() is None:
                        _terminate_private_worker_group(process)
                    raise
        finally:
            os.close(lifecycle_write_fd)
        if return_code != 0:
            tail = _preflight_stderr_tail(stderr_path)
            raise RuntimeError(
                "coset DSL checkpoint root evaluator failed"
                + (f": {tail}" if tail else "")
            )
        try:
            payload = json.loads(result_path.read_text(encoding="utf-8"))
        except (OSError, UnicodeDecodeError, json.JSONDecodeError) as exc:
            raise RuntimeError(
                "coset DSL checkpoint root result is unreadable"
            ) from exc
    if (
        not isinstance(payload, dict)
        or set(payload) != {"schema_version", "status", "metrics", "artifacts"}
        or payload.get("schema_version") != 1
        or payload.get("status") != "completed"
        or not isinstance(payload.get("metrics"), dict)
        or not isinstance(payload.get("artifacts"), dict)
    ):
        raise RuntimeError("coset DSL checkpoint root result schema is invalid")
    metrics = dict(payload["metrics"])
    artifacts = dict(payload["artifacts"])
    _validated_winner_preflight_markers(
        metrics,
        expected_contract_id=expected_contract_id,
        evaluator_kind=EVALUATOR_KIND_COSET_TWO_BLOCK,
    )
    _validated_map_descriptor_version(
        metrics, label="coset DSL checkpoint root"
    )
    _checkpoint_evaluator_kind(
        metrics,
        expected_kind=EVALUATOR_KIND_COSET_TWO_BLOCK,
        label="coset DSL checkpoint root",
    )
    if metrics.get(COSET_GENOME_FORMAT_ID_METRIC) != (
        _coset_genome_format_id_for_schema(expected_map_schema_version)
    ):
        raise RuntimeError("coset DSL checkpoint root genome marker is invalid")
    _fixed_coset_feature_coords(
        argparse.Namespace(id="checkpoint-root", metrics=metrics),
        schema_version=expected_map_schema_version,
    )
    after = candidate_log_range_identity(
        candidate_log,
        start_offset=int(before["end_offset"]),
    )
    migration_range = {
        "path": after["path"],
        "start_offset": after["start_offset"],
        "end_offset": after["end_offset"],
        "sha256": after["sha256"],
        "bytes": after["bytes"],
        "wal_clean": after["wal_clean"],
    }
    return metrics, artifacts, migration_range


def _install_coset_checkpoint_dsl_epoch(
    database: Any,
    *,
    source_checkpoint: dict[str, Any],
    evaluator_path: str | Path,
    expected_contract_id: int,
    wall_timeout: float,
    coset_map_schema_version: int | None = None,
    search_portfolio_schema_version: int | None = None,
) -> dict[str, Any]:
    """Atomically replace a sealed legacy population with one trusted DSL root."""

    from openevolve.database import Program

    if _strict_coset_checkpoint_genome_kind(database) != "legacy-python":
        raise RuntimeError("coset DSL epoch migration received a non-legacy archive")
    source_program_set_sha256 = _coset_checkpoint_program_set_sha256(database)
    source_last_iteration = getattr(database, "last_iteration", None)
    if (
        isinstance(source_last_iteration, bool)
        or not isinstance(source_last_iteration, int)
        or source_last_iteration != source_checkpoint.get("last_iteration")
    ):
        raise RuntimeError("coset migration checkpoint iteration is inconsistent")
    source_count = len(database.programs)
    if source_count != source_checkpoint.get("programs"):
        raise RuntimeError("coset migration checkpoint program count changed")

    if (
        coset_map_schema_version is not None
        and search_portfolio_schema_version is not None
        and coset_map_schema_version != search_portfolio_schema_version
    ):
        raise RuntimeError("coset migration schema selectors disagree")
    selected_map_schema = (
        coset_map_schema_version
        if coset_map_schema_version is not None
        else search_portfolio_schema_version
    )
    # Frozen direct callers predate a coset-specific selector and produced the
    # v2 DSL root.  Managed v3 recovery always passes coset_map_schema_version.
    if selected_map_schema is None:
        selected_map_schema = 3
    if selected_map_schema == 3:
        from evolve.coset_policy_dsl import (
            canonical_policy_json,
            default_policy,
            policy_digest,
        )
    elif selected_map_schema == 4:
        from evolve.coset_policy_dsl_v3 import (
            canonical_policy_json,
            default_policy,
            policy_digest,
        )
    else:
        raise RuntimeError(
            "coset DSL migration requires a registered MAP schema"
        )
    policy = default_policy()
    code = canonical_policy_json(policy) + "\n"
    code_sha256 = hashlib.sha256(code.encode("utf-8")).hexdigest()
    root_binding = {
        "schema_version": COSET_CHECKPOINT_MIGRATION_SCHEMA_VERSION,
        "kind": "qcode-coset-checkpoint-dsl-epoch",
        "source_checkpoint_sha256": source_checkpoint["sha256"],
        "source_program_set_sha256": source_program_set_sha256,
        "source_last_iteration": source_last_iteration,
        "policy_sha256": policy_digest(policy),
        "code_sha256": code_sha256,
        "contract_id": expected_contract_id,
    }
    root_id = "coset-dsl-root-" + hashlib.sha256(json.dumps(
        root_binding,
        sort_keys=True,
        separators=(",", ":"),
        allow_nan=False,
    ).encode("utf-8")).hexdigest()[:32]
    metrics, artifacts, migration_range = (
        _execute_coset_checkpoint_root_evaluation(
            evaluator_path,
            code,
            expected_contract_id=expected_contract_id,
            wall_timeout=wall_timeout,
            expected_map_schema_version=selected_map_schema,
        )
    )
    root_artifacts = dict(artifacts)
    root_artifacts["checkpoint_genome_epoch"] = root_binding
    root = Program(
        id=root_id,
        code=code,
        changes_description=(
            "Trusted typed-DSL epoch root installed from sealed checkpoint "
            f"{source_checkpoint['sha256']}."
        ),
        language="json",
        parent_id=None,
        generation=0,
        timestamp=0.0,
        iteration_found=source_last_iteration,
        metrics=metrics,
        metadata={
            "island": 0,
            "checkpoint_genome_epoch": root_binding,
        },
        artifacts_json=json.dumps(
            root_artifacts,
            sort_keys=True,
            separators=(",", ":"),
            allow_nan=False,
        ),
    )

    # The potentially expensive evaluation above has no in-memory side
    # effects.  Install the replacement only after every source, policy,
    # metric, artifact, and candidate-range check has succeeded.
    configured_islands = getattr(
        getattr(database, "config", None), "num_islands", None
    )
    if (
        isinstance(configured_islands, bool)
        or not isinstance(configured_islands, int)
        or configured_islands < 1
    ):
        configured_islands = len(getattr(database, "islands", ()))
    if configured_islands < 1:
        raise RuntimeError("coset checkpoint has no configured island")
    database.programs = {root_id: root}
    database.last_iteration = source_last_iteration
    database.current_island = 0
    database.island_generations = [0] * configured_islands
    database.last_migration_generation = 0
    database.islands = [set() for _ in range(configured_islands)]
    database.islands[0].add(root_id)
    database.island_feature_maps = [
        {} for _ in range(configured_islands)
    ]
    database.archive = {root_id}
    database.best_program_id = root_id
    database.island_best_programs = [root_id] + [None] * (
        configured_islands - 1
    )
    database.feature_stats = {}
    database.diversity_cache = {}
    database.diversity_reference_set = []
    if coset_map_schema_version is not None:
        _rebuild_fixed_coset_feature_maps(
            database,
            schema_version=coset_map_schema_version,
        )
    else:
        coordinate_builder = getattr(
            database, "_calculate_feature_coords", None
        )
        if not callable(coordinate_builder):
            raise RuntimeError(
                "native coset checkpoint database has no feature mapper"
            )
        coordinates = coordinate_builder(root)
        if (
            not isinstance(coordinates, (list, tuple))
            or not coordinates
            or any(
                isinstance(value, bool) or not isinstance(value, int)
                for value in coordinates
            )
        ):
            raise RuntimeError(
                "native coset checkpoint root feature coordinates are invalid"
            )
        database.island_feature_maps[0]["-".join(
            str(value) for value in coordinates
        )] = root_id
    _validate_typed_coset_checkpoint_programs(
        database,
        expected_map_schema_version=coset_map_schema_version,
    )
    return {
        "schema_version": 2,
        "status": "completed",
        "contract_version": WINNER_PREFLIGHT_CONTRACT_VERSION,
        "contract_id": expected_contract_id,
        "mode": "legacy-python-to-typed-json-dsl-root",
        "source_checkpoint": dict(source_checkpoint),
        "source_programs": source_count,
        "source_program_set_sha256": source_program_set_sha256,
        "target_programs": 1,
        "root_program_id": root_id,
        "root_policy_sha256": policy_digest(policy),
        "root_code_sha256": code_sha256,
        "migration_candidate_range": migration_range,
    }


def _install_coset_activation_bridge_epoch(
    database: Any,
    *,
    source_checkpoint: dict[str, Any],
    evaluator_path: str | Path,
    expected_contract_id: int,
    wall_timeout: float,
    cascade_threshold: float | None,
    expected_map_schema_version: int,
    activation_document: dict[str, Any],
) -> dict[str, Any]:
    """Replace an activation-incompatible population with one trusted root.

    The base checkpoint remains immutable.  The replacement exists only in
    the resumed controller's memory until normal slice accounting commits the
    result checkpoint.  Metrics are produced by a fresh, killable evaluator
    run; no fitness or artifacts are copied from an incompatible parent.
    """

    from openevolve.database import Program
    from evolve.coset_policy_dispatch import parse_and_render_activated_policy
    from evolve.coset_policy_dsl_v3 import (
        canonical_policy_json,
        default_policy,
        policy_digest,
    )

    if expected_map_schema_version != 4:
        raise RuntimeError(
            "coset activation bridge requires renderer-v3 MAP schema"
        )
    activation = _validated_coset_activation_document(activation_document)
    if _activation_compatible_coset_program_ids(
        database, activation_document
    ):
        raise RuntimeError(
            "coset activation bridge received a compatible checkpoint"
        )
    source_program_set_sha256 = _coset_checkpoint_program_set_sha256(database)
    source_programs = getattr(database, "programs", None)
    source_last_iteration = getattr(database, "last_iteration", None)
    if (
        not isinstance(source_programs, dict)
        or len(source_programs) != source_checkpoint.get("programs")
        or isinstance(source_last_iteration, bool)
        or not isinstance(source_last_iteration, int)
        or source_last_iteration != source_checkpoint.get("last_iteration")
    ):
        raise RuntimeError("coset activation bridge source changed")

    approved_splits = activation.approved_support_splits
    if not approved_splits:
        raise RuntimeError("coset activation bridge has no approved split")
    # The activation document is registry-ordered and hash-bound. Its first
    # approved split is therefore a deterministic bootstrap root, while the
    # full activation remains authoritative for all subsequent mutations.
    target_split = approved_splits[0]
    multi_split_activation = len(approved_splits) > 1
    policy = default_policy(support_split=target_split)
    code = canonical_policy_json(policy) + "\n"
    rendered = parse_and_render_activated_policy(code, activation)
    if rendered.policy_sha256 != policy_digest(policy):
        raise RuntimeError("coset activation bridge policy identity changed")
    code_sha256 = hashlib.sha256(code.encode("utf-8")).hexdigest()
    root_binding = {
        "schema_version": (
            COSET_ACTIVATION_BRIDGE_SCHEMA_VERSION
            if multi_split_activation
            else COSET_ACTIVATION_BRIDGE_LEGACY_SCHEMA_VERSION
        ),
        "kind": "qcode-coset-activation-bridge-root",
        "source_checkpoint_sha256": source_checkpoint["sha256"],
        "source_program_set_sha256": source_program_set_sha256,
        "source_last_iteration": source_last_iteration,
        "activation_sha256": activation_document["activation_sha256"],
        "policy_sha256": rendered.policy_sha256,
        "code_sha256": code_sha256,
        "contract_id": expected_contract_id,
    }
    if multi_split_activation:
        root_binding["approved_support_splits"] = [
            list(split) for split in approved_splits
        ]
        root_binding["root_support_split"] = list(target_split)
    else:
        root_binding["approved_support_split"] = list(target_split)
    root_id = "coset-activation-root-" + hashlib.sha256(json.dumps(
        root_binding,
        sort_keys=True,
        separators=(",", ":"),
        allow_nan=False,
    ).encode("utf-8")).hexdigest()[:32]
    metrics, artifacts, candidate_range = (
        _execute_coset_checkpoint_root_evaluation(
            evaluator_path,
            code,
            expected_contract_id=expected_contract_id,
            wall_timeout=wall_timeout,
            expected_map_schema_version=expected_map_schema_version,
        )
    )
    _validated_managed_stage2_state(
        metrics,
        artifacts,
        expected_contract_id=expected_contract_id,
        cascade_threshold=cascade_threshold,
    )
    root_artifacts = dict(artifacts)
    root_artifacts["checkpoint_activation_bridge"] = root_binding
    root = Program(
        id=root_id,
        code=code,
        changes_description=(
            "Trusted activation bridge installed from sealed checkpoint "
            f"{source_checkpoint['sha256']}."
        ),
        language="json",
        parent_id=None,
        generation=0,
        timestamp=0.0,
        iteration_found=source_last_iteration,
        metrics=metrics,
        metadata={
            "island": 0,
            "checkpoint_activation_bridge": root_binding,
        },
        artifacts_json=json.dumps(
            root_artifacts,
            sort_keys=True,
            separators=(",", ":"),
            allow_nan=False,
        ),
    )

    configured_islands = getattr(
        getattr(database, "config", None), "num_islands", None
    )
    if (
        isinstance(configured_islands, bool)
        or not isinstance(configured_islands, int)
        or configured_islands < 1
    ):
        configured_islands = len(getattr(database, "islands", ()))
    if configured_islands < 1:
        raise RuntimeError("coset checkpoint has no configured island")

    # Commit the in-memory epoch only after every expensive and semantic
    # check above succeeded.  No old metric survives this replacement.
    database.programs = {root_id: root}
    database.last_iteration = source_last_iteration
    database.current_island = 0
    database.island_generations = [0] * configured_islands
    database.last_migration_generation = 0
    database.islands = [set() for _ in range(configured_islands)]
    database.islands[0].add(root_id)
    database.island_feature_maps = [{} for _ in range(configured_islands)]
    database.archive = {root_id}
    database.best_program_id = root_id
    database.island_best_programs = [root_id] + [None] * (
        configured_islands - 1
    )
    database.feature_stats = {}
    database.diversity_cache = {}
    database.diversity_reference_set = []
    _rebuild_fixed_coset_feature_maps(
        database,
        schema_version=expected_map_schema_version,
        eligible_program_ids={root_id},
    )
    _validate_typed_coset_checkpoint_programs(
        database,
        expected_map_schema_version=expected_map_schema_version,
    )
    if _activation_compatible_coset_program_ids(
        database, activation_document
    ) != (root_id,):
        raise RuntimeError("coset activation bridge root is not executable")
    report = {
        "schema_version": 4 if multi_split_activation else 3,
        "status": "completed",
        "contract_version": WINNER_PREFLIGHT_CONTRACT_VERSION,
        "contract_id": expected_contract_id,
        "mode": "typed-json-dsl-activation-bridge-root",
        "source_checkpoint": dict(source_checkpoint),
        "source_programs": len(source_programs),
        "source_program_set_sha256": source_program_set_sha256,
        "target_programs": 1,
        "root_program_id": root_id,
        "root_policy_sha256": rendered.policy_sha256,
        "root_code_sha256": code_sha256,
        "activation_sha256": activation_document["activation_sha256"],
        "bridge_candidate_range": candidate_range,
    }
    if multi_split_activation:
        report["approved_support_splits"] = [
            list(split) for split in approved_splits
        ]
        report["root_support_split"] = list(target_split)
    else:
        report["approved_support_split"] = list(target_split)
    return report


def _backfill_checkpoint_programs(
    database: Any,
    *,
    evaluator_path: str | Path,
    expected_contract_id: int,
    max_workers: int,
    wall_timeout: float,
    evaluator_kind: str = EVALUATOR_KIND_DEFAULT,
) -> dict[str, Any]:
    """Preflight every unique old checkpoint program before evolution resumes."""

    if (
        isinstance(max_workers, bool)
        or not isinstance(max_workers, int)
        or max_workers < 1
    ):
        raise RuntimeError("winner preflight worker cap must be positive")
    programs = getattr(database, "programs", None)
    if not isinstance(programs, dict) or not programs:
        raise RuntimeError("loaded checkpoint contains no program database")

    groups: dict[tuple[str, str], list[Any]] = {}
    for program_id in sorted(programs):
        program = programs[program_id]
        code = getattr(program, "code", None)
        metrics = getattr(program, "metrics", None)
        if not isinstance(code, str) or not code:
            raise RuntimeError(
                f"loaded checkpoint program has invalid code: {program_id}"
            )
        if not isinstance(metrics, dict):
            raise RuntimeError(
                f"loaded checkpoint program has invalid metrics: {program_id}"
            )
        _validated_map_descriptor_version(
            metrics,
            label=f"loaded checkpoint program {program_id}",
        )
        digest = hashlib.sha256(code.encode("utf-8")).hexdigest()
        groups.setdefault((digest, code), []).append(program)

    pending: list[tuple[tuple[str, str], list[Any]]] = []
    already_complete = 0
    for key, group in sorted(groups.items(), key=lambda item: item[0][0]):
        complete = True
        for program in group:
            try:
                _validated_winner_preflight_markers(
                    program.metrics,
                    expected_contract_id=expected_contract_id,
                    evaluator_kind=evaluator_kind,
                )
            except RuntimeError:
                complete = False
                break
        if complete:
            already_complete += len(group)
        else:
            pending.append((key, group))

    results: dict[tuple[str, str], dict[str, float]] = {}
    cancel_event = threading.Event()
    if pending:
        executor = concurrent.futures.ThreadPoolExecutor(
            max_workers=min(max_workers, len(pending)),
            thread_name_prefix="checkpoint-preflight",
        )
        futures = {
            executor.submit(
                _execute_winner_preflight,
                evaluator_path,
                key[1],
                expected_contract_id=expected_contract_id,
                wall_timeout=wall_timeout,
                cancel_event=cancel_event,
                evaluator_kind=evaluator_kind,
            ): key
            for key, _group in pending
        }
        try:
            for future in concurrent.futures.as_completed(futures):
                results[futures[future]] = future.result()
        except BaseException:
            cancel_event.set()
            for future in futures:
                future.cancel()
            executor.shutdown(wait=True, cancel_futures=True)
            raise
        else:
            executor.shutdown(wait=True)

    # Mutate only after every missing unique source completed.  A failure
    # leaves the loaded in-memory DB untouched; the immutable base checkpoint
    # is never opened for writing in either case.
    updated = 0
    for key, group in pending:
        markers = results[key]
        for program in group:
            metrics = dict(program.metrics)
            metrics.update(markers)
            program.metrics = metrics
            updated += 1

    for program in programs.values():
        _validated_winner_preflight_markers(
            program.metrics,
            expected_contract_id=expected_contract_id,
            evaluator_kind=evaluator_kind,
        )
    return {
        "schema_version": 1,
        "status": "completed",
        "contract_version": WINNER_PREFLIGHT_CONTRACT_VERSION,
        "contract_id": expected_contract_id,
        "programs": len(programs),
        "unique_program_codes": len(groups),
        "programs_already_complete": already_complete,
        "unique_program_codes_evaluated": len(pending),
        "programs_updated": updated,
        "worker_cap": min(max_workers, max(1, len(pending))),
    }


def _strong_checkpoint_descriptor(
    output_dir: str | Path,
    checkpoint: str | Path,
    *,
    expected_iteration: int | None = None,
) -> dict[str, Any]:
    checkpoint_root = (Path(output_dir) / "checkpoints").resolve()
    original = Path(checkpoint)
    if original.is_symlink():
        raise RuntimeError(f"checkpoint may not be a symlink: {original}")
    try:
        resolved = original.resolve(strict=True)
    except OSError as exc:
        raise RuntimeError(f"checkpoint is missing: {original}") from exc
    if not resolved.is_dir() or resolved.parent != checkpoint_root:
        raise RuntimeError(f"checkpoint does not belong to this run: {resolved}")
    prefix = "checkpoint_"
    if not resolved.name.startswith(prefix):
        raise RuntimeError(f"invalid checkpoint directory name: {resolved}")
    try:
        named_iteration = int(resolved.name[len(prefix):])
    except ValueError as exc:
        raise RuntimeError(
            f"invalid checkpoint iteration in path: {resolved}"
        ) from exc

    metadata_path = resolved / "metadata.json"
    best_info_path = resolved / "best_program_info.json"
    programs_dir = resolved / "programs"
    metadata = _read_json_object(metadata_path, "checkpoint metadata")
    best_info = _read_json_object(
        best_info_path, "checkpoint best-program info"
    )
    best_candidates = sorted(resolved.glob("best_program.*"))
    if (
        len(best_candidates) != 1
        or best_candidates[0].suffix not in {".py", ".json"}
    ):
        raise RuntimeError(
            "checkpoint must contain exactly one supported language-specific "
            f"best_program file: {resolved}"
        )
    best_path = best_candidates[0]
    if (
        best_path.is_symlink()
        or not best_path.is_file()
        or best_path.stat().st_size < 1
    ):
        raise RuntimeError(
            f"checkpoint best program is not a non-empty regular file: "
            f"{best_path}"
        )
    if programs_dir.is_symlink() or not programs_dir.is_dir():
        raise RuntimeError(
            f"checkpoint programs directory is missing: {programs_dir}"
        )

    iteration = metadata.get("last_iteration")
    if (
        isinstance(iteration, bool)
        or not isinstance(iteration, int)
        or iteration < 0
    ):
        raise RuntimeError(
            f"checkpoint last_iteration is invalid: "
            f"{metadata_path}: {iteration!r}"
        )
    if iteration != named_iteration:
        raise RuntimeError(
            "checkpoint path/metadata iteration mismatch: "
            f"{named_iteration} != {iteration}"
        )
    if expected_iteration is not None and iteration != expected_iteration:
        raise RuntimeError(
            f"checkpoint iteration mismatch: expected "
            f"{expected_iteration}, got {iteration}"
        )

    archive = metadata.get("archive")
    best_id = metadata.get("best_program_id")
    if (
        not isinstance(archive, list)
        or not archive
        or any(not isinstance(item, str) or not item for item in archive)
        or not isinstance(best_id, str)
        or not best_id
    ):
        raise RuntimeError(
            f"checkpoint archive/best_program_id is incomplete: {metadata_path}"
        )
    if (
        best_info.get("id") != best_id
        or best_info.get("current_iteration") != iteration
    ):
        raise RuntimeError(
            "checkpoint best-program info disagrees with metadata: "
            f"{best_info_path}"
        )

    referenced = set(archive)
    referenced.add(best_id)

    def add_optional_reference(value: Any, label: str) -> None:
        if value in (None, ""):
            return
        if not isinstance(value, str):
            raise RuntimeError(
                f"checkpoint {label} contains a non-string program id"
            )
        referenced.add(value)

    islands = metadata.get("islands", [])
    if not isinstance(islands, list) or any(
        not isinstance(island, list) for island in islands
    ):
        raise RuntimeError("checkpoint islands metadata is invalid")
    for island in islands:
        for program_id in island:
            add_optional_reference(program_id, "islands")
    island_best = metadata.get("island_best_programs", [])
    if not isinstance(island_best, list):
        raise RuntimeError(
            "checkpoint island_best_programs metadata is invalid"
        )
    for program_id in island_best:
        add_optional_reference(program_id, "island_best_programs")
    feature_maps = metadata.get("island_feature_maps", [])
    if not isinstance(feature_maps, list) or any(
        not isinstance(feature_map, dict) for feature_map in feature_maps
    ):
        raise RuntimeError(
            "checkpoint island_feature_maps metadata is invalid"
        )
    for feature_map in feature_maps:
        for program_id in feature_map.values():
            add_optional_reference(program_id, "island_feature_maps")

    program_files = sorted(programs_dir.glob("*.json"))
    if not program_files:
        raise RuntimeError(
            f"checkpoint contains no programs: {programs_dir}"
        )
    program_ids: set[str] = set()
    best_program_code: str | None = None
    file_hashes: dict[str, str] = {
        "metadata.json": _file_sha256(metadata_path),
        best_path.name: _file_sha256(best_path),
        "best_program_info.json": _file_sha256(best_info_path),
    }
    for program_path in program_files:
        program = _read_json_object(program_path, "checkpoint program")
        program_id = program.get("id")
        if program_id != program_path.stem:
            raise RuntimeError(
                f"checkpoint program id/path mismatch: {program_path}"
            )
        code = program.get("code")
        metrics = program.get("metrics")
        if not isinstance(code, str) or not code:
            raise RuntimeError(
                f"checkpoint program has no non-empty code: {program_path}"
            )
        if not isinstance(metrics, dict):
            raise RuntimeError(
                f"checkpoint program metrics is not an object: {program_path}"
            )
        program_ids.add(program_id)
        if program_id == best_id:
            best_program_code = code
        file_hashes[f"programs/{program_path.name}"] = _file_sha256(
            program_path
        )
    missing = sorted(referenced - program_ids)
    if missing:
        raise RuntimeError(
            "checkpoint is missing referenced programs: "
            + ", ".join(missing)
        )
    if (
        best_program_code is None
        or best_path.read_text() != best_program_code
    ):
        raise RuntimeError(
            f"checkpoint {best_path.name} does not match the stored "
            "best program code"
        )
    checkpoint_hash = hashlib.sha256(
        json.dumps(
            file_hashes, sort_keys=True, separators=(",", ":")
        ).encode()
    ).hexdigest()
    return {
        "path": str(resolved),
        "last_iteration": iteration,
        "sha256": checkpoint_hash,
        "programs": len(program_files),
    }


def _checkpoint_last_iteration(checkpoint: str | Path | None) -> int:
    if checkpoint is None:
        return 0
    checkpoint_path = Path(checkpoint)
    output_dir = checkpoint_path.parent.parent
    return int(
        _strong_checkpoint_descriptor(output_dir, checkpoint_path)["last_iteration"]
    )


def _atomic_write_json_artifact(path: Path, payload: dict[str, Any]) -> None:
    path.parent.mkdir(parents=True, exist_ok=True)
    temporary_descriptor, temporary_name = tempfile.mkstemp(
        prefix=f".{path.name}.tmp-", dir=path.parent
    )
    temporary = Path(temporary_name)
    encoded = (json.dumps(payload, sort_keys=True, indent=2) + "\n").encode()
    try:
        with os.fdopen(temporary_descriptor, "wb") as stream:
            stream.write(encoded)
            stream.flush()
            os.fsync(stream.fileno())
        temporary.replace(path)
        descriptor = os.open(
            path.parent, os.O_RDONLY | getattr(os, "O_DIRECTORY", 0)
        )
        try:
            os.fsync(descriptor)
        finally:
            os.close(descriptor)
    finally:
        try:
            temporary.unlink()
        except FileNotFoundError:
            pass


def _slice_iterations_sha256(start_iteration: int, count: int) -> str:
    iterations = list(range(start_iteration, start_iteration + count))
    encoded = json.dumps(iterations, separators=(",", ":")).encode("utf-8")
    return hashlib.sha256(encoded).hexdigest()


def _validate_lifecycle_lease(fd: int, path_value: str) -> Path:
    if isinstance(fd, bool) or not isinstance(fd, int) or fd < 0:
        raise RuntimeError("lifecycle lease fd must be a non-negative integer")
    path = Path(path_value)
    if not path.is_absolute():
        raise RuntimeError("lifecycle lease path must be absolute")
    if path.is_symlink():
        raise RuntimeError(f"lifecycle lease may not be a symlink: {path}")
    try:
        resolved = path.resolve(strict=True)
        descriptor_stat = os.fstat(fd)
        path_stat = os.stat(path, follow_symlinks=False)
    except OSError as exc:
        raise RuntimeError(f"cannot validate lifecycle lease: {path}: {exc}") from exc
    if resolved != path:
        raise RuntimeError(
            f"lifecycle lease path must be canonical and symlink-free: {path}"
        )
    if not stat.S_ISREG(descriptor_stat.st_mode) or not stat.S_ISREG(path_stat.st_mode):
        raise RuntimeError("lifecycle lease must be a regular file")
    if (descriptor_stat.st_dev, descriptor_stat.st_ino) != (
        path_stat.st_dev,
        path_stat.st_ino,
    ):
        raise RuntimeError("lifecycle lease path does not match inherited fd")
    nofollow = getattr(os, "O_NOFOLLOW", None)
    if nofollow is None:
        raise RuntimeError("O_NOFOLLOW is required for lifecycle leases")
    probe_fd = os.open(path, os.O_RDWR | nofollow | getattr(os, "O_CLOEXEC", 0))
    try:
        try:
            fcntl.flock(probe_fd, fcntl.LOCK_EX | fcntl.LOCK_NB)
        except BlockingIOError:
            pass
        else:
            fcntl.flock(probe_fd, fcntl.LOCK_UN)
            raise RuntimeError("lifecycle lease was not locked before inheritance")
    finally:
        os.close(probe_fd)
    fcntl.flock(fd, fcntl.LOCK_EX | fcntl.LOCK_NB)
    os.set_inheritable(fd, False)
    return path


def _search_portfolio_spec(
    schema_version: int,
) -> tuple[tuple[str, ...], dict[str, int]]:
    try:
        return SEARCH_PORTFOLIO_SPECS[schema_version]
    except (KeyError, TypeError) as exc:
        raise RuntimeError(
            f"unsupported search portfolio schema: {schema_version!r}"
        ) from exc


def _validated_search_portfolio_config(
    config: Any,
    schema_version: int = SEARCH_PORTFOLIO_SCHEMA_VERSION,
) -> int:
    """Validate the fixed five-island mechanism-aware search geometry.

    OpenEvolve normally rescales every custom MAP dimension from the values
    observed so far.  That makes a checkpoint's cells depend on evaluation
    completion order.  The managed ansatz campaign instead has a versioned,
    categorical grid; accepting any other shape would silently mix archives.
    """

    dimensions_contract, bins_contract = _search_portfolio_spec(
        schema_version
    )
    database = getattr(config, "database", None)
    if database is None:
        raise RuntimeError("search portfolio config has no database section")
    if getattr(database, "num_islands", None) != SEARCH_PORTFOLIO_ISLAND_COUNT:
        raise RuntimeError(
            "search portfolio requires exactly five islands"
        )
    dimensions = getattr(database, "feature_dimensions", None)
    if (
        not isinstance(dimensions, list)
        or dimensions != list(dimensions_contract)
    ):
        raise RuntimeError(
            "search portfolio feature_dimensions must be the fixed "
            f"schema-v{schema_version} categorical tuple"
        )
    bins = getattr(database, "feature_bins", None)
    if (
        not isinstance(bins, dict)
        or set(bins) != set(bins_contract)
        or any(
            isinstance(bins[name], bool)
            or not isinstance(bins[name], int)
            or bins[name] != expected
            for name, expected in bins_contract.items()
        )
    ):
        raise RuntimeError(
            "search portfolio feature_bins must be exactly 5/6/3"
        )
    seed = getattr(config, "random_seed", None)
    if isinstance(seed, bool) or not isinstance(seed, int):
        raise RuntimeError(
            "search portfolio requires an integer config random_seed"
        )
    return seed


def _search_portfolio_schema_version(
    config_path: str | Path,
) -> int | None:
    """Return the explicitly selected fixed-portfolio schema, if any."""

    path = Path(config_path)
    try:
        value = yaml.safe_load(path.read_text())
    except (OSError, UnicodeError, yaml.YAMLError) as exc:
        raise RuntimeError(
            f"cannot inspect search portfolio config: {path}: {exc}"
        ) from exc
    if not isinstance(value, dict):
        raise RuntimeError("evolution config must contain a YAML object")
    if SEARCH_PORTFOLIO_CONFIG_KEY not in value:
        return None
    marker = value[SEARCH_PORTFOLIO_CONFIG_KEY]
    if (
        not isinstance(marker, dict)
        or set(marker) != {"enabled", "schema_version"}
        or marker["enabled"] is not True
        or type(marker["schema_version"]) is not int
        or marker["schema_version"] not in SEARCH_PORTFOLIO_SPECS
    ):
        raise RuntimeError(
            "qcode_search_portfolio marker must be exactly "
            "{enabled: true, schema_version: 2|3}"
        )
    return int(marker["schema_version"])


def _search_portfolio_requested(config_path: str | Path) -> bool:
    """Return whether a YAML config opts into any supported portfolio."""

    return _search_portfolio_schema_version(config_path) is not None


def _coset_search_portfolio_schema_version(
    config_path: str | Path,
) -> int | None:
    """Return the explicitly selected fixed coset MAP schema, if present."""

    from evolve.coset_search_contract import (
        COSET_PROOF_LADDER_CONFIG_KEY,
        coset_renderer_portfolio_contract,
        proof_ladder_config_contract,
    )

    path = Path(config_path)
    try:
        value = yaml.safe_load(path.read_text())
    except (OSError, UnicodeError, yaml.YAMLError) as exc:
        raise RuntimeError(
            f"cannot inspect coset search portfolio config: {path}: {exc}"
        ) from exc
    if not isinstance(value, dict):
        raise RuntimeError("evolution config must contain a YAML object")
    if COSET_SEARCH_PORTFOLIO_CONFIG_KEY not in value:
        return None
    marker = value[COSET_SEARCH_PORTFOLIO_CONFIG_KEY]
    if type(marker) is not dict or set(marker) != {
        "enabled",
        "schema_version",
        "representation_id",
        "checkpoint_compatibility_group",
    }:
        raise RuntimeError(
            "qcode_coset_search_portfolio fields are not exact"
        )
    representation_id = marker.get("representation_id")
    if type(representation_id) is not str:
        raise RuntimeError("coset portfolio representation_id is invalid")
    try:
        contract = coset_renderer_portfolio_contract(representation_id)
    except (TypeError, ValueError) as exc:
        raise RuntimeError(
            "coset portfolio representation is not registered"
        ) from exc
    expected = {
        "enabled": True,
        "schema_version": contract["map_schema_version"],
        "representation_id": contract["representation_id"],
        "checkpoint_compatibility_group": contract[
            "checkpoint_compatibility_group"
        ],
    }
    if type(marker) is not dict or marker != expected:
        raise RuntimeError(
            "qcode_coset_search_portfolio must exactly select the current "
            "representation, descriptor schema, and compatibility group"
        )
    if value.get(COSET_PROOF_LADDER_CONFIG_KEY) != (
        proof_ladder_config_contract()
    ):
        raise RuntimeError(
            "qcode_coset_stage1_proof_ladder must exactly match the current "
            "proof ladder and budget contract"
        )
    return int(contract["map_schema_version"])


def _validated_coset_search_portfolio_config(
    config: Any,
    schema_version: int,
) -> int:
    """Validate the categorical geometry registered for this renderer epoch."""

    contract = _coset_portfolio_contract_for_schema(schema_version)
    database = getattr(config, "database", None)
    if database is None:
        raise RuntimeError("coset search portfolio has no database section")
    if getattr(database, "num_islands", None) != contract["num_islands"]:
        raise RuntimeError(
            "coset search portfolio island count disagrees with its renderer"
        )
    if getattr(database, "feature_dimensions", None) != list(
        contract["feature_dimensions"]
    ):
        raise RuntimeError(
            "coset feature_dimensions do not match the descriptor schema"
        )
    if getattr(database, "feature_bins", None) != dict(
        contract["feature_bins"]
    ):
        raise RuntimeError(
            "coset feature_bins do not match the descriptor schema"
        )
    seed = getattr(config, "random_seed", None)
    if isinstance(seed, bool) or not isinstance(seed, int):
        raise RuntimeError("coset search portfolio requires an integer random_seed")
    return seed


def _validated_search_geometry_contract(
    portfolio_schema_version: int | None,
) -> str | None:
    """Bind the portfolio schema to the contract selected before import.

    The twisted evaluator imports its lattice/deep-marker constants at module
    load time, so setting an environment variable after this point would be
    too late.  Fail closed if a direct or managed launcher pairs schema v3
    with the rectangular default, or injects the twisted contract into a
    schema-v2/ordinary campaign.  Legacy witnesses retain their old byte
    shape by returning ``None``.
    """

    if portfolio_schema_version == SEARCH_PORTFOLIO_V3_SCHEMA_VERSION:
        if ACTIVE_GEOMETRY_CONTRACT != TWISTED_TORUS_GEOMETRY_CONTRACT:
            raise RuntimeError(
                "search portfolio schema v3 requires the launch-bound "
                f"{SEARCH_GEOMETRY_CONTRACT_ENV}="
                f"{TWISTED_TORUS_GEOMETRY_CONTRACT} before runner import"
            )
        return TWISTED_TORUS_GEOMETRY_CONTRACT
    if ACTIVE_GEOMETRY_CONTRACT != LEGACY_GEOMETRY_CONTRACT:
        raise RuntimeError(
            "the twisted-torus geometry contract requires search portfolio "
            "schema v3"
        )
    return None


def _validated_adaptive_mutation_policy(
    humanize_context: str | None,
) -> dict[str, int]:
    """Read the one optional, canonical Humanize policy line.

    The right hand side is an exact JSON object whose keys are the fixed
    tactic vocabulary and whose values are non-negative integer weights.
    A malformed marker is not treated as absence: managed search fails closed
    so reviewer intent cannot be silently ignored.
    """

    text = humanize_context or ""
    marker = ADAPTIVE_MUTATION_POLICY_PREFIX[:-1]
    lines: list[str] = []
    for line in text.splitlines():
        if marker not in line:
            continue
        if not line.startswith(ADAPTIVE_MUTATION_POLICY_PREFIX):
            raise RuntimeError(
                "adaptive mutation policy marker must start a line exactly"
            )
        lines.append(line[len(ADAPTIVE_MUTATION_POLICY_PREFIX):])
    if not lines:
        return dict(DEFAULT_ADAPTIVE_MUTATION_POLICY)
    if len(lines) != 1:
        raise RuntimeError(
            "humanize context contains more than one adaptive mutation policy"
        )
    def reject_constant(value: str) -> None:
        raise ValueError(f"non-finite JSON number: {value}")

    def reject_duplicates(pairs: list[tuple[str, Any]]) -> dict[str, Any]:
        result: dict[str, Any] = {}
        for key, item in pairs:
            if key in result:
                raise ValueError(f"duplicate JSON key: {key}")
            result[key] = item
        return result

    try:
        value = json.loads(
            lines[0],
            parse_constant=reject_constant,
            object_pairs_hook=reject_duplicates,
        )
    except (TypeError, json.JSONDecodeError, ValueError) as exc:
        raise RuntimeError("adaptive mutation policy is not valid JSON") from exc
    if (
        not isinstance(value, dict)
        or set(value) != set(ADAPTIVE_MUTATION_TACTICS)
        or any(
            isinstance(value[name], bool)
            or not isinstance(value[name], int)
            or value[name] < 0
            for name in ADAPTIVE_MUTATION_TACTICS
        )
        or sum(value.values()) != ADAPTIVE_MUTATION_TOTAL_WEIGHT
        or value["novel_structure_exploration"]
        < ADAPTIVE_MUTATION_EXPLORATION_FLOOR
    ):
        raise RuntimeError(
            "adaptive mutation policy must contain the exact tactic "
            "vocabulary, total weight 1000, and exploration floor 250"
        )
    canonical = json.dumps(
        value,
        sort_keys=True,
        separators=(",", ":"),
        allow_nan=False,
    )
    if lines[0] != canonical:
        raise RuntimeError(
            "adaptive mutation policy must use canonical compact JSON"
        )
    return {name: value[name] for name in ADAPTIVE_MUTATION_TACTICS}


def _adaptive_mutation_policy_sha256(policy: dict[str, int]) -> str:
    encoded = json.dumps(
        policy,
        sort_keys=True,
        separators=(",", ":"),
        allow_nan=False,
    ).encode("utf-8")
    return hashlib.sha256(encoded).hexdigest()


def _validated_search_regime(
    humanize_context: str | None,
) -> dict[str, Any]:
    """Read the optional machine-authored mechanism search regime marker."""

    text = humanize_context or ""
    marker_specs = tuple(
        (version, prefix, prefix[:-1])
        for version, prefix in SEARCH_REGIME_PREFIX_BY_POLICY_VERSION.items()
    )
    lines: list[tuple[int, str]] = []
    for line in text.splitlines():
        mentioned = [
            (version, prefix)
            for version, prefix, token in marker_specs
            if token in line
        ]
        if not mentioned:
            continue
        exact = [
            (version, prefix)
            for version, prefix in mentioned
            if line.startswith(prefix)
        ]
        if len(mentioned) != 1 or len(exact) != 1:
            raise RuntimeError(
                "search regime marker must start a line exactly"
            )
        version, prefix = exact[0]
        lines.append((version, line[len(prefix):]))
    if not lines:
        return dict(DEFAULT_SEARCH_REGIME)
    if len(lines) != 1 or len(lines[0][1]) > 16_384:
        raise RuntimeError("humanize context has an invalid search regime marker")

    def reject_constant(value: str) -> None:
        raise ValueError(f"non-finite JSON number: {value}")

    def reject_duplicates(pairs: list[tuple[str, Any]]) -> dict[str, Any]:
        result: dict[str, Any] = {}
        for key, item in pairs:
            if key in result:
                raise ValueError(f"duplicate JSON key: {key}")
            result[key] = item
        return result

    policy_version, encoded = lines[0]
    try:
        value = json.loads(
            encoded,
            parse_constant=reject_constant,
            object_pairs_hook=reject_duplicates,
        )
    except (TypeError, json.JSONDecodeError, ValueError) as exc:
        raise RuntimeError("search regime marker is not valid JSON") from exc
    if (
        not isinstance(value, dict)
        or value.get("schema_version") != 1
        or value.get("status") not in (
            SEARCH_REGIME_V1_STATUSES
            if policy_version == 1
            else SEARCH_REGIME_V2_STATUSES
        )
    ):
        raise RuntimeError("search regime marker has an unsupported schema/status")
    canonical = json.dumps(
        value,
        sort_keys=True,
        separators=(",", ":"),
        allow_nan=False,
    )
    if encoded != canonical:
        raise RuntimeError("search regime marker must use canonical compact JSON")
    if policy_version == 1:
        return value
    if "policy_version" in value:
        raise RuntimeError(
            "versioned search regime marker must encode its version in the prefix"
        )
    return {**value, "policy_version": policy_version}


def _search_island_schedule(
    iterations: int,
    regime_status: str,
) -> tuple[int, ...]:
    """Return a deterministic per-slice mechanism quota schedule.

    Normal/exploit slices remain balanced. Family expansion keeps every
    mechanism at four or more trials in a production 25-iteration slice while
    giving restart eight. Representation change keeps three trials in each
    mechanism lane and gives the restart lane thirteen.
    """

    if (
        isinstance(iterations, bool)
        or not isinstance(iterations, int)
        or iterations < 1
        or regime_status not in SEARCH_REGIME_STATUSES
    ):
        raise RuntimeError("search island schedule inputs are invalid")
    counts = [iterations // SEARCH_PORTFOLIO_ISLAND_COUNT] * (
        SEARCH_PORTFOLIO_ISLAND_COUNT
    )
    for island in range(iterations % SEARCH_PORTFOLIO_ISLAND_COUNT):
        counts[island] += 1
    order = list(range(SEARCH_PORTFOLIO_ISLAND_COUNT))
    if regime_status == "representation_change_required" and iterations >= 5:
        minimum = max(1, min(3, iterations // 8))
        counts = [minimum] * (SEARCH_PORTFOLIO_ISLAND_COUNT - 1)
        counts.append(iterations - sum(counts))
        order = [4, 0, 1, 2, 3]
    elif regime_status == "expand_required" and iterations >= 10:
        minimum = 2
        counts = [minimum] * SEARCH_PORTFOLIO_ISLAND_COUNT
        remaining = iterations - minimum * SEARCH_PORTFOLIO_ISLAND_COUNT
        restart_target = min(
            iterations - minimum * (SEARCH_PORTFOLIO_ISLAND_COUNT - 1),
            max(minimum, round(iterations * 0.32)),
        )
        restart_extra = min(remaining, restart_target - minimum)
        counts[-1] += restart_extra
        remaining -= restart_extra
        mechanism_order = (0, 2, 1, 3)
        for index in range(remaining):
            counts[mechanism_order[index % len(mechanism_order)]] += 1
        order = [4, 0, 2, 1, 3]

    schedule: list[int] = []
    left = list(counts)
    while len(schedule) < iterations:
        for island in order:
            if left[island] <= 0:
                continue
            schedule.append(island)
            left[island] -= 1
    if len(schedule) != iterations or any(left):
        raise RuntimeError("search island schedule construction was inconsistent")
    return tuple(schedule)


def _adaptive_mutation_tactic(
    policy: dict[str, int],
    *,
    program_code: str,
    iteration: int,
) -> str:
    if not isinstance(program_code, str):
        raise RuntimeError("adaptive mutation parent code is not text")
    if isinstance(iteration, bool) or not isinstance(iteration, int):
        raise RuntimeError("adaptive mutation iteration is not an integer")
    policy_sha256 = _adaptive_mutation_policy_sha256(policy)
    code_sha256 = hashlib.sha256(program_code.encode("utf-8")).hexdigest()
    digest = hashlib.sha256(
        (
            policy_sha256
            + "\0"
            + code_sha256
            + "\0"
            + str(iteration)
        ).encode("ascii")
    ).digest()
    draw = int.from_bytes(digest, "big") % sum(policy.values())
    for tactic in ADAPTIVE_MUTATION_TACTICS:
        weight = policy[tactic]
        if draw < weight:
            return tactic
        draw -= weight
    raise RuntimeError("adaptive mutation policy selection was inconsistent")


def _fixed_search_feature_coords(
    program: Any,
    schema_version: int = SEARCH_PORTFOLIO_SCHEMA_VERSION,
) -> list[int]:
    metrics = getattr(program, "metrics", None)
    _validated_map_descriptor_version(
        metrics, label=f"search portfolio program {getattr(program, 'id', '?')}"
    )
    assert isinstance(metrics, dict)
    dimensions, bins = _search_portfolio_spec(schema_version)
    categories: list[int] = []
    for name in dimensions:
        value = metrics.get(name)
        limit = bins[name]
        if (
            isinstance(value, bool)
            or not isinstance(value, (int, float))
            or not math.isfinite(float(value))
            or not float(value).is_integer()
            or not 0 <= int(value) < limit
        ):
            raise RuntimeError(
                f"search portfolio metric {name} is not a fixed category"
            )
        categories.append(int(value))
    return categories


def _fixed_coset_feature_coords(
    program: Any,
    schema_version: int,
) -> list[int]:
    """Map coset categorical metrics directly, without dynamic min/max."""

    from evolve.coset_search_contract import (
        COSET_MAP_SCHEMA_METRIC,
        COSET_PROOF_LADDER_SCHEMA_VERSION,
        COSET_PROOF_LADDER_VERSION_METRIC,
    )

    contract = _coset_portfolio_contract_for_schema(schema_version)
    metrics = getattr(program, "metrics", None)
    _validated_map_descriptor_version(
        metrics, label=f"coset MAP program {getattr(program, 'id', '?')}"
    )
    assert isinstance(metrics, dict)
    marker = metrics.get(COSET_MAP_SCHEMA_METRIC)
    if (
        isinstance(marker, bool)
        or not isinstance(marker, (int, float))
        or not math.isfinite(float(marker))
        or not float(marker).is_integer()
        or int(marker) != schema_version
    ):
        raise RuntimeError("coset program MAP schema marker is incompatible")
    proof_marker = metrics.get(COSET_PROOF_LADDER_VERSION_METRIC)
    if (
        isinstance(proof_marker, bool)
        or not isinstance(proof_marker, (int, float))
        or not math.isfinite(float(proof_marker))
        or not float(proof_marker).is_integer()
        or int(proof_marker) != COSET_PROOF_LADDER_SCHEMA_VERSION
    ):
        raise RuntimeError(
            "coset program proof-ladder contract is incompatible; "
            "start a fresh checkpoint"
        )
    coordinates: list[int] = []
    for name in contract["feature_dimensions"]:
        value = metrics.get(name)
        limit = contract["feature_bins"][name]
        if (
            isinstance(value, bool)
            or not isinstance(value, (int, float))
            or not math.isfinite(float(value))
            or not float(value).is_integer()
            or not 0 <= int(value) < limit
        ):
            raise RuntimeError(
                f"coset MAP metric {name} is not a fixed category"
            )
        coordinates.append(int(value))
    return coordinates


def _activation_compatible_coset_program_ids(
    database: Any,
    activation_document: dict[str, Any] | None,
) -> tuple[str, ...]:
    """Return only typed policies executable under the sealed activation."""

    from evolve.coset_policy_dispatch import (
        parse_and_render_activated_policy,
        parse_and_render_registered_policy,
    )

    programs = getattr(database, "programs", None)
    if not isinstance(programs, dict):
        raise RuntimeError("coset checkpoint program database is invalid")
    activation = (
        None
        if activation_document is None
        else _validated_coset_activation_document(activation_document)
    )
    compatible: list[tuple[str, str]] = []
    policy_owners: dict[str, str] = {}
    for program_id in sorted(programs):
        program = programs[program_id]
        code = getattr(program, "code", None)
        if not isinstance(program_id, str) or not isinstance(code, str):
            raise RuntimeError("coset checkpoint program identity is invalid")
        try:
            rendered = (
                parse_and_render_registered_policy(code)
                if activation is None
                else parse_and_render_activated_policy(code, activation)
            )
        except (TypeError, ValueError):
            # A registered policy from an older reviewer activation remains
            # immutable history, but is not an executable parent in this
            # slice.
            continue
        previous = policy_owners.get(rendered.policy_sha256)
        if previous is not None:
            raise RuntimeError(
                "activation-compatible coset policies are duplicated: "
                f"{previous}, {program_id}"
            )
        policy_owners[rendered.policy_sha256] = program_id
        compatible.append((rendered.policy_sha256, program_id))
    return tuple(
        program_id for _policy_sha256, program_id in sorted(compatible)
    )


def _rebuild_fixed_coset_feature_maps(
    database: Any,
    *,
    schema_version: int,
    eligible_program_ids: set[str] | frozenset[str] | None = None,
) -> None:
    """Deterministically rebuild registered lineage-island coset archives."""

    contract = _coset_portfolio_contract_for_schema(schema_version)
    island_count = int(contract["num_islands"])

    programs = getattr(database, "programs", None)
    previous_islands = getattr(database, "islands", None)
    if not isinstance(programs, dict):
        raise RuntimeError("coset MAP database programs are invalid")
    if (
        not isinstance(previous_islands, list)
        or len(previous_islands) != island_count
    ):
        raise RuntimeError("coset MAP database islands are invalid")

    membership: dict[str, set[int]] = {}
    for island, program_ids in enumerate(previous_islands):
        if not isinstance(program_ids, (set, list, tuple)):
            raise RuntimeError("coset MAP island membership is invalid")
        for program_id in program_ids:
            membership.setdefault(program_id, set()).add(island)

    winners: list[dict[str, str]] = [
        {} for _ in range(island_count)
    ]
    for program_id in sorted(membership):
        if (
            eligible_program_ids is not None
            and program_id not in eligible_program_ids
        ):
            continue
        islands = membership[program_id]
        if len(islands) != 1:
            raise RuntimeError(
                f"coset MAP program {program_id} belongs to multiple islands"
            )
        program = programs.get(program_id)
        if program is None or getattr(program, "id", None) != program_id:
            raise RuntimeError("coset MAP island references a missing program")
        island = next(iter(islands))
        metadata = getattr(program, "metadata", None)
        if not isinstance(metadata, dict) or metadata.get("island") != island:
            raise RuntimeError(
                f"coset MAP program {program_id} has inconsistent island metadata"
            )
        key = "-".join(str(value) for value in _fixed_coset_feature_coords(
            program,
            schema_version=schema_version,
        ))
        existing_id = winners[island].get(key)
        if existing_id is None:
            winners[island][key] = program_id
            continue
        candidate_key = (-_search_program_fitness(program), program_id)
        existing_key = (
            -_search_program_fitness(programs[existing_id]),
            existing_id,
        )
        if candidate_key < existing_key:
            winners[island][key] = program_id

    database.island_feature_maps = winners
    database.islands = [set(feature_map.values()) for feature_map in winners]
    elite_ids = set().union(*(set(item.values()) for item in winners))
    config = getattr(database, "config", None)
    archive_size = getattr(config, "archive_size", len(elite_ids) or 1)
    if (
        isinstance(archive_size, bool)
        or not isinstance(archive_size, int)
        or archive_size < 1
    ):
        raise RuntimeError("coset MAP archive_size is invalid")
    ranked = sorted(
        elite_ids,
        key=lambda program_id: (
            -_search_program_fitness(programs[program_id]),
            program_id,
        ),
    )
    database.archive = set(ranked[:archive_size])
    database.feature_stats = {}
    database.feature_bins_per_dim = dict(contract["feature_bins"])
    database.island_best_programs = [
        (
            min(
                feature_map.values(),
                key=lambda program_id: (
                    -_search_program_fitness(programs[program_id]),
                    program_id,
                ),
            )
            if feature_map
            else None
        )
        for feature_map in winners
    ]
    database.best_program_id = ranked[0] if ranked else None


def _search_program_fitness(program: Any) -> float:
    metrics = getattr(program, "metrics", None)
    if not isinstance(metrics, dict):
        raise RuntimeError("search portfolio program metrics are not an object")
    combined = metrics.get("combined_score")
    if (
        isinstance(combined, bool)
        or not isinstance(combined, (int, float))
        or not math.isfinite(float(combined))
    ):
        raise RuntimeError(
            "search portfolio program has no finite combined_score"
        )
    return float(combined)


def _rebuild_fixed_search_feature_maps(
    database: Any,
    schema_version: int = SEARCH_PORTFOLIO_SCHEMA_VERSION,
) -> None:
    """Reconstruct lineage-island MAP cells and their selectable elites.

    An island is the mutation role that produced a child, not a hard
    classifier gate over the child's whole generated pool.  A useful mutation
    may legitimately change its dominant mechanism, so every accepted child
    remains eligible in the scheduler-selected island.  Relation matching is
    applied as a parent-selection preference in :func:`_search_elite_ids`.
    """

    programs = getattr(database, "programs", None)
    if not isinstance(programs, dict):
        raise RuntimeError("search portfolio database programs are invalid")
    previous_islands = getattr(database, "islands", None)
    if (
        not isinstance(previous_islands, list)
        or len(previous_islands) != SEARCH_PORTFOLIO_ISLAND_COUNT
    ):
        raise RuntimeError("search portfolio database islands are invalid")
    membership: dict[str, set[int]] = {}
    for island, program_ids in enumerate(previous_islands):
        for program_id in program_ids:
            membership.setdefault(program_id, set()).add(island)

    winners: list[dict[str, str]] = [
        {} for _ in range(SEARCH_PORTFOLIO_ISLAND_COUNT)
    ]
    for program_id in sorted(membership):
        prior = membership[program_id]
        if len(prior) != 1:
            raise RuntimeError(
                f"search portfolio program {program_id} belongs to "
                "more than one island"
            )
        if program_id not in programs:
            raise RuntimeError(
                f"search portfolio island references missing program "
                f"{program_id}"
            )
        program = programs[program_id]
        if getattr(program, "id", None) != program_id:
            raise RuntimeError("search portfolio program id is inconsistent")
        metadata = getattr(program, "metadata", None)
        if not isinstance(metadata, dict):
            raise RuntimeError("search portfolio program metadata are invalid")
        island = metadata.get("island")
        recorded_island = next(iter(prior))
        if (
            isinstance(island, bool)
            or not isinstance(island, int)
            or not 0 <= island < SEARCH_PORTFOLIO_ISLAND_COUNT
        ):
            raise RuntimeError(
                f"search portfolio program {program_id} has invalid island "
                "metadata"
            )
        if island != recorded_island:
            raise RuntimeError(
                f"search portfolio program {program_id} island metadata "
                "disagrees with membership"
            )
        coords = _fixed_search_feature_coords(
            program, schema_version=schema_version
        )
        if coords[0] not in SEARCH_PORTFOLIO_RELATION_CATEGORIES[island]:
            if getattr(program, "parent_id", None) is None:
                # OpenEvolve always inserts the one fresh bootstrap Program
                # into island 0, regardless of its actual descriptor.  Bind a
                # root/seed to its real mechanism island.  Mutated children,
                # by contrast, keep the scheduler-selected lineage island
                # even when their generated pool has a different dominant
                # relation.
                island = _mechanism_island_for_relation(coords[0])
                metadata["island"] = island
        key = "-".join(str(value) for value in coords)
        existing_id = winners[island].get(key)
        if existing_id is None:
            winners[island][key] = program_id
            continue
        existing = programs[existing_id]
        candidate_key = (-_search_program_fitness(program), program_id)
        existing_key = (-_search_program_fitness(existing), existing_id)
        if candidate_key < existing_key:
            winners[island][key] = program_id

    database.island_feature_maps = winners
    database.islands = [set(feature_map.values()) for feature_map in winners]
    elite_ids = set().union(*(set(values.values()) for values in winners))
    database_config = getattr(database, "config", None)
    archive_limit = getattr(database_config, "archive_size", len(elite_ids))
    if (
        isinstance(archive_limit, bool)
        or not isinstance(archive_limit, int)
        or archive_limit < 1
    ):
        raise RuntimeError("search portfolio archive_size is invalid")
    ranked_elites = sorted(
        elite_ids,
        key=lambda program_id: (
            -_search_program_fitness(programs[program_id]),
            program_id,
        ),
    )
    # OpenEvolve's global archive is a bounded compatibility index.  Parent
    # selection below uses every per-island MAP cell directly, so capping this
    # redundant set does not discard MAP-Elites coverage.
    database.archive = set(ranked_elites[:archive_limit])
    database.feature_stats = {}
    _dimensions, bins = _search_portfolio_spec(schema_version)
    database.feature_bins_per_dim = dict(bins)
    database.island_best_programs = [
        (
            min(
                feature_map.values(),
                key=lambda program_id: (
                    -_search_program_fitness(programs[program_id]),
                    program_id,
                ),
            )
            if feature_map
            else None
        )
        for feature_map in winners
    ]
    database.best_program_id = (
        min(
            elite_ids,
            key=lambda program_id: (
                -_search_program_fitness(programs[program_id]),
                program_id,
            ),
        )
        if elite_ids
        else None
    )


def _search_elite_ids(
    database: Any,
    island: int,
    schema_version: int = SEARCH_PORTFOLIO_SCHEMA_VERSION,
) -> list[str]:
    if (
        isinstance(island, bool)
        or not isinstance(island, int)
        or not 0 <= island < SEARCH_PORTFOLIO_ISLAND_COUNT
    ):
        raise RuntimeError("search portfolio island is invalid")
    feature_maps = getattr(database, "island_feature_maps", None)
    if (
        not isinstance(feature_maps, list)
        or len(feature_maps) != SEARCH_PORTFOLIO_ISLAND_COUNT
    ):
        raise RuntimeError("search portfolio feature maps are invalid")
    programs = getattr(database, "programs", None)
    if not isinstance(programs, dict) or not programs:
        raise RuntimeError("search portfolio has no parent program")

    expected_relations = SEARCH_PORTFOLIO_RELATION_CATEGORIES[island]

    def matching(program_ids: list[str]) -> list[str]:
        matches: list[str] = []
        for program_id in program_ids:
            program = programs.get(program_id)
            if program is None:
                raise RuntimeError(
                    "search portfolio feature map references missing program "
                    f"{program_id}"
                )
            if _fixed_search_feature_coords(
                program, schema_version=schema_version
            )[0] in expected_relations:
                matches.append(program_id)
        return matches

    local = sorted(set(feature_maps[island].values()))
    local_matches = matching(local)
    if local_matches:
        return local_matches
    # A lineage island must be able to bootstrap even before it has produced
    # its target mechanism.  Prefer its own off-role history over abandoning
    # the lineage, then fall back to relation-matched/global elites.
    if local:
        return local
    global_elites = sorted({
        program_id
        for feature_map in feature_maps
        for program_id in feature_map.values()
    })
    global_matches = matching(global_elites)
    if global_matches:
        return global_matches
    if global_elites:
        return global_elites
    all_programs = sorted(programs)
    all_matches = matching(all_programs)
    return all_matches or all_programs


def _deterministic_search_order(
    program_ids: list[str],
    *,
    programs: dict[str, Any],
    seed: int,
    iteration: int,
    island: int,
) -> list[str]:
    role = SEARCH_PORTFOLIO_ROLES[island]
    island_sha256 = hashlib.sha256(role.encode("utf-8")).hexdigest()

    def key(program_id: str) -> tuple[bytes, str]:
        program = programs.get(program_id)
        code = getattr(program, "code", None)
        if not isinstance(code, str):
            raise RuntimeError(
                f"search portfolio parent {program_id} has invalid code"
            )
        code_sha256 = hashlib.sha256(code.encode("utf-8")).hexdigest()
        digest = hashlib.sha256(
            (
                str(seed)
                + "\0"
                + str(iteration)
                + "\0"
                + island_sha256
                + "\0"
                + code_sha256
            ).encode("ascii")
        ).digest()
        return digest, program_id

    return sorted(
        program_ids,
        key=key,
    )


def _deterministic_coset_order(
    program_ids: list[str],
    *,
    programs: dict[str, Any],
    seed: int,
    iteration: int,
    island: int,
    activation_sha256: str,
) -> list[str]:
    """Order active coset parents without completion-order dependence."""

    if (
        isinstance(seed, bool)
        or not isinstance(seed, int)
        or isinstance(iteration, bool)
        or not isinstance(iteration, int)
        or isinstance(island, bool)
        or not isinstance(island, int)
        or not isinstance(activation_sha256, str)
        or re.fullmatch(r"[0-9a-f]{64}", activation_sha256) is None
    ):
        raise RuntimeError("coset deterministic parent order is unbound")

    def key(program_id: str) -> tuple[bytes, str]:
        program = programs.get(program_id)
        code = getattr(program, "code", None)
        if not isinstance(code, str):
            raise RuntimeError(
                f"coset parent {program_id} has invalid code"
            )
        code_sha256 = hashlib.sha256(code.encode("utf-8")).hexdigest()
        digest = hashlib.sha256(
            (
                str(seed)
                + "\0"
                + str(iteration)
                + "\0"
                + str(island)
                + "\0"
                + activation_sha256
                + "\0"
                + code_sha256
            ).encode("ascii")
        ).digest()
        return digest, program_id

    return sorted(program_ids, key=key)


class _ObservedFuture:
    def __init__(self, raw: Any, iteration: int, observer: "_SliceObserver"):
        self._raw = raw
        self._iteration = iteration
        self._observer = observer

    def done(self) -> bool:
        return self._raw.done()

    def cancel(self) -> bool:
        return self._raw.cancel()

    def cancelled(self) -> bool:
        return self._raw.cancelled()

    def result(self, *args: Any, **kwargs: Any) -> Any:
        try:
            result = self._raw.result(*args, **kwargs)
        except BaseException as exc:
            self._observer.record_future_exception(self._iteration, exc)
            raise
        return self._observer.record_future_result(self._iteration, result)

    def __getattr__(self, name: str) -> Any:
        return getattr(self._raw, name)


@dataclass
class _SliceObserver:
    base_iteration: int
    iterations: int
    result_type: type
    expected_preflight_contract_id: int | None = None
    evaluator_kind: str = EVALUATOR_KIND_DEFAULT
    stage2_cascade_threshold: float | None = None
    checkpoint_preflight_required: bool = False
    search_portfolio_schema_version: int = SEARCH_PORTFOLIO_SCHEMA_VERSION
    coset_map_schema_version: int | None = None
    run_calls: int = 0
    shutdown_requested: bool = False
    submission_attempts: list[dict[str, Any]] = field(default_factory=list)
    consumed: dict[int, int] = field(default_factory=dict)
    outcomes: dict[int, dict[str, Any]] = field(default_factory=dict)
    expected_programs: dict[int, dict[str, Any]] = field(default_factory=dict)
    integrated_programs: dict[int, str] = field(default_factory=dict)
    auxiliary_programs: list[dict[str, Any]] = field(default_factory=list)
    violations: list[str] = field(default_factory=list)
    accounting_complete: bool = False
    checkpoint_saves: list[dict[str, Any]] = field(default_factory=list)
    checkpoint_controller: Any = None
    checkpoint_preflight_report: dict[str, Any] | None = None
    search_policy_sha256: str | None = None
    search_regime_status: str = "normal"
    search_role_submission_counts: dict[str, int] = field(default_factory=dict)

    @property
    def start_iteration(self) -> int:
        return self.base_iteration + 1

    @property
    def end_iteration(self) -> int:
        return self.base_iteration + self.iterations

    @property
    def expected_iterations(self) -> list[int]:
        return list(range(self.start_iteration, self.end_iteration + 1))

    def begin(self, start: int, count: int, target_score: Any) -> None:
        self.run_calls += 1
        if self.run_calls != 1:
            self.violations.append("ProcessParallelController.run_evolution called more than once")
        if start != self.start_iteration or count != self.iterations:
            self.violations.append(
                f"evolution range mismatch: {(start, count)} != "
                f"{(self.start_iteration, self.iterations)}"
            )
        if target_score is not None:
            self.violations.append("managed evolution may not use target_score")

    def record_submission(
        self,
        iteration: int,
        island_id: Any,
        future: Any,
        *,
        search_role: str | None = None,
        search_tactic: str | None = None,
        search_parent_program_id: str | None = None,
        search_parent_code_sha256: str | None = None,
    ) -> Any:
        if isinstance(iteration, bool) or not isinstance(iteration, int):
            self.violations.append("submission iteration is not an integer")
        if isinstance(island_id, bool) or not isinstance(island_id, int):
            self.violations.append(
                f"submission {iteration!r} has an invalid island id"
            )
        result = "future" if future is not None else "none"
        attempt = {
            "iteration": iteration,
            "island_id": island_id,
            "result": result,
        }
        if self.search_policy_sha256 is not None:
            schedule = _search_island_schedule(
                self.iterations,
                self.search_regime_status,
            )
            expected_island: int | None = None
            if isinstance(iteration, int) and not isinstance(iteration, bool):
                offset = iteration - self.start_iteration
                if 0 <= offset < len(schedule):
                    expected_island = schedule[offset]
            if expected_island is None:
                self.violations.append(
                    f"submission {iteration!r} is outside the scheduled slice"
                )
            elif island_id != expected_island:
                self.violations.append(
                    f"submission {iteration!r} did not use its effective island"
                )
            expected_role = (
                None
                if expected_island is None
                else SEARCH_PORTFOLIO_ROLES[expected_island]
            )
            if expected_role is not None and search_role != expected_role:
                self.violations.append(
                    f"submission {iteration!r} has an invalid search role"
                )
            if search_tactic not in ADAPTIVE_MUTATION_TACTICS:
                self.violations.append(
                    f"submission {iteration!r} has an invalid search tactic"
                )
            if (
                not isinstance(search_parent_program_id, str)
                or not search_parent_program_id
                or Path(search_parent_program_id).name
                != search_parent_program_id
            ):
                self.violations.append(
                    f"submission {iteration!r} has an invalid parent program id"
                )
            if (
                not isinstance(search_parent_code_sha256, str)
                or len(search_parent_code_sha256) != 64
                or any(
                    character not in "0123456789abcdef"
                    for character in search_parent_code_sha256
                )
            ):
                self.violations.append(
                    f"submission {iteration!r} has an invalid parent code hash"
                )
            attempt.update({
                "search_portfolio_schema_version":
                    self.search_portfolio_schema_version,
                "search_policy_sha256": self.search_policy_sha256,
                "search_regime_status": self.search_regime_status,
                "search_role": search_role,
                "search_tactic": search_tactic,
                "search_parent_program_id": search_parent_program_id,
                "search_parent_code_sha256": search_parent_code_sha256,
            })
            if search_role is not None:
                self.search_role_submission_counts[search_role] = (
                    self.search_role_submission_counts.get(search_role, 0) + 1
                )
        elif self.coset_map_schema_version is not None:
            if (
                not isinstance(search_parent_program_id, str)
                or not search_parent_program_id
                or Path(search_parent_program_id).name
                != search_parent_program_id
            ):
                self.violations.append(
                    f"submission {iteration!r} has no valid coset parent"
                )
            if (
                not isinstance(search_parent_code_sha256, str)
                or len(search_parent_code_sha256) != 64
                or any(
                    character not in "0123456789abcdef"
                    for character in search_parent_code_sha256
                )
            ):
                self.violations.append(
                    f"submission {iteration!r} has no valid coset parent hash"
                )
            attempt.update({
                "coset_parent_program_id": search_parent_program_id,
                "coset_parent_code_sha256": search_parent_code_sha256,
            })
        self.submission_attempts.append(attempt)
        if future is None:
            return None
        return _ObservedFuture(future, iteration, self)

    def record_future_exception(self, iteration: int, exc: BaseException) -> None:
        self.consumed[iteration] = self.consumed.get(iteration, 0) + 1
        self.violations.append(
            f"future {iteration} raised {type(exc).__name__}"
        )

    def _record_worker_error(
        self,
        iteration: int,
        error: str,
        *,
        error_kind: str | None = None,
    ) -> None:
        encoded = error.encode("utf-8")
        outcome = {
            "iteration": iteration,
            "status": "worker_error",
            "error_sha256": hashlib.sha256(encoded).hexdigest(),
            "error_bytes": len(encoded),
        }
        if error_kind is not None:
            outcome["error_kind"] = error_kind
        self.outcomes[iteration] = outcome

    def record_future_result(self, iteration: int, result: Any) -> Any:
        self.consumed[iteration] = self.consumed.get(iteration, 0) + 1
        if not isinstance(result, self.result_type):
            self.violations.append(
                f"future {iteration} returned a non-SerializableResult"
            )
            return result
        result_iteration = getattr(result, "iteration", None)
        if (
            isinstance(result_iteration, bool)
            or not isinstance(result_iteration, int)
            or result_iteration != iteration
        ):
            self.violations.append(f"future {iteration} returned a mismatched iteration")
            return result
        error = getattr(result, "error", None)
        child = getattr(result, "child_program_dict", None)
        if error is not None:
            if not isinstance(error, str) or not error or child is not None:
                self.violations.append(
                    f"future {iteration} returned an invalid worker error"
                )
                return result
            rejection_kind: str | None = None
            if self.coset_map_schema_version is not None:
                attempt = next(
                    (
                        item for item in self.submission_attempts
                        if item.get("iteration") == iteration
                    ),
                    None,
                )
                parent_sha256 = (
                    attempt.get("coset_parent_code_sha256")
                    if isinstance(attempt, dict)
                    else None
                )
                if isinstance(parent_sha256, str):
                    rejection_kind = _recognized_coset_mutation_rejection(
                        error,
                        expected_parent_code_sha256=parent_sha256,
                    )
            self._record_worker_error(
                iteration,
                error,
                error_kind=rejection_kind,
            )
            return result
        if not isinstance(child, dict):
            self.violations.append(f"future {iteration} returned neither error nor child")
            return result
        program_id = child.get("id")
        if not isinstance(program_id, str) or not program_id:
            self.violations.append(f"future {iteration} returned an invalid child id")
            return result
        child_iteration = child.get("iteration_found")
        if (
            isinstance(child_iteration, bool)
            or not isinstance(child_iteration, int)
            or child_iteration != iteration
        ):
            self.violations.append(
                f"future {iteration} returned a child with mismatched iteration"
            )
            return result
        if any(
            expected["id"] == program_id
            for expected in self.expected_programs.values()
        ):
            self.violations.append(
                f"future {iteration} reused child program id {program_id}"
            )
            return result
        try:
            encoded_child = json.dumps(
                child,
                sort_keys=True,
                separators=(",", ":"),
                allow_nan=False,
            ).encode("utf-8")
        except (TypeError, ValueError) as exc:
            self.violations.append(
                f"future {iteration} returned invalid child content: "
                f"{type(exc).__name__}"
            )
            return result
        if self.expected_preflight_contract_id is not None:
            result_artifacts = getattr(result, "artifacts", None)
            stage1_outer_failure = (
                _pre_marker_stage1_failure_evidence(
                    child.get("metrics"),
                    result_artifacts,
                )
                if self.evaluator_kind == EVALUATOR_KIND_COSET_TWO_BLOCK
                else None
            )
            if stage1_outer_failure is not None:
                failure = {
                    "child_program_bytes": len(encoded_child),
                    "child_program_sha256": hashlib.sha256(
                        encoded_child
                    ).hexdigest(),
                    "evidence": stage1_outer_failure,
                    "iteration": iteration,
                    "kind": "stage1_outer_cascade_incomplete",
                    "preflight_contract_id":
                        self.expected_preflight_contract_id,
                    "program_id": program_id,
                }
                canonical_error = json.dumps(
                    failure,
                    sort_keys=True,
                    separators=(",", ":"),
                    allow_nan=False,
                )
                sanitized = self.result_type(
                    child_program_dict=None,
                    iteration=iteration,
                    error=canonical_error,
                )
                self._record_worker_error(iteration, canonical_error)
                return sanitized
            incomplete = _exact_incomplete_winner_preflight_markers(
                child.get("metrics"),
                expected_contract_id=self.expected_preflight_contract_id,
                evaluator_kind=self.evaluator_kind,
            )
            if incomplete is not None:
                invalid_mutation = (
                    _exact_coset_invalid_mutation_evidence(
                        child.get("metrics"),
                        result_artifacts,
                        expected_contract_id=(
                            self.expected_preflight_contract_id
                        ),
                    )
                    if self.evaluator_kind
                    == EVALUATOR_KIND_COSET_TWO_BLOCK
                    else None
                )
                source_error = str(child["metrics"]["error"]).encode("utf-8")
                failure = {
                    "child_program_bytes": len(encoded_child),
                    "child_program_sha256": hashlib.sha256(
                        encoded_child
                    ).hexdigest(),
                    "failure_error_bytes": len(source_error),
                    "failure_error_sha256": hashlib.sha256(
                        source_error
                    ).hexdigest(),
                    "hard_timeout": int(
                        incomplete[WINNER_PREFLIGHT_HARD_TIMEOUT_METRIC]
                    ),
                    "iteration": iteration,
                    "kind": (
                        "coset_invalid_mutation"
                        if invalid_mutation is not None
                        else "winner_preflight_incomplete"
                    ),
                    "preflight_contract_id":
                        self.expected_preflight_contract_id,
                    "program_id": program_id,
                }
                if invalid_mutation is not None:
                    failure["invalid_mutation"] = invalid_mutation
                canonical_error = json.dumps(
                    failure,
                    sort_keys=True,
                    separators=(",", ":"),
                    allow_nan=False,
                )
                sanitized = self.result_type(
                    child_program_dict=None,
                    iteration=iteration,
                    error=canonical_error,
                )
                self._record_worker_error(
                    iteration,
                    canonical_error,
                    error_kind=(
                        "invalid_mutation"
                        if invalid_mutation is not None
                        else None
                    ),
                )
                return sanitized
            try:
                _validated_winner_preflight_markers(
                    child.get("metrics"),
                    expected_contract_id=(
                        self.expected_preflight_contract_id
                    ),
                    evaluator_kind=self.evaluator_kind,
                )
                preflight_is_complete = True
            except RuntimeError:
                preflight_is_complete = False
            stage2_incomplete = (
                _exact_incomplete_stage2_markers(
                    child.get("metrics"),
                    result_artifacts,
                    expected_contract_id=(
                        self.expected_preflight_contract_id
                    ),
                    evaluator_kind=self.evaluator_kind,
                )
                if preflight_is_complete
                else None
            )
            if stage2_incomplete is not None:
                failure_text = str(
                    getattr(result, "artifacts", {}).get(
                        "stage2_subprocess_error"
                    )
                ).encode("utf-8")
                failure = {
                    "child_program_bytes": len(encoded_child),
                    "child_program_sha256": hashlib.sha256(
                        encoded_child
                    ).hexdigest(),
                    "completed_lattices": int(
                        stage2_incomplete[STAGE2_LATTICES_METRIC]
                    ),
                    "failure_error_bytes": len(failure_text),
                    "failure_error_sha256": hashlib.sha256(
                        failure_text
                    ).hexdigest(),
                    "hard_timeout": int(
                        stage2_incomplete[STAGE2_HARD_TIMEOUT_METRIC]
                    ),
                    "iteration": iteration,
                    "kind": "stage2_evaluation_incomplete",
                    "preflight_contract_id":
                        self.expected_preflight_contract_id,
                    "program_id": program_id,
                }
                canonical_error = json.dumps(
                    failure,
                    sort_keys=True,
                    separators=(",", ":"),
                    allow_nan=False,
                )
                sanitized = self.result_type(
                    child_program_dict=None,
                    iteration=iteration,
                    error=canonical_error,
                )
                self._record_worker_error(iteration, canonical_error)
                return sanitized
            pre_marker_failure = (
                _pre_marker_stage2_failure_evidence(
                    child.get("metrics"),
                    result_artifacts,
                )
                if preflight_is_complete
                else None
            )
            if pre_marker_failure is not None:
                failure = {
                    "child_program_bytes": len(encoded_child),
                    "child_program_sha256": hashlib.sha256(
                        encoded_child
                    ).hexdigest(),
                    "evidence": pre_marker_failure,
                    "iteration": iteration,
                    "kind": "stage2_outer_cascade_incomplete",
                    "preflight_contract_id":
                        self.expected_preflight_contract_id,
                    "program_id": program_id,
                }
                canonical_error = json.dumps(
                    failure,
                    sort_keys=True,
                    separators=(",", ":"),
                    allow_nan=False,
                )
                sanitized = self.result_type(
                    child_program_dict=None,
                    iteration=iteration,
                    error=canonical_error,
                )
                self._record_worker_error(iteration, canonical_error)
                return sanitized
            try:
                if preflight_is_complete:
                    _validated_managed_stage2_state(
                        child.get("metrics"),
                        result_artifacts,
                        expected_contract_id=(
                            self.expected_preflight_contract_id
                        ),
                        cascade_threshold=self.stage2_cascade_threshold,
                    )
            except RuntimeError as exc:
                self.violations.append(
                    f"future {iteration} returned invalid Stage 2 state: "
                    f"{exc}"
                )
                failure = {
                    "child_program_bytes": len(encoded_child),
                    "child_program_sha256": hashlib.sha256(
                        encoded_child
                    ).hexdigest(),
                    "iteration": iteration,
                    "kind": "stage2_evaluation_invalid",
                    "preflight_contract_id":
                        self.expected_preflight_contract_id,
                    "program_id": program_id,
                }
                canonical_error = json.dumps(
                    failure,
                    sort_keys=True,
                    separators=(",", ":"),
                    allow_nan=False,
                )
                sanitized = self.result_type(
                    child_program_dict=None,
                    iteration=iteration,
                    error=canonical_error,
                )
                self._record_worker_error(iteration, canonical_error)
                return sanitized
        if (
            self.evaluator_kind == EVALUATOR_KIND_COSET_TWO_BLOCK
            and self.coset_map_schema_version is not None
        ):
            # The worker-side literal patcher rejects a parent no-op before
            # evaluation.  Recheck the semantic and artifact bindings at the
            # controller trust boundary so a future OpenEvolve refactor cannot
            # silently reintroduce duplicate typed policies.
            from evolve.coset_policy_dispatch import (
                parse_and_render_activated_policy,
                parse_and_render_registered_policy,
            )
            from evolve.coset_search_contract import (
                COSET_MAP_SCHEMA_METRIC,
                coset_batch_map_descriptor_registered,
            )

            child_code = child.get("code")
            parent_id = getattr(result, "parent_id", None)
            controller = self.checkpoint_controller
            database = getattr(controller, "database", None)
            programs = getattr(database, "programs", None)
            parent = (
                programs.get(parent_id)
                if isinstance(programs, dict) and isinstance(parent_id, str)
                else None
            )
            result_artifacts = getattr(result, "artifacts", None)
            binding_error: str | None = None
            child_policy_sha256: str | None = None
            child_metrics = child.get("metrics")
            expected_genome_marker = _coset_genome_format_id_for_schema(
                self.coset_map_schema_version
            )
            if _exact_pre_marker_stage1_failure_metrics(child_metrics):
                # OpenEvolve converts a trusted evaluator exception into this
                # exact two-zero metric envelope.  A genuine mutation-origin
                # exception was already isolated above; anything remaining is
                # fatal, but it is not a genome-format failure.
                binding_error = "stage1_evaluation_failed_before_markers"
            elif (
                not isinstance(child_metrics, dict)
                or child_metrics.get(COSET_GENOME_FORMAT_ID_METRIC)
                != expected_genome_marker
            ):
                binding_error = "genome_format_marker_mismatch"
            elif not isinstance(child_code, str) or not child_code:
                binding_error = "child_code_invalid"
            elif parent is None or not isinstance(
                getattr(parent, "code", None), str
            ):
                binding_error = "parent_binding_missing"
            elif not isinstance(result_artifacts, dict):
                binding_error = "evaluation_artifacts_missing"
            else:
                try:
                    active_renderer = _configured_coset_renderer_activation()
                    child_render = (
                        parse_and_render_registered_policy(child_code)
                        if active_renderer is None
                        else parse_and_render_activated_policy(
                            child_code, active_renderer
                        )
                    )
                    parent_render = (
                        parse_and_render_registered_policy(parent.code)
                        if active_renderer is None
                        else parse_and_render_activated_policy(
                            parent.code, active_renderer
                        )
                    )
                    child_policy_sha256 = child_render.policy_sha256
                    parent_policy_sha256 = parent_render.policy_sha256
                except Exception:
                    binding_error = "typed_policy_parse_failed"
                else:
                    if (
                        child_render.descriptor.map_schema_version
                        != self.coset_map_schema_version
                        or parent_render.descriptor.map_schema_version
                        != self.coset_map_schema_version
                    ):
                        binding_error = "renderer_epoch_mismatch"
                    expected_program_sha256 = hashlib.sha256(
                        child_code.encode("utf-8")
                    ).hexdigest()
                    if binding_error is not None:
                        pass
                    elif result_artifacts.get("program_sha256") != (
                        expected_program_sha256
                    ):
                        binding_error = "program_sha256_mismatch"
                    elif result_artifacts.get("policy_sha256") != (
                        child_policy_sha256
                    ):
                        binding_error = "policy_sha256_mismatch"
                    else:
                        expected_descriptor = (
                            coset_batch_map_descriptor_registered(
                                child_render.candidates,
                                policy_sha256=child_policy_sha256,
                                renderer_activation=child_render.activation,
                            )
                        )
                        if result_artifacts.get("map_descriptor") != (
                            expected_descriptor
                        ):
                            binding_error = "map_descriptor_mismatch"
                        elif child_metrics.get(
                            COSET_MAP_SCHEMA_METRIC
                        ) != float(expected_descriptor["schema_version"]):
                            binding_error = "map_schema_metric_mismatch"
                        elif any(
                            child_metrics.get(name)
                            != float(expected_descriptor["coordinates"][name])
                            for name in child_render.descriptor.feature_dimensions
                        ):
                            binding_error = "map_coordinate_metric_mismatch"
                    if binding_error is None and (
                        child_policy_sha256 == parent_policy_sha256
                    ):
                        binding_error = "semantic_parent_noop"
                    elif binding_error is None:
                        for existing_id, existing in sorted(programs.items()):
                            if existing_id == parent_id:
                                continue
                            existing_code = getattr(existing, "code", None)
                            if not isinstance(existing_code, str):
                                binding_error = "archive_code_invalid"
                                break
                            try:
                                existing_digest = (
                                    parse_and_render_registered_policy(
                                        existing_code
                                    ).policy_sha256
                                )
                            except Exception:
                                binding_error = "archive_policy_invalid"
                                break
                            if existing_digest == child_policy_sha256:
                                binding_error = "semantic_archive_duplicate"
                                break
            if binding_error is not None:
                expected_no_effect = binding_error in {
                    "semantic_parent_noop",
                    "semantic_archive_duplicate",
                }
                stage1_evaluation_failed = (
                    binding_error
                    == "stage1_evaluation_failed_before_markers"
                )
                failure = {
                    "child_program_bytes": len(encoded_child),
                    "child_program_sha256": hashlib.sha256(
                        encoded_child
                    ).hexdigest(),
                    "iteration": iteration,
                    "kind": (
                        "coset_no_effect_mutation"
                        if expected_no_effect
                        else "coset_stage1_evaluation_failed"
                        if stage1_evaluation_failed
                        else "coset_mutation_binding_invalid"
                    ),
                    "program_id": program_id,
                    "reason": binding_error,
                }
                if child_policy_sha256 is not None:
                    failure["policy_sha256"] = child_policy_sha256
                if stage1_evaluation_failed and isinstance(
                    result_artifacts, dict
                ):
                    error_type = result_artifacts.get("error_type")
                    if isinstance(error_type, str) and error_type:
                        failure["error_type"] = error_type
                    error_message = result_artifacts.get("error_message")
                    if isinstance(error_message, str):
                        encoded_error = error_message.encode("utf-8")
                        failure.update({
                            "evaluator_error_bytes": len(encoded_error),
                            "evaluator_error_sha256": hashlib.sha256(
                                encoded_error
                            ).hexdigest(),
                        })
                canonical_error = json.dumps(
                    failure,
                    sort_keys=True,
                    separators=(",", ":"),
                    allow_nan=False,
                )
                sanitized = self.result_type(
                    child_program_dict=None,
                    iteration=iteration,
                    error=canonical_error,
                )
                if stage1_evaluation_failed:
                    self.violations.append(
                        f"future {iteration} failed trusted Stage 1 "
                        "evaluation before markers"
                    )
                elif not expected_no_effect:
                    self.violations.append(
                        f"future {iteration} violated coset mutation binding: "
                        f"{binding_error}"
                    )
                self._record_worker_error(
                    iteration,
                    canonical_error,
                    error_kind=(
                        "no_effect_mutation"
                        if expected_no_effect
                        else "stage1_evaluation_failed"
                        if stage1_evaluation_failed
                        else "mutation_binding_invalid"
                    ),
                )
                return sanitized
        self.expected_programs[iteration] = {
            "id": program_id,
            "sha256": hashlib.sha256(encoded_child).hexdigest(),
            "bytes": len(encoded_child),
        }
        return result

    def record_program_add(self, iteration: Any, program: Any) -> None:
        if (
            isinstance(iteration, bool)
            or not isinstance(iteration, int)
            or iteration not in self.expected_iterations
        ):
            self.violations.append(
                f"database add used unexpected iteration {iteration!r}"
            )
            return
        program_id = getattr(program, "id", None)
        if not isinstance(program_id, str) or not program_id:
            self.violations.append(
                f"database add for iteration {iteration} has an invalid program id"
            )
            return
        if iteration in self.integrated_programs:
            self.violations.append(f"iteration {iteration} was integrated twice")
            return
        expected = self.expected_programs.get(iteration)
        if expected is None or expected["id"] != program_id:
            self.violations.append(
                f"database add for iteration {iteration} used an unexpected program"
            )
            return
        if getattr(program, "iteration_found", None) != iteration:
            self.violations.append(
                f"database add for iteration {iteration} stored a mismatched iteration"
            )
            return
        if self.expected_preflight_contract_id is not None:
            try:
                _validated_winner_preflight_markers(
                    getattr(program, "metrics", None),
                    expected_contract_id=self.expected_preflight_contract_id,
                    evaluator_kind=self.evaluator_kind,
                )
                _validated_map_descriptor_version(
                    getattr(program, "metrics", None),
                    label=f"database add for iteration {iteration}",
                )
                _validated_managed_stage2_state(
                    getattr(program, "metrics", None),
                    expected_contract_id=self.expected_preflight_contract_id,
                    cascade_threshold=self.stage2_cascade_threshold,
                )
            except RuntimeError as exc:
                self.violations.append(
                    f"database add for iteration {iteration} has incomplete "
                    f"winner preflight or managed Stage 2 evaluation: {exc}"
                )
                return
        to_dict = getattr(program, "to_dict", None)
        value = to_dict() if callable(to_dict) else vars(program)
        if not isinstance(value, dict):
            self.violations.append(
                f"database add for iteration {iteration} is not serializable"
            )
            return
        try:
            encoded = json.dumps(
                value,
                sort_keys=True,
                separators=(",", ":"),
                allow_nan=False,
            ).encode("utf-8")
        except (TypeError, ValueError) as exc:
            self.violations.append(
                f"database add for iteration {iteration} has invalid content: "
                f"{type(exc).__name__}"
            )
            return
        observed_sha256 = hashlib.sha256(encoded).hexdigest()
        if (
            expected["sha256"] != observed_sha256
            or expected["bytes"] != len(encoded)
        ):
            self.violations.append(
                f"database add for iteration {iteration} changed child content"
            )
            return
        self.integrated_programs[int(iteration)] = str(program_id)
        self.outcomes[int(iteration)] = {
            "iteration": int(iteration),
            "status": "program_added",
            "program_id": program_id,
            "program_sha256": observed_sha256,
            "program_bytes": len(encoded),
        }

    def record_checkpoint_preflight(
        self,
        report: dict[str, Any],
    ) -> None:
        if self.checkpoint_preflight_report is not None:
            self.violations.append(
                "checkpoint winner preflight was recorded more than once"
            )
            return
        if (
            not isinstance(report, dict)
            or report.get("schema_version") not in {1, 2, 3, 4}
            or report.get("status") != "completed"
            or report.get("contract_version")
            != WINNER_PREFLIGHT_CONTRACT_VERSION
            or report.get("contract_id")
            != self.expected_preflight_contract_id
        ):
            self.violations.append(
                "checkpoint winner preflight report is invalid"
            )
            return
        if report.get("schema_version") == 2:
            source_programs = report.get("source_programs")
            if (
                report.get("mode")
                != "legacy-python-to-typed-json-dsl-root"
                or not isinstance(report.get("source_checkpoint"), dict)
                or isinstance(source_programs, bool)
                or not isinstance(source_programs, int)
                or source_programs < 1
                or report.get("target_programs") != 1
                or not isinstance(report.get("root_program_id"), str)
                or not isinstance(
                    report.get("migration_candidate_range"), dict
                )
            ):
                self.violations.append(
                    "checkpoint genome migration report is invalid"
                )
                return
        elif report.get("schema_version") == 3:
            expected_fields = {
                "schema_version",
                "status",
                "contract_version",
                "contract_id",
                "mode",
                "source_checkpoint",
                "source_programs",
                "source_program_set_sha256",
                "target_programs",
                "root_program_id",
                "root_policy_sha256",
                "root_code_sha256",
                "activation_sha256",
                "approved_support_split",
                "bridge_candidate_range",
            }
            hashes = (
                report.get("source_program_set_sha256"),
                report.get("root_policy_sha256"),
                report.get("root_code_sha256"),
                report.get("activation_sha256"),
            )
            if (
                set(report) != expected_fields
                or report.get("mode")
                != "typed-json-dsl-activation-bridge-root"
                or not isinstance(report.get("source_checkpoint"), dict)
                or isinstance(report.get("source_programs"), bool)
                or not isinstance(report.get("source_programs"), int)
                or report["source_programs"] < 1
                or report.get("target_programs") != 1
                or not isinstance(report.get("root_program_id"), str)
                or not report["root_program_id"].startswith(
                    "coset-activation-root-"
                )
                or any(
                    not isinstance(value, str)
                    or re.fullmatch(r"[0-9a-f]{64}", value) is None
                    for value in hashes
                )
                or type(report.get("approved_support_split")) is not list
                or len(report["approved_support_split"]) != 2
                or any(
                    type(value) is not int
                    for value in report["approved_support_split"]
                )
                or not isinstance(
                    report.get("bridge_candidate_range"), dict
                )
            ):
                self.violations.append(
                    "checkpoint activation bridge report is invalid"
                )
                return
        elif report.get("schema_version") == 4:
            expected_fields = {
                "schema_version",
                "status",
                "contract_version",
                "contract_id",
                "mode",
                "source_checkpoint",
                "source_programs",
                "source_program_set_sha256",
                "target_programs",
                "root_program_id",
                "root_policy_sha256",
                "root_code_sha256",
                "activation_sha256",
                "approved_support_splits",
                "root_support_split",
                "bridge_candidate_range",
            }
            hashes = (
                report.get("source_program_set_sha256"),
                report.get("root_policy_sha256"),
                report.get("root_code_sha256"),
                report.get("activation_sha256"),
            )
            approved_splits = report.get("approved_support_splits")
            root_split = report.get("root_support_split")
            def valid_split(split: Any) -> bool:
                return (
                    type(split) is list
                    and len(split) == 2
                    and all(
                        type(value) is int and value > 0
                        for value in split
                    )
                )
            if (
                set(report) != expected_fields
                or report.get("mode")
                != "typed-json-dsl-activation-bridge-root"
                or not isinstance(report.get("source_checkpoint"), dict)
                or isinstance(report.get("source_programs"), bool)
                or not isinstance(report.get("source_programs"), int)
                or report["source_programs"] < 1
                or report.get("target_programs") != 1
                or not isinstance(report.get("root_program_id"), str)
                or not report["root_program_id"].startswith(
                    "coset-activation-root-"
                )
                or any(
                    not isinstance(value, str)
                    or re.fullmatch(r"[0-9a-f]{64}", value) is None
                    for value in hashes
                )
                or type(approved_splits) is not list
                or len(approved_splits) <= 1
                or any(not valid_split(split) for split in approved_splits)
                or len({tuple(split) for split in approved_splits})
                != len(approved_splits)
                or not valid_split(root_split)
                or root_split != approved_splits[0]
                or not isinstance(
                    report.get("bridge_candidate_range"), dict
                )
            ):
                self.violations.append(
                    "checkpoint activation bridge report is invalid"
                )
                return
        self.checkpoint_preflight_report = dict(report)

    def record_auxiliary_program_add(
        self,
        *,
        program: Any,
        stored: Any,
        parent: Any,
        target_island: Any,
        num_islands: Any,
    ) -> None:
        """Account for a pinned OpenEvolve migration without treating it as a future.

        ``ProgramDatabase.migrate_programs`` inserts deterministic copies with
        ``iteration=None``.  They are database side effects of an already
        accounted evaluation, not additional submitted futures.  Accept only
        that exact shape; an evaluated child accidentally added without its
        iteration still leaves its expected future unintegrated and fails
        :meth:`verify`.
        """

        program_id = getattr(program, "id", None)
        stored_id = getattr(stored, "id", None)
        parent_id = getattr(program, "parent_id", None)
        metadata = getattr(program, "metadata", None)
        if (
            not isinstance(program_id, str)
            or not program_id
            or stored_id != program_id
            or parent is None
            or not isinstance(parent_id, str)
            or parent_id != getattr(parent, "id", None)
            or isinstance(target_island, bool)
            or not isinstance(target_island, int)
            or isinstance(num_islands, bool)
            or not isinstance(num_islands, int)
            or num_islands < 1
            or not 0 <= target_island < num_islands
            or not isinstance(metadata, dict)
            or metadata.get("migrant") is not True
            or metadata.get("island") != target_island
            # The pinned OpenEvolve Program dataclass defaults omitted
            # ``iteration_found`` to zero for migration copies.
            or getattr(program, "iteration_found", None) != 0
            or getattr(stored, "iteration_found", None) != 0
            or getattr(program, "code", None) != getattr(parent, "code", None)
            or getattr(program, "metrics", None)
            != getattr(parent, "metrics", None)
            or program_id
            in {
                expected["id"]
                for expected in self.expected_programs.values()
            }
            or any(
                item.get("program_id") == program_id
                for item in self.auxiliary_programs
            )
        ):
            self.violations.append(
                "database add with iteration None was not a valid migration"
            )
            return
        to_dict = getattr(stored, "to_dict", None)
        value = to_dict() if callable(to_dict) else vars(stored)
        if not isinstance(value, dict):
            self.violations.append("migration database add is not serializable")
            return
        try:
            encoded = json.dumps(
                value,
                sort_keys=True,
                separators=(",", ":"),
                allow_nan=False,
            ).encode("utf-8")
        except (TypeError, ValueError) as exc:
            self.violations.append(
                "migration database add has invalid content: "
                f"{type(exc).__name__}"
            )
            return
        self.auxiliary_programs.append(
            {
                "program_id": program_id,
                "parent_id": parent_id,
                "target_island": target_island,
                "program_sha256": hashlib.sha256(encoded).hexdigest(),
                "program_bytes": len(encoded),
            }
        )

    def verify(self, controller: Any) -> None:
        expected = self.expected_iterations
        attempt_ids = [item["iteration"] for item in self.submission_attempts]
        if attempt_ids != expected or any(
            item["result"] != "future" for item in self.submission_attempts
        ):
            self.violations.append("submitted futures are not the exact requested range")
        if self.search_policy_sha256 is not None:
            schedule = _search_island_schedule(
                self.iterations,
                self.search_regime_status,
            )
            expected_counts = [schedule.count(island) for island in range(
                SEARCH_PORTFOLIO_ISLAND_COUNT
            )]
            counts = [
                self.search_role_submission_counts.get(role, 0)
                for role in SEARCH_PORTFOLIO_ROLES
            ]
            if counts != expected_counts:
                self.violations.append(
                    "search portfolio submissions do not match mechanism quotas"
                )
            role_counts = {
                role: self.search_role_submission_counts.get(role, 0)
                for role in SEARCH_PORTFOLIO_ROLES
            }
            for attempt in self.submission_attempts:
                attempt["search_role_submission_counts"] = role_counts
        if self.shutdown_requested or controller.shutdown_event.is_set():
            self.violations.append("shutdown was requested")
        if controller.early_stopping_triggered:
            self.violations.append("early stopping was triggered")
        if any(self.consumed.get(iteration) != 1 for iteration in expected):
            self.violations.append("not every requested future was consumed exactly once")
        if sorted(self.outcomes) != expected:
            self.violations.append("not every requested future produced an accounted outcome")
        successful = sum(
            outcome.get("status") == "program_added"
            for outcome in self.outcomes.values()
        )
        expected_mutation_rejections = sum(
            outcome.get("status") == "worker_error"
            and outcome.get("error_kind") in {
                "invalid_mutation",
                "no_effect_mutation",
            }
            for outcome in self.outcomes.values()
        )
        # A worker_error has no checkpoint Program.  It covers both an LLM/diff
        # failure that never produced a child and the exact evaluator-generated
        # incomplete-preflight or incomplete-Stage-2 envelope sanitized before
        # database.add. Neither outcome claims that a candidate universe was
        # enumerated completely. Malformed/forged marker claims and future
        # exceptions remain violations.
        # A complete batch of either evaluator-authenticated bad DSL mutations
        # or source-bound pre-evaluation diff/no-op rejections is still a
        # completely accounted evolution slice. Save an unchanged-population
        # checkpoint so the next round can ask for new mutations. Timeouts,
        # LLM transport errors, Stage-2 failures, and unclassified worker
        # errors retain the at-least-one-success requirement and fail closed.
        if (
            successful < 1
            and expected_mutation_rejections != len(expected)
        ):
            self.violations.append(
                "the OpenEvolve slice produced no successful evaluations"
            )
        if (
            self.checkpoint_preflight_required
            and self.checkpoint_preflight_report is None
        ):
            self.violations.append(
                "checkpoint winner preflight did not complete"
            )
        for iteration, expected in self.expected_programs.items():
            program_id = expected["id"]
            if self.integrated_programs.get(iteration) != program_id:
                self.violations.append(
                    f"program for iteration {iteration} was not integrated"
                )
        if self.run_calls != 1:
            self.violations.append("managed evolution did not make exactly one run call")
        if self.violations:
            raise RuntimeError("incomplete OpenEvolve slice: " + "; ".join(self.violations))
        self.accounting_complete = True

    def ensure_final_checkpoint(self) -> None:
        if not self.accounting_complete or self.checkpoint_controller is None:
            raise RuntimeError("cannot save a checkpoint before slice accounting")
        if any(
            save.get("iteration") == self.end_iteration
            and save.get("accounting_complete") is True
            and isinstance(save.get("checkpoint_sha256"), str)
            and isinstance(save.get("checkpoint_programs"), int)
            for save in self.checkpoint_saves
        ):
            return
        self.checkpoint_controller._save_checkpoint(self.end_iteration)

    def record_checkpoint_save(self, controller: Any, iteration: int) -> None:
        record: dict[str, Any] = {
            "iteration": iteration,
            "accounting_complete": self.accounting_complete,
            "checkpoint_sha256": None,
            "checkpoint_programs": None,
        }
        checkpoint = (
            Path(controller.output_dir)
            / "checkpoints"
            / f"checkpoint_{iteration}"
        )
        try:
            descriptor = _strong_checkpoint_descriptor(
                controller.output_dir, checkpoint, expected_iteration=iteration
            )
        except RuntimeError:
            if self.accounting_complete and iteration == self.end_iteration:
                raise
        else:
            record["checkpoint_sha256"] = descriptor["sha256"]
            record["checkpoint_programs"] = descriptor["programs"]
        self.checkpoint_saves.append(record)


def _openevolve_source_binding() -> tuple[dict[str, dict[str, Any]], Any, Any]:
    import openevolve
    import openevolve.api as api_module
    import openevolve.controller as controller_module
    import openevolve.database as database_module
    import openevolve.evaluator as evaluator_module
    import openevolve.process_parallel as process_module

    if openevolve.__version__ != SUPPORTED_OPENEVOLVE_VERSION:
        raise RuntimeError(
            f"unsupported OpenEvolve version: {openevolve.__version__}; "
            f"expected {SUPPORTED_OPENEVOLVE_VERSION}"
        )
    modules = {
        "controller": controller_module,
        "process_parallel": process_module,
        "database": database_module,
        "api": api_module,
        "evaluator": evaluator_module,
    }
    binding: dict[str, dict[str, Any]] = {}
    for name, module in modules.items():
        identity = _file_identity(module.__file__, f"OpenEvolve {name} source")
        if identity["sha256"] != SUPPORTED_OPENEVOLVE_SHA256[name]:
            raise RuntimeError(f"unsupported OpenEvolve {name} source hash")
        binding[name] = identity
    return binding, controller_module, process_module


def _raise_coset_mutation_rejection(
    reason: str,
    *,
    parent_code: str,
    detail: dict[str, Any],
) -> None:
    """Raise one canonical, controller-verifiable mutation rejection."""

    if reason not in COSET_MUTATION_REJECTION_KINDS:
        raise RuntimeError("unknown coset mutation rejection reason")
    detail_sha256 = hashlib.sha256(json.dumps(
        detail,
        sort_keys=True,
        separators=(",", ":"),
        allow_nan=False,
    ).encode("utf-8")).hexdigest()
    payload = {
        "schema_version": COSET_MUTATION_REJECTION_SCHEMA_VERSION,
        "kind": "qcode-coset-mutation-rejected",
        "reason": reason,
        "parent_code_sha256": hashlib.sha256(
            parent_code.encode("utf-8")
        ).hexdigest(),
        "detail_sha256": detail_sha256,
    }
    raise ValueError(
        COSET_MUTATION_REJECTION_PREFIX
        + json.dumps(
            payload,
            sort_keys=True,
            separators=(",", ":"),
            allow_nan=False,
        )
    )


def _recognized_coset_mutation_rejection(
    error: str,
    *,
    expected_parent_code_sha256: str,
) -> str | None:
    """Authenticate a pre-evaluation rejection emitted by the pinned worker."""

    if error == "No valid diffs found in response":
        # This exact envelope is emitted by pinned OpenEvolve immediately
        # before our patcher would be called.  The submission's parent hash is
        # independently bound in the slice witness.
        return "invalid_mutation"
    if not error.startswith(COSET_MUTATION_REJECTION_PREFIX):
        return None
    encoded = error[len(COSET_MUTATION_REJECTION_PREFIX):]
    try:
        payload = json.loads(encoded)
    except (json.JSONDecodeError, ValueError):
        return None
    if (
        type(payload) is not dict
        or set(payload) != {
            "schema_version",
            "kind",
            "reason",
            "parent_code_sha256",
            "detail_sha256",
        }
        or payload.get("schema_version")
        != COSET_MUTATION_REJECTION_SCHEMA_VERSION
        or payload.get("kind") != "qcode-coset-mutation-rejected"
        or payload.get("parent_code_sha256")
        != expected_parent_code_sha256
        or not isinstance(payload.get("detail_sha256"), str)
        or len(payload["detail_sha256"]) != 64
        or any(
            character not in "0123456789abcdef"
            for character in payload["detail_sha256"]
        )
        or encoded != json.dumps(
            payload,
            sort_keys=True,
            separators=(",", ":"),
            allow_nan=False,
        )
    ):
        return None
    return COSET_MUTATION_REJECTION_KINDS.get(payload.get("reason"))


def _configured_coset_renderer_activation():
    """Return only the registry-replayed activation inherited by a worker."""

    raw = os.environ.get(COSET_RENDERER_ACTIVATION_JSON_ENV)
    if raw is None:
        return None

    def reject_duplicates(pairs: list[tuple[str, Any]]) -> dict[str, Any]:
        result: dict[str, Any] = {}
        for name, value in pairs:
            if name in result:
                raise ValueError(f"duplicate activation field: {name}")
            result[name] = value
        return result

    def reject_constant(value: str) -> None:
        raise ValueError(f"non-finite activation value: {value}")

    try:
        document = json.loads(
            raw,
            object_pairs_hook=reject_duplicates,
            parse_constant=reject_constant,
        )
        from evolve.coset_search_contract import (
            trusted_coset_renderer_activation_from_document,
        )

        return trusted_coset_renderer_activation_from_document(document)
    except (TypeError, ValueError, json.JSONDecodeError) as exc:
        raise RuntimeError(
            "configured coset renderer activation is invalid"
        ) from exc


def _apply_coset_literal_diff(
    original_code: str,
    diff_text: str,
    diff_pattern: str = (
        r"<<<<<<< SEARCH\n(.*?)=======\n(.*?)>>>>>>> REPLACE"
    ),
) -> str:
    """Apply every coset SEARCH/REPLACE block as an exact JSON substring.

    Pinned OpenEvolve's generic helper compares complete *lines*.  A typed
    coset policy becomes one canonical JSON line after its first accepted
    mutation, so a perfectly valid field-level SEARCH block otherwise applies
    zero edits and is silently evaluated as a duplicate child.  Coset genomes
    are data, not source code: exact, unique substring replacement is the
    narrow contract we need here.

    All blocks must apply exactly once, and the resulting canonical policy
    must be semantically different from its parent.  Raising here happens in
    the mutation worker before the expensive evaluator or candidate log is
    touched.
    """

    from openevolve.utils.code_utils import extract_diffs
    from evolve.coset_policy_dispatch import (
        CosetPolicyDispatchError,
        parse_and_render_activated_policy,
        parse_and_render_registered_policy,
    )

    if not isinstance(original_code, str) or not original_code:
        raise ValueError("coset mutation parent is not JSON text")
    if not isinstance(diff_text, str) or not diff_text:
        _raise_coset_mutation_rejection(
            "no_diff_blocks",
            parent_code=original_code,
            detail={"empty_response": True},
        )
    blocks = extract_diffs(diff_text, diff_pattern)
    if not blocks:
        _raise_coset_mutation_rejection(
            "no_diff_blocks",
            parent_code=original_code,
            detail={"empty_response": False},
        )

    parent_render = parse_and_render_registered_policy(original_code)
    mutated = original_code
    for index, (search_text, replace_text) in enumerate(blocks, start=1):
        if not search_text:
            _raise_coset_mutation_rejection(
                "empty_search",
                parent_code=original_code,
                detail={"block": index},
            )
        if search_text == replace_text:
            _raise_coset_mutation_rejection(
                "textual_noop",
                parent_code=original_code,
                detail={"block": index},
            )
        matches = mutated.count(search_text)
        if matches != 1:
            _raise_coset_mutation_rejection(
                "unmatched_search" if matches == 0 else "ambiguous_search",
                parent_code=original_code,
                detail={"block": index, "matches": matches},
            )
        mutated = mutated.replace(search_text, replace_text, 1)

    try:
        activation = _configured_coset_renderer_activation()
        child_render = (
            parse_and_render_registered_policy(mutated)
            if activation is None
            else parse_and_render_activated_policy(mutated, activation)
        )
    except Exception as exc:
        rejection_reason = (
            "dsl_noncanonical"
            if type(exc) is CosetPolicyDispatchError
            and str(exc) == "policy text is not canonicalizable"
            else "dsl_invalid"
        )
        response_payload = diff_text.encode("utf-8")
        mutated_payload = mutated.encode("utf-8")
        _raise_coset_mutation_rejection(
            rejection_reason,
            parent_code=original_code,
            detail={
                "error_type": type(exc).__name__,
                "response_sha256": hashlib.sha256(
                    response_payload
                ).hexdigest(),
                "response_bytes": len(response_payload),
                "mutated_sha256": hashlib.sha256(
                    mutated_payload
                ).hexdigest(),
                "mutated_bytes": len(mutated_payload),
            },
        )
    if child_render.policy_sha256 == parent_render.policy_sha256:
        _raise_coset_mutation_rejection(
            "semantic_noop",
            parent_code=original_code,
            detail={"policy_sha256": parent_render.policy_sha256},
        )
    return mutated


def _managed_openevolve_worker_init(
    config_dict: dict[str, Any],
    evaluation_file: str,
    parent_env: dict[str, str] | None = None,
) -> None:
    """Initialize a pinned worker and preserve live exception provenance.

    ``traceback.format_exc()`` is presentation text: exception chaining and
    PEP 678 notes make it unsuitable as the sole trust boundary.  This wrapper
    runs inside each spawned worker and records frames directly from the live
    exception object before pinned OpenEvolve serializes its Stage-1 envelope.
    """

    import openevolve.evaluator as evaluator_module
    import openevolve.process_parallel as process_module
    import openevolve.utils.code_utils as code_utils_module

    original_initializer = getattr(
        process_module,
        "_qcode_original_worker_init",
        process_module._worker_init,
    )
    if original_initializer is _managed_openevolve_worker_init:
        raise RuntimeError("managed OpenEvolve worker initializer recursed")
    original_initializer(config_dict, evaluation_file, parent_env)
    if (
        Path(evaluation_file).resolve()
        != Path(EVALUATOR_COSET_TWO_BLOCK).resolve()
    ):
        return

    # Install only inside a source-pinned coset worker.  Other OpenEvolve
    # evaluators retain the upstream line-oriented source-code patcher.
    code_utils_module.apply_diff = _apply_coset_literal_diff

    evaluator_type = evaluator_module.Evaluator
    original_context = evaluator_type._create_cascade_error_context

    def structured_context(
        evaluator: Any,
        stage: str,
        error: Exception,
    ) -> dict[str, Any]:
        context = original_context(evaluator, stage, error)
        if not isinstance(context, dict):
            raise RuntimeError("OpenEvolve cascade error context is invalid")
        frames: list[dict[str, str]] = []
        traceback_cursor = error.__traceback__
        while traceback_cursor is not None:
            code = traceback_cursor.tb_frame.f_code
            frames.append({
                "path": str(Path(code.co_filename).resolve()),
                "function": str(code.co_name),
            })
            traceback_cursor = traceback_cursor.tb_next
        enriched = dict(context)
        if STAGE1_EXCEPTION_PROVENANCE_FIELD in enriched:
            raise RuntimeError(
                "OpenEvolve cascade error context reused qcode provenance"
            )
        enriched[STAGE1_EXCEPTION_PROVENANCE_FIELD] = {
            "schema_version": STAGE1_EXCEPTION_PROVENANCE_SCHEMA_VERSION,
            "stage": stage,
            "frames": frames,
        }
        return enriched

    evaluator_type._create_cascade_error_context = structured_context


@contextmanager
def _verified_slice_controller(
    base_iteration: int,
    iterations: int,
    *,
    expected_preflight_contract_id: int | None = None,
    evaluator_kind: str = EVALUATOR_KIND_DEFAULT,
    stage2_cascade_threshold: float | None = None,
    checkpoint_preflight_required: bool = False,
    search_config: Any = None,
    search_portfolio_schema_version: int = SEARCH_PORTFOLIO_SCHEMA_VERSION,
    adaptive_mutation_policy: dict[str, int] | None = None,
    search_regime: dict[str, Any] | None = None,
    coset_map_schema_version: int | None = None,
    coset_renderer_activation: dict[str, Any] | None = None,
):
    if isinstance(iterations, bool) or not isinstance(iterations, int) or iterations < 1:
        raise RuntimeError("managed slice iterations must be positive")
    source_binding, controller_module, process_module = _openevolve_source_binding()
    if coset_map_schema_version is not None and (
        evaluator_kind != EVALUATOR_KIND_COSET_TWO_BLOCK
        or search_config is not None
    ):
        raise RuntimeError(
            "fixed coset MAP geometry requires the coset evaluator and cannot "
            "share the BB search portfolio"
        )
    if coset_renderer_activation is not None and (
        evaluator_kind != EVALUATOR_KIND_COSET_TWO_BLOCK
        or coset_map_schema_version != 4
    ):
        raise RuntimeError(
            "renderer activation requires the renderer-v3 coset portfolio"
        )
    if coset_map_schema_version == 4 and coset_renderer_activation is None:
        raise RuntimeError(
            "renderer-v3 coset scheduling requires a sealed activation"
        )
    validated_coset_activation = (
        None
        if coset_renderer_activation is None
        else _validated_coset_activation_document(
            coset_renderer_activation
        )
    )
    coset_activation_sha256 = (
        hashlib.sha256(b"qcode-coset-registered-default").hexdigest()
        if coset_renderer_activation is None
        else str(coset_renderer_activation["activation_sha256"])
    )
    coset_island_count = (
        int(_coset_portfolio_contract_for_schema(
            coset_map_schema_version
        )["num_islands"])
        if coset_map_schema_version is not None
        else 0
    )
    observer = _SliceObserver(
        base_iteration=base_iteration,
        iterations=iterations,
        result_type=process_module.SerializableResult,
        expected_preflight_contract_id=expected_preflight_contract_id,
        evaluator_kind=evaluator_kind,
        stage2_cascade_threshold=stage2_cascade_threshold,
        checkpoint_preflight_required=checkpoint_preflight_required,
        search_portfolio_schema_version=search_portfolio_schema_version,
        coset_map_schema_version=coset_map_schema_version,
    )
    portfolio_seed: int | None = None
    portfolio_policy: dict[str, int] | None = None
    portfolio_regime = dict(DEFAULT_SEARCH_REGIME)
    if search_config is not None:
        portfolio_seed = _validated_search_portfolio_config(
            search_config,
            schema_version=search_portfolio_schema_version,
        )
        portfolio_policy = (
            dict(DEFAULT_ADAPTIVE_MUTATION_POLICY)
            if adaptive_mutation_policy is None
            else dict(adaptive_mutation_policy)
        )
        # Validate explicit callers through the same exact parser contract.
        if (
            set(portfolio_policy) != set(ADAPTIVE_MUTATION_TACTICS)
            or any(
                isinstance(portfolio_policy[name], bool)
                or not isinstance(portfolio_policy[name], int)
                or portfolio_policy[name] < 0
                for name in ADAPTIVE_MUTATION_TACTICS
            )
            or sum(portfolio_policy.values())
            != ADAPTIVE_MUTATION_TOTAL_WEIGHT
            or portfolio_policy["novel_structure_exploration"]
            < ADAPTIVE_MUTATION_EXPLORATION_FLOOR
        ):
            raise RuntimeError("adaptive mutation policy is invalid")
        observer.search_policy_sha256 = (
            _adaptive_mutation_policy_sha256(portfolio_policy)
        )
        if search_regime is not None:
            marker_regime = dict(search_regime)
            regime_policy_version = marker_regime.pop("policy_version", 1)
            if (
                isinstance(regime_policy_version, bool)
                or regime_policy_version
                not in SEARCH_REGIME_PREFIX_BY_POLICY_VERSION
            ):
                raise RuntimeError(
                    "explicit search regime has an invalid policy version"
                )
            encoded_regime = json.dumps(
                marker_regime,
                sort_keys=True,
                separators=(",", ":"),
                allow_nan=False,
            )
            portfolio_regime = _validated_search_regime(
                SEARCH_REGIME_PREFIX_BY_POLICY_VERSION[
                    regime_policy_version
                ]
                + encoded_regime
            )
        observer.search_regime_status = str(portfolio_regime["status"])
    original_parallel = controller_module.ProcessParallelController
    original_save = controller_module.OpenEvolve._save_checkpoint
    original_worker_init: Any = None
    original_worker_init_alias: Any = None
    had_worker_init_alias = False
    if evaluator_kind == EVALUATOR_KIND_COSET_TWO_BLOCK:
        original_worker_init = getattr(process_module, "_worker_init", None)
        if not callable(original_worker_init):
            raise RuntimeError("pinned OpenEvolve worker initializer is missing")
        had_worker_init_alias = hasattr(
            process_module, "_qcode_original_worker_init"
        )
        original_worker_init_alias = getattr(
            process_module,
            "_qcode_original_worker_init",
            None,
        )
        process_module._qcode_original_worker_init = original_worker_init
        process_module._worker_init = _managed_openevolve_worker_init

    class VerifiedProcessParallelController(original_parallel):
        def __init__(self, *args: Any, **kwargs: Any) -> None:
            super().__init__(*args, **kwargs)
            self._search_iteration_targets: dict[int, int] = {}
            self._search_slice_elites: tuple[tuple[str, ...], ...] | None = (
                None
            )
            self._search_slice_programs: dict[str, Any] | None = None
            self._search_slice_snapshot: dict[str, Any] | None = None
            self._search_slice_artifacts: dict[str, dict[str, Any]] | None = None
            self._coset_iteration_targets: dict[int, int] = {}
            self._coset_active_program_ids: set[str] | None = None
            self._coset_slice_elites: tuple[tuple[str, ...], ...] | None = None
            self._coset_slice_programs: dict[str, Any] | None = None
            self._coset_slice_snapshot: dict[str, Any] | None = None
            self._coset_slice_artifacts: dict[str, dict[str, Any]] | None = None
            if portfolio_seed is not None:
                _validated_search_portfolio_config(
                    self.config,
                    schema_version=search_portfolio_schema_version,
                )
                self.database._calculate_feature_coords = (
                    lambda program: _fixed_search_feature_coords(
                        program,
                        schema_version=search_portfolio_schema_version,
                    )
                )
                _rebuild_fixed_search_feature_maps(
                    self.database,
                    schema_version=search_portfolio_schema_version,
                )
            if coset_map_schema_version is not None:
                _validated_coset_search_portfolio_config(
                    self.config,
                    coset_map_schema_version,
                )
                self.database._calculate_feature_coords = (
                    lambda program: _fixed_coset_feature_coords(
                        program,
                        schema_version=coset_map_schema_version,
                    )
                )
                active_ids = _activation_compatible_coset_program_ids(
                    self.database,
                    coset_renderer_activation,
                )
                if not active_ids:
                    raise RuntimeError(
                        "coset checkpoint has no parent compatible with the "
                        "sealed renderer activation"
                    )
                self._coset_active_program_ids = set(active_ids)
                _rebuild_fixed_coset_feature_maps(
                    self.database,
                    schema_version=coset_map_schema_version,
                    eligible_program_ids=self._coset_active_program_ids,
                )
                # Coset workers are already scheduled across all registered
                # lineage
                # islands.  OpenEvolve migration creates new UUIDs containing
                # identical policies, which wastes evaluations and obscures
                # semantic uniqueness without adding a new MAP cell.
                self.database.should_migrate = lambda: False

        def request_shutdown(self) -> None:
            observer.shutdown_requested = True
            return super().request_shutdown()

        def _submit_iteration(self, iteration: int, island_id: Any = None) -> Any:
            if portfolio_seed is None and coset_map_schema_version is None:
                future = super()._submit_iteration(iteration, island_id)
                return observer.record_submission(iteration, island_id, future)
            if coset_map_schema_version is not None:
                if (
                    isinstance(island_id, bool)
                    or not isinstance(island_id, int)
                    or not 0 <= island_id < coset_island_count
                ):
                    raise RuntimeError("coset iteration has an invalid island")
                # Pinned OpenEvolve fills only the first ``2 * workers``
                # island slots when worker count is smaller than island count,
                # then repeatedly refills those same slots.  Bind the coset
                # lineage to the global iteration instead, so even a one-
                # worker smoke run and every resumed slice cover every island.
                target_island = (
                    iteration - 1
                ) % coset_island_count
                if (
                    self._coset_slice_elites is None
                    or self._coset_slice_programs is None
                    or self._coset_slice_snapshot is None
                    or self._coset_slice_artifacts is None
                ):
                    raise RuntimeError(
                        "coset activation-compatible parent archive was not "
                        "frozen"
                    )
                selectable = list(
                    self._coset_slice_elites[target_island]
                )
                if not selectable:
                    selectable = sorted({
                        program_id
                        for island_elites in self._coset_slice_elites
                        for program_id in island_elites
                    })
                if not selectable:
                    raise RuntimeError(
                        "coset slice has no activation-compatible parent"
                    )
                random_seed = getattr(self.config, "random_seed", None)
                if isinstance(random_seed, bool) or not isinstance(
                    random_seed, int
                ):
                    raise RuntimeError(
                        "coset portfolio random seed is not fixed"
                    )
                ordered_ids = _deterministic_coset_order(
                    selectable,
                    programs=self._coset_slice_programs,
                    seed=random_seed,
                    iteration=iteration,
                    island=target_island,
                    activation_sha256=coset_activation_sha256,
                )
                parent = self._coset_slice_programs[ordered_ids[0]]
                inspiration_ids = ordered_ids[
                    1:1 + self.config.prompt.num_top_programs
                ]
                snapshot = copy.deepcopy(self._coset_slice_snapshot)
                snapshot["artifacts"] = {
                    program_id: copy.deepcopy(
                        self._coset_slice_artifacts[program_id]
                    )
                    for program_id in (parent.id, *inspiration_ids)
                    if program_id in self._coset_slice_artifacts
                }
                snapshot["current_island"] = target_island
                snapshot["sampling_island"] = target_island
                parent_row = snapshot["programs"].get(parent.id)
                if not isinstance(parent_row, dict):
                    raise RuntimeError("coset parent is missing from snapshot")
                metadata = parent_row.get("metadata")
                if not isinstance(metadata, dict):
                    raise RuntimeError("coset parent metadata are invalid")
                parent_row["metadata"] = {
                    **metadata,
                    "island": target_island,
                }
                snapshot["islands"][target_island] = sorted({
                    *snapshot["islands"][target_island],
                    parent.id,
                    *inspiration_ids,
                })
                from evolve.coset_policy_dispatch import (
                    parse_and_render_activated_policy,
                    parse_and_render_registered_policy,
                )

                parent_render = (
                    parse_and_render_registered_policy(parent.code)
                    if validated_coset_activation is None
                    else parse_and_render_activated_policy(
                        parent.code, validated_coset_activation
                    )
                )
                if not parent_render.policy_sha256:
                    raise RuntimeError("coset parent policy identity is empty")
                self._coset_iteration_targets[iteration] = target_island
                future = self.executor.submit(
                    process_module._run_iteration_worker,
                    iteration,
                    snapshot,
                    parent.id,
                    inspiration_ids,
                )
                return observer.record_submission(
                    iteration,
                    target_island,
                    future,
                    search_parent_program_id=parent.id,
                    search_parent_code_sha256=hashlib.sha256(
                        parent.code.encode("utf-8")
                    ).hexdigest(),
                )
            assert portfolio_policy is not None
            schedule = _search_island_schedule(
                observer.iterations,
                observer.search_regime_status,
            )
            target_island = schedule[iteration - observer.start_iteration]
            self._search_iteration_targets[iteration] = target_island
            if (
                self._search_slice_elites is None
                or self._search_slice_programs is None
                or self._search_slice_snapshot is None
                or self._search_slice_artifacts is None
            ):
                raise RuntimeError(
                    "search portfolio parent archive was not frozen"
                )
            selectable_elites = list(
                self._search_slice_elites[target_island]
            )
            if not selectable_elites:
                selectable_elites = sorted({
                    program_id
                    for island_elites in self._search_slice_elites
                    for program_id in island_elites
                })
            if not selectable_elites:
                raise RuntimeError(
                    "search portfolio has no frozen parent elite"
                )
            if any(
                program_id not in self._search_slice_programs
                for program_id in selectable_elites
            ):
                raise RuntimeError(
                    "search portfolio frozen parent snapshot is incomplete"
                )
            elite_ids = _deterministic_search_order(
                selectable_elites,
                programs=self._search_slice_programs,
                seed=portfolio_seed,
                iteration=iteration,
                island=target_island,
            )
            parent = self._search_slice_programs[elite_ids[0]]
            inspiration_ids = elite_ids[
                1:1 + self.config.prompt.num_top_programs
            ]
            # Every worker in this managed slice sees the same immutable
            # start-of-slice database.  A population cleanup caused by an
            # earlier completion therefore cannot delete a parent needed by a
            # later submission, and completion order cannot affect prompts.
            snapshot = copy.deepcopy(self._search_slice_snapshot)
            snapshot["artifacts"] = {
                program_id: copy.deepcopy(
                    self._search_slice_artifacts[program_id]
                )
                for program_id in (parent.id, *inspiration_ids)
                if program_id in self._search_slice_artifacts
            }
            snapshot["current_island"] = target_island
            snapshot["sampling_island"] = target_island
            parent_row = snapshot["programs"].get(parent.id)
            if not isinstance(parent_row, dict):
                raise RuntimeError("selected parent is missing from snapshot")
            parent_metadata = parent_row.get("metadata")
            if not isinstance(parent_metadata, dict):
                raise RuntimeError("selected parent snapshot metadata are invalid")
            parent_metadata = dict(parent_metadata)
            parent_metadata["island"] = target_island
            parent_row["metadata"] = parent_metadata
            snapshot["islands"][target_island] = sorted({
                *snapshot["islands"][target_island],
                parent.id,
                *inspiration_ids,
            })
            tactic = _adaptive_mutation_tactic(
                portfolio_policy,
                program_code=parent.code,
                iteration=iteration,
            )
            parent_artifacts = snapshot["artifacts"].get(parent.id)
            if parent_artifacts is None:
                parent_artifacts = {}
            if not isinstance(parent_artifacts, dict):
                raise RuntimeError("selected parent artifacts are not an object")
            parent_artifacts = dict(parent_artifacts)
            parent_artifacts[SEARCH_PORTFOLIO_ARTIFACT_KEY] = {
                "schema_version": search_portfolio_schema_version,
                "island_id": target_island,
                "island_role": SEARCH_PORTFOLIO_ROLES[target_island],
                "island_directive":
                    SEARCH_PORTFOLIO_DIRECTIVES[target_island],
                "support_split_targets": [
                    list(split)
                    for split in SEARCH_PORTFOLIO_SUPPORT_TARGETS[
                        target_island
                    ]
                ],
                "adaptive_mutation_tactic": tactic,
                "adaptive_mutation_directive":
                    ADAPTIVE_MUTATION_DIRECTIVES[tactic],
                "search_regime": copy.deepcopy(portfolio_regime),
                "search_regime_directive": SEARCH_REGIME_DIRECTIVES[
                    observer.search_regime_status
                ],
                "policy_sha256": observer.search_policy_sha256,
            }
            snapshot["artifacts"][parent.id] = parent_artifacts
            future = self.executor.submit(
                process_module._run_iteration_worker,
                iteration,
                snapshot,
                parent.id,
                inspiration_ids,
            )
            return observer.record_submission(
                iteration,
                target_island,
                future,
                search_role=SEARCH_PORTFOLIO_ROLES[target_island],
                search_tactic=tactic,
                search_parent_program_id=parent.id,
                search_parent_code_sha256=hashlib.sha256(
                    parent.code.encode("utf-8")
                ).hexdigest(),
            )

        async def run_evolution(
            self,
            start_iteration: int,
            max_iterations: int,
            target_score: Any = None,
            checkpoint_callback: Any = None,
        ) -> Any:
            observer.begin(start_iteration, max_iterations, target_score)
            if portfolio_seed is not None:
                _rebuild_fixed_search_feature_maps(
                    self.database,
                    schema_version=search_portfolio_schema_version,
                )
                self._search_slice_elites = tuple(
                    tuple(_search_elite_ids(
                        self.database,
                        island,
                        schema_version=search_portfolio_schema_version,
                    ))
                    for island in range(SEARCH_PORTFOLIO_ISLAND_COUNT)
                )
                frozen_ids = {
                    program_id
                    for island_elites in self._search_slice_elites
                    for program_id in island_elites
                }
                self._search_slice_programs = {
                    program_id: copy.deepcopy(
                        self.database.programs[program_id]
                    )
                    for program_id in frozen_ids
                }
                self._search_slice_snapshot = copy.deepcopy(
                    self._create_database_snapshot()
                )
                # OpenEvolve normally includes artifacts only for the first
                # ``max_snapshot_artifacts`` insertion-ordered programs. Our
                # deterministic MAP-Elites parent can be any frozen elite, so
                # that generic cap could silently strip the low-weight witness
                # feedback from the actual parent/inspirations. Freeze the
                # artifacts for every selectable elite in controller memory,
                # then inject only the selected parent/inspirations per worker.
                self._search_slice_artifacts = {}
                for program_id in sorted(frozen_ids):
                    artifact_getter = getattr(
                        self.database, "get_artifacts", None
                    )
                    frozen_artifacts = (
                        artifact_getter(program_id)
                        if callable(artifact_getter)
                        else getattr(self.database, "artifacts", {}).get(
                            program_id
                        )
                    )
                    if frozen_artifacts:
                        self._search_slice_artifacts[program_id] = copy.deepcopy(
                            frozen_artifacts
                        )
            if coset_map_schema_version is not None:
                if not self._coset_active_program_ids:
                    raise RuntimeError(
                        "coset slice has no activation-compatible programs"
                    )
                _rebuild_fixed_coset_feature_maps(
                    self.database,
                    schema_version=coset_map_schema_version,
                    eligible_program_ids=self._coset_active_program_ids,
                )
                self._coset_slice_elites = tuple(
                    tuple(sorted(program_ids))
                    for program_ids in self.database.islands
                )
                frozen_coset_ids = {
                    program_id
                    for island_elites in self._coset_slice_elites
                    for program_id in island_elites
                }
                if not frozen_coset_ids:
                    raise RuntimeError(
                        "coset compatible MAP archive has no elite"
                    )
                self._coset_slice_programs = {
                    program_id: copy.deepcopy(
                        self.database.programs[program_id]
                    )
                    for program_id in frozen_coset_ids
                }
                self._coset_slice_snapshot = copy.deepcopy(
                    self._create_database_snapshot()
                )
                self._coset_slice_artifacts = {}
                for program_id in sorted(frozen_coset_ids):
                    artifact_getter = getattr(
                        self.database, "get_artifacts", None
                    )
                    frozen_artifacts = (
                        artifact_getter(program_id)
                        if callable(artifact_getter)
                        else getattr(self.database, "artifacts", {}).get(
                            program_id
                        )
                    )
                    if frozen_artifacts:
                        self._coset_slice_artifacts[program_id] = copy.deepcopy(
                            frozen_artifacts
                        )
            checkpoint_controller = getattr(checkpoint_callback, "__self__", None)
            if checkpoint_controller is None:
                observer.violations.append(
                    "checkpoint callback is not bound to OpenEvolve"
                )
            elif observer.checkpoint_controller not in (None, checkpoint_controller):
                observer.violations.append(
                    "checkpoint controller changed during the slice"
                )
            else:
                observer.checkpoint_controller = checkpoint_controller
            original_add = self.database.add

            def observed_add(program: Any, iteration: Any = None, target_island: Any = None) -> Any:
                parent = (
                    self.database.programs.get(getattr(program, "parent_id", None))
                    if iteration is None
                    else None
                )
                effective_target = target_island
                if portfolio_seed is not None and iteration is not None:
                    effective_target = self._search_iteration_targets.get(
                        iteration
                    )
                    if effective_target is None:
                        observer.violations.append(
                            f"database add for iteration {iteration} has no "
                            "effective island"
                        )
                    metadata = getattr(program, "metadata", None)
                    if (
                        not isinstance(metadata, dict)
                        or metadata.get("island") != effective_target
                    ):
                        observer.violations.append(
                            f"database add for iteration {iteration} changed "
                            "worker island content"
                        )
                elif (
                    coset_map_schema_version is not None
                    and iteration is not None
                ):
                    effective_target = self._coset_iteration_targets.get(
                        iteration
                    )
                    if effective_target is None:
                        observer.violations.append(
                            f"database add for iteration {iteration} has no "
                            "coset target island"
                        )
                    metadata = getattr(program, "metadata", None)
                    if (
                        not isinstance(metadata, dict)
                        or metadata.get("island") != effective_target
                    ):
                        observer.violations.append(
                            f"database add for iteration {iteration} changed "
                            "coset worker island content"
                        )
                result = original_add(
                    program,
                    iteration=iteration,
                    target_island=effective_target,
                )
                if portfolio_seed is not None:
                    _rebuild_fixed_search_feature_maps(
                        self.database,
                        schema_version=search_portfolio_schema_version,
                    )
                elif coset_map_schema_version is not None:
                    if self._coset_active_program_ids is None:
                        observer.violations.append(
                            "coset active program set was not initialized"
                        )
                    elif self.database.programs.get(
                        getattr(program, "id", None)
                    ) is not None:
                        self._coset_active_program_ids.add(program.id)
                    _rebuild_fixed_coset_feature_maps(
                        self.database,
                        schema_version=coset_map_schema_version,
                        eligible_program_ids=(
                            self._coset_active_program_ids
                        ),
                    )
                stored = self.database.programs.get(getattr(program, "id", None))
                if stored is None:
                    observer.violations.append(
                        f"database add for iteration {iteration} did not store the program"
                    )
                elif iteration is None:
                    observer.record_auxiliary_program_add(
                        program=program,
                        stored=stored,
                        parent=parent,
                        target_island=target_island,
                        num_islands=self.num_islands,
                    )
                else:
                    observer.record_program_add(iteration, stored)
                return result

            self.database.add = observed_add
            try:
                result = await super().run_evolution(
                    start_iteration,
                    max_iterations,
                    target_score,
                    checkpoint_callback,
                )
            finally:
                self.database.add = original_add
            observer.verify(self)
            return result

    def observed_save(controller: Any, iteration: int) -> None:
        valid_iteration = (
            not isinstance(iteration, bool)
            and isinstance(iteration, int)
            and observer.start_iteration <= iteration <= observer.end_iteration
        )
        if not observer.accounting_complete:
            if not valid_iteration:
                observer.violations.append(
                    f"checkpoint save used out-of-slice iteration {iteration!r}"
                )
            observer.checkpoint_saves.append({
                "iteration": iteration,
                "accounting_complete": False,
                "checkpoint_sha256": None,
                "checkpoint_programs": None,
                "suppressed": True,
            })
            return
        if iteration != observer.end_iteration:
            observer.violations.append(
                f"post-accounting checkpoint save was not the slice end: {iteration!r}"
            )
            raise RuntimeError(observer.violations[-1])
        original_save(controller, iteration)
        observer.record_checkpoint_save(controller, iteration)

    controller_module.ProcessParallelController = VerifiedProcessParallelController
    controller_module.OpenEvolve._save_checkpoint = observed_save
    try:
        yield observer, source_binding
        observer.ensure_final_checkpoint()
    finally:
        controller_module.OpenEvolve._save_checkpoint = original_save
        controller_module.ProcessParallelController = original_parallel
        if evaluator_kind == EVALUATOR_KIND_COSET_TWO_BLOCK:
            process_module._worker_init = original_worker_init
            if had_worker_init_alias:
                process_module._qcode_original_worker_init = (
                    original_worker_init_alias
                )
            else:
                delattr(process_module, "_qcode_original_worker_init")


def _launch_input_identities(
    config_path: str | Path,
    seed_path: str | Path,
    evaluator_path: str | Path,
    context_path: str | Path,
    context_identity: dict[str, Any],
    dependency_identities: dict[str, dict[str, Any]],
    backend_path: str | Path | None,
    codex_executable_identity: dict[str, Any] | None,
    evaluator_kind: str = EVALUATOR_KIND_DEFAULT,
    negative_feedback_snapshot_identity: dict[str, Any] | None = None,
    negative_feedback_manifest_identity: dict[str, Any] | None = None,
    renderer_activation_identity: dict[str, Any] | None = None,
) -> dict[str, dict[str, Any]]:
    observed_context = _file_identity(
        context_path, "evolution humanize context"
    )
    if observed_context != context_identity:
        raise RuntimeError("evolution humanize context changed after snapshot")
    observed_dependencies = _evaluator_dependency_identities(evaluator_kind)
    if observed_dependencies != dependency_identities:
        raise RuntimeError("evolution evaluator dependencies changed during the slice")
    identities = {
        "config": _file_identity(config_path, "evolution config"),
        "seed": _file_identity(seed_path, "evolution seed"),
        "launcher": _file_identity(Path(__file__), "evolution launcher"),
        "evaluator": _file_identity(evaluator_path, "evolution evaluator"),
        "context": dict(context_identity),
    }
    identities.update(
        {name: dict(value) for name, value in dependency_identities.items()}
    )
    if (negative_feedback_snapshot_identity is None) != (
        negative_feedback_manifest_identity is None
    ):
        raise RuntimeError("negative-feedback launch identity is incomplete")
    if negative_feedback_snapshot_identity is not None:
        identities["coset_negative_feedback_snapshot"] = dict(
            negative_feedback_snapshot_identity
        )
        identities["coset_negative_feedback_snapshot_manifest"] = dict(
            negative_feedback_manifest_identity
        )
    if renderer_activation_identity is not None:
        if evaluator_kind != EVALUATOR_KIND_COSET_TWO_BLOCK:
            raise RuntimeError(
                "renderer activation launch identity requires coset evaluator"
            )
        identities["coset_renderer_activation"] = dict(
            renderer_activation_identity
        )
    if backend_path is not None:
        identities["backend"] = _file_identity(
            backend_path, "evolution model backend"
        )
    if codex_executable_identity is not None:
        executable_path = codex_executable_identity.get("path")
        if not isinstance(executable_path, str):
            raise RuntimeError("Codex executable identity has no path")
        observed_executable = _file_identity(
            executable_path, "Codex CLI native executable"
        )
        observed_executable["mode"] = stat.S_IMODE(
            Path(executable_path).stat().st_mode
        )
        if observed_executable != codex_executable_identity:
            raise RuntimeError(
                "Codex CLI native executable changed during the slice"
            )
        identities["codex_executable"] = dict(codex_executable_identity)
    return identities


def _resolve_native_codex_path(requested_bin: str) -> Path:
    launcher = shutil.which(requested_bin)
    if launcher is None:
        raise RuntimeError(f"Codex CLI executable is unavailable: {requested_bin}")
    launcher_path = Path(launcher).resolve(strict=True)
    with launcher_path.open("rb") as stream:
        magic = stream.read(4)
    if magic in (b"\x7fELF", b"MZ\x90\x00"):
        return launcher_path
    if launcher_path.name != "codex.js" or launcher_path.parent.name != "bin":
        raise RuntimeError(
            "managed QCODE_CODEX_BIN must be the official codex.js launcher "
            "or a native Codex executable"
        )
    system = platform_module.system().lower()
    machine = platform_module.machine().lower()
    targets = {
        ("linux", "x86_64"): (
            "@openai/codex-linux-x64",
            "x86_64-unknown-linux-musl",
            "codex",
        ),
        ("linux", "aarch64"): (
            "@openai/codex-linux-arm64",
            "aarch64-unknown-linux-musl",
            "codex",
        ),
        ("darwin", "x86_64"): (
            "@openai/codex-darwin-x64",
            "x86_64-apple-darwin",
            "codex",
        ),
        ("darwin", "arm64"): (
            "@openai/codex-darwin-arm64",
            "aarch64-apple-darwin",
            "codex",
        ),
        ("windows", "amd64"): (
            "@openai/codex-win32-x64",
            "x86_64-pc-windows-msvc",
            "codex.exe",
        ),
        ("windows", "arm64"): (
            "@openai/codex-win32-arm64",
            "aarch64-pc-windows-msvc",
            "codex.exe",
        ),
    }
    target = targets.get((system, machine))
    if target is None:
        raise RuntimeError(
            f"unsupported managed Codex platform: {system}/{machine}"
        )
    package_name, target_triple, executable_name = target
    package_root = launcher_path.parent.parent
    candidates = (
        package_root
        / "node_modules"
        / Path(*package_name.split("/"))
        / "vendor"
        / target_triple
        / "bin"
        / executable_name,
        package_root / "vendor" / target_triple / "bin" / executable_name,
    )
    for candidate in candidates:
        try:
            resolved = candidate.resolve(strict=True)
        except OSError:
            continue
        if resolved.is_file():
            return resolved
    raise RuntimeError(
        "cannot resolve the official Codex launcher to its native executable"
    )


def _resolve_codex_execution_binding(
) -> tuple[dict[str, Any], str, str]:
    native_path = _resolve_native_codex_path(
        os.environ.get("QCODE_CODEX_BIN", "codex")
    )
    if not native_path.is_file() or not os.access(native_path, os.X_OK):
        raise RuntimeError(
            f"Codex CLI native binary is not executable: {native_path}"
        )
    identity = _file_identity(native_path, "Codex CLI native executable")
    identity["mode"] = stat.S_IMODE(native_path.stat().st_mode)
    project_root = Path(PROJECT_ROOT).resolve(strict=True)
    requested_cwd = Path(
        os.environ.get("QCODE_CODEX_CWD", str(project_root))
    ).resolve(strict=True)
    if requested_cwd != project_root:
        raise RuntimeError(
            "managed Codex CLI cwd must be the qcode-discovery project root"
        )
    try:
        completed = subprocess.run(
            [str(native_path), "--version"],
            check=True,
            capture_output=True,
            text=True,
            timeout=10,
        )
    except (OSError, subprocess.SubprocessError) as exc:
        raise RuntimeError("cannot identify the Codex CLI version") from exc
    version = completed.stdout.strip()
    if not version or len(version) > 500:
        raise RuntimeError("Codex CLI returned an invalid version identity")
    os.environ["QCODE_CODEX_BIN"] = str(native_path)
    os.environ["QCODE_CODEX_CWD"] = str(project_root)
    return identity, version, str(project_root)


def _validated_negative_feedback_binding(
    *,
    live_archive_path: str | None,
    snapshot_path: str | None,
    snapshot_sha256: str | None,
    archive_sha256: str | None,
    manifest_path: str | None,
    manifest_sha256: str | None,
    feedback_epoch: int | None,
    required: bool,
    expected_run_id: str | None = None,
) -> tuple[dict[str, Any], dict[str, Any], dict[str, Any]] | None:
    """Validate the managed mutable-write/immutable-read archive split."""

    values = (
        live_archive_path,
        snapshot_path,
        snapshot_sha256,
        archive_sha256,
        manifest_path,
        manifest_sha256,
        feedback_epoch,
    )
    supplied = tuple(value is not None for value in values)
    if not any(supplied):
        if required:
            raise RuntimeError(
                "managed coset evolution requires a negative-feedback snapshot"
            )
        return None
    if not all(supplied):
        raise RuntimeError("negative-feedback invocation binding is incomplete")
    assert (
        live_archive_path is not None
        and snapshot_path is not None
        and snapshot_sha256 is not None
        and archive_sha256 is not None
        and manifest_path is not None
        and manifest_sha256 is not None
        and feedback_epoch is not None
    )
    live = Path(live_archive_path)
    snapshot = Path(snapshot_path)
    manifest_file = Path(manifest_path)
    if (
        not live.is_absolute()
        or not snapshot.is_absolute()
        or not manifest_file.is_absolute()
        or len({live, snapshot, manifest_file}) != 3
        or isinstance(feedback_epoch, bool)
        or feedback_epoch < 1
        or any(
            re.fullmatch(r"[0-9a-f]{64}", value) is None
            for value in (snapshot_sha256, archive_sha256, manifest_sha256)
        )
    ):
        raise RuntimeError("negative-feedback invocation identity is invalid")
    snapshot_identity = _file_identity(snapshot, "negative-feedback snapshot")
    manifest_identity = _file_identity(
        manifest_file, "negative-feedback snapshot manifest"
    )
    if (
        snapshot_identity["sha256"] != snapshot_sha256
        or manifest_identity["sha256"] != manifest_sha256
    ):
        raise RuntimeError("negative-feedback snapshot bytes changed")
    from evolve.coset_negative_archive import (
        NegativeArchiveError,
        load_feedback_snapshot_manifest,
    )

    try:
        manifest = load_feedback_snapshot_manifest(
            manifest_file,
            expected_live_archive_path=live,
            expected_snapshot_path=snapshot,
            expected_feedback_epoch=feedback_epoch,
            expected_run_id=expected_run_id,
        )
    except (OSError, NegativeArchiveError) as exc:
        raise RuntimeError(
            f"negative-feedback snapshot validation failed: {exc}"
        ) from exc
    if (
        manifest["snapshot_sha256"] != snapshot_sha256
        or manifest["archive_sha256"] != archive_sha256
    ):
        raise RuntimeError("negative-feedback archive identity changed")
    invocation = {
        "qcode_negative_feedback_live_archive_path": str(live),
        "qcode_negative_feedback_snapshot_path": str(snapshot),
        "qcode_negative_feedback_snapshot_sha256": snapshot_sha256,
        "qcode_negative_feedback_archive_sha256": archive_sha256,
        "qcode_negative_feedback_manifest_path": str(manifest_file),
        "qcode_negative_feedback_manifest_sha256": manifest_sha256,
        "qcode_negative_feedback_epoch": feedback_epoch,
    }
    return invocation, snapshot_identity, manifest_identity


def _validated_renderer_activation_binding(
    activation_path: str | Path | None,
    *,
    required: bool,
) -> tuple[dict[str, Any], dict[str, Any]] | None:
    """Replay one source-registry activation and bind its exact file bytes."""

    if activation_path is None:
        if required:
            raise RuntimeError(
                "managed renderer-v3 evolution requires a sealed activation"
            )
        return None
    path = Path(activation_path)
    if not path.is_absolute():
        raise RuntimeError("coset renderer activation path must be absolute")
    identity = _file_identity(path, "coset renderer activation")

    def reject_duplicates(pairs: list[tuple[str, Any]]) -> dict[str, Any]:
        result: dict[str, Any] = {}
        for name, value in pairs:
            if name in result:
                raise ValueError(f"duplicate activation field: {name}")
            result[name] = value
        return result

    try:
        document = json.loads(
            path.read_text(encoding="utf-8"),
            object_pairs_hook=reject_duplicates,
            parse_constant=lambda value: (_ for _ in ()).throw(
                ValueError(f"non-finite activation value: {value}")
            ),
        )
        from evolve.coset_search_contract import (
            coset_renderer_activation_document,
            trusted_coset_renderer_activation_from_document,
        )

        activation = trusted_coset_renderer_activation_from_document(document)
        replayed = coset_renderer_activation_document(activation)
    except (OSError, UnicodeError, ValueError, json.JSONDecodeError) as exc:
        raise RuntimeError(
            f"coset renderer activation cannot be replayed: {exc}"
        ) from exc
    if document != replayed:
        raise RuntimeError("coset renderer activation is not canonical data")
    return replayed, identity


def _validated_invocation_binding(
    invocation: dict[str, Any],
    backend_path: str | Path | None,
    codex_executable_identity: dict[str, Any] | None,
    renderer_activation: dict[str, Any] | None = None,
) -> dict[str, Any]:
    expected_fields = {
        "model_names",
        "reasoning_effort",
        "codex_cli",
        "max_parallel_evaluations",
        "api_base",
        "temperature_disabled",
        "codex_version",
        "codex_cwd",
        "codex_executable_mode",
    }
    if ACTIVE_GEOMETRY_CONTRACT != LEGACY_GEOMETRY_CONTRACT:
        expected_fields.add(SEARCH_GEOMETRY_CONTRACT_FIELD)
    if not isinstance(invocation, dict):
        raise RuntimeError("managed invocation binding fields are incomplete")
    observed_fields = set(invocation)
    has_evaluator_kind = EVALUATOR_KIND_BINDING_FIELD in observed_fields
    has_action_catalog = (
        ACTION_CATALOG_SHA256_BINDING_FIELD in observed_fields
    )
    has_renderer_activation = (
        COSET_RENDERER_ACTIVATION_SHA256_BINDING_FIELD in observed_fields
    )
    feedback_fields = observed_fields & set(
        COSET_NEGATIVE_FEEDBACK_INVOCATION_FIELDS
    )
    if feedback_fields and feedback_fields != set(
        COSET_NEGATIVE_FEEDBACK_INVOCATION_FIELDS
    ):
        raise RuntimeError("managed invocation negative-feedback binding is incomplete")
    if has_evaluator_kind != has_action_catalog:
        raise RuntimeError("managed invocation coset binding is incomplete")
    if has_evaluator_kind:
        expected_fields.add(EVALUATOR_KIND_BINDING_FIELD)
        expected_fields.add(ACTION_CATALOG_SHA256_BINDING_FIELD)
        if feedback_fields:
            expected_fields.update(COSET_NEGATIVE_FEEDBACK_INVOCATION_FIELDS)
        if has_renderer_activation:
            expected_fields.add(
                COSET_RENDERER_ACTIVATION_SHA256_BINDING_FIELD
            )
    elif has_renderer_activation or feedback_fields:
        raise RuntimeError(
            "managed invocation coset extension has no coset evaluator"
        )
    if observed_fields != expected_fields:
        raise RuntimeError("managed invocation binding fields are incomplete")
    if has_evaluator_kind:
        evaluator_kind = invocation[EVALUATOR_KIND_BINDING_FIELD]
        if evaluator_kind != EVALUATOR_KIND_COSET_TWO_BLOCK:
            raise RuntimeError("managed invocation evaluator kind is invalid")
        if (
            invocation[ACTION_CATALOG_SHA256_BINDING_FIELD]
            != _coset_action_catalog_sha256()
        ):
            raise RuntimeError("managed invocation action catalog changed")
        if has_renderer_activation:
            if renderer_activation is None:
                from evolve.coset_search_contract import (
                    coset_renderer_activation_document,
                    default_coset_renderer_activation,
                )

                renderer_activation = coset_renderer_activation_document(
                    default_coset_renderer_activation()
                )
            else:
                try:
                    from evolve.coset_search_contract import (
                        coset_renderer_activation_document,
                        trusted_coset_renderer_activation_from_document,
                    )

                    activation_value = (
                        trusted_coset_renderer_activation_from_document(
                            renderer_activation
                        )
                    )
                    if coset_renderer_activation_document(
                        activation_value
                    ) != renderer_activation:
                        raise ValueError("activation replay changed")
                except (TypeError, ValueError) as exc:
                    raise RuntimeError(
                        "managed invocation renderer activation is invalid"
                    ) from exc
            expected_activation = renderer_activation.get(
                "activation_sha256"
            )
            if invocation[
                COSET_RENDERER_ACTIVATION_SHA256_BINDING_FIELD
            ] != expected_activation:
                raise RuntimeError(
                    "managed invocation renderer activation changed"
                )
        if feedback_fields:
            replayed = _validated_negative_feedback_binding(
                live_archive_path=invocation[
                    "qcode_negative_feedback_live_archive_path"
                ],
                snapshot_path=invocation[
                    "qcode_negative_feedback_snapshot_path"
                ],
                snapshot_sha256=invocation[
                    "qcode_negative_feedback_snapshot_sha256"
                ],
                archive_sha256=invocation[
                    "qcode_negative_feedback_archive_sha256"
                ],
                manifest_path=invocation[
                    "qcode_negative_feedback_manifest_path"
                ],
                manifest_sha256=invocation[
                    "qcode_negative_feedback_manifest_sha256"
                ],
                feedback_epoch=invocation["qcode_negative_feedback_epoch"],
                required=True,
            )
            assert replayed is not None
            if replayed[0] != {
                name: invocation[name]
                for name in COSET_NEGATIVE_FEEDBACK_INVOCATION_FIELDS
            }:
                raise RuntimeError(
                    "managed invocation negative-feedback binding changed"
                )
    model_names = invocation["model_names"]
    if (
        not isinstance(model_names, list)
        or not model_names
        or any(not isinstance(name, str) or not name for name in model_names)
    ):
        raise RuntimeError("managed invocation model_names are invalid")
    reasoning_effort = invocation["reasoning_effort"]
    if reasoning_effort is not None and (
        not isinstance(reasoning_effort, str) or not reasoning_effort
    ):
        raise RuntimeError("managed invocation reasoning_effort is invalid")
    codex_cli = invocation["codex_cli"]
    if not isinstance(codex_cli, bool):
        raise RuntimeError("managed invocation codex_cli is invalid")
    if codex_cli != (
        backend_path is not None and codex_executable_identity is not None
    ):
        raise RuntimeError("managed invocation backend binding is inconsistent")
    codex_version = invocation["codex_version"]
    codex_cwd = invocation["codex_cwd"]
    codex_mode = invocation["codex_executable_mode"]
    if codex_cli:
        if not isinstance(codex_version, str) or not codex_version:
            raise RuntimeError("managed invocation codex_version is invalid")
        if (
            not isinstance(codex_cwd, str)
            or Path(codex_cwd) != Path(PROJECT_ROOT).resolve()
        ):
            raise RuntimeError("managed invocation codex_cwd is invalid")
        if (
            isinstance(codex_mode, bool)
            or not isinstance(codex_mode, int)
            or codex_mode != codex_executable_identity.get("mode")
        ):
            raise RuntimeError(
                "managed invocation codex_executable_mode is invalid"
            )
    elif any(
        value is not None for value in (codex_version, codex_cwd, codex_mode)
    ):
        raise RuntimeError("non-Codex invocation contains Codex execution fields")
    workers = invocation["max_parallel_evaluations"]
    if isinstance(workers, bool) or not isinstance(workers, int) or workers < 1:
        raise RuntimeError(
            "managed invocation max_parallel_evaluations is invalid"
        )
    api_base = invocation["api_base"]
    if not isinstance(api_base, str) or not api_base:
        raise RuntimeError("managed invocation api_base is invalid")
    if not isinstance(invocation["temperature_disabled"], bool):
        raise RuntimeError("managed invocation temperature_disabled is invalid")
    if ACTIVE_GEOMETRY_CONTRACT != LEGACY_GEOMETRY_CONTRACT and (
        invocation.get(SEARCH_GEOMETRY_CONTRACT_FIELD)
        != ACTIVE_GEOMETRY_CONTRACT
    ):
        raise RuntimeError(
            "managed invocation search geometry contract is invalid"
        )
    return dict(invocation)


def _write_slice_witness(
    witness_path: str | Path,
    *,
    observer: _SliceObserver,
    source_binding: dict[str, dict[str, Any]],
    output_dir: str | Path,
    resume_checkpoint: str | Path | None,
    iterations: int,
    config_path: str | Path,
    seed_path: str | Path,
    evaluator_path: str | Path,
    context_path: str | Path,
    context_identity: dict[str, Any],
    dependency_identities: dict[str, dict[str, Any]],
    backend_path: str | Path | None,
    codex_executable_identity: dict[str, Any] | None,
    invocation: dict[str, Any],
    candidate_log_path: str | Path,
    candidate_start_offset: int,
    renderer_activation: dict[str, Any] | None = None,
    renderer_activation_identity: dict[str, Any] | None = None,
) -> tuple[dict[str, Any], dict[str, Any]]:
    if not observer.accounting_complete:
        raise RuntimeError("OpenEvolve slice accounting did not complete")
    effective_invocation = _validated_invocation_binding(
        invocation,
        backend_path,
        codex_executable_identity,
        renderer_activation,
    )
    current_source_binding, _, _ = _openevolve_source_binding()
    if current_source_binding != source_binding:
        raise RuntimeError("OpenEvolve source binding changed during the slice")
    resolved_output = Path(output_dir).resolve()
    result_checkpoint = _strong_checkpoint_descriptor(
        resolved_output,
        resolved_output / "checkpoints" / f"checkpoint_{observer.end_iteration}",
        expected_iteration=observer.end_iteration,
    )
    if observer.expected_preflight_contract_id is not None:
        _checkpoint_preflight_summary(
            result_checkpoint["path"],
            expected_contract_id=observer.expected_preflight_contract_id,
            cascade_threshold=observer.stage2_cascade_threshold,
            evaluator_kind=observer.evaluator_kind,
            coset_map_schema_version=observer.coset_map_schema_version,
        )
    if (
        observer.checkpoint_preflight_required
        and observer.checkpoint_preflight_report is None
    ):
        raise RuntimeError(
            "checkpoint winner preflight did not complete before witness"
        )
    if not any(
        save["iteration"] == observer.end_iteration
        and save["accounting_complete"] is True
        and save["checkpoint_sha256"] == result_checkpoint["sha256"]
        and save["checkpoint_programs"] == result_checkpoint["programs"]
        for save in observer.checkpoint_saves
    ):
        raise RuntimeError(
            "expected checkpoint was not saved after complete slice accounting"
        )
    launch_binding = _launch_input_identities(
        config_path,
        seed_path,
        evaluator_path,
        context_path,
        context_identity,
        dependency_identities,
        backend_path,
        codex_executable_identity,
        effective_invocation.get(
            EVALUATOR_KIND_BINDING_FIELD,
            EVALUATOR_KIND_DEFAULT,
        ),
        (
            _file_identity(
                effective_invocation["qcode_negative_feedback_snapshot_path"],
                "negative-feedback snapshot",
            )
            if COSET_NEGATIVE_FEEDBACK_INVOCATION_FIELDS.issubset(
                effective_invocation
            )
            else None
        ),
        (
            _file_identity(
                effective_invocation["qcode_negative_feedback_manifest_path"],
                "negative-feedback snapshot manifest",
            )
            if COSET_NEGATIVE_FEEDBACK_INVOCATION_FIELDS.issubset(
                effective_invocation
            )
            else None
        ),
        renderer_activation_identity,
    )
    from evolve.openevolve_evaluator import candidate_log_range_identity

    candidate_source = candidate_log_range_identity(
        Path(candidate_log_path).resolve(),
        start_offset=candidate_start_offset,
    )
    payload: dict[str, Any] = {
        "schema_version": EVOLUTION_SLICE_WITNESS_SCHEMA_VERSION,
        "status": "completed",
        "output_dir": str(resolved_output),
        "resume_checkpoint": (
            None if resume_checkpoint is None else str(Path(resume_checkpoint).resolve())
        ),
        "base_last_iteration": observer.base_iteration,
        "iterations_requested": iterations,
        "slice_start_iteration": observer.start_iteration,
        "slice_end_iteration": observer.end_iteration,
        "slice_iteration_count": iterations,
        "slice_iterations_sha256": _slice_iterations_sha256(
            observer.start_iteration, iterations
        ),
        "submission_attempts": sorted(
            observer.submission_attempts, key=lambda item: item["iteration"]
        ),
        "outcomes": [observer.outcomes[i] for i in observer.expected_iterations],
        "successful_evaluations": sum(
            outcome.get("status") == "program_added"
            for outcome in observer.outcomes.values()
        ),
        "worker_errors": sum(
            outcome.get("status") == "worker_error"
            for outcome in observer.outcomes.values()
        ),
        "checkpoint_saves": observer.checkpoint_saves,
        "result_checkpoint": result_checkpoint["path"],
        "result_last_iteration": result_checkpoint["last_iteration"],
        "result_checkpoint_sha256": result_checkpoint["sha256"],
        "result_checkpoint_programs": result_checkpoint["programs"],
        "candidate_log_path": candidate_source["path"],
        "candidate_log_device": candidate_source["device"],
        "candidate_log_inode": candidate_source["inode"],
        "candidate_start_offset": candidate_source["start_offset"],
        "candidate_end_offset": candidate_source["end_offset"],
        "candidate_range_sha256": candidate_source["sha256"],
        "candidate_range_bytes": candidate_source["bytes"],
        "candidate_wal_clean": candidate_source["wal_clean"],
        "openevolve_version": SUPPORTED_OPENEVOLVE_VERSION,
        "completed_at": datetime.now().astimezone().isoformat(),
        "search_portfolio": (
            None
            if observer.search_policy_sha256 is None
            else {
                "schema_version": observer.search_portfolio_schema_version,
                "island_count": SEARCH_PORTFOLIO_ISLAND_COUNT,
                "roles": list(SEARCH_PORTFOLIO_ROLES),
                "feature_dimensions": list(
                    _search_portfolio_spec(
                        observer.search_portfolio_schema_version
                    )[0]
                ),
                "regime_status": observer.search_regime_status,
                "policy_sha256": observer.search_policy_sha256,
                "role_submission_counts": {
                    role: observer.search_role_submission_counts.get(role, 0)
                    for role in SEARCH_PORTFOLIO_ROLES
                },
            }
        ),
    }
    if resume_checkpoint is not None:
        # Schema 7 makes the resume preflight (including a one-time legacy
        # genome epoch replacement) durable instead of merely checking it in
        # controller memory.  The witness hash then binds the sealed source
        # checkpoint to the exact DSL root used by every submitted mutation.
        if observer.checkpoint_preflight_report is None:
            raise RuntimeError(
                "resumed OpenEvolve slice has no checkpoint preflight report"
            )
        payload["checkpoint_preflight"] = copy.deepcopy(
            observer.checkpoint_preflight_report
        )
    payload.update(effective_invocation)
    for name, identity in launch_binding.items():
        for field_name in ("path", "sha256", "bytes"):
            payload[f"{name}_{field_name}"] = identity[field_name]
    for name, identity in source_binding.items():
        prefix = f"openevolve_{name}"
        for field_name in ("path", "sha256", "bytes"):
            payload[f"{prefix}_{field_name}"] = identity[field_name]
    witness = Path(witness_path)
    if witness.is_symlink() or witness.exists():
        raise RuntimeError(f"refusing to overwrite slice witness: {witness}")
    _atomic_write_json_artifact(witness, payload)
    witness_identity = _file_identity(witness, "OpenEvolve slice witness")
    witness_identity.update({
        "candidate_log_path": candidate_source["path"],
        "candidate_log_device": candidate_source["device"],
        "candidate_log_inode": candidate_source["inode"],
        "candidate_start_offset": candidate_source["start_offset"],
        "candidate_end_offset": candidate_source["end_offset"],
        "candidate_range_sha256": candidate_source["sha256"],
        "candidate_range_bytes": candidate_source["bytes"],
        "candidate_wal_clean": candidate_source["wal_clean"],
    })
    return result_checkpoint, witness_identity


def _write_completion_marker(
    marker_path: str | Path,
    *,
    output_dir: str | Path,
    resume_checkpoint: str | Path | None,
    iterations: int,
    config_path: str | Path,
    seed_path: str | Path,
    evaluator_path: str | Path,
    context_path: str | Path,
    context_identity: dict[str, Any],
    dependency_identities: dict[str, dict[str, Any]],
    backend_path: str | Path | None,
    codex_executable_identity: dict[str, Any] | None,
    invocation: dict[str, Any],
    result_checkpoint: dict[str, Any],
    slice_witness: dict[str, Any],
    renderer_activation: dict[str, Any] | None = None,
    renderer_activation_identity: dict[str, Any] | None = None,
) -> None:
    effective_invocation = _validated_invocation_binding(
        invocation,
        backend_path,
        codex_executable_identity,
        renderer_activation,
    )
    resolved_output = Path(output_dir).resolve()
    launch_binding = _launch_input_identities(
        config_path,
        seed_path,
        evaluator_path,
        context_path,
        context_identity,
        dependency_identities,
        backend_path,
        codex_executable_identity,
        effective_invocation.get(
            EVALUATOR_KIND_BINDING_FIELD,
            EVALUATOR_KIND_DEFAULT,
        ),
        (
            _file_identity(
                effective_invocation["qcode_negative_feedback_snapshot_path"],
                "negative-feedback snapshot",
            )
            if COSET_NEGATIVE_FEEDBACK_INVOCATION_FIELDS.issubset(
                effective_invocation
            )
            else None
        ),
        (
            _file_identity(
                effective_invocation["qcode_negative_feedback_manifest_path"],
                "negative-feedback snapshot manifest",
            )
            if COSET_NEGATIVE_FEEDBACK_INVOCATION_FIELDS.issubset(
                effective_invocation
            )
            else None
        ),
        renderer_activation_identity,
    )
    payload: dict[str, Any] = {
        "schema_version": EVOLUTION_COMPLETION_SCHEMA_VERSION,
        "status": "completed",
        "output_dir": str(resolved_output),
        "resume_checkpoint": (
            None if resume_checkpoint is None else str(Path(resume_checkpoint).resolve())
        ),
        "base_last_iteration": result_checkpoint["last_iteration"] - iterations,
        "iterations_requested": iterations,
        "result_checkpoint": result_checkpoint["path"],
        "result_last_iteration": result_checkpoint["last_iteration"],
        "result_checkpoint_sha256": result_checkpoint["sha256"],
        "result_checkpoint_programs": result_checkpoint["programs"],
        "slice_witness_path": slice_witness["path"],
        "slice_witness_sha256": slice_witness["sha256"],
        "slice_witness_bytes": slice_witness["bytes"],
        "candidate_log_path": slice_witness["candidate_log_path"],
        "candidate_log_device": slice_witness["candidate_log_device"],
        "candidate_log_inode": slice_witness["candidate_log_inode"],
        "candidate_start_offset": slice_witness["candidate_start_offset"],
        "candidate_end_offset": slice_witness["candidate_end_offset"],
        "candidate_range_sha256": slice_witness[
            "candidate_range_sha256"
        ],
        "candidate_range_bytes": slice_witness["candidate_range_bytes"],
        "candidate_wal_clean": slice_witness["candidate_wal_clean"],
        "completed_at": datetime.now().astimezone().isoformat(),
    }
    payload.update(effective_invocation)
    for name, identity in launch_binding.items():
        for field_name in ("path", "sha256", "bytes"):
            payload[f"{name}_{field_name}"] = identity[field_name]
    marker = Path(marker_path)
    if marker.is_symlink() or marker.exists():
        raise RuntimeError(f"refusing to overwrite completion marker: {marker}")
    _atomic_write_json_artifact(marker, payload)


def _cap_parallel_evaluations(config, cap: int | None) -> tuple[int, int]:
    """Cap OpenEvolve evaluation lanes without increasing the YAML setting."""
    configured = getattr(config.evaluator, "parallel_evaluations", None)
    if (
        isinstance(configured, bool)
        or not isinstance(configured, int)
        or configured < 1
    ):
        raise ValueError(
            "config evaluator.parallel_evaluations must be a positive integer"
        )
    if cap is not None:
        if isinstance(cap, bool) or not isinstance(cap, int) or cap < 1:
            raise ValueError("max parallel evaluations must be a positive integer")
        effective = min(configured, cap)
    else:
        effective = configured
    config.evaluator.parallel_evaluations = effective
    return configured, effective


def _resolve_api_base(args) -> str:
    """Resolve the API base URL from args or environment."""
    if args.api_base:
        return args.api_base
    for var in ("OPENAI_API_BASE", "LITELLM_API_BASE"):
        val = os.environ.get(var)
        if val:
            return val
    return "http://localhost:4000/v1"


def _resolve_output_dir(args) -> str:
    """Compute the output directory from --output or --run-name."""
    if args.output:
        return args.output
    run_name = args.run_name or f"run_{datetime.now().strftime('%Y%m%d_%H%M%S')}"
    return str(Path(EVOLUTION_BASE) / run_name)


def _set_reasoning_effort(config, effort: str | None) -> None:
    """Forward reasoning effort, refusing a silent downgrade."""
    if not effort:
        return
    configured = 0
    for model in [*config.llm.models, *config.llm.evaluator_models]:
        if hasattr(model, "reasoning_effort"):
            setattr(model, "reasoning_effort", effort)
            configured += 1
            continue
        for attribute in ("extra_params", "model_kwargs", "extra_body"):
            extra = getattr(model, attribute, None)
            if isinstance(extra, dict):
                extra["reasoning_effort"] = effort
                configured += 1
                break
    if configured == 0:
        raise RuntimeError(
            "This OpenEvolve version cannot forward reasoning_effort; upgrade it."
        )


def _build_config(
    args,
    api_base: str,
    model_names: list[str] | None,
    *,
    humanize_context_text: str | None = None,
):
    """Load config YAML and apply CLI overrides for models, temperature, etc."""
    import yaml
    from openevolve import Config
    from openevolve.config import LLMModelConfig

    config = Config.from_yaml(args.config)
    config.max_iterations = args.iterations
    _cap_parallel_evaluations(
        config,
        getattr(args, "max_parallel_evaluations", None),
    )

    # Propagate api_base to all model configs.
    # Setting config.llm.api_base alone does NOT propagate because
    # __post_init__ already ran during from_yaml().
    config.llm.api_base = api_base
    config.llm.update_model_params({"api_base": api_base}, overwrite=True)

    # Override model list if CLI specifies models; otherwise keep config as-is
    if model_names is not None:
        config.llm.models = [
            LLMModelConfig(name=name, weight=1.0)
            for name in model_names
        ]
        # Propagate ALL shared params to the new models -- not just api_base.
        # Fresh LLMModelConfig objects have None for max_tokens, timeout, retries,
        # etc.  Without propagation the retry loop crashes (range(None + 1)).
        shared = {
            "api_base": api_base,
            "api_key": config.llm.api_key,
            "temperature": config.llm.temperature,
            "top_p": config.llm.top_p,
            "max_tokens": config.llm.max_tokens,
            "timeout": config.llm.timeout,
            "retries": config.llm.retries,
            "retry_delay": config.llm.retry_delay,
            "system_message": config.llm.system_message,
        }
        config.llm.update_model_params(shared, overwrite=False)
        # Force api_base from CLI (overwrite any config default)
        config.llm.update_model_params({"api_base": api_base}, overwrite=True)
        # Reset evaluator_models to match
        config.llm.evaluator_models = config.llm.models.copy()
        config.llm.update_model_params({"api_base": api_base}, overwrite=True)
    else:
        # Using config YAML as-is. Re-apply per-model temperature overrides
        # that were lost during Config.from_yaml() -- OpenEvolve's __post_init__
        # calls update_model_params(overwrite=False), which overwrites explicit
        # null values with the global temperature.
        with open(args.config) as f:
            raw = yaml.safe_load(f)
        for i, model_raw in enumerate(raw.get("llm", {}).get("models", [])):
            if i < len(config.llm.models) and "temperature" in model_raw:
                config.llm.models[i].temperature = model_raw["temperature"]
                if i < len(config.llm.evaluator_models):
                    config.llm.evaluator_models[i].temperature = model_raw["temperature"]

    # Handle temperature: some models (e.g. GPT-5.1 Codex) reject it
    if args.no_temperature:
        config.llm.temperature = None
        config.llm.update_model_params({"temperature": None}, overwrite=True)
    elif args.temperature is not None:
        config.llm.temperature = args.temperature
        config.llm.update_model_params(
            {"temperature": args.temperature}, overwrite=True
        )

    _set_reasoning_effort(config, args.reasoning_effort)
    if args.humanize_context:
        context = (
            humanize_context_text
            if humanize_context_text is not None
            else getattr(args, "_humanize_context_text", None)
            or Path(args.humanize_context).read_text()
        ).strip()
        if context:
            config.prompt.system_message += (
                "\n\nHumanize cross-round memory and reviewer focus:\n" + context
            )
    return config


# ---------------------------------------------------------------------------
# W&B sync: background thread reads JSONL written by evaluator subprocesses
# ---------------------------------------------------------------------------

class WandbSyncer:
    """Tails the metrics JSONL file and logs each new line to W&B.

    The evaluator writes one JSON record per stage-2 evaluation from
    subprocess workers (where wandb.run is None). This thread runs in
    the main process and streams those records to W&B with proper step
    indices, plus running-best tracking.
    """

    def __init__(self, metrics_file: str, poll_interval: float = 5.0):
        self.metrics_file = metrics_file
        self.poll_interval = poll_interval
        self._stop = threading.Event()
        self._thread: threading.Thread | None = None
        self._byte_offset = 0
        self._step = 0
        self._best_fom = 0.0
        self._best_bp_fom_upper_bound = 0.0

    def start(self):
        # Truncate any stale metrics from a previous run
        Path(self.metrics_file).parent.mkdir(parents=True, exist_ok=True)
        with open(self.metrics_file, "w"):
            pass
        self._byte_offset = 0
        self._thread = threading.Thread(target=self._run, daemon=True)
        self._thread.start()

    def stop(self):
        self._stop.set()
        if self._thread:
            self._thread.join(timeout=10)

    def _run(self):
        while not self._stop.is_set():
            self._drain()
            self._stop.wait(self.poll_interval)
        # Final drain to catch any records written during shutdown
        self._drain()

    def _drain(self):
        import wandb

        try:
            with open(self.metrics_file, "r") as f:
                f.seek(self._byte_offset)
                new_data = f.read()
                self._byte_offset = f.tell()
        except FileNotFoundError:
            return

        if not new_data:
            return

        for line in new_data.splitlines():
            line = line.strip()
            if not line:
                continue
            try:
                record = json.loads(line)
            except json.JSONDecodeError:
                continue

            self._step += 1
            if "best_bp_fom_upper_bound" in record:
                upper_bound = record.get("best_bp_fom_upper_bound", 0)
                self._best_bp_fom_upper_bound = max(
                    self._best_bp_fom_upper_bound,
                    upper_bound,
                )
                distance_metrics = {
                    "eval/best_bp_fom_upper_bound": upper_bound,
                    "eval/mean_bp_fom_upper_bound": record.get(
                        "mean_bp_fom_upper_bound", 0
                    ),
                    "eval/fitness_distance_credit": record.get(
                        "fitness_distance_credit", 0
                    ),
                    "eval/fitness_survivor_credit": record.get(
                        "fitness_survivor_credit", 0
                    ),
                    "eval/fitness_rate_tie_break": record.get(
                        "fitness_rate_tie_break", 0
                    ),
                    "eval/fitness_structural_tie_break": record.get(
                        "fitness_structural_tie_break", 0
                    ),
                    "eval/screen_survivor_count": record.get(
                        "screen_survivor_count", 0
                    ),
                    "eval/screen_terminal_negative_count": record.get(
                        "screen_terminal_negative_count", 0
                    ),
                    "progress/running_best_bp_fom_upper_bound": (
                        self._best_bp_fom_upper_bound
                    ),
                }
            else:
                fom = record.get("best_fom", 0)
                self._best_fom = max(self._best_fom, fom)
                distance_metrics = {
                    "eval/best_fom": fom,
                    "eval/mean_fom": record.get("mean_fom", 0),
                    "eval/codes_above_fom6": record.get("num_above_6", 0),
                    "eval/codes_above_fom12": record.get("num_above_12", 0),
                    "progress/running_best_fom": self._best_fom,
                }

            wandb.log({
                **distance_metrics,
                "eval/num_valid_codes": record.get("num_valid", 0),
                "eval/num_high_k_codes": record.get("num_high_k", 0),
                "eval/lattices_with_high_k": record.get("lattices_with_high_k", 0),
                "eval/best_encoding_rate": record.get("best_encoding_rate", 0),
                "eval/total_candidates": record.get("total_candidates", 0),
            }, step=self._step)


# ---------------------------------------------------------------------------
# Evolution runners
# ---------------------------------------------------------------------------

def _preflighted_fresh_controller_type(
    controller_type: type,
    initial_program_preflight: Any,
) -> type:
    """Wrap the pinned controller's otherwise-unobserved initial DB add."""

    class PreflightedFreshOpenEvolve(controller_type):
        async def run(self, *args: Any, **kwargs: Any) -> Any:
            original_add = self.database.add
            initial_observed = False

            def checked_add(
                program: Any,
                iteration: Any = None,
                target_island: Any = None,
            ) -> Any:
                nonlocal initial_observed
                if not initial_observed:
                    if (
                        iteration is not None
                        or getattr(self.database, "programs", None)
                        or getattr(program, "code", None)
                        != getattr(self, "initial_program_code", None)
                        or getattr(program, "iteration_found", None) != 0
                    ):
                        raise RuntimeError(
                            "fresh OpenEvolve initial database add has an "
                            "unexpected shape"
                        )
                    pending = getattr(
                        getattr(self, "evaluator", None),
                        "_pending_artifacts",
                        None,
                    )
                    artifacts = (
                        pending.get(getattr(program, "id", None))
                        if isinstance(pending, dict)
                        else None
                    )
                    initial_program_preflight(
                        getattr(program, "metrics", None),
                        artifacts,
                    )
                    initial_observed = True
                return original_add(
                    program,
                    iteration=iteration,
                    target_island=target_island,
                )

            self.database.add = checked_add
            try:
                result = await super().run(*args, **kwargs)
            finally:
                self.database.add = original_add
            if not initial_observed:
                raise RuntimeError(
                    "fresh OpenEvolve run did not add one validated initial "
                    "program"
                )
            return result

    return PreflightedFreshOpenEvolve


def _run_fresh(
    config,
    output_dir: str,
    iterations: int,
    seed: str = SEED_SOLUTION,
    evaluator: str = EVALUATOR,
    initial_program_preflight: Any = None,
):
    """Run a fresh evolution using the high-level API."""
    from openevolve import run_evolution

    if initial_program_preflight is None:
        return run_evolution(
            initial_program=seed,
            evaluator=evaluator,
            config=config,
            iterations=iterations,
            output_dir=output_dir,
            cleanup=False,
        )

    import openevolve.api as api_module

    original_controller = api_module.OpenEvolve
    api_module.OpenEvolve = _preflighted_fresh_controller_type(
        original_controller,
        initial_program_preflight,
    )
    try:
        return run_evolution(
            initial_program=seed,
            evaluator=evaluator,
            config=config,
            iterations=iterations,
            output_dir=output_dir,
            cleanup=False,
        )
    finally:
        api_module.OpenEvolve = original_controller


def _run_resume(config, output_dir: str, iterations: int, checkpoint_path: str,
                seed: str = SEED_SOLUTION, evaluator: str = EVALUATOR,
                checkpoint_preflight: Any = None):
    """Resume evolution from a checkpoint using the controller directly.

    The high-level run_evolution() API doesn't expose checkpoint_path,
    so we instantiate the OpenEvolve controller ourselves.
    """
    from openevolve.controller import OpenEvolve

    if checkpoint_preflight is None:
        controller_type = OpenEvolve
    else:
        class PreflightedResumeOpenEvolve(OpenEvolve):
            def _load_checkpoint(self, path: str) -> None:
                super()._load_checkpoint(path)
                checkpoint_preflight(self.database)

        controller_type = PreflightedResumeOpenEvolve

    os.makedirs(output_dir, exist_ok=True)
    controller = controller_type(
        initial_program_path=seed,
        evaluation_file=evaluator,
        config=config,
        output_dir=output_dir,
    )
    best_program = asyncio.run(
        controller.run(iterations=iterations, checkpoint_path=checkpoint_path)
    )
    return best_program


def _validated_evaluator_kind(
    requested: str,
    *,
    noncss: bool,
    milp: bool,
) -> str:
    """Validate the explicit evaluator route before loading run inputs.

    The coset representation is checkpoint-incompatible with the historical
    BB evaluator.  Keeping the route as a closed vocabulary prevents a path
    supplied by campaign data from becoming executable code.
    """

    if requested not in EVALUATOR_KINDS:
        raise RuntimeError(f"unsupported evaluator kind: {requested!r}")
    if requested == EVALUATOR_KIND_COSET_TWO_BLOCK and (noncss or milp):
        raise RuntimeError(
            "coset-two-block evaluator cannot be combined with --noncss or "
            "--milp"
        )
    return requested


def _coset_action_catalog_sha256() -> str:
    from evaluation.coset_action_catalog import (
        V2_CATALOG_ID,
        action_catalog_sha256,
    )

    value = action_catalog_sha256(V2_CATALOG_ID)
    if (
        not isinstance(value, str)
        or len(value) != 64
        or any(character not in "0123456789abcdef" for character in value)
    ):
        raise RuntimeError("coset action catalog SHA-256 is invalid")
    return value


def _coset_action_catalog_contract_id() -> int:
    # OpenEvolve metrics are JSON numbers. Thirteen hexadecimal digits remain
    # exactly representable through a binary64 checkpoint round trip.
    return int(_coset_action_catalog_sha256()[:13], 16)


def _checkpoint_evaluator_kind(
    metrics: Any,
    *,
    expected_kind: str,
    label: str,
) -> str:
    """Reject a checkpoint produced by a different representation evaluator.

    Historical BB checkpoints predate the marker and remain valid only for the
    default route.  The new coset route requires an exact marker, so it can
    never resume a BB checkpoint (or vice versa when a marker is present).
    """

    if not isinstance(metrics, dict):
        raise RuntimeError(f"{label} metrics are not an object")
    observed = metrics.get(EVALUATOR_KIND_ID_METRIC)
    expected_id = EVALUATOR_KIND_IDS[expected_kind]
    if expected_kind == EVALUATOR_KIND_DEFAULT:
        if observed not in (None, float(expected_id), expected_id):
            raise RuntimeError(
                f"{label} belongs to evaluator id {observed!r}, not default"
            )
        return EVALUATOR_KIND_DEFAULT
    if (
        isinstance(observed, bool)
        or not isinstance(observed, (int, float))
        or not math.isfinite(float(observed))
        or float(observed) != float(expected_id)
    ):
        raise RuntimeError(
            f"{label} belongs to evaluator id {observed!r}, not "
            f"{expected_kind!r}; "
            "start a fresh checkpoint"
        )
    catalog_id = metrics.get(ACTION_CATALOG_ID_METRIC)
    expected_catalog_id = _coset_action_catalog_contract_id()
    if (
        isinstance(catalog_id, bool)
        or not isinstance(catalog_id, (int, float))
        or not math.isfinite(float(catalog_id))
        or float(catalog_id) != float(expected_catalog_id)
    ):
        raise RuntimeError(
            f"{label} belongs to action catalog id {catalog_id!r}, not "
            f"{expected_catalog_id}; start a fresh checkpoint"
        )
    from evolve.coset_search_contract import (
        COSET_PROOF_LADDER_SCHEMA_VERSION,
        COSET_PROOF_LADDER_VERSION_METRIC,
    )

    proof_marker = metrics.get(COSET_PROOF_LADDER_VERSION_METRIC)
    if (
        isinstance(proof_marker, bool)
        or not isinstance(proof_marker, (int, float))
        or not math.isfinite(float(proof_marker))
        or float(proof_marker) != float(COSET_PROOF_LADDER_SCHEMA_VERSION)
    ):
        raise RuntimeError(
            f"{label} belongs to proof-ladder contract "
            f"{proof_marker!r}, not {COSET_PROOF_LADDER_SCHEMA_VERSION}; "
            "start a fresh checkpoint"
        )
    return expected_kind


def main():
    parser = argparse.ArgumentParser(
        description="Run OpenEvolve evolutionary search for BB codes."
    )
    # --- Model selection ---
    parser.add_argument(
        "--model", type=str, default=None,
        help="Single LiteLLM model identifier (e.g. anthropic/claude-sonnet-4-5-20250514). "
             "Use --models for ensemble.",
    )
    parser.add_argument(
        "--models", type=str, nargs="+", default=None,
        help="Multiple LiteLLM model identifiers for ensemble evolution "
             "(e.g. --models gemini/gemini-2.5-flash anthropic/claude-sonnet-4-5-20250514). "
             "Takes precedence over --model.",
    )
    # --- Run management ---
    parser.add_argument(
        "--run-name", type=str, default=None,
        help="Run name (output goes to results/evolution/<run-name>/). "
             "Default: auto-generated as run_YYYYMMDD_HHMMSS.",
    )
    parser.add_argument(
        "--resume", type=str, default=None, metavar="CHECKPOINT_PATH",
        help="Resume from a checkpoint directory "
             "(e.g. results/evolution/run_xyz/checkpoints/checkpoint_100).",
    )
    # --- Standard options ---
    parser.add_argument(
        "--iterations", type=int, default=100,
        help="Number of evolutionary iterations.",
    )
    parser.add_argument(
        "--api-base", type=str, default=None,
        help="LiteLLM proxy base URL (default: $OPENAI_API_BASE or "
             "$LITELLM_API_BASE or http://localhost:4000/v1).",
    )
    parser.add_argument(
        "--config", type=str, default=None,
        help="Path to OpenEvolve config YAML (default: config.yaml, "
             "or config_noncss.yaml when --noncss is set).",
    )
    parser.add_argument(
        "--evaluator",
        choices=EVALUATOR_KINDS,
        default=EVALUATOR_KIND_DEFAULT,
        help=(
            "Versioned evaluator route. 'coset-two-block' selects the "
            "proof-safe coset Stage-1 evaluator; arbitrary evaluator paths "
            "are intentionally unsupported."
        ),
    )
    parser.add_argument(
        "--output", type=str, default=None,
        help="Explicit output directory (overrides --run-name).",
    )
    parser.add_argument(
        "--completion-marker", type=str, default=None,
        help="Atomically write a success marker after the final checkpoint is durable.",
    )
    parser.add_argument(
        "--slice-witness", type=str, default=None,
        help="Atomically write exact full-slice accounting before the success marker.",
    )
    parser.add_argument(
        "--candidate-start-offset", type=int, default=None,
        help="Durable candidate-log frontier frozen by the managed round.",
    )
    parser.add_argument(
        "--lifecycle-lease-fd", type=int, default=None,
        help="Inherited locked lifecycle lease descriptor for managed runs.",
    )
    parser.add_argument(
        "--lifecycle-lease-path", type=str, default=None,
        help="Fixed path matching the inherited lifecycle lease descriptor.",
    )
    parser.add_argument(
        "--max-parallel-evaluations", type=int, default=None,
        help="Cap OpenEvolve evaluator workers without increasing the YAML value.",
    )
    parser.add_argument(
        "--wandb", action="store_true",
        help="Enable Weights & Biases tracking.",
    )
    parser.add_argument(
        "--temperature", type=float, default=None,
        help="LLM temperature (default: from config). Use 0 or omit for models "
             "that don't support it (e.g. GPT-5.1 Codex).",
    )
    parser.add_argument(
        "--no-temperature", action="store_true",
        help="Disable sending temperature parameter (for models that reject it).",
    )
    parser.add_argument(
        "--reasoning-effort", type=str, default=None,
        help="Reasoning effort forwarded to all search/evaluator models; "
             "fails rather than silently downgrading when unsupported.",
    )
    parser.add_argument(
        "--humanize-context", type=str, default=None,
        help="Read-only BitLesson/reviewer context appended to the search prompt.",
    )
    parser.add_argument(
        "--negative-feedback-live-archive", type=str, default=None,
        help="Managed coset live archive used only for verified append.",
    )
    parser.add_argument(
        "--negative-feedback-snapshot", type=str, default=None,
        help="Managed coset immutable archive snapshot used for scoring.",
    )
    parser.add_argument(
        "--negative-feedback-snapshot-sha256", type=str, default=None,
    )
    parser.add_argument(
        "--negative-feedback-archive-sha256", type=str, default=None,
    )
    parser.add_argument(
        "--negative-feedback-manifest", type=str, default=None,
    )
    parser.add_argument(
        "--negative-feedback-manifest-sha256", type=str, default=None,
    )
    parser.add_argument(
        "--negative-feedback-epoch", type=int, default=None,
    )
    parser.add_argument(
        "--coset-renderer-activation",
        type=str,
        default=None,
        help=(
            "Absolute path to the source-registry activation sealed for this "
            "managed renderer-v3 slice."
        ),
    )
    parser.add_argument(
        "--codex-cli", action="store_true",
        help="Use authenticated Codex CLI via OpenEvolve init_client.",
    )
    parser.add_argument(
        "--wandb-project", type=str, default="qcode-discovery",
        help="W&B project name.",
    )
    # --- MILP evolution (Campaign 4+) ---
    parser.add_argument(
        "--milp", action="store_true",
        help="Use MILP exact distance instead of BP-OSD. Requires "
             "evaluate_stage2_milp in the evaluator.",
    )
    # --- Non-CSS PBB evolution ---
    parser.add_argument(
        "--noncss", action="store_true",
        help="Evolve non-CSS PBB codes instead of CSS BB codes. "
             "Uses seed_solution_noncss.py, openevolve_evaluator_noncss.py, "
             "and config_noncss.yaml by default.",
    )
    parser.add_argument(
        "--seed", type=str, default=None,
        help="Path to seed solution file (default: evolve/seed_solution.py, "
             "or evolve/seed_solution_milp.py when --milp is set, "
             "or evolve/seed_solution_noncss.py when --noncss is set).",
    )
    args = parser.parse_args()
    managed_values = (
        args.completion_marker,
        args.slice_witness,
        args.candidate_start_offset,
        args.lifecycle_lease_fd,
        args.lifecycle_lease_path,
    )
    managed_requested = any(value is not None for value in managed_values)
    if managed_requested and not all(value is not None for value in managed_values):
        parser.error(
            "--completion-marker, --slice-witness, --candidate-start-offset, "
            "--lifecycle-lease-fd, and --lifecycle-lease-path must be "
            "supplied together"
        )
    if managed_requested and args.humanize_context is None:
        parser.error("--humanize-context is required for managed evolution")
    if managed_requested and args.milp:
        parser.error(
            "managed --milp is unsupported until its evaluator implements "
            "the versioned Stage 2 completion contract"
        )
    if managed_requested:
        _validate_lifecycle_lease(
            args.lifecycle_lease_fd, args.lifecycle_lease_path
        )

    try:
        evaluator_kind = _validated_evaluator_kind(
            args.evaluator,
            noncss=bool(args.noncss),
            milp=bool(args.milp),
        )
    except RuntimeError as exc:
        parser.error(str(exc))

    # Resolve model list (None means "use config as-is")
    if args.models:
        model_names = args.models
    elif args.model:
        model_names = [args.model]
    else:
        model_names = None  # use whatever is in the config YAML

    # Resolve config path
    if args.config is None:
        if evaluator_kind == EVALUATOR_KIND_COSET_TWO_BLOCK:
            args.config = DEFAULT_CONFIG_COSET_TWO_BLOCK
        else:
            args.config = DEFAULT_CONFIG_NONCSS if args.noncss else DEFAULT_CONFIG

    selected_coset_schema = (
        _coset_search_portfolio_schema_version(args.config)
        if evaluator_kind == EVALUATOR_KIND_COSET_TWO_BLOCK
        else None
    )

    api_base = _resolve_api_base(args)
    output_dir = _resolve_output_dir(args)
    run_name = Path(output_dir).name
    feedback_requested = any(value is not None for value in (
        args.negative_feedback_live_archive,
        args.negative_feedback_snapshot,
        args.negative_feedback_snapshot_sha256,
        args.negative_feedback_archive_sha256,
        args.negative_feedback_manifest,
        args.negative_feedback_manifest_sha256,
        args.negative_feedback_epoch,
    ))
    if feedback_requested and evaluator_kind != EVALUATOR_KIND_COSET_TWO_BLOCK:
        parser.error("negative-feedback snapshots require the coset evaluator")
    try:
        negative_feedback_binding = _validated_negative_feedback_binding(
            live_archive_path=args.negative_feedback_live_archive,
            snapshot_path=args.negative_feedback_snapshot,
            snapshot_sha256=args.negative_feedback_snapshot_sha256,
            archive_sha256=args.negative_feedback_archive_sha256,
            manifest_path=args.negative_feedback_manifest,
            manifest_sha256=args.negative_feedback_manifest_sha256,
            feedback_epoch=args.negative_feedback_epoch,
            required=(
                managed_requested
                and evaluator_kind == EVALUATOR_KIND_COSET_TWO_BLOCK
            ),
            expected_run_id=(
                run_name.removeprefix("humanize_")
                if run_name.startswith("humanize_")
                else None
            ),
        )
    except RuntimeError as exc:
        parser.error(str(exc))
    if (
        args.coset_renderer_activation is not None
        and (
            evaluator_kind != EVALUATOR_KIND_COSET_TWO_BLOCK
            or selected_coset_schema != 4
        )
    ):
        parser.error(
            "--coset-renderer-activation requires the renderer-v3 coset config"
        )
    try:
        renderer_activation_binding = _validated_renderer_activation_binding(
            args.coset_renderer_activation,
            required=(
                managed_requested
                and evaluator_kind == EVALUATOR_KIND_COSET_TWO_BLOCK
                and selected_coset_schema == 4
            ),
        )
    except RuntimeError as exc:
        parser.error(str(exc))

    # OpenEvolve calls evaluators with no extra routing arguments. Bind the
    # exact absolute candidate log before loading any evolved program. This is
    # also required by --milp, whose patched evaluator copy lives inside the
    # output directory and therefore cannot infer PROJECT_ROOT from __file__.
    mutated_environment_names = (
        "QCODE_RUN_NAME",
        CANDIDATE_LOG_PATH_ENV,
        "QCODE_EVALUATOR_OUTER_TIMEOUT_S",
        WINNER_PREFLIGHT_CONTRACT_ID_ENV,
        "QCODE_CODEX_BIN",
        "QCODE_CODEX_CWD",
        NEGATIVE_ARCHIVE_PATH_ENV,
        NEGATIVE_ARCHIVE_SNAPSHOT_PATH_ENV,
        COSET_RENDERER_ACTIVATION_JSON_ENV,
        "ENABLE_ARTIFACTS",
    )
    original_environment = {
        name: os.environ.get(name)
        for name in mutated_environment_names
    }
    os.environ["QCODE_RUN_NAME"] = run_name
    candidate_log_path = (
        Path(output_dir).expanduser().resolve() / "all_codes.jsonl"
    )
    os.environ[CANDIDATE_LOG_PATH_ENV] = str(candidate_log_path)
    os.environ.pop(COSET_RENDERER_ACTIVATION_JSON_ENV, None)
    if negative_feedback_binding is not None:
        feedback_invocation = negative_feedback_binding[0]
        os.environ[NEGATIVE_ARCHIVE_PATH_ENV] = feedback_invocation[
            "qcode_negative_feedback_live_archive_path"
        ]
        os.environ[NEGATIVE_ARCHIVE_SNAPSHOT_PATH_ENV] = feedback_invocation[
            "qcode_negative_feedback_snapshot_path"
        ]
    if renderer_activation_binding is not None:
        os.environ[COSET_RENDERER_ACTIVATION_JSON_ENV] = json.dumps(
            renderer_activation_binding[0],
            sort_keys=True,
            separators=(",", ":"),
            ensure_ascii=False,
            allow_nan=False,
        )
    if managed_requested:
        # Slice accounting needs pinned OpenEvolve's rich exception envelope
        # to distinguish an invalid evolved program from a trusted evaluator
        # failure. Do not let an inherited environment disable that evidence.
        os.environ["ENABLE_ARTIFACTS"] = "true"
        if args.candidate_start_offset < 0:
            parser.error("--candidate-start-offset must be non-negative")
        from evolve.openevolve_evaluator import candidate_log_range_identity

        initial_candidate_source = candidate_log_range_identity(
            candidate_log_path,
            start_offset=args.candidate_start_offset,
        )
        if (
            initial_candidate_source["end_offset"]
            != args.candidate_start_offset
        ):
            raise RuntimeError(
                "managed candidate log contains an unbound tail before "
                "evolution starts"
            )

    # Resolve seed solution
    if args.seed:
        seed_path = args.seed
    elif evaluator_kind == EVALUATOR_KIND_COSET_TWO_BLOCK:
        seed_path = (
            SEED_SOLUTION_COSET_TWO_BLOCK_V2
            if selected_coset_schema == 3
            else SEED_SOLUTION_COSET_TWO_BLOCK_V3
        )
    elif args.noncss:
        seed_path = SEED_SOLUTION_NONCSS
    elif args.milp:
        seed_path = SEED_SOLUTION_MILP
    else:
        seed_path = SEED_SOLUTION
    if not Path(seed_path).exists():
        print(f"Error: seed solution not found: {seed_path}")
        sys.exit(1)

    # When --noncss is set, use the non-CSS evaluator directly (no patching needed).
    if evaluator_kind == EVALUATOR_KIND_COSET_TWO_BLOCK:
        EVALUATOR_ACTIVE = EVALUATOR_COSET_TWO_BLOCK
        if not Path(EVALUATOR_ACTIVE).exists():
            print(
                "Error: coset two-block evaluator not found: "
                f"{EVALUATOR_ACTIVE}"
            )
            sys.exit(1)
        print("Coset mode: using coset_openevolve_evaluator.py")
    elif args.noncss:
        EVALUATOR_ACTIVE = EVALUATOR_NONCSS
        if not Path(EVALUATOR_ACTIVE).exists():
            print(f"Error: non-CSS evaluator not found: {EVALUATOR_ACTIVE}")
            sys.exit(1)
        print(f"Non-CSS mode: using openevolve_evaluator_noncss.py")
    # When --milp is set, monkey-patch the evaluator to use MILP stage 2.
    # OpenEvolve calls evaluate_stage2() by name from the evaluator module,
    # so we replace it at module level after import.
    elif args.milp:
        import importlib.util
        spec = importlib.util.spec_from_file_location("oe_evaluator", EVALUATOR)
        _ev_mod = importlib.util.module_from_spec(spec)
        spec.loader.exec_module(_ev_mod)
        if hasattr(_ev_mod, "evaluate_stage2_milp"):
            _ev_mod.evaluate_stage2 = _ev_mod.evaluate_stage2_milp
            _ev_mod.evaluate = _ev_mod.evaluate_stage2_milp
            # Write a patched copy the evaluator will use
            _milp_eval_path = str(Path(output_dir) / "_evaluator_milp.py")
            os.makedirs(output_dir, exist_ok=True)
            eval_source = Path(EVALUATOR).read_text()
            # Append the alias at the end of the file
            patched = eval_source + (
                "\n\n# --- MILP mode: override stage 2 ---\n"
                "evaluate_stage2 = evaluate_stage2_milp\n"
                "evaluate = evaluate_stage2_milp\n"
            )
            Path(_milp_eval_path).write_text(patched)
            # Use the patched evaluator
            EVALUATOR_ACTIVE = _milp_eval_path
            print(f"MILP mode: using evaluate_stage2_milp (patched evaluator)")
        else:
            print("Warning: evaluate_stage2_milp not found in evaluator, "
                  "falling back to BP-OSD")
            EVALUATOR_ACTIVE = EVALUATOR
    else:
        EVALUATOR_ACTIVE = EVALUATOR

    # Validate resume path
    if args.resume and not Path(args.resume).exists():
        print(f"Error: checkpoint path does not exist: {args.resume}")
        sys.exit(1)

    # Start W&B if requested
    wandb_syncer: WandbSyncer | None = None
    if args.wandb:
        try:
            import wandb
            wandb.init(
                project=args.wandb_project,
                config={
                    "models": model_names or "config-default",
                    "iterations": args.iterations,
                    "config": args.config,
                    "api_base": api_base,
                    "resume": args.resume,
                    "output_dir": output_dir,
                },
            )
            print(f"W&B run: {wandb.run.url}")
            # Start background sync from JSONL → W&B
            wandb_syncer = WandbSyncer(METRICS_FILE)
            wandb_syncer.start()
        except ImportError:
            print("wandb not installed. Run: uv sync --group tracking")
            sys.exit(1)

    # Run OpenEvolve
    observer: _SliceObserver | None = None
    source_binding: dict[str, dict[str, Any]] | None = None
    context_identity: dict[str, Any] | None = None
    dependency_identities: dict[str, dict[str, Any]] | None = None
    codex_executable_identity: dict[str, Any] | None = None
    preflight_contract_id: int | None = None
    stage2_cascade_threshold: float | None = None
    adaptive_mutation_policy: dict[str, int] | None = None
    search_regime: dict[str, Any] | None = None
    search_portfolio_enabled = False
    search_portfolio_schema_version: int | None = None
    coset_map_schema_version: int | None = None
    search_geometry_contract: str | None = None
    try:
        context_text: str | None = None
        if managed_requested:
            context_text, context_identity = _read_text_snapshot(
                args.humanize_context, "evolution humanize context"
            )
            if not args.noncss:
                adaptive_mutation_policy = (
                    _validated_adaptive_mutation_policy(context_text)
                )
                search_regime = _validated_search_regime(context_text)
            dependency_identities = _evaluator_dependency_identities(
                evaluator_kind
            )
            args._humanize_context_text = context_text
        codex_version: str | None = None
        codex_cwd: str | None = None
        codex_executable_mode: int | None = None
        if managed_requested and args.codex_cli:
            (
                codex_executable_identity,
                codex_version,
                codex_cwd,
            ) = _resolve_codex_execution_binding()
            codex_executable_mode = int(codex_executable_identity["mode"])
        config = _build_config(args, api_base, model_names)
        if evaluator_kind == EVALUATOR_KIND_COSET_TWO_BLOCK:
            config.prompt.system_message += (
                "\n\n" + _coset_mutation_bounds_prompt(
                    None
                    if renderer_activation_binding is None
                    else renderer_activation_binding[0]
                )
            )
            coset_map_schema_version = (
                _coset_search_portfolio_schema_version(args.config)
            )
            if coset_map_schema_version is not None:
                if not managed_requested:
                    raise RuntimeError(
                        "qcode_coset_search_portfolio requires managed "
                        "Humanize slice accounting"
                    )
                _validated_coset_search_portfolio_config(
                    config,
                    coset_map_schema_version,
                )
        if not args.noncss:
            search_portfolio_schema_version = (
                _search_portfolio_schema_version(
                    args.config
                )
            )
            search_portfolio_enabled = (
                search_portfolio_schema_version is not None
            )
            search_geometry_contract = _validated_search_geometry_contract(
                search_portfolio_schema_version
            )
            if search_portfolio_enabled and not managed_requested:
                raise RuntimeError(
                    "qcode_search_portfolio requires managed Humanize "
                    "slice accounting"
                )
            if search_portfolio_enabled:
                assert search_portfolio_schema_version is not None
                _validated_search_portfolio_config(
                    config,
                    schema_version=search_portfolio_schema_version,
                )
        evaluator_timeout = getattr(config.evaluator, "timeout", None)
        if (
            isinstance(evaluator_timeout, bool)
            or not isinstance(evaluator_timeout, (int, float))
            or not math.isfinite(float(evaluator_timeout))
            or evaluator_timeout <= 0
        ):
            raise RuntimeError(
                "config evaluator.timeout must be a positive finite number"
            )
        os.environ["QCODE_EVALUATOR_OUTER_TIMEOUT_S"] = str(
            float(evaluator_timeout)
        )
        if not args.noncss:
            cascade_thresholds = getattr(
                config.evaluator,
                "cascade_thresholds",
                None,
            )
            if (
                not isinstance(cascade_thresholds, (list, tuple))
                or not cascade_thresholds
                or isinstance(cascade_thresholds[0], bool)
                or not isinstance(cascade_thresholds[0], (int, float))
                or not math.isfinite(float(cascade_thresholds[0]))
            ):
                raise RuntimeError(
                    "config evaluator.cascade_thresholds[0] must be a "
                    "finite number"
                )
            stage2_cascade_threshold = float(cascade_thresholds[0])
            # OpenEvolve applies this value as a total Stage 1 timeout.  The
            # evaluator itself now owns the useful safety boundary: the same
            # configured budget is an inactivity timeout for each durable
            # lattice.  Expand only the outer guard so cumulative healthy
            # progress cannot be discarded at 1200 seconds.
            config.evaluator.timeout = _winner_preflight_outer_timeout(
                float(evaluator_timeout)
            )
        if managed_requested and not args.noncss:
            assert dependency_identities is not None
            preflight_contract_id = _winner_preflight_contract_id(
                EVALUATOR_ACTIVE,
                dependency_identities,
                candidate_log_path=candidate_log_path,
                evaluator_kind=evaluator_kind,
            )
            os.environ[WINNER_PREFLIGHT_CONTRACT_ID_ENV] = str(
                preflight_contract_id
            )
        if args.codex_cli:
            from evolve.codex_cli_llm import make_codex_cli_client
            for model_config in config.llm.models + config.llm.evaluator_models:
                model_config.init_client = make_codex_cli_client

        # Startup banner
        active_models = [m.name for m in config.llm.models]
        invocation_binding = {
            "model_names": active_models,
            "reasoning_effort": args.reasoning_effort,
            "codex_cli": bool(args.codex_cli),
            "max_parallel_evaluations": config.evaluator.parallel_evaluations,
            "api_base": api_base,
            "temperature_disabled": bool(args.no_temperature),
            "codex_version": codex_version,
            "codex_cwd": codex_cwd,
            "codex_executable_mode": codex_executable_mode,
        }
        if evaluator_kind == EVALUATOR_KIND_COSET_TWO_BLOCK:
            invocation_binding[EVALUATOR_KIND_BINDING_FIELD] = evaluator_kind
            invocation_binding[ACTION_CATALOG_SHA256_BINDING_FIELD] = (
                _coset_action_catalog_sha256()
            )
            if negative_feedback_binding is not None:
                invocation_binding.update(negative_feedback_binding[0])
            if coset_map_schema_version == 4:
                if renderer_activation_binding is None:
                    from evolve.coset_search_contract import (
                        coset_renderer_activation_document,
                        default_coset_renderer_activation,
                    )

                    activation = coset_renderer_activation_document(
                        default_coset_renderer_activation()
                    )
                else:
                    activation = renderer_activation_binding[0]
                invocation_binding[
                    COSET_RENDERER_ACTIVATION_SHA256_BINDING_FIELD
                ] = activation["activation_sha256"]
        if search_geometry_contract is not None:
            invocation_binding[SEARCH_GEOMETRY_CONTRACT_FIELD] = (
                search_geometry_contract
            )
        backend_path = (
            Path(__file__).resolve().parent / "codex_cli_llm.py"
            if args.codex_cli
            else None
        )
        print(f"\nStarting evolution:")
        if len(active_models) == 1:
            print(f"  Model: {active_models[0]}")
        else:
            print(f"  Ensemble ({len(active_models)} models):")
            for name in active_models:
                print(f"    - {name}")
        print(f"  Iterations: {args.iterations}")
        parallel = config.evaluator.parallel_evaluations
        if args.max_parallel_evaluations is None:
            print(f"  Parallel evaluations: {parallel}")
        else:
            print(
                f"  Parallel evaluations: {parallel} "
                f"(cap: {args.max_parallel_evaluations})"
            )
        print(f"  Model backend: {'Codex CLI' if args.codex_cli else api_base}")
        if search_portfolio_enabled:
            print(
                "  Search portfolio: fixed MAP-Elites v4, "
                "5 algebraic-mechanism islands "
                f"(regime={search_regime['status'] if search_regime else 'normal'})"
            )
        if coset_map_schema_version is not None:
            coset_islands = _coset_portfolio_contract_for_schema(
                coset_map_schema_version
            )["num_islands"]
            print(
                "  Coset portfolio: fixed categorical MAP-Elites "
                f"schema v{coset_map_schema_version}, "
                f"{coset_islands} lineage islands"
            )
        print(f"  Seed: {seed_path}")
        if evaluator_kind == EVALUATOR_KIND_COSET_TWO_BLOCK:
            print("  Mode: CSS coset two-block actions")
            print("  Distance: proof-safe low-weight oracle (no BP credit)")
        elif args.noncss:
            print(f"  Mode: Non-CSS PBB codes")
            print(f"  Distance: BP-OSD multi-channel (non-CSS)")
        elif args.milp:
            print(f"  Distance: MILP (exact or upper bound)")
        else:
            print(f"  Distance: BP-OSD (estimate)")
        print(f"  Output: {output_dir}")
        if managed_requested:
            base_iteration = _checkpoint_last_iteration(args.resume)
            slice_context = _verified_slice_controller(
                base_iteration,
                args.iterations,
                expected_preflight_contract_id=preflight_contract_id,
                evaluator_kind=evaluator_kind,
                stage2_cascade_threshold=stage2_cascade_threshold,
                checkpoint_preflight_required=(
                    args.resume is not None
                    and preflight_contract_id is not None
                ),
                search_config=(
                    config
                    if search_portfolio_enabled
                    else None
                ),
                search_portfolio_schema_version=(
                    search_portfolio_schema_version
                    if search_portfolio_schema_version is not None
                    else SEARCH_PORTFOLIO_SCHEMA_VERSION
                ),
                adaptive_mutation_policy=adaptive_mutation_policy,
                search_regime=search_regime,
                coset_map_schema_version=coset_map_schema_version,
                coset_renderer_activation=(
                    None
                    if renderer_activation_binding is None
                    else renderer_activation_binding[0]
                ),
            )
        else:
            slice_context = nullcontext((None, None))
        with slice_context as verification:
            if managed_requested:
                observer, source_binding = verification
            if args.resume:
                print(f"  Resuming from: {args.resume}")
            print()

            if args.resume:
                checkpoint_preflight = None
                if not args.noncss:
                    def checkpoint_preflight(database: Any) -> None:
                        programs = getattr(database, "programs", None)
                        if not isinstance(programs, dict) or not programs:
                            raise RuntimeError(
                                "loaded checkpoint contains no program "
                                "database"
                            )
                        # Validate the descriptor schema before any evaluator
                        # subprocess can mutate the in-memory checkpoint.
                        for program_id in sorted(programs):
                            _checkpoint_evaluator_kind(
                                getattr(
                                    programs[program_id],
                                    "metrics",
                                    None,
                                ),
                                expected_kind=evaluator_kind,
                                label=(
                                    "loaded checkpoint program "
                                    f"{program_id}"
                                ),
                            )
                            _validated_map_descriptor_version(
                                getattr(
                                    programs[program_id],
                                    "metrics",
                                    None,
                                ),
                                label=(
                                    "loaded checkpoint program "
                                    f"{program_id}"
                                ),
                            )
                        if preflight_contract_id is None:
                            return
                        assert observer is not None
                        _validate_loaded_checkpoint_database(
                            database,
                            args.resume,
                        )
                        source_checkpoint = _strong_checkpoint_descriptor(
                            output_dir,
                            args.resume,
                            expected_iteration=_checkpoint_last_iteration(
                                args.resume
                            ),
                        )
                        if evaluator_kind == EVALUATOR_KIND_COSET_TWO_BLOCK:
                            genome_kind = _strict_coset_checkpoint_genome_kind(
                                database,
                                expected_map_schema_version=(
                                    coset_map_schema_version
                                ),
                            )
                            if genome_kind == "legacy-python":
                                report = _install_coset_checkpoint_dsl_epoch(
                                    database,
                                    source_checkpoint=source_checkpoint,
                                    evaluator_path=EVALUATOR_ACTIVE,
                                    expected_contract_id=preflight_contract_id,
                                    wall_timeout=_winner_preflight_wall_timeout(
                                        evaluator_timeout
                                    ),
                                    coset_map_schema_version=(
                                        coset_map_schema_version
                                    ),
                                )
                                observer.record_checkpoint_preflight(report)
                                return
                            _validate_typed_coset_checkpoint_programs(
                                database,
                                expected_map_schema_version=(
                                    coset_map_schema_version
                                ),
                            )
                            if coset_map_schema_version == 4:
                                if renderer_activation_binding is None:
                                    raise RuntimeError(
                                        "renderer-v3 checkpoint preflight has "
                                        "no sealed activation"
                                    )
                                if not _activation_compatible_coset_program_ids(
                                    database,
                                    renderer_activation_binding[0],
                                ):
                                    report = (
                                        _install_coset_activation_bridge_epoch(
                                            database,
                                            source_checkpoint=(
                                                source_checkpoint
                                            ),
                                            evaluator_path=EVALUATOR_ACTIVE,
                                            expected_contract_id=(
                                                preflight_contract_id
                                            ),
                                            wall_timeout=(
                                                _winner_preflight_wall_timeout(
                                                    evaluator_timeout
                                                )
                                            ),
                                            cascade_threshold=(
                                                stage2_cascade_threshold
                                            ),
                                            expected_map_schema_version=(
                                                coset_map_schema_version
                                            ),
                                            activation_document=(
                                                renderer_activation_binding[0]
                                            ),
                                        )
                                    )
                                    observer.record_checkpoint_preflight(report)
                                    return
                        _validate_loaded_checkpoint_stage2_contract(
                            database,
                            expected_contract_id=preflight_contract_id,
                            cascade_threshold=stage2_cascade_threshold,
                        )
                        report = _backfill_checkpoint_programs(
                            database,
                            evaluator_path=EVALUATOR_ACTIVE,
                            expected_contract_id=preflight_contract_id,
                            max_workers=config.evaluator.parallel_evaluations,
                            wall_timeout=_winner_preflight_wall_timeout(
                                evaluator_timeout
                            ),
                            evaluator_kind=evaluator_kind,
                        )
                        observer.record_checkpoint_preflight(report)

                best_program = _run_resume(
                    config, output_dir, args.iterations, args.resume,
                    seed=seed_path, evaluator=EVALUATOR_ACTIVE,
                    checkpoint_preflight=checkpoint_preflight,
                )
                print(f"\nEvolution complete!")
                if best_program:
                    score = (best_program.metrics or {}).get("combined_score", 0)
                    print(f"  Best score: {score:.4f}")
                    # Save best program
                    best_filename = (
                        "best_coset_policy.json"
                        if evaluator_kind == EVALUATOR_KIND_COSET_TWO_BLOCK
                        else "best_generate_candidates.py"
                    )
                    best_path = Path(output_dir) / best_filename
                    best_path.parent.mkdir(parents=True, exist_ok=True)
                    best_path.write_text(best_program.code)
                    print(f"  Best program: {best_path}")
                print(f"  Output: {output_dir}")
            else:
                initial_program_preflight = None
                if preflight_contract_id is not None:
                    def initial_program_preflight(
                        metrics: Any,
                        artifacts: Any,
                    ) -> None:
                        _checkpoint_evaluator_kind(
                            metrics,
                            expected_kind=evaluator_kind,
                            label="fresh initial program",
                        )
                        if evaluator_kind == EVALUATOR_KIND_COSET_TWO_BLOCK and (
                            metrics.get(COSET_GENOME_FORMAT_ID_METRIC)
                            != (
                                _coset_genome_format_id_for_schema(
                                    coset_map_schema_version
                                )
                                if coset_map_schema_version is not None
                                else COSET_TYPED_DSL_GENOME_FORMAT_ID
                            )
                        ):
                            raise RuntimeError(
                                "fresh coset program lacks its typed DSL marker"
                            )
                        _validate_managed_initial_evaluation(
                            metrics,
                            artifacts,
                            expected_contract_id=preflight_contract_id,
                            cascade_threshold=stage2_cascade_threshold,
                            evaluator_kind=evaluator_kind,
                        )

                result = _run_fresh(config, output_dir, args.iterations,
                                    seed=seed_path, evaluator=EVALUATOR_ACTIVE,
                                    initial_program_preflight=(
                                        initial_program_preflight
                                    ))

                print(f"\nEvolution complete!")
                print(f"  Best score: {result.best_score:.4f}")
                print(f"  Output: {result.output_dir}")

                # Save best program
                if result.best_code:
                    best_filename = (
                        "best_coset_policy.json"
                        if evaluator_kind == EVALUATOR_KIND_COSET_TWO_BLOCK
                        else "best_generate_candidates.py"
                    )
                    best_path = Path(output_dir) / best_filename
                    best_path.parent.mkdir(parents=True, exist_ok=True)
                    best_path.write_text(result.best_code)
                    print(f"  Best program: {best_path}")

                    if args.wandb:
                        try:
                            import wandb
                            artifact = wandb.Artifact("best-program", type="code")
                            artifact.add_file(str(best_path))
                            wandb.log_artifact(artifact)
                        except Exception:
                            pass

        if managed_requested:
            assert (
                observer is not None
                and source_binding is not None
                and context_identity is not None
                and dependency_identities is not None
            )
            if negative_feedback_binding is not None:
                replayed_feedback = _validated_negative_feedback_binding(
                    live_archive_path=args.negative_feedback_live_archive,
                    snapshot_path=args.negative_feedback_snapshot,
                    snapshot_sha256=args.negative_feedback_snapshot_sha256,
                    archive_sha256=args.negative_feedback_archive_sha256,
                    manifest_path=args.negative_feedback_manifest,
                    manifest_sha256=args.negative_feedback_manifest_sha256,
                    feedback_epoch=args.negative_feedback_epoch,
                    required=True,
                    expected_run_id=(
                        run_name.removeprefix("humanize_")
                        if run_name.startswith("humanize_")
                        else None
                    ),
                )
                if replayed_feedback != negative_feedback_binding:
                    raise RuntimeError(
                        "negative-feedback binding changed during the slice"
                    )
            if renderer_activation_binding is not None:
                replayed_activation = _validated_renderer_activation_binding(
                    args.coset_renderer_activation,
                    required=True,
                )
                if replayed_activation != renderer_activation_binding:
                    raise RuntimeError(
                        "coset renderer activation changed during the slice"
                    )
            result_checkpoint, witness_identity = _write_slice_witness(
                args.slice_witness,
                observer=observer,
                source_binding=source_binding,
                output_dir=output_dir,
                resume_checkpoint=args.resume,
                iterations=args.iterations,
                config_path=args.config,
                seed_path=seed_path,
                evaluator_path=EVALUATOR_ACTIVE,
                context_path=args.humanize_context,
                context_identity=context_identity,
                dependency_identities=dependency_identities,
                backend_path=backend_path,
                codex_executable_identity=codex_executable_identity,
                invocation=invocation_binding,
                candidate_log_path=candidate_log_path,
                candidate_start_offset=args.candidate_start_offset,
                renderer_activation=(
                    None
                    if renderer_activation_binding is None
                    else renderer_activation_binding[0]
                ),
                renderer_activation_identity=(
                    None
                    if renderer_activation_binding is None
                    else renderer_activation_binding[1]
                ),
            )
            _write_completion_marker(
                args.completion_marker,
                output_dir=output_dir,
                resume_checkpoint=args.resume,
                iterations=args.iterations,
                config_path=args.config,
                seed_path=seed_path,
                evaluator_path=EVALUATOR_ACTIVE,
                context_path=args.humanize_context,
                context_identity=context_identity,
                dependency_identities=dependency_identities,
                backend_path=backend_path,
                codex_executable_identity=codex_executable_identity,
                invocation=invocation_binding,
                result_checkpoint=result_checkpoint,
                slice_witness=witness_identity,
                renderer_activation=(
                    None
                    if renderer_activation_binding is None
                    else renderer_activation_binding[0]
                ),
                renderer_activation_identity=(
                    None
                    if renderer_activation_binding is None
                    else renderer_activation_binding[1]
                ),
            )

    except SystemExit as exc:
        if managed_requested and (
            exc.code in (None, 0)
            or (observer is not None and observer.shutdown_requested)
        ):
            raise SystemExit(130) from exc
        raise
    except ImportError:
        print("openevolve not installed. Run: uv sync --group evolve")
        sys.exit(1)
    except KeyboardInterrupt:
        print("\nEvolution interrupted by user.")
        raise SystemExit(130)
    finally:
        for name, original_value in original_environment.items():
            if original_value is None:
                os.environ.pop(name, None)
            else:
                os.environ[name] = original_value
        if wandb_syncer:
            wandb_syncer.stop()
        if args.wandb:
            try:
                import wandb
                wandb.finish()
            except Exception:
                pass


if __name__ == "__main__":
    main()
