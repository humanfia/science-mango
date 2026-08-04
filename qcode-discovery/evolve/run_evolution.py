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
* Best evolved program: ``results/evolution/<run_name>/best_generate_candidates.py``
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

from evolve.dependency_contract import LOCAL_EVALUATOR_DEPENDENCIES
from evaluation.search_contract import EVOLUTION_LATTICES

SEED_SOLUTION = str(Path(__file__).parent / "seed_solution.py")
SEED_SOLUTION_MILP = str(Path(__file__).parent / "seed_solution_milp.py")
SEED_SOLUTION_NONCSS = str(Path(__file__).parent / "seed_solution_noncss.py")
EVALUATOR = str(Path(__file__).parent / "openevolve_evaluator.py")
EVALUATOR_NONCSS = str(Path(__file__).parent / "openevolve_evaluator_noncss.py")
DEFAULT_CONFIG = str(Path(__file__).parent / "config.yaml")
DEFAULT_CONFIG_NONCSS = str(Path(__file__).parent / "config_noncss.yaml")
EVOLUTION_BASE = str(Path(PROJECT_ROOT) / "results" / "evolution")
METRICS_FILE = str(Path(PROJECT_ROOT) / "results" / "evolution_metrics.jsonl")


# Schema 5 binds the mechanism-portfolio semantics (relation-first MAP cells,
# lineage islands, and the recorded search regime).  Schema 4 artifacts remain
# legacy inputs for the Humanize recovery layer; this launcher never emits a
# schema-4 artifact with the new semantics.
EVOLUTION_LEGACY_COMPLETION_SCHEMA_VERSION = 4
EVOLUTION_LEGACY_SLICE_WITNESS_SCHEMA_VERSION = 4
EVOLUTION_COMPLETION_SCHEMA_VERSION = 5
EVOLUTION_SLICE_WITNESS_SCHEMA_VERSION = 5
WINNER_PREFLIGHT_CONTRACT_VERSION = 2
WINNER_PREFLIGHT_CONTRACT_ID_ENV = "QCODE_WINNER_PREFLIGHT_CONTRACT_ID"
CANDIDATE_LOG_PATH_ENV = "QCODE_CANDIDATE_LOG_PATH"
STAGE1_PREFLIGHT_JOURNAL_SCHEMA_VERSION = 1
STAGE1_PREFLIGHT_JOURNAL_DIRECTORY = ".stage1-preflight"
STAGE1_PREFLIGHT_MAX_EPOCH_ATTEMPTS = 2
STAGE1_PREFLIGHT_WORKER_ATTEMPTS = 2
STAGE1_PREFLIGHT_LOCK_WAIT_INTERVALS = 2
STAGE1_PREFLIGHT_OUTER_MARGIN_S = 120.0
STAGE2_DEEP_CONTRACT_VERSION = 2
STAGE2_DEEP_LATTICE_COUNT = 11
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
SEARCH_PORTFOLIO_FEATURE_DIMENSIONS = (
    MAP_DESCRIPTOR_ALGEBRAIC_RELATION_METRIC,
    MAP_DESCRIPTOR_SUPPORT_SPLIT_METRIC,
    MAP_DESCRIPTOR_ORBIT_SPAN_METRIC,
)
SEARCH_PORTFOLIO_FEATURE_BINS = {
    MAP_DESCRIPTOR_ALGEBRAIC_RELATION_METRIC: 5,
    MAP_DESCRIPTOR_SUPPORT_SPLIT_METRIC: 6,
    MAP_DESCRIPTOR_ORBIT_SPAN_METRIC: 3,
}
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
        "Disrupt replayed low-weight X logical mechanisms while preserving "
        "commutation, positive k, and structural novelty."
    ),
    "repair_z_low_weight": (
        "Disrupt replayed low-weight Z logical mechanisms while preserving "
        "commutation, positive k, and structural novelty."
    ),
    "repair_dual_balance": (
        "Change the A/B relationship so neither X nor Z logical direction "
        "remains an easy low-weight failure mode."
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
SEARCH_REGIME_PREFIX_BY_POLICY_VERSION = {
    1: SEARCH_REGIME_POLICY_PREFIX,
    2: SEARCH_REGIME_POLICY_V2_PREFIX,
    3: SEARCH_REGIME_POLICY_V3_PREFIX,
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
}

def _evaluator_dependency_identities() -> dict[str, dict[str, Any]]:
    project_root = Path(PROJECT_ROOT)
    return {
        name: _file_identity(
            project_root / relative_path,
            f"evolution evaluator dependency {name}",
        )
        for name, relative_path in LOCAL_EVALUATOR_DEPENDENCIES.items()
    }


def _winner_preflight_contract_id(
    evaluator_path: str | Path,
    dependency_identities: dict[str, dict[str, Any]],
    *,
    candidate_log_path: str | Path,
) -> int:
    """Bind checkpoint markers to code, lattices, and their durable run sink."""

    evaluator = _file_identity(
        evaluator_path, "winner preflight evaluator"
    )
    dependency_hashes: dict[str, str] = {}
    for name in sorted(LOCAL_EVALUATOR_DEPENDENCIES):
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


_WINNER_PREFLIGHT_MARKER_FIELDS = (
    WINNER_PREFLIGHT_CONTRACT_VERSION_METRIC,
    WINNER_PREFLIGHT_CONTRACT_ID_METRIC,
    WINNER_PREFLIGHT_COMPLETE_METRIC,
    WINNER_PREFLIGHT_INCOMPLETE_METRIC,
    WINNER_PREFLIGHT_LATTICES_METRIC,
    WINNER_PREFLIGHT_EVALUATED_METRIC,
    WINNER_PREFLIGHT_ELIGIBLE_METRIC,
    WINNER_PREFLIGHT_PERSISTED_METRIC,
    WINNER_PREFLIGHT_OMITTED_METRIC,
    WINNER_PREFLIGHT_HARD_TIMEOUT_METRIC,
    WINNER_PREFLIGHT_SUBPROCESS_FAILED_METRIC,
)

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
) -> dict[str, float]:
    if not isinstance(metrics, dict):
        raise RuntimeError("winner preflight metrics are not an object")
    values = {
        name: _exact_nonnegative_metric(metrics, name)
        for name in _WINNER_PREFLIGHT_MARKER_FIELDS
    }
    if (
        values[WINNER_PREFLIGHT_CONTRACT_VERSION_METRIC]
        != WINNER_PREFLIGHT_CONTRACT_VERSION
        or values[WINNER_PREFLIGHT_CONTRACT_ID_METRIC]
        != expected_contract_id
        or values[WINNER_PREFLIGHT_COMPLETE_METRIC] != 1
        or values[WINNER_PREFLIGHT_INCOMPLETE_METRIC] != 0
        or values[WINNER_PREFLIGHT_LATTICES_METRIC]
        != len(EVOLUTION_LATTICES)
        or values[WINNER_PREFLIGHT_OMITTED_METRIC] != 0
        or values[WINNER_PREFLIGHT_HARD_TIMEOUT_METRIC] != 0
        or values[WINNER_PREFLIGHT_SUBPROCESS_FAILED_METRIC] != 0
        or values[WINNER_PREFLIGHT_PERSISTED_METRIC]
        != values[WINNER_PREFLIGHT_ELIGIBLE_METRIC]
        or values[WINNER_PREFLIGHT_EVALUATED_METRIC]
        < values[WINNER_PREFLIGHT_ELIGIBLE_METRIC]
    ):
        raise RuntimeError(
            "winner preflight markers do not prove complete persistence"
        )
    return {name: float(values[name]) for name in values}


def _exact_incomplete_winner_preflight_markers(
    metrics: Any,
    *,
    expected_contract_id: int,
) -> dict[str, float] | None:
    """Recognize only the evaluator's canonical incomplete-preflight envelope.

    A child with this envelope is a fully observed *failed attempt*, not a
    checkpointable program.  Returning ``None`` is deliberately fail-closed:
    malformed markers, a wrong contract, or an inconsistent claim continue
    through the normal database-add observer and make the whole slice fail.
    """

    expected_fields = _WINNER_PREFLIGHT_FAILURE_BASE_FIELDS.union(
        _WINNER_PREFLIGHT_MARKER_FIELDS
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
    try:
        values = {
            name: _exact_nonnegative_metric(metrics, name)
            for name in _WINNER_PREFLIGHT_MARKER_FIELDS
        }
    except RuntimeError:
        return None
    if (
        values[WINNER_PREFLIGHT_CONTRACT_VERSION_METRIC]
        != WINNER_PREFLIGHT_CONTRACT_VERSION
        or values[WINNER_PREFLIGHT_CONTRACT_ID_METRIC]
        != expected_contract_id
        or values[WINNER_PREFLIGHT_COMPLETE_METRIC] != 0
        or values[WINNER_PREFLIGHT_INCOMPLETE_METRIC] != 1
        or values[WINNER_PREFLIGHT_LATTICES_METRIC] != 0
        or values[WINNER_PREFLIGHT_EVALUATED_METRIC] != 0
        or values[WINNER_PREFLIGHT_ELIGIBLE_METRIC] != 0
        or values[WINNER_PREFLIGHT_PERSISTED_METRIC] != 0
        or values[WINNER_PREFLIGHT_OMITTED_METRIC] != 0
        or values[WINNER_PREFLIGHT_HARD_TIMEOUT_METRIC] not in (0, 1)
        or values[WINNER_PREFLIGHT_SUBPROCESS_FAILED_METRIC] != 1
    ):
        return None
    return {name: float(values[name]) for name in values}


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
) -> dict[str, float] | None:
    """Recognize only the evaluator's bound Stage 2 failure envelope."""

    if not isinstance(metrics, dict) or not isinstance(artifacts, dict):
        return None
    try:
        _validated_winner_preflight_markers(
            metrics,
            expected_contract_id=expected_contract_id,
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
        _validated_winner_preflight_markers(
            program.get("metrics"),
            expected_contract_id=expected_contract_id,
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
) -> None:
    """Fail before a fresh seed with incomplete evaluation enters the DB."""

    _validated_winner_preflight_markers(
        metrics,
        expected_contract_id=expected_contract_id,
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
        if (
            not isinstance(payload, dict)
            or set(payload) != {"schema_version", "status", "metrics"}
            or payload.get("schema_version") != 1
            or payload.get("status") != "completed"
            or not isinstance(payload.get("metrics"), dict)
            or set(payload["metrics"]) != set(_WINNER_PREFLIGHT_MARKER_FIELDS)
        ):
            raise _WinnerPreflightChildFailure(
                "winner preflight result schema is invalid"
            )
        return _validated_winner_preflight_markers(
            payload["metrics"],
            expected_contract_id=expected_contract_id,
        )


def _execute_winner_preflight(
    evaluator_path: str | Path,
    code: str,
    *,
    expected_contract_id: int,
    wall_timeout: float,
    cancel_event: threading.Event,
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
                )
            except (
                _WinnerPreflightTimeout,
                _WinnerPreflightChildFailure,
                OSError,
            ):
                if attempt >= STAGE1_PREFLIGHT_WORKER_ATTEMPTS:
                    raise
        raise AssertionError("winner preflight retry loop did not return")


def _backfill_checkpoint_programs(
    database: Any,
    *,
    evaluator_path: str | Path,
    expected_contract_id: int,
    max_workers: int,
    wall_timeout: float,
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
    best_path = resolved / "best_program.py"
    best_info_path = resolved / "best_program_info.json"
    programs_dir = resolved / "programs"
    metadata = _read_json_object(metadata_path, "checkpoint metadata")
    best_info = _read_json_object(
        best_info_path, "checkpoint best-program info"
    )
    if (
        best_path.is_symlink()
        or not best_path.is_file()
        or best_path.stat().st_size < 1
    ):
        raise RuntimeError(
            f"checkpoint best_program.py is missing or empty: {best_path}"
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
        "best_program.py": _file_sha256(best_path),
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
            "checkpoint best_program.py does not match the stored "
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


def _validated_search_portfolio_config(config: Any) -> int:
    """Validate the fixed five-island mechanism-aware search geometry.

    OpenEvolve normally rescales every custom MAP dimension from the values
    observed so far.  That makes a checkpoint's cells depend on evaluation
    completion order.  The managed ansatz campaign instead has a versioned,
    categorical grid; accepting any other shape would silently mix archives.
    """

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
        or dimensions != list(SEARCH_PORTFOLIO_FEATURE_DIMENSIONS)
    ):
        raise RuntimeError(
            "search portfolio feature_dimensions must be the fixed "
            "mechanism/support/orbit tuple"
        )
    bins = getattr(database, "feature_bins", None)
    if (
        not isinstance(bins, dict)
        or set(bins) != set(SEARCH_PORTFOLIO_FEATURE_BINS)
        or any(
            isinstance(bins[name], bool)
            or not isinstance(bins[name], int)
            or bins[name] != expected
            for name, expected in SEARCH_PORTFOLIO_FEATURE_BINS.items()
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


def _search_portfolio_requested(config_path: str | Path) -> bool:
    """Return whether a YAML config explicitly opts into the fixed portfolio."""

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
        return False
    marker = value[SEARCH_PORTFOLIO_CONFIG_KEY]
    if (
        not isinstance(marker, dict)
        or set(marker) != {"enabled", "schema_version"}
        or marker["enabled"] is not True
        or type(marker["schema_version"]) is not int
        or marker["schema_version"] != SEARCH_PORTFOLIO_SCHEMA_VERSION
    ):
        raise RuntimeError(
            "qcode_search_portfolio marker must be exactly "
            "{enabled: true, schema_version: 2}"
        )
    return True


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


def _fixed_search_feature_coords(program: Any) -> list[int]:
    metrics = getattr(program, "metrics", None)
    _validated_map_descriptor_version(
        metrics, label=f"search portfolio program {getattr(program, 'id', '?')}"
    )
    assert isinstance(metrics, dict)
    categories: list[int] = []
    for name in SEARCH_PORTFOLIO_FEATURE_DIMENSIONS:
        value = metrics.get(name)
        limit = SEARCH_PORTFOLIO_FEATURE_BINS[name]
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


def _rebuild_fixed_search_feature_maps(database: Any) -> None:
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
        coords = _fixed_search_feature_coords(program)
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
    database.feature_bins_per_dim = dict(SEARCH_PORTFOLIO_FEATURE_BINS)
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


def _search_elite_ids(database: Any, island: int) -> list[str]:
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
            if _fixed_search_feature_coords(program)[0] in expected_relations:
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
    stage2_cascade_threshold: float | None = None
    checkpoint_preflight_required: bool = False
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
                    SEARCH_PORTFOLIO_SCHEMA_VERSION,
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
        self.submission_attempts.append(attempt)
        if future is None:
            return None
        return _ObservedFuture(future, iteration, self)

    def record_future_exception(self, iteration: int, exc: BaseException) -> None:
        self.consumed[iteration] = self.consumed.get(iteration, 0) + 1
        self.violations.append(
            f"future {iteration} raised {type(exc).__name__}"
        )

    def _record_worker_error(self, iteration: int, error: str) -> None:
        encoded = error.encode("utf-8")
        self.outcomes[iteration] = {
            "iteration": iteration,
            "status": "worker_error",
            "error_sha256": hashlib.sha256(encoded).hexdigest(),
            "error_bytes": len(encoded),
        }

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
            self._record_worker_error(iteration, error)
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
            incomplete = _exact_incomplete_winner_preflight_markers(
                child.get("metrics"),
                expected_contract_id=self.expected_preflight_contract_id,
            )
            if incomplete is not None:
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
                    "kind": "winner_preflight_incomplete",
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
                _validated_winner_preflight_markers(
                    child.get("metrics"),
                    expected_contract_id=(
                        self.expected_preflight_contract_id
                    ),
                )
                preflight_is_complete = True
            except RuntimeError:
                preflight_is_complete = False
            result_artifacts = getattr(result, "artifacts", None)
            stage2_incomplete = (
                _exact_incomplete_stage2_markers(
                    child.get("metrics"),
                    result_artifacts,
                    expected_contract_id=(
                        self.expected_preflight_contract_id
                    ),
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
            or report.get("schema_version") != 1
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
        # A worker_error has no checkpoint Program.  It covers both an LLM/diff
        # failure that never produced a child and the exact evaluator-generated
        # incomplete-preflight or incomplete-Stage-2 envelope sanitized before
        # database.add. Neither outcome claims that a candidate universe was
        # enumerated completely. Malformed/forged marker claims and future
        # exceptions remain violations.
        if successful < 1:
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
    }
    binding: dict[str, dict[str, Any]] = {}
    for name, module in modules.items():
        identity = _file_identity(module.__file__, f"OpenEvolve {name} source")
        if identity["sha256"] != SUPPORTED_OPENEVOLVE_SHA256[name]:
            raise RuntimeError(f"unsupported OpenEvolve {name} source hash")
        binding[name] = identity
    return binding, controller_module, process_module


@contextmanager
def _verified_slice_controller(
    base_iteration: int,
    iterations: int,
    *,
    expected_preflight_contract_id: int | None = None,
    stage2_cascade_threshold: float | None = None,
    checkpoint_preflight_required: bool = False,
    search_config: Any = None,
    adaptive_mutation_policy: dict[str, int] | None = None,
    search_regime: dict[str, Any] | None = None,
):
    if isinstance(iterations, bool) or not isinstance(iterations, int) or iterations < 1:
        raise RuntimeError("managed slice iterations must be positive")
    source_binding, controller_module, process_module = _openevolve_source_binding()
    observer = _SliceObserver(
        base_iteration=base_iteration,
        iterations=iterations,
        result_type=process_module.SerializableResult,
        expected_preflight_contract_id=expected_preflight_contract_id,
        stage2_cascade_threshold=stage2_cascade_threshold,
        checkpoint_preflight_required=checkpoint_preflight_required,
    )
    portfolio_seed: int | None = None
    portfolio_policy: dict[str, int] | None = None
    portfolio_regime = dict(DEFAULT_SEARCH_REGIME)
    if search_config is not None:
        portfolio_seed = _validated_search_portfolio_config(search_config)
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

    class VerifiedProcessParallelController(original_parallel):
        def __init__(self, *args: Any, **kwargs: Any) -> None:
            super().__init__(*args, **kwargs)
            self._search_iteration_targets: dict[int, int] = {}
            self._search_slice_elites: tuple[tuple[str, ...], ...] | None = (
                None
            )
            self._search_slice_programs: dict[str, Any] | None = None
            self._search_slice_snapshot: dict[str, Any] | None = None
            if portfolio_seed is not None:
                _validated_search_portfolio_config(self.config)
                self.database._calculate_feature_coords = (
                    _fixed_search_feature_coords
                )
                _rebuild_fixed_search_feature_maps(self.database)

        def request_shutdown(self) -> None:
            observer.shutdown_requested = True
            return super().request_shutdown()

        def _submit_iteration(self, iteration: int, island_id: Any = None) -> Any:
            if portfolio_seed is None:
                future = super()._submit_iteration(iteration, island_id)
                return observer.record_submission(iteration, island_id, future)
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
                "schema_version": SEARCH_PORTFOLIO_SCHEMA_VERSION,
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
                _rebuild_fixed_search_feature_maps(self.database)
                self._search_slice_elites = tuple(
                    tuple(_search_elite_ids(self.database, island))
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
                result = original_add(
                    program,
                    iteration=iteration,
                    target_island=effective_target,
                )
                if portfolio_seed is not None:
                    _rebuild_fixed_search_feature_maps(self.database)
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


def _launch_input_identities(
    config_path: str | Path,
    seed_path: str | Path,
    evaluator_path: str | Path,
    context_path: str | Path,
    context_identity: dict[str, Any],
    dependency_identities: dict[str, dict[str, Any]],
    backend_path: str | Path | None,
    codex_executable_identity: dict[str, Any] | None,
) -> dict[str, dict[str, Any]]:
    observed_context = _file_identity(
        context_path, "evolution humanize context"
    )
    if observed_context != context_identity:
        raise RuntimeError("evolution humanize context changed after snapshot")
    observed_dependencies = _evaluator_dependency_identities()
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


def _validated_invocation_binding(
    invocation: dict[str, Any],
    backend_path: str | Path | None,
    codex_executable_identity: dict[str, Any] | None,
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
    if not isinstance(invocation, dict) or set(invocation) != expected_fields:
        raise RuntimeError("managed invocation binding fields are incomplete")
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
) -> tuple[dict[str, Any], dict[str, Any]]:
    if not observer.accounting_complete:
        raise RuntimeError("OpenEvolve slice accounting did not complete")
    effective_invocation = _validated_invocation_binding(
        invocation, backend_path, codex_executable_identity
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
                "schema_version": SEARCH_PORTFOLIO_SCHEMA_VERSION,
                "island_count": SEARCH_PORTFOLIO_ISLAND_COUNT,
                "roles": list(SEARCH_PORTFOLIO_ROLES),
                "feature_dimensions": list(
                    SEARCH_PORTFOLIO_FEATURE_DIMENSIONS
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
) -> None:
    effective_invocation = _validated_invocation_binding(
        invocation, backend_path, codex_executable_identity
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

    # Resolve model list (None means "use config as-is")
    if args.models:
        model_names = args.models
    elif args.model:
        model_names = [args.model]
    else:
        model_names = None  # use whatever is in the config YAML

    # Resolve config path
    if args.config is None:
        args.config = DEFAULT_CONFIG_NONCSS if args.noncss else DEFAULT_CONFIG

    api_base = _resolve_api_base(args)
    output_dir = _resolve_output_dir(args)

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
    )
    original_environment = {
        name: os.environ.get(name)
        for name in mutated_environment_names
    }
    run_name = Path(output_dir).name
    os.environ["QCODE_RUN_NAME"] = run_name
    candidate_log_path = (
        Path(output_dir).expanduser().resolve() / "all_codes.jsonl"
    )
    os.environ[CANDIDATE_LOG_PATH_ENV] = str(candidate_log_path)
    if managed_requested:
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
    if args.noncss:
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
            dependency_identities = _evaluator_dependency_identities()
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
        if not args.noncss:
            search_portfolio_enabled = _search_portfolio_requested(
                args.config
            )
            if search_portfolio_enabled and not managed_requested:
                raise RuntimeError(
                    "qcode_search_portfolio requires managed Humanize "
                    "slice accounting"
                )
            if search_portfolio_enabled:
                _validated_search_portfolio_config(config)
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
        print(f"  Seed: {seed_path}")
        if args.noncss:
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
                adaptive_mutation_policy=adaptive_mutation_policy,
                search_regime=search_regime,
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
                    best_path = Path(output_dir) / "best_generate_candidates.py"
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
                        _validate_managed_initial_evaluation(
                            metrics,
                            artifacts,
                            expected_contract_id=preflight_contract_id,
                            cascade_threshold=stage2_cascade_threshold,
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
                    best_path = Path(output_dir) / "best_generate_candidates.py"
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
