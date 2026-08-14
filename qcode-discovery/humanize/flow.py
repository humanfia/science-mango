"""Humanize RLCR controller around OpenEvolve, MILP, and qcode artifacts."""

from __future__ import annotations

import copy
import fcntl
import hashlib
import inspect
import json
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

import yaml
from collections.abc import Collection, Mapping
from concurrent.futures import ThreadPoolExecutor, as_completed
from contextlib import contextmanager
from dataclasses import asdict, dataclass, replace
from pathlib import Path
from typing import Any, Callable, Iterator, Protocol

from evolve.dependency_contract import (
    ANSATZ_V3_EVALUATOR_DEPENDENCIES,
    COSET_EVALUATOR_DEPENDENCIES,
    LOCAL_EVALUATOR_DEPENDENCIES,
)
from evolve.coset_search_contract import (
    COSET_FEATURE_BINS,
    COSET_FEATURE_DIMENSIONS,
    COSET_MAP_SCHEMA_VERSION,
    COSET_PROOF_LADDER_CONFIG_KEY,
    COSET_REPRESENTATION_ID,
    COSET_REPRESENTATION_ID_V3,
    coset_renderer_portfolio_contract,
    proof_ladder_config_contract,
)
from evaluation.geometry import candidate_geometry
from evaluation.search_contract import (
    LEGACY_GEOMETRY_CONTRACT,
    PUBLISHED_VOLUME_ANSATZ_V3_REPRESENTATION_ID,
    SEARCH_GEOMETRY_CONTRACT_ENV,
    geometry_contract_for_representation,
    is_twisted_geometry_contract,
)
from evaluation.target_policy import (
    DEFAULT_TARGET_MODE,
    TARGET_MODE_GIST,
    classify_target_win,
    target_binding,
    validate_target_binding,
    validate_target_mode,
)

from .audit_state import (
    AuditOutcome,
    AuditStateError,
    authoritative_candidate_digest,
    candidate_digest_definition_sha256,
    classify_evaluation,
    is_fully_exact,
    rebuild_audit_state,
    retry_budget,
    seal_audit_attempt_evidence,
    select_retry_lane,
)
from .reviewer import (
    CodexReviewer,
    ReviewError,
    build_review_prompt,
    replay_historical_scalar_only_search_oracle_witness_geometry,
    replay_search_oracle_upper_bound_geometry,
    replay_search_oracle_witness_geometry,
    validate_review,
)
from .state import (
    EliteArchive,
    RunStore,
    atomic_write_bytes,
    atomic_write_json,
    atomic_write_jsonl,
    candidate_evidence_priority,
    candidate_fom,
    candidate_proven_fom,
    candidate_terminal_negative,
    code_key,
    read_jsonl_range,
    utc_now,
)


class Reviewer(Protocol):
    def review(self, prompt: str, round_dir: Path) -> dict[str, Any]: ...


MilpEvaluator = Callable[..., dict[str, Any]]
EvolutionRunner = Callable[["FlowConfig", dict[str, Any], Path], Path | None]


ROUND_TRANSACTION_LEGACY_PROTOCOL_VERSION = 2
ROUND_TRANSACTION_LEGACY_SCHEMA_VERSION = 2
ROUND_TRANSACTION_PROTOCOL_VERSION = 3
ROUND_TRANSACTION_SCHEMA_VERSION = 3
ROUND_TRANSACTION_SUPPORTED_IDENTITIES = (
    (
        ROUND_TRANSACTION_LEGACY_SCHEMA_VERSION,
        ROUND_TRANSACTION_LEGACY_PROTOCOL_VERSION,
    ),
    (ROUND_TRANSACTION_SCHEMA_VERSION, ROUND_TRANSACTION_PROTOCOL_VERSION),
)
ROUND_TRANSACTION_SUPPORTED_PROTOCOL_VERSIONS = tuple(
    protocol for _schema, protocol in ROUND_TRANSACTION_SUPPORTED_IDENTITIES
)
CANDIDATE_BATCH_POLICY_LEGACY_VERSION = 1
CANDIDATE_BATCH_POLICY_LOWER_BOUND_VERSION = 2
CANDIDATE_BATCH_POLICY_EVIDENCE_MERGE_VERSION = 3
CANDIDATE_BATCH_POLICY_WITNESS_METADATA_VERSION = 4
CANDIDATE_BATCH_POLICY_COMPOSITE_PROVENANCE_VERSION = 5
CANDIDATE_BATCH_POLICY_AUDIT_FUNNEL_VERSION = 6
CANDIDATE_BATCH_POLICY_VERSION = (
    CANDIDATE_BATCH_POLICY_AUDIT_FUNNEL_VERSION
)
CANDIDATE_BATCH_POLICY_VERSIONS = (
    CANDIDATE_BATCH_POLICY_LEGACY_VERSION,
    CANDIDATE_BATCH_POLICY_LOWER_BOUND_VERSION,
    CANDIDATE_BATCH_POLICY_EVIDENCE_MERGE_VERSION,
    CANDIDATE_BATCH_POLICY_WITNESS_METADATA_VERSION,
    CANDIDATE_BATCH_POLICY_COMPOSITE_PROVENANCE_VERSION,
    CANDIDATE_BATCH_POLICY_VERSION,
)
SEARCH_DISTANCE_INTERVAL_PROOF_SCHEMA_VERSION = 1
SEARCH_DISTANCE_INTERVAL_PROOF_KIND = (
    "qcode-humanize-search-distance-interval-proof"
)
ROUND_CANDIDATE_DIVERSITY_SCHEMA_VERSION = 1
SEALED_ROUND_EXACT_SCHEMA_VERSION = 1
SEARCH_REGIME_SCHEMA_VERSION = 1
SEARCH_REGIME_KIND = "qcode-humanize-search-regime"
SEARCH_REGIME_PREFIX = "QCODE_SEARCH_REGIME_V1="
SEARCH_REGIME_V2_PREFIX = "QCODE_SEARCH_REGIME_V2="
SEARCH_REGIME_V3_PREFIX = "QCODE_SEARCH_REGIME_V3="
SEARCH_REGIME_V4_PREFIX = "QCODE_SEARCH_REGIME_V4="
SEARCH_REGIME_POLICY_VERSIONS = (1, 2, 3, 4)
SEARCH_REGIME_BUDGET_BOUND_POLICY_VERSIONS = frozenset({3, 4})
SEARCH_REGIME_PREFIX_BY_POLICY_VERSION = {
    1: SEARCH_REGIME_PREFIX,
    2: SEARCH_REGIME_V2_PREFIX,
    3: SEARCH_REGIME_V3_PREFIX,
    4: SEARCH_REGIME_V4_PREFIX,
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
SEARCH_REGIME_STAGNATION_ROUNDS = 3
SEARCH_REGIME_EXPANSION_ROUNDS = 4
SEARCH_REGIME_REPRESENTATION_ROUNDS = 7
SEARCH_REGIME_DUPLICATE_RATE = 0.8
SEARCH_HANDOFF_REASON_REPRESENTATION_CHANGE = (
    "representation_change_required"
)
FAILURE_DIRECTION_FEEDBACK_SCHEMA_VERSION = 1
FAILURE_DIRECTION_FEEDBACK_KIND = (
    "qcode-humanize-failure-direction-feedback"
)
SEARCH_ORACLE_FEEDBACK_SCHEMA_VERSION = 1
SEARCH_ORACLE_FEEDBACK_KIND = "qcode-humanize-low-weight-oracle-feedback"
SEARCH_ORACLE_FEEDBACK_MAX_PER_SIDE = 4
SEARCH_ORACLE_FEEDBACK_MAX_ATTEMPTS = (
    2 * SEARCH_ORACLE_FEEDBACK_MAX_PER_SIDE
)
HISTORICAL_SCALAR_ONLY_COSET_EVALUATOR_SHA256 = frozenset({
    "7ddb1351f36476ed77871c1d376bc2b834bd7325d0f5dd3545ab9c0553432d8a",
})
ADAPTIVE_MUTATION_POLICY_SCHEMA_VERSION = 1
ADAPTIVE_MUTATION_TOTAL_WEIGHT = 1000
ADAPTIVE_MUTATION_EXPLORATION_FLOOR = 250
ADAPTIVE_MUTATION_TACTICS = (
    "novel_structure_exploration",
    "repair_x_low_weight",
    "repair_z_low_weight",
    "repair_dual_balance",
)
ADAPTIVE_MUTATION_POLICY_PREFIX = "QCODE_ADAPTIVE_MUTATION_POLICY_V1="
DEFAULT_ADAPTIVE_MUTATION_POLICY = {
    "novel_structure_exploration": 1000,
    "repair_x_low_weight": 0,
    "repair_z_low_weight": 0,
    "repair_dual_balance": 0,
}
LEGACY_BATCH_SCHEMA_VERSION = 1
EVOLUTION_COMPLETION_SCHEMA_VERSION = 7
EVOLUTION_SLICE_WITNESS_PREVIOUS_SCHEMA_VERSION = 4
EVOLUTION_SLICE_WITNESS_PRE_EVALUATOR_BINDING_SCHEMA_VERSION = 5
EVOLUTION_SLICE_WITNESS_SCHEMA_VERSION = 7
EVOLUTION_SLICE_WITNESS_LEGACY_SCHEMA_VERSIONS = frozenset({2, 3, 4, 5, 6})
EVOLUTION_SLICE_WITNESS_MECHANISM_SCHEMA_VERSIONS = frozenset({5, 6, 7})
EVOLUTION_SLICE_WITNESS_PORTFOLIO_SCHEMA_VERSIONS = frozenset({4, 5, 6, 7})
OPENEVOLVE_BASE_WITNESS_SOURCES = (
    "openevolve_controller",
    "openevolve_process_parallel",
    "openevolve_database",
    "openevolve_api",
)
OPENEVOLVE_EVALUATOR_BOUND_WITNESS_SOURCES = (
    *OPENEVOLVE_BASE_WITNESS_SOURCES,
    "openevolve_evaluator",
)
SEARCH_PORTFOLIO_SCHEMA_VERSION = 2
SEARCH_PORTFOLIO_CONFIG_KEY = "qcode_search_portfolio"
SEARCH_PORTFOLIO_ISLAND_COUNT = 5
COSET_SEARCH_PORTFOLIO_CONFIG_KEY = "qcode_coset_search_portfolio"
COSET_SEARCH_PORTFOLIO_COMPATIBILITY_GROUP = (
    "coset-two-block-catalog-v2-dsl-map-v3-proof-ladder-v3"
)
COSET_SEARCH_PORTFOLIO_ISLAND_COUNT = 4
SEARCH_PORTFOLIO_FEATURE_DIMENSIONS = (
    "algebraic_relation_type",
    "support_split_type",
    "orbit_span_bin",
)
SEARCH_PORTFOLIO_FEATURE_BINS = {
    "algebraic_relation_type": 5,
    "support_split_type": 6,
    "orbit_span_bin": 3,
}
SEARCH_PORTFOLIO_V3_SCHEMA_VERSION = 3
SEARCH_PORTFOLIO_V3_FEATURE_DIMENSIONS = (
    "algebraic_relation_type",
    "support_split_type",
    "geometry_twist_class",
)
SEARCH_PORTFOLIO_V3_FEATURE_BINS = {
    "algebraic_relation_type": 5,
    "support_split_type": 6,
    "geometry_twist_class": 3,
}
SEARCH_PORTFOLIO_SPECS = {
    SEARCH_PORTFOLIO_SCHEMA_VERSION: (
        SEARCH_PORTFOLIO_FEATURE_DIMENSIONS,
        SEARCH_PORTFOLIO_FEATURE_BINS,
    ),
    SEARCH_PORTFOLIO_V3_SCHEMA_VERSION: (
        SEARCH_PORTFOLIO_V3_FEATURE_DIMENSIONS,
        SEARCH_PORTFOLIO_V3_FEATURE_BINS,
    ),
}
SEARCH_PORTFOLIO_ROLES = (
    "affine_automorphism_cover",
    "shared_anchor_coset_cover",
    "complementary_diagonal_cover",
    "asymmetric_anchor_cover",
    "failure_repair_restart",
)
# Schema-v4 witnesses were produced by the original support-shape portfolio.
# Keep its vocabulary frozen solely to validate already-written recovery
# artifacts.  New slices must never emit or reinterpret this contract.
LEGACY_V4_SEARCH_PORTFOLIO_SCHEMA_VERSION = 1
LEGACY_V4_SEARCH_PORTFOLIO_FEATURE_DIMENSIONS = (
    "pattern_type",
    "support_split_type",
    "search_structural_entropy",
)
LEGACY_V4_SEARCH_PORTFOLIO_FEATURE_BINS = {
    "pattern_type": 6,
    "support_split_type": 6,
    "search_structural_entropy": 5,
}
LEGACY_V4_SEARCH_PORTFOLIO_ROLES = (
    "compact_mixed_2_2",
    "hybrid_2_3_3_2",
    "balanced_3_3",
    "asymmetric_2_4_4_2",
    "failure_repair_novelty",
)
CANDIDATE_WITNESS_FIELDS = (
    "candidate_log_path",
    "candidate_log_device",
    "candidate_log_inode",
    "candidate_start_offset",
    "candidate_end_offset",
    "candidate_range_sha256",
    "candidate_range_bytes",
    "candidate_wal_clean",
)
LOCAL_EVOLUTION_DEPENDENCIES = LOCAL_EVALUATOR_DEPENDENCIES
# Transactions prepared before ``evaluation_final_gate`` was added have no
# explicit binding-schema field.  Keep the exact historical shape allowlisted
# so an *unbound* prepared transaction can abandon its old slice and rebind.
# Do not accept arbitrary subsets: a missing dependency could otherwise turn
# manifest corruption into an unaudited source upgrade.
_COSET_DSL_LAUNCH_FIELDS = frozenset({
    "coset_policy_dsl",
    "coset_policy_dsl_v3",
    "coset_policy_dispatch",
    "coset_mutation_preflight",
    "coset_negative_archive",
    "coset_sparse_kernel_oracle",
    "coset_witness_symmetry_verifier",
    "coset_reviewer_contract",
    "coset_reviewer_activation",
})
COSET_NEGATIVE_FEEDBACK_LAUNCH_FIELDS = frozenset({
    "coset_negative_feedback_snapshot",
    "coset_negative_feedback_snapshot_manifest",
})
COSET_RENDERER_ACTIVATION_LAUNCH_FIELDS = frozenset({
    "coset_renderer_activation",
})
LEGACY_EVOLUTION_LAUNCH_MISSING_FIELDS = (
    _COSET_DSL_LAUNCH_FIELDS
    | {"evaluation_geometry"}
    | COSET_NEGATIVE_FEEDBACK_LAUNCH_FIELDS
    | COSET_RENDERER_ACTIVATION_LAUNCH_FIELDS,
    _COSET_DSL_LAUNCH_FIELDS | {
        "evaluation_geometry",
        "evaluation_final_gate",
        "evaluation_proof_runtime",
        "evaluation_search_contract",
        "evaluation_structural_features",
        "evolution_dependency_contract",
    }
    | COSET_NEGATIVE_FEEDBACK_LAUNCH_FIELDS
    | COSET_RENDERER_ACTIVATION_LAUNCH_FIELDS,
    _COSET_DSL_LAUNCH_FIELDS | {
        "evaluation_geometry",
        "evaluation_proof_runtime",
        "evaluation_search_contract",
        "evaluation_structural_features",
        "evolution_dependency_contract",
    }
    | COSET_NEGATIVE_FEEDBACK_LAUNCH_FIELDS
    | COSET_RENDERER_ACTIVATION_LAUNCH_FIELDS,
    _COSET_DSL_LAUNCH_FIELDS | {
        "evaluation_geometry",
        "evaluation_structural_features",
    }
    | COSET_NEGATIVE_FEEDBACK_LAUNCH_FIELDS
    | COSET_RENDERER_ACTIVATION_LAUNCH_FIELDS,
    _COSET_DSL_LAUNCH_FIELDS
    | COSET_NEGATIVE_FEEDBACK_LAUNCH_FIELDS
    | COSET_RENDERER_ACTIVATION_LAUNCH_FIELDS,
    COSET_NEGATIVE_FEEDBACK_LAUNCH_FIELDS
    | COSET_RENDERER_ACTIVATION_LAUNCH_FIELDS,
    COSET_RENDERER_ACTIVATION_LAUNCH_FIELDS,
)
# A committed round cannot be rebound, but the immediately preceding
# append-only dependency schema remains replayable from its immutable
# manifest/witness hashes. Older incomplete schemas stay rejected.
COMMITTED_PREVIOUS_EVOLUTION_LAUNCH_MISSING_FIELDS = (
    frozenset({"evaluation_geometry"})
    | COSET_NEGATIVE_FEEDBACK_LAUNCH_FIELDS
    | COSET_RENDERER_ACTIVATION_LAUNCH_FIELDS,
    _COSET_DSL_LAUNCH_FIELDS
    | COSET_NEGATIVE_FEEDBACK_LAUNCH_FIELDS
    | COSET_RENDERER_ACTIVATION_LAUNCH_FIELDS,
    COSET_NEGATIVE_FEEDBACK_LAUNCH_FIELDS
    | COSET_RENDERER_ACTIVATION_LAUNCH_FIELDS,
    COSET_RENDERER_ACTIVATION_LAUNCH_FIELDS,
)
EVOLUTION_INVOCATION_FIELDS = frozenset({
    "model_names",
    "reasoning_effort",
    "codex_cli",
    "max_parallel_evaluations",
    "api_base",
    "temperature_disabled",
    "codex_version",
    "codex_cwd",
    "codex_executable_mode",
})
ANSATZ_V3_CODEX_VIEW_LAUNCH_FIELD = "ansatz_v3_codex_view_manifest"
ANSATZ_V3_CODEX_VIEW_INVOCATION_FIELDS = frozenset({
    "ansatz_v3_codex_view_manifest_path",
    "ansatz_v3_codex_view_manifest_sha256",
    "ansatz_v3_codex_view_source_fingerprint_sha256",
    "ansatz_v3_codex_filesystem_boundary",
})
COSET_EVOLUTION_INVOCATION_FIELDS = frozenset({
    "qcode_evaluator_kind",
    "qcode_action_catalog_sha256",
})
COSET_RENDERER_ACTIVATION_SHA256_BINDING_FIELD = (
    "qcode_coset_renderer_activation_sha256"
)
COSET_RENDERER_ACTIVATION_FILENAME = "coset-renderer-activation.json"
COSET_RENDERER_RESOLUTION_FILENAME = "coset-renderer-resolution.json"
COSET_RENDERER_RESOLUTION_SUMMARY_FIELD = "renderer_resolution_binding"
COSET_NEGATIVE_FEEDBACK_INVOCATION_FIELDS = frozenset({
    "qcode_negative_feedback_live_archive_path",
    "qcode_negative_feedback_snapshot_path",
    "qcode_negative_feedback_snapshot_sha256",
    "qcode_negative_feedback_archive_sha256",
    "qcode_negative_feedback_manifest_path",
    "qcode_negative_feedback_manifest_sha256",
    "qcode_negative_feedback_epoch",
})
SEARCH_GEOMETRY_CONTRACT_INVOCATION_FIELD = "search_geometry_contract"
LEGACY_COSET_REPRESENTATION_ID = "css-coset-two-block-actions-v1"


class RoundTransactionError(RuntimeError):
    """A round cannot be replayed without risking duplicate evolution work."""


class LegacySliceWitnessUpgradeRequired(RoundTransactionError):
    """A prepared legacy slice has no candidate-range completion proof."""


class HumanizeRunAlreadyActiveError(RoundTransactionError):
    """Another process owns the same Humanize run identity."""


class UnresolvedAuditError(RuntimeError):
    """Stage 1 exhausted its rounds with winner-capable audits unresolved."""


@dataclass(frozen=True)
class FlowConfig:
    repo_dir: Path
    run_id: str
    max_rounds: int = 5
    iterations_per_round: int = 20
    model: str = "gpt-5.5"
    reasoning_effort: str = "xhigh"
    review_model: str = "gpt-5.5"
    review_effort: str = "xhigh"
    api_base: str | None = None
    evolution_config: Path | None = None
    evolution_seed: Path | None = None
    formal_audit_quota_contract: Path | None = None
    finite_search_domain_contract: Path | None = None
    dual_track_contract: Path | None = None
    evolution_evaluator: str = "default"
    # The search termination rule is part of the immutable Stage-1 identity.
    # Legacy stand-alone Humanize runs retain the historical gist policy;
    # five-stage scalar campaigns pass their explicit policy through here.
    target_mode: str = DEFAULT_TARGET_MODE
    # Optional, explicit identity of the search genotype.  It is deliberately
    # separate from the CSS-BB claim representation consumed by Stages 2-5.
    # Automatic campaign escalation fails closed when this identity is absent.
    search_representation_id: str | None = None
    # Policy v1 is the historical three-round diversity-collapse algorithm.
    # Policy v2 opts a fresh run into four/seven-round structural transitions.
    # Policy v3 keeps timeout/empty-exact rounds neutral and closes an exhausted
    # expansion budget with a representation-change handoff. Policy v4 also
    # closes a fully exhausted no-WIN budget when Stage-1 exact work is empty.
    # Versions are never reinterpreted so sealed v1-v3 campaigns remain
    # byte-replayable.
    search_regime_policy_version: int = 1
    stop_on_representation_change: bool = False
    milp_top: int = 3
    milp_timeout_per_logical: int = 300
    milp_total_timeout: int = 7200
    milp_early_stop: int = 0
    patience: int = 3
    min_improvement: float = 0.01
    candidate_file: Path | None = None
    codex_cli: bool = False
    # Test/development-only escape hatch for evaluators that cannot emit the
    # immutable schema-v2 checkpoint contract. Production defaults fail closed.
    allow_debug_audit_evaluator: bool = False
    # Operational scheduling cap. The outer pipeline fingerprints and persists
    # it, so Humanize omits it from logical search identity to allow safe
    # checkpoint resume with a changed resource allocation.
    max_total_workers: int | None = None

    def serializable(self) -> dict[str, Any]:
        value = asdict(self)
        value["repo_dir"] = str(self.repo_dir)
        value["candidate_file"] = str(self.candidate_file) if self.candidate_file else None
        value.pop("max_total_workers", None)
        if not self.allow_debug_audit_evaluator:
            value.pop("allow_debug_audit_evaluator", None)
        # Omit unset optional launch fields so pre-fix failed runs retain an
        # identical serialized configuration and can resume their audit.
        for name in (
            "evolution_config",
            "evolution_seed",
            "formal_audit_quota_contract",
            "finite_search_domain_contract",
            "dual_track_contract",
        ):
            path = value.get(name)
            if path is None:
                value.pop(name, None)
            else:
                value[name] = str(path)
        if self.evolution_evaluator == "default":
            value.pop("evolution_evaluator", None)
        if self.target_mode == DEFAULT_TARGET_MODE:
            value.pop("target_mode", None)
        if self.search_representation_id is None:
            value.pop("search_representation_id", None)
        if self.search_regime_policy_version == 1:
            value.pop("search_regime_policy_version", None)
        if not self.stop_on_representation_change:
            value.pop("stop_on_representation_change", None)
        return value

    def validate(self) -> None:
        # RunStore.create() applies the same strict validator.  Validate here
        # as well so no evolution, candidate, or state path can be constructed
        # from an identity that would later be rewritten.
        from .pipeline_process import validate_run_id

        validate_run_id(self.run_id)
        if self.max_rounds < 1:
            raise ValueError("max_rounds must be positive")
        if self.iterations_per_round < 1 and self.candidate_file is None:
            raise ValueError("iterations_per_round must be positive")
        if self.milp_top < 0:
            raise ValueError("milp_top must be non-negative")
        if self.evolution_evaluator not in {"default", "coset-two-block"}:
            raise ValueError(
                "evolution_evaluator must be default or coset-two-block"
            )
        validate_target_mode(self.target_mode)
        if self.evolution_evaluator == "coset-two-block" and self.milp_top != 0:
            raise ValueError(
                "coset-two-block Stage 1 requires milp_top=0; exact audits "
                "begin at Stage 2"
            )
        if not isinstance(self.allow_debug_audit_evaluator, bool):
            raise ValueError("allow_debug_audit_evaluator must be boolean")
        if self.milp_early_stop < 0:
            raise ValueError("milp_early_stop must be non-negative")
        if self.milp_top > 0:
            for name in ("milp_timeout_per_logical", "milp_total_timeout"):
                value = getattr(self, name)
                if (
                    isinstance(value, bool)
                    or not isinstance(value, int)
                    or value < 1
                ):
                    raise ValueError(f"{name} must be a positive integer")
        if (
            self.max_total_workers is not None
            and (
                isinstance(self.max_total_workers, bool)
                or not isinstance(self.max_total_workers, int)
                or self.max_total_workers < 1
            )
        ):
            raise ValueError("max_total_workers must be a positive integer")
        if self.patience < 1:
            raise ValueError("patience must be positive")

        for name in (
            "evolution_config",
            "evolution_seed",
            "formal_audit_quota_contract",
            "finite_search_domain_contract",
            "dual_track_contract",
        ):
            path = getattr(self, name)
            if path is not None and not path.is_file():
                raise ValueError(f"{name} does not exist: {path}")
        if self.search_representation_id is not None and (
            not isinstance(self.search_representation_id, str)
            or re.fullmatch(
                r"[A-Za-z0-9][A-Za-z0-9_.-]{0,127}",
                self.search_representation_id,
            )
            is None
        ):
            raise ValueError(
                "search_representation_id must be a safe explicit identifier"
            )
        if (
            isinstance(self.search_regime_policy_version, bool)
            or self.search_regime_policy_version
            not in SEARCH_REGIME_POLICY_VERSIONS
        ):
            raise ValueError(
                "search_regime_policy_version must be 1, 2, 3, or 4"
            )
        if not isinstance(self.stop_on_representation_change, bool):
            raise ValueError("stop_on_representation_change must be boolean")
        if self.search_regime_policy_version in {2, 3, 4} and (
            self.search_representation_id is None
        ):
            raise ValueError(
                "search regime policy v2/v3/v4 requires search_representation_id"
            )
        if (
            self.stop_on_representation_change
            and self.search_regime_policy_version not in {2, 3, 4}
        ):
            raise ValueError(
                "stop_on_representation_change requires policy version 2, 3, or 4"
            )
        if self.formal_audit_quota_contract is not None:
            if self.search_representation_id != (
                PUBLISHED_VOLUME_ANSATZ_V3_REPRESENTATION_ID
            ):
                raise ValueError(
                    "formal_audit_quota_contract is installed only for the "
                    "published-volume ansatz-v3 representation"
                )
            from evaluation.formal_audit_quota import load_quota_contract

            load_quota_contract(
                self.formal_audit_quota_contract,
                representation_id=self.search_representation_id,
                rounds=self.max_rounds,
                slots_per_round=self.milp_top,
            )
        if self.search_representation_id == (
            PUBLISHED_VOLUME_ANSATZ_V3_REPRESENTATION_ID
        ) and (
            self.formal_audit_quota_contract is None
            or self.finite_search_domain_contract is None
            or self.dual_track_contract is None
        ):
            raise ValueError(
                "published-volume ansatz-v3 requires all preregistration contracts"
            )
        if self.search_representation_id == (
            PUBLISHED_VOLUME_ANSATZ_V3_REPRESENTATION_ID
        ):
            expected_contracts = {
                "formal_audit_quota_contract": (
                    self.repo_dir
                    / "configs/twisted_torus_ansatz_v3.formal_audit_quota.v1.json"
                ).resolve(),
                "finite_search_domain_contract": (
                    self.repo_dir
                    / "configs/twisted_torus_ansatz_v3.finite_domain.v1.json"
                ).resolve(),
                "dual_track_contract": (
                    self.repo_dir
                    / "configs/twisted_torus_ansatz_v3.dual_track.v1.json"
                ).resolve(),
            }
            for name, expected in expected_contracts.items():
                if Path(getattr(self, name)).resolve() != expected:
                    raise ValueError(
                        f"published-volume ansatz-v3 requires installed {name}"
                    )
        if self.finite_search_domain_contract is not None:
            from evaluation.ansatz_v3_contract import load_finite_domain_contract

            load_finite_domain_contract(
                self.finite_search_domain_contract,
                representation_id=self.search_representation_id,
                rounds=self.max_rounds,
                iterations_per_round=self.iterations_per_round,
            )
        if self.dual_track_contract is not None:
            from evaluation.ansatz_v3_dual_track import load_dual_track_contract

            load_dual_track_contract(
                self.dual_track_contract,
                repo_dir=self.repo_dir,
            )


def _file_sha256(path: Path) -> str:
    digest = hashlib.sha256()
    with path.open("rb") as stream:
        for chunk in iter(lambda: stream.read(1024 * 1024), b""):
            digest.update(chunk)
    return digest.hexdigest()


def _canonical_compact_json(value: Any) -> str:
    try:
        return json.dumps(
            value,
            sort_keys=True,
            separators=(",", ":"),
            ensure_ascii=False,
            allow_nan=False,
        )
    except (TypeError, ValueError) as exc:
        raise RoundTransactionError(
            "adaptive mutation feedback must be strict JSON data"
        ) from exc


def _canonical_payload_sha256(value: Any) -> str:
    return hashlib.sha256(
        _canonical_compact_json(value).encode("utf-8")
    ).hexdigest()


def _strict_json_object_bytes(payload: bytes, label: str) -> dict[str, Any]:
    def reject_constant(value: str) -> None:
        raise ValueError(f"non-finite JSON number: {value}")

    def reject_duplicates(pairs: list[tuple[str, Any]]) -> dict[str, Any]:
        value: dict[str, Any] = {}
        for key, item in pairs:
            if key in value:
                raise ValueError(f"duplicate JSON key: {key}")
            value[key] = item
        return value

    try:
        parsed = json.loads(
            payload.decode("utf-8"),
            parse_constant=reject_constant,
            object_pairs_hook=reject_duplicates,
        )
    except (UnicodeDecodeError, json.JSONDecodeError, ValueError) as exc:
        raise RoundTransactionError(f"{label} is not strict JSON: {exc}") from exc
    if not isinstance(parsed, dict):
        raise RoundTransactionError(f"{label} must contain a JSON object")
    expected = (_canonical_compact_json(parsed) + "\n").encode("utf-8")
    if payload != expected:
        raise RoundTransactionError(f"{label} is not canonical compact JSON")
    return parsed


def _strict_jsonl_objects(payload: bytes, label: str) -> list[dict[str, Any]]:
    if payload and not payload.endswith(b"\n"):
        raise RoundTransactionError(f"{label} ends in a partial JSONL row")

    def reject_constant(value: str) -> None:
        raise ValueError(f"non-finite JSON number: {value}")

    def reject_duplicates(pairs: list[tuple[str, Any]]) -> dict[str, Any]:
        value: dict[str, Any] = {}
        for key, item in pairs:
            if key in value:
                raise ValueError(f"duplicate JSON key: {key}")
            value[key] = item
        return value

    rows: list[dict[str, Any]] = []
    for line_number, raw in enumerate(payload.splitlines(), 1):
        try:
            row = json.loads(
                raw.decode("utf-8"),
                parse_constant=reject_constant,
                object_pairs_hook=reject_duplicates,
            )
        except (UnicodeDecodeError, json.JSONDecodeError, ValueError) as exc:
            raise RoundTransactionError(
                f"{label} row {line_number} is not strict JSON: {exc}"
            ) from exc
        if not isinstance(row, dict):
            raise RoundTransactionError(
                f"{label} row {line_number} is not a JSON object"
            )
        rows.append(row)
    return rows


def _file_descriptor(path: Path, label: str) -> dict[str, Any]:
    original = Path(path)
    if original.is_symlink():
        raise RoundTransactionError(f"{label} may not be a symlink: {original}")
    try:
        resolved = original.resolve(strict=True)
    except OSError as exc:
        raise RoundTransactionError(f"{label} is missing: {original}") from exc
    if not resolved.is_file():
        raise RoundTransactionError(f"{label} is not a regular file: {resolved}")
    return {
        "path": str(resolved),
        "sha256": _file_sha256(resolved),
        "bytes": resolved.stat().st_size,
    }


def _tree_descriptor(path: Path, label: str) -> dict[str, Any]:
    original = Path(path)
    if original.is_symlink() or not original.is_dir():
        raise RoundTransactionError(f"{label} must be a regular directory: {original}")
    resolved = original.resolve(strict=True)
    hashes: dict[str, dict[str, Any]] = {}
    total_bytes = 0
    for item in sorted(resolved.rglob("*")):
        if item.is_symlink():
            raise RoundTransactionError(f"{label} contains a symlink: {item}")
        if item.is_dir():
            continue
        if not item.is_file():
            raise RoundTransactionError(f"{label} contains a non-file: {item}")
        relative = item.relative_to(resolved).as_posix()
        size = item.stat().st_size
        hashes[relative] = {"sha256": _file_sha256(item), "bytes": size}
        total_bytes += size
    encoded = json.dumps(hashes, sort_keys=True, separators=(",", ":")).encode()
    return {
        "path": str(resolved),
        "sha256": hashlib.sha256(encoded).hexdigest(),
        "bytes": total_bytes,
        "files": len(hashes),
    }


def _fsync_directory(path: Path) -> None:
    descriptor = os.open(path, os.O_RDONLY | getattr(os, "O_DIRECTORY", 0))
    try:
        os.fsync(descriptor)
    finally:
        os.close(descriptor)


def _quarantined_artifact_descriptor(
    path: Path,
    label: str,
) -> dict[str, Any]:
    if path.is_symlink():
        target = os.readlink(path).encode("utf-8", errors="surrogateescape")
        return {
            "path": str(path.absolute()),
            "kind": "symlink",
            "sha256": hashlib.sha256(target).hexdigest(),
            "bytes": len(target),
        }
    if path.is_dir():
        descriptor = _tree_descriptor(path, label)
        descriptor["kind"] = "directory"
        return descriptor
    descriptor = _file_descriptor(path, label)
    descriptor["kind"] = "file"
    return descriptor


def _read_json_object(path: Path, label: str) -> dict[str, Any]:
    if path.is_symlink() or not path.is_file():
        raise RoundTransactionError(f"{label} must be a regular file: {path}")
    try:
        value = json.loads(path.read_text())
    except (OSError, json.JSONDecodeError) as exc:
        raise RoundTransactionError(f"cannot read {label}: {path}: {exc}") from exc
    if not isinstance(value, dict):
        raise RoundTransactionError(f"{label} must contain a JSON object: {path}")
    return value


def _checkpoint_descriptor(
    output_dir: Path,
    checkpoint: Path,
    *,
    expected_iteration: int | None = None,
) -> dict[str, Any]:
    """Validate one complete checkpoint owned by this evolution output."""
    checkpoint_root = (output_dir / "checkpoints").resolve()
    original = Path(checkpoint)
    if original.is_symlink():
        raise RoundTransactionError(f"checkpoint may not be a symlink: {original}")
    try:
        resolved = original.resolve(strict=True)
    except OSError as exc:
        raise RoundTransactionError(f"checkpoint is missing: {original}") from exc
    if not resolved.is_dir() or resolved.parent != checkpoint_root:
        raise RoundTransactionError(
            f"checkpoint does not belong to this run: {resolved}"
        )
    prefix = "checkpoint_"
    if not resolved.name.startswith(prefix):
        raise RoundTransactionError(f"invalid checkpoint directory name: {resolved}")
    try:
        named_iteration = int(resolved.name[len(prefix):])
    except ValueError as exc:
        raise RoundTransactionError(
            f"invalid checkpoint iteration in path: {resolved}"
        ) from exc

    metadata_path = resolved / "metadata.json"
    best_info_path = resolved / "best_program_info.json"
    programs_dir = resolved / "programs"
    metadata = _read_json_object(metadata_path, "checkpoint metadata")
    best_info = _read_json_object(best_info_path, "checkpoint best-program info")
    best_candidates = sorted(resolved.glob("best_program.*"))
    if (
        len(best_candidates) != 1
        or best_candidates[0].suffix not in {".py", ".json"}
    ):
        raise RoundTransactionError(
            "checkpoint must contain exactly one supported language-specific "
            f"best_program file: {resolved}"
        )
    best_path = best_candidates[0]
    if best_path.is_symlink() or not best_path.is_file() or best_path.stat().st_size < 1:
        raise RoundTransactionError(
            "checkpoint best program is not a non-empty regular file: "
            f"{best_path}"
        )
    if programs_dir.is_symlink() or not programs_dir.is_dir():
        raise RoundTransactionError(
            f"checkpoint programs directory is missing: {programs_dir}"
        )

    iteration = metadata.get("last_iteration")
    if isinstance(iteration, bool) or not isinstance(iteration, int) or iteration < 0:
        raise RoundTransactionError(
            f"checkpoint last_iteration is invalid: {metadata_path}: {iteration!r}"
        )
    if iteration != named_iteration:
        raise RoundTransactionError(
            f"checkpoint path/metadata iteration mismatch: {named_iteration} != {iteration}"
        )
    if expected_iteration is not None and iteration != expected_iteration:
        raise RoundTransactionError(
            f"checkpoint iteration mismatch: expected {expected_iteration}, got {iteration}"
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
        raise RoundTransactionError(
            f"checkpoint archive/best_program_id is incomplete: {metadata_path}"
        )
    if best_info.get("id") != best_id or best_info.get("current_iteration") != iteration:
        raise RoundTransactionError(
            f"checkpoint best-program info disagrees with metadata: {best_info_path}"
        )

    referenced = set(archive)
    referenced.add(best_id)

    def add_optional_reference(value: Any, label: str) -> None:
        if value in (None, ""):
            return
        if not isinstance(value, str):
            raise RoundTransactionError(
                f"checkpoint {label} contains a non-string program id"
            )
        referenced.add(value)

    islands = metadata.get("islands", [])
    if not isinstance(islands, list) or any(
        not isinstance(island, list) for island in islands
    ):
        raise RoundTransactionError("checkpoint islands metadata is invalid")
    for island in islands:
        for program_id in island:
            add_optional_reference(program_id, "islands")
    island_best = metadata.get("island_best_programs", [])
    if not isinstance(island_best, list):
        raise RoundTransactionError(
            "checkpoint island_best_programs metadata is invalid"
        )
    for program_id in island_best:
        add_optional_reference(program_id, "island_best_programs")
    feature_maps = metadata.get("island_feature_maps", [])
    if not isinstance(feature_maps, list) or any(
        not isinstance(feature_map, dict) for feature_map in feature_maps
    ):
        raise RoundTransactionError(
            "checkpoint island_feature_maps metadata is invalid"
        )
    for feature_map in feature_maps:
        for program_id in feature_map.values():
            add_optional_reference(program_id, "island_feature_maps")

    program_files = sorted(programs_dir.glob("*.json"))
    if not program_files:
        raise RoundTransactionError(f"checkpoint contains no programs: {programs_dir}")
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
            raise RoundTransactionError(
                f"checkpoint program id/path mismatch: {program_path}"
            )
        code = program.get("code")
        metrics = program.get("metrics")
        if not isinstance(code, str) or not code:
            raise RoundTransactionError(
                f"checkpoint program has no non-empty code: {program_path}"
            )
        if not isinstance(metrics, dict):
            raise RoundTransactionError(
                f"checkpoint program metrics is not an object: {program_path}"
            )
        program_ids.add(program_id)
        if program_id == best_id:
            best_program_code = code
        file_hashes[f"programs/{program_path.name}"] = _file_sha256(program_path)
    missing = sorted(referenced - program_ids)
    if missing:
        raise RoundTransactionError(
            "checkpoint is missing referenced programs: " + ", ".join(missing)
        )
    if best_program_code is None or best_path.read_text() != best_program_code:
        raise RoundTransactionError(
            f"checkpoint {best_path.name} does not match the stored best program code"
        )
    checkpoint_hash = hashlib.sha256(
        json.dumps(file_hashes, sort_keys=True, separators=(",", ":")).encode()
    ).hexdigest()
    return {
        "path": str(resolved),
        "last_iteration": iteration,
        "sha256": checkpoint_hash,
        "programs": len(program_files),
    }


def _checkpoint_program_set_sha256(
    checkpoint: dict[str, Any],
) -> str:
    """Recompute the frozen migration source identity without executing code."""

    programs_dir = Path(checkpoint["path"]) / "programs"
    if programs_dir.is_symlink() or not programs_dir.is_dir():
        raise RoundTransactionError(
            "checkpoint migration source programs directory is missing"
        )
    program_files = sorted(programs_dir.glob("*.json"))
    if len(program_files) != checkpoint.get("programs"):
        raise RoundTransactionError(
            "checkpoint migration source program count changed"
        )
    rows: list[dict[str, str]] = []
    for path in program_files:
        program = _read_json_object(path, "checkpoint migration source program")
        program_id = program.get("id")
        code = program.get("code")
        if program_id != path.stem or not isinstance(code, str):
            raise RoundTransactionError(
                "checkpoint migration source program identity is invalid"
            )
        rows.append({
            "id": program_id,
            "code_sha256": hashlib.sha256(
                code.encode("utf-8")
            ).hexdigest(),
        })
    return hashlib.sha256(
        json.dumps(
            rows,
            sort_keys=True,
            separators=(",", ":"),
            allow_nan=False,
        ).encode("utf-8")
    ).hexdigest()


def _historical_coset_policy_v1_identity(
    root_code: Any,
    *,
    expected_catalog_sha256: Any,
) -> dict[str, Any]:
    """Validate a sealed typed root as data, independent of live renderers."""

    if (
        not isinstance(root_code, str)
        or not isinstance(expected_catalog_sha256, str)
        or re.fullmatch(r"[0-9a-f]{64}", expected_catalog_sha256) is None
    ):
        raise RoundTransactionError(
            "checkpoint DSL migration root policy identity is invalid"
        )
    try:
        root_document = _strict_json_object_bytes(
            root_code.encode("utf-8"),
            "checkpoint DSL migration root policy",
        )
    except (UnicodeError, RoundTransactionError) as exc:
        raise RoundTransactionError(
            "checkpoint DSL migration root policy is invalid"
        ) from exc
    identity = (
        root_document.get("schema_version"),
        root_document.get("kind"),
        root_document.get("representation_id"),
    )
    supported = {
        (
            1,
            "qcode-coset-policy-dsl-v1",
            "css-coset-two-block-actions-v1",
        ),
        (
            2,
            "qcode-coset-policy-dsl-v2",
            "css-coset-two-block-actions-v2",
        ),
        (
            3,
            "qcode-coset-policy-dsl-v3",
            "css-coset-two-block-actions-v3",
        ),
    }
    if (
        identity not in supported
        or root_document.get("action_catalog_sha256")
        != expected_catalog_sha256
    ):
        raise RoundTransactionError(
            "checkpoint DSL migration root policy contract is invalid"
        )
    canonical_policy = _canonical_compact_json(root_document)
    return {
        "document": root_document,
        "policy_sha256": hashlib.sha256(
            canonical_policy.encode("utf-8")
        ).hexdigest(),
        "code_sha256": hashlib.sha256(
            root_code.encode("utf-8")
        ).hexdigest(),
    }


def _assert_checkpoint_frontier(
    output_dir: Path,
    base_iteration: int,
    *,
    allowed_iterations: frozenset[int] = frozenset(),
) -> None:
    """Reject checkpoint directories not bound to the durable slice frontier."""
    checkpoint_root = output_dir / "checkpoints"
    if checkpoint_root.is_symlink():
        raise RoundTransactionError(
            f"checkpoint root may not be a symlink: {checkpoint_root}"
        )
    if not checkpoint_root.exists():
        return
    if not checkpoint_root.is_dir():
        raise RoundTransactionError(
            f"checkpoint root is not a directory: {checkpoint_root}"
        )
    for checkpoint in checkpoint_root.iterdir():
        if not checkpoint.name.startswith("checkpoint_"):
            continue
        suffix = checkpoint.name[len("checkpoint_"):]
        try:
            iteration = int(suffix)
        except ValueError as exc:
            raise RoundTransactionError(
                f"checkpoint frontier contains an invalid entry: {checkpoint}"
            ) from exc
        if checkpoint.name != f"checkpoint_{iteration}":
            raise RoundTransactionError(
                f"checkpoint frontier contains a non-canonical entry: {checkpoint}"
            )
        if iteration <= base_iteration:
            continue
        if checkpoint.is_symlink():
            raise RoundTransactionError(
                f"checkpoint frontier contains a symlink: {checkpoint}"
            )
        if iteration not in allowed_iterations:
            raise RoundTransactionError(
                "checkpoint frontier contains an unbound checkpoint newer than "
                f"the durable base: {checkpoint}"
            )


def _completion_marker_path(round_dir: Path) -> Path:
    return round_dir / "openevolve-completed.json"


def _slice_witness_path(round_dir: Path) -> Path:
    return round_dir / "openevolve-slice-witness.json"


def _round_lifecycle_lock_path(round_dir: Path) -> Path:
    return round_dir / "openevolve-lifecycle.lock"


@dataclass(frozen=True)
class _HumanizeRunLease:
    fd: int
    path: Path
    owner_pid: int
    token: object


_HUMANIZE_RUN_LEASE_REGISTRY_LOCK = threading.RLock()
_ACTIVE_HUMANIZE_RUN_LEASES: dict[object, _HumanizeRunLease] = {}


def _validate_humanize_run_lease_inode(
    root_fd: int,
    root_path: Path,
    lock_fd: int,
    lock_name: str,
) -> None:
    """Bind an acquired descriptor to one regular file in the fixed run root."""
    try:
        descriptor_root = os.fstat(root_fd)
        path_root = os.stat(root_path, follow_symlinks=False)
        descriptor_lock = os.fstat(lock_fd)
        path_lock = os.stat(
            lock_name,
            dir_fd=root_fd,
            follow_symlinks=False,
        )
    except OSError as exc:
        raise RoundTransactionError(
            f"cannot validate Humanize run lease: {root_path / lock_name}: {exc}"
        ) from exc
    if (
        not stat.S_ISDIR(descriptor_root.st_mode)
        or not stat.S_ISDIR(path_root.st_mode)
        or (descriptor_root.st_dev, descriptor_root.st_ino)
        != (path_root.st_dev, path_root.st_ino)
    ):
        raise RoundTransactionError(
            f"Humanize run root was replaced or is unsafe: {root_path}"
        )
    if (
        not stat.S_ISREG(descriptor_lock.st_mode)
        or not stat.S_ISREG(path_lock.st_mode)
    ):
        raise RoundTransactionError(
            "Humanize run lease must be a regular file: "
            f"{root_path / lock_name}"
        )
    if (descriptor_lock.st_dev, descriptor_lock.st_ino) != (
        path_lock.st_dev,
        path_lock.st_ino,
    ):
        raise RoundTransactionError(
            f"Humanize run lease path was replaced: {root_path / lock_name}"
        )


def _validate_inherited_humanize_run_lease(
    store: RunStore,
    lease: _HumanizeRunLease,
) -> None:
    """Accept only the exact active in-process lease for this run."""
    if not isinstance(lease, _HumanizeRunLease):
        raise RoundTransactionError("inherited Humanize run lease has invalid type")
    expected_path = store.lock_path.absolute()
    if lease.path != expected_path or lease.owner_pid != os.getpid():
        raise RoundTransactionError(
            "inherited Humanize run lease belongs to a different run or process"
        )
    with _HUMANIZE_RUN_LEASE_REGISTRY_LOCK:
        if _ACTIVE_HUMANIZE_RUN_LEASES.get(lease.token) is not lease:
            raise RoundTransactionError(
                "inherited Humanize run lease is not currently active"
            )

    nofollow = getattr(os, "O_NOFOLLOW", None)
    if nofollow is None:
        raise RoundTransactionError("O_NOFOLLOW is required for Humanize run leases")
    root_path = store.root.absolute()
    root_flags = (
        os.O_RDONLY
        | getattr(os, "O_DIRECTORY", 0)
        | getattr(os, "O_CLOEXEC", 0)
        | nofollow
    )
    try:
        root_fd = os.open(root_path, root_flags)
    except OSError as exc:
        raise RoundTransactionError(
            f"cannot validate inherited Humanize run root: {root_path}: {exc}"
        ) from exc
    try:
        _validate_humanize_run_lease_inode(
            root_fd,
            root_path,
            lease.fd,
            expected_path.name,
        )
    finally:
        os.close(root_fd)


@contextmanager
def _acquire_humanize_run_lease(
    store: RunStore,
) -> Iterator[_HumanizeRunLease]:
    """Exclusively own one direct Humanize run for its complete execution."""
    root_path = store.root.absolute()
    lock_path = store.lock_path.absolute()
    if lock_path.parent != root_path or lock_path.name != "run.lock":
        raise RoundTransactionError(
            f"Humanize run lease path is outside its fixed run root: {lock_path}"
        )
    nofollow = getattr(os, "O_NOFOLLOW", None)
    if nofollow is None:
        raise RoundTransactionError("O_NOFOLLOW is required for Humanize run leases")

    root_flags = (
        os.O_RDONLY
        | getattr(os, "O_DIRECTORY", 0)
        | getattr(os, "O_CLOEXEC", 0)
        | nofollow
    )
    try:
        root_fd = os.open(root_path, root_flags)
    except OSError as exc:
        raise RoundTransactionError(
            f"cannot open Humanize run root for its lease: {root_path}: {exc}"
        ) from exc

    lock_fd: int | None = None
    locked = False
    try:
        lock_flags = (
            os.O_RDWR
            | os.O_CREAT
            | getattr(os, "O_CLOEXEC", 0)
            | getattr(os, "O_NONBLOCK", 0)
            | nofollow
        )
        try:
            lock_fd = os.open(
                lock_path.name,
                lock_flags,
                0o600,
                dir_fd=root_fd,
            )
        except OSError as exc:
            raise RoundTransactionError(
                f"cannot open Humanize run lease: {lock_path}: {exc}"
            ) from exc
        _validate_humanize_run_lease_inode(
            root_fd,
            root_path,
            lock_fd,
            lock_path.name,
        )
        try:
            fcntl.flock(lock_fd, fcntl.LOCK_EX | fcntl.LOCK_NB)
        except BlockingIOError as exc:
            raise HumanizeRunAlreadyActiveError(
                f"Humanize run {store.run_id!r} is already active"
            ) from exc
        locked = True
        _validate_humanize_run_lease_inode(
            root_fd,
            root_path,
            lock_fd,
            lock_path.name,
        )
        lease = _HumanizeRunLease(
            fd=lock_fd,
            path=lock_path,
            owner_pid=os.getpid(),
            token=object(),
        )
        with _HUMANIZE_RUN_LEASE_REGISTRY_LOCK:
            _ACTIVE_HUMANIZE_RUN_LEASES[lease.token] = lease
        try:
            yield lease
        finally:
            with _HUMANIZE_RUN_LEASE_REGISTRY_LOCK:
                if _ACTIVE_HUMANIZE_RUN_LEASES.get(lease.token) is lease:
                    del _ACTIVE_HUMANIZE_RUN_LEASES[lease.token]
    finally:
        if lock_fd is not None:
            try:
                if locked:
                    fcntl.flock(lock_fd, fcntl.LOCK_UN)
            finally:
                os.close(lock_fd)
        os.close(root_fd)


@dataclass(frozen=True)
class _RoundLifecycleLease:
    fd: int
    path: Path


def _validate_round_lifecycle_inode(fd: int, path: Path) -> None:
    try:
        descriptor_stat = os.fstat(fd)
        path_stat = os.stat(path, follow_symlinks=False)
    except OSError as exc:
        raise RoundTransactionError(
            f"cannot validate OpenEvolve lifecycle lease: {path}: {exc}"
        ) from exc
    if not stat.S_ISREG(descriptor_stat.st_mode) or not stat.S_ISREG(
        path_stat.st_mode
    ):
        raise RoundTransactionError(
            f"OpenEvolve lifecycle lease must be a regular file: {path}"
        )
    if (descriptor_stat.st_dev, descriptor_stat.st_ino) != (
        path_stat.st_dev,
        path_stat.st_ino,
    ):
        raise RoundTransactionError(
            f"OpenEvolve lifecycle lease path was replaced: {path}"
        )


@contextmanager
def _acquire_round_lifecycle_lease(
    round_dir: Path,
) -> Iterator[_RoundLifecycleLease]:
    """Hold one fixed round lease across recovery and the whole child tree."""
    original_round = round_dir.absolute()
    try:
        resolved_round = round_dir.resolve(strict=True)
    except OSError as exc:
        raise RoundTransactionError(
            f"round directory is missing for lifecycle lease: {round_dir}"
        ) from exc
    if resolved_round != original_round or not resolved_round.is_dir():
        raise RoundTransactionError(
            f"round directory must be canonical and may not use symlinks: {round_dir}"
        )
    path = _round_lifecycle_lock_path(original_round).absolute()
    if path.is_symlink():
        raise RoundTransactionError(
            f"OpenEvolve lifecycle lease may not be a symlink: {path}"
        )
    flags = os.O_RDWR | os.O_CREAT | getattr(os, "O_CLOEXEC", 0)
    nofollow = getattr(os, "O_NOFOLLOW", None)
    if nofollow is None:
        raise RoundTransactionError("O_NOFOLLOW is required for lifecycle leases")
    flags |= nofollow
    try:
        fd = os.open(path, flags, 0o600)
    except OSError as exc:
        raise RoundTransactionError(
            f"cannot open OpenEvolve lifecycle lease: {path}: {exc}"
        ) from exc
    try:
        _validate_round_lifecycle_inode(fd, path)
        fcntl.flock(fd, fcntl.LOCK_EX)
        _validate_round_lifecycle_inode(fd, path)
        yield _RoundLifecycleLease(fd=fd, path=path)
    finally:
        try:
            fcntl.flock(fd, fcntl.LOCK_UN)
        finally:
            os.close(fd)


def _process_group_exists(process_group: int) -> bool:
    try:
        os.killpg(process_group, 0)
    except ProcessLookupError:
        return False
    except PermissionError:
        return True
    return True


def _terminate_process_group(
    process: subprocess.Popen,
    *,
    grace_seconds: float = 2.0,
) -> None:
    """Terminate the launcher and every process left in its private group."""
    process_group = process.pid
    try:
        os.killpg(process_group, signal.SIGTERM)
    except ProcessLookupError:
        pass
    try:
        process.wait(timeout=grace_seconds)
    except subprocess.TimeoutExpired:
        try:
            os.killpg(process_group, signal.SIGKILL)
        except ProcessLookupError:
            pass
        process.wait()

    deadline = time.monotonic() + grace_seconds
    while _process_group_exists(process_group) and time.monotonic() < deadline:
        time.sleep(0.05)
    if _process_group_exists(process_group):
        try:
            os.killpg(process_group, signal.SIGKILL)
        except ProcessLookupError:
            pass


def _wait_for_managed_process(
    process: subprocess.Popen,
    command: list[str],
) -> None:
    try:
        return_code = process.wait()
        _terminate_process_group(process)
    except BaseException:
        # A first SIGTERM can arrive during normal post-wait cleanup.  The
        # pipeline handler masks subsequent SIGTERM before raising, so retry
        # the cleanup here to avoid abandoning surviving group members.
        _terminate_process_group(process)
        raise
    if return_code:
        raise subprocess.CalledProcessError(return_code, command)


def _flow_evaluator_kind(config: FlowConfig) -> str:
    return config.evolution_evaluator


def _expected_evolution_config(config: FlowConfig) -> Path:
    coset_config = "coset_config_v3.yaml"
    if config.search_representation_id == COSET_REPRESENTATION_ID:
        coset_config = "coset_config_v2.yaml"
    return Path(os.path.abspath(
        config.evolution_config
        or config.repo_dir / "evolve" / (
            coset_config
            if _flow_evaluator_kind(config) == "coset-two-block"
            else "config.yaml"
        )
    ))


def _configured_coset_representation_id(config: FlowConfig) -> str:
    """Bind the FlowConfig field to the exact selected YAML marker."""

    if _flow_evaluator_kind(config) != "coset-two-block":
        raise RoundTransactionError("non-coset flow has no coset representation")
    path = _expected_evolution_config(config)
    try:
        value = yaml.safe_load(path.read_text())
    except (OSError, UnicodeError, yaml.YAMLError) as exc:
        raise RoundTransactionError(
            "cannot inspect coset representation binding"
        ) from exc
    marker = (
        value.get(COSET_SEARCH_PORTFOLIO_CONFIG_KEY)
        if isinstance(value, dict)
        else None
    )
    representation_id = (
        marker.get("representation_id")
        if isinstance(marker, dict)
        else None
    )
    if not isinstance(representation_id, str):
        raise RoundTransactionError(
            "coset evolution config has no representation marker"
        )
    if (
        config.search_representation_id is not None
        and config.search_representation_id != representation_id
    ):
        raise RoundTransactionError(
            "FlowConfig search_representation_id disagrees with the coset "
            "evolution config"
        )
    return representation_id


def _expected_evolution_seed(config: FlowConfig) -> Path:
    coset_seed = "coset_seed_solution_v3.py"
    representation_id = config.search_representation_id
    if _flow_evaluator_kind(config) == "coset-two-block":
        representation_id = _configured_coset_representation_id(config)
    if representation_id == COSET_REPRESENTATION_ID:
        coset_seed = "coset_seed_solution_v2.py"
    return Path(os.path.abspath(
        config.evolution_seed
        or config.repo_dir / "evolve" / (
            coset_seed
            if _flow_evaluator_kind(config) == "coset-two-block"
            else "seed_solution.py"
        )
    ))


def _expected_evolution_launcher(config: FlowConfig) -> Path:
    return Path(os.path.abspath(config.repo_dir / "evolve" / "run_evolution.py"))


def _expected_evolution_evaluator(config: FlowConfig) -> Path:
    return Path(
        os.path.abspath(config.repo_dir / "evolve" / (
            "coset_openevolve_evaluator.py"
            if _flow_evaluator_kind(config) == "coset-two-block"
            else "openevolve_evaluator.py"
        ))
    )


def _evolution_dependencies(config: FlowConfig) -> dict[str, str]:
    dependencies = dict(LOCAL_EVOLUTION_DEPENDENCIES)
    if config.search_representation_id == (
        PUBLISHED_VOLUME_ANSATZ_V3_REPRESENTATION_ID
    ):
        dependencies.update(ANSATZ_V3_EVALUATOR_DEPENDENCIES)
    if _flow_evaluator_kind(config) == "coset-two-block":
        dependencies.update(COSET_EVALUATOR_DEPENDENCIES)
    return dependencies


def _coset_action_catalog_dependency_key(config: FlowConfig) -> str:
    """Select the immutable catalog named by the campaign representation.

    Both catalogs remain in the frozen dependency manifest so historical v1
    transactions can still be replayed.  A new v2 launch must bind the v2
    bytes explicitly; using the legacy default here would prepare a valid-
    looking Humanize transaction that the child launcher immediately rejects.
    """

    representation_id = _configured_coset_representation_id(config)
    if representation_id in {
        COSET_REPRESENTATION_ID,
        COSET_REPRESENTATION_ID_V3,
    }:
        return "coset_action_catalog_v2"
    if representation_id == LEGACY_COSET_REPRESENTATION_ID:
        return "coset_action_catalog"
    raise RoundTransactionError(
        "coset evaluator has no catalog for search representation "
        f"{representation_id!r}"
    )


def _expected_evolution_backend(config: FlowConfig) -> Path:
    return Path(os.path.abspath(config.repo_dir / "evolve" / "codex_cli_llm.py"))


def _configured_evolution_workers(config_path: Path) -> int:
    try:
        lines = config_path.read_text().splitlines()
    except OSError as exc:
        raise RoundTransactionError(
            f"cannot read evolution config worker budget: {config_path}: {exc}"
        ) from exc
    evaluator_indent: int | None = None
    configured_values: list[int] = []
    for raw_line in lines:
        content = raw_line.split("#", 1)[0].rstrip()
        if not content:
            continue
        indent = len(content) - len(content.lstrip())
        stripped = content.strip()
        if evaluator_indent is None:
            if stripped == "evaluator:":
                evaluator_indent = indent
            continue
        if indent <= evaluator_indent:
            evaluator_indent = None
            if stripped == "evaluator:":
                evaluator_indent = indent
            continue
        matched = re.fullmatch(
            r"parallel_evaluations:\s*(?:[\"']([0-9]+)[\"']|([0-9]+))",
            stripped,
        )
        if matched:
            configured_values.append(
                int(matched.group(1) or matched.group(2))
            )
    configured = (
        configured_values[0] if len(configured_values) == 1 else None
    )
    if (
        isinstance(configured, bool)
        or not isinstance(configured, int)
        or configured < 1
    ):
        raise RoundTransactionError(
            "evolution config evaluator.parallel_evaluations must be "
            "a positive integer"
        )
    return configured


def _resolve_native_codex_path(requested_bin: str) -> Path:
    launcher = shutil.which(requested_bin)
    if launcher is None:
        raise RoundTransactionError(
            f"Codex CLI executable is unavailable: {requested_bin}"
        )
    launcher_path = Path(launcher).resolve(strict=True)
    with launcher_path.open("rb") as stream:
        magic = stream.read(4)
    if magic in (b"\x7fELF", b"MZ\x90\x00"):
        return launcher_path
    if launcher_path.name != "codex.js" or launcher_path.parent.name != "bin":
        raise RoundTransactionError(
            "managed QCODE_CODEX_BIN must be the official codex.js launcher "
            "or a native Codex executable"
        )
    target = {
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
    }.get(
        (
            platform_module.system().lower(),
            platform_module.machine().lower(),
        )
    )
    if target is None:
        raise RoundTransactionError(
            "unsupported managed Codex platform: "
            f"{platform_module.system().lower()}/"
            f"{platform_module.machine().lower()}"
        )
    package_name, target_triple, executable_name = target
    package_root = launcher_path.parent.parent
    for candidate in (
        package_root
        / "node_modules"
        / Path(*package_name.split("/"))
        / "vendor"
        / target_triple
        / "bin"
        / executable_name,
        package_root / "vendor" / target_triple / "bin" / executable_name,
    ):
        try:
            resolved = candidate.resolve(strict=True)
        except OSError:
            continue
        if resolved.is_file():
            return resolved
    raise RoundTransactionError(
        "cannot resolve the official Codex launcher to its native executable"
    )


def _codex_version(executable: Path) -> str:
    try:
        completed = subprocess.run(
            [str(executable), "--version"],
            check=True,
            capture_output=True,
            text=True,
            timeout=10,
        )
    except (OSError, subprocess.SubprocessError) as exc:
        raise RoundTransactionError(
            "cannot identify the Codex CLI version"
        ) from exc
    version = completed.stdout.strip()
    if not version or len(version) > 500:
        raise RoundTransactionError(
            "Codex CLI returned an invalid version identity"
        )
    return version


def _fresh_codex_binding(
    config: FlowConfig,
    *,
    round_dir: Path | None = None,
) -> tuple[dict[str, Any], str, str]:
    executable = _resolve_native_codex_path(
        os.environ.get("QCODE_CODEX_BIN", "codex")
    )
    if not executable.is_file() or not os.access(executable, os.X_OK):
        raise RoundTransactionError(
            f"Codex CLI native binary is not executable: {executable}"
        )
    identity = _file_descriptor(
        executable, "Codex CLI native executable"
    )
    identity["mode"] = stat.S_IMODE(executable.stat().st_mode)
    if config.search_representation_id == (
        PUBLISHED_VOLUME_ANSATZ_V3_REPRESENTATION_ID
    ):
        if round_dir is None:
            raise RoundTransactionError(
                "ansatz-v3 Codex binding requires a round-local sanitized view"
            )
        from evolve.ansatz_v3_codex_view import (
            AnsatzV3CodexViewError,
            VIEW_DIRECTORY_NAME,
            materialize_sanitized_codex_view,
        )

        try:
            view = materialize_sanitized_codex_view(
                config.repo_dir,
                Path(os.path.abspath(round_dir / VIEW_DIRECTORY_NAME)),
            )
        except (OSError, AnsatzV3CodexViewError) as exc:
            raise RoundTransactionError(
                f"cannot prepare ansatz-v3 sanitized Codex view: {exc}"
            ) from exc
        cwd = str(view["view_path"])
    else:
        cwd = str(config.repo_dir.resolve(strict=True))
    return identity, _codex_version(executable), cwd


def _resolved_api_base(config: FlowConfig) -> str:
    if config.api_base:
        return config.api_base
    for name in ("OPENAI_API_BASE", "LITELLM_API_BASE"):
        value = os.environ.get(name)
        if value:
            return value
    return "http://localhost:4000/v1"


def _negative_feedback_epoch_number(round_dir: Path) -> int:
    match = re.fullmatch(r"round-([0-9]+)", round_dir.name)
    if match is None or int(match.group(1)) < 1:
        raise RoundTransactionError(
            "managed negative-feedback snapshot has an invalid round directory"
        )
    return int(match.group(1))


def _negative_feedback_epoch_binding(
    config: FlowConfig,
    round_dir: Path,
) -> tuple[dict[str, Any], dict[str, Any], dict[str, Any]]:
    """Materialize and describe the immutable read view for one round."""

    from evolve.coset_negative_archive import (
        NegativeArchiveError,
        load_feedback_snapshot_manifest,
        materialize_feedback_snapshot,
        resolve_archive_path,
    )

    number = _negative_feedback_epoch_number(round_dir)
    absolute_round = Path(os.path.abspath(round_dir))
    candidate_log = Path(os.path.abspath(
        config.repo_dir
        / "results"
        / "evolution"
        / f"humanize_{config.run_id}"
        / "all_codes.jsonl"
    ))
    try:
        live = resolve_archive_path(candidate_log)
    except NegativeArchiveError as exc:
        raise RoundTransactionError(str(exc)) from exc
    if live is None:
        raise RoundTransactionError(
            "managed coset evolution has no live negative archive"
        )
    live = Path(os.path.abspath(live))
    snapshot = absolute_round / "negative-feedback-snapshot.json"
    manifest_path = absolute_round / "negative-feedback-snapshot-manifest.json"
    parent_snapshot_sha256: str | None = None
    if number > 1:
        parent_manifest_path = (
            absolute_round.parent
            / f"round-{number - 1:03d}"
            / "negative-feedback-snapshot-manifest.json"
        )
        if parent_manifest_path.is_file() and not parent_manifest_path.is_symlink():
            try:
                parent = load_feedback_snapshot_manifest(
                    parent_manifest_path,
                    expected_live_archive_path=live,
                    expected_run_id=config.run_id,
                    expected_round_number=number - 1,
                )
            except (OSError, NegativeArchiveError) as exc:
                raise RoundTransactionError(
                    f"previous negative-feedback epoch is invalid: {exc}"
                ) from exc
            parent_snapshot_sha256 = str(parent["snapshot_sha256"])
    try:
        manifest = materialize_feedback_snapshot(
            live,
            snapshot,
            manifest_path,
            run_id=config.run_id,
            round_number=number,
            feedback_epoch=number,
            parent_snapshot_sha256=parent_snapshot_sha256,
        )
    except (OSError, NegativeArchiveError) as exc:
        raise RoundTransactionError(
            f"cannot materialize negative-feedback epoch: {exc}"
        ) from exc
    return (
        manifest,
        _file_descriptor(snapshot, "negative-feedback snapshot"),
        _file_descriptor(manifest_path, "negative-feedback snapshot manifest"),
    )


def _negative_feedback_invocation(
    config: FlowConfig,
    launch_binding: Mapping[str, Any],
) -> dict[str, Any]:
    """Replay dynamic snapshot descriptors into the managed invocation."""

    from evolve.coset_negative_archive import (
        NegativeArchiveError,
        load_feedback_snapshot_manifest,
    )

    snapshot = launch_binding.get("coset_negative_feedback_snapshot")
    manifest_descriptor = launch_binding.get(
        "coset_negative_feedback_snapshot_manifest"
    )
    if not isinstance(snapshot, Mapping) or not isinstance(
        manifest_descriptor, Mapping
    ):
        raise RoundTransactionError(
            "coset negative-feedback launch binding is incomplete"
        )
    observed_snapshot = _file_descriptor(
        Path(str(snapshot.get("path", ""))), "negative-feedback snapshot"
    )
    observed_manifest = _file_descriptor(
        Path(str(manifest_descriptor.get("path", ""))),
        "negative-feedback snapshot manifest",
    )
    if observed_snapshot != dict(snapshot) or observed_manifest != dict(
        manifest_descriptor
    ):
        raise RoundTransactionError(
            "negative-feedback snapshot changed after transaction prepare"
        )
    try:
        manifest = load_feedback_snapshot_manifest(
            Path(observed_manifest["path"]),
            expected_snapshot_path=Path(observed_snapshot["path"]),
            expected_run_id=config.run_id,
        )
    except (OSError, NegativeArchiveError) as exc:
        raise RoundTransactionError(
            f"negative-feedback snapshot replay failed: {exc}"
        ) from exc
    return {
        "qcode_negative_feedback_live_archive_path": manifest[
            "live_archive_path"
        ],
        "qcode_negative_feedback_snapshot_path": manifest["snapshot_path"],
        "qcode_negative_feedback_snapshot_sha256": manifest[
            "snapshot_sha256"
        ],
        "qcode_negative_feedback_archive_sha256": manifest["archive_sha256"],
        "qcode_negative_feedback_manifest_path": observed_manifest["path"],
        "qcode_negative_feedback_manifest_sha256": observed_manifest["sha256"],
        "qcode_negative_feedback_epoch": manifest["feedback_epoch"],
    }


def _fresh_invocation_binding(
    config: FlowConfig,
    *,
    codex_identity: dict[str, Any] | None,
    codex_version: str | None,
    codex_cwd: str | None,
    launch_binding: Mapping[str, Any] | None = None,
) -> dict[str, Any]:
    configured_workers = _configured_evolution_workers(
        _expected_evolution_config(config)
    )
    worker_cap = config.max_total_workers
    effective_workers = (
        configured_workers
        if worker_cap is None
        else min(configured_workers, worker_cap)
    )
    invocation = {
        "model_names": [config.model],
        "reasoning_effort": config.reasoning_effort,
        "codex_cli": config.codex_cli,
        "max_parallel_evaluations": effective_workers,
        "api_base": _resolved_api_base(config),
        "temperature_disabled": True,
        "codex_version": codex_version,
        "codex_cwd": codex_cwd,
        "codex_executable_mode": (
            None if codex_identity is None else codex_identity["mode"]
        ),
    }
    geometry_contract = _managed_search_geometry_contract(
        config,
        _expected_evolution_config(config),
    )
    if geometry_contract is not None:
        invocation[SEARCH_GEOMETRY_CONTRACT_INVOCATION_FIELD] = (
            geometry_contract
        )
    if (
        config.codex_cli
        and config.search_representation_id
        == PUBLISHED_VOLUME_ANSATZ_V3_REPRESENTATION_ID
    ):
        from evolve.ansatz_v3_codex_view import (
            AnsatzV3CodexViewError,
            validate_sanitized_codex_view,
        )

        if codex_cwd is None:
            raise RoundTransactionError(
                "ansatz-v3 Codex invocation lacks its sanitized view"
            )
        try:
            view = validate_sanitized_codex_view(
                config.repo_dir,
                Path(codex_cwd),
            )
        except (OSError, AnsatzV3CodexViewError) as exc:
            raise RoundTransactionError(
                f"ansatz-v3 sanitized Codex view failed replay: {exc}"
            ) from exc
        invocation.update({
            "ansatz_v3_codex_view_manifest_path": view["manifest_path"],
            "ansatz_v3_codex_view_manifest_sha256": view[
                "manifest_file_sha256"
            ],
            "ansatz_v3_codex_view_source_fingerprint_sha256": view[
                "source_fingerprint_sha256"
            ],
            "ansatz_v3_codex_filesystem_boundary": view[
                "filesystem_boundary"
            ],
        })
    if _flow_evaluator_kind(config) == "coset-two-block":
        from evaluation.coset_action_catalog import (
            LEGACY_CATALOG_ID,
            V2_CATALOG_ID,
            action_catalog_sha256,
        )

        catalog_id = (
            V2_CATALOG_ID
            if _coset_action_catalog_dependency_key(config)
            == "coset_action_catalog_v2"
            else LEGACY_CATALOG_ID
        )

        invocation.update({
            "qcode_evaluator_kind": "coset-two-block",
            "qcode_action_catalog_sha256": action_catalog_sha256(catalog_id),
        })
        if launch_binding is not None and COSET_NEGATIVE_FEEDBACK_LAUNCH_FIELDS.issubset(
            launch_binding
        ):
            invocation.update(
                _negative_feedback_invocation(config, launch_binding)
            )
        if _configured_coset_representation_id(config) == (
            COSET_REPRESENTATION_ID_V3
        ):
            activation_descriptor = (
                None
                if launch_binding is None
                else launch_binding.get("coset_renderer_activation")
            )
            if activation_descriptor is None:
                from evolve.coset_search_contract import (
                    coset_renderer_activation_document,
                    default_coset_renderer_activation,
                )

                activation = coset_renderer_activation_document(
                    default_coset_renderer_activation()
                )
            elif not isinstance(activation_descriptor, Mapping):
                raise RoundTransactionError(
                    "coset renderer activation launch binding is malformed"
                )
            else:
                activation = _validated_coset_renderer_activation_file(
                    Path(str(activation_descriptor.get("path", "")))
                )
                if _file_descriptor(
                    Path(str(activation_descriptor.get("path", ""))),
                    "coset renderer activation",
                ) != activation_descriptor:
                    raise RoundTransactionError(
                        "coset renderer activation launch binding changed"
                    )
            invocation[
                COSET_RENDERER_ACTIVATION_SHA256_BINDING_FIELD
            ] = activation["activation_sha256"]
    return invocation


def _managed_search_geometry_contract(
    config: FlowConfig,
    config_path: Path,
) -> str | None:
    """Bind a representation, portfolio schema, and child geometry contract.

    The legacy invocation shape deliberately remains unchanged.  Geometry-
    aware schema-v3 launches are the only ones that carry an extra field, so
    their completion witness records the exact evaluator contract while old
    rectangular transactions remain byte-replayable.
    """

    try:
        portfolio = _search_portfolio_contract_from_config(config_path)
    except RoundTransactionError as current_error:
        # Schema-v4 recovery uses the historical portfolio marker
        # ``schema_version: 1``.  It has no geometry-aware invocation field
        # and must retain its exact frozen semantics.
        try:
            legacy_portfolio = (
                _legacy_v4_search_portfolio_enabled_from_config(config_path)
            )
        except RoundTransactionError:
            raise current_error
        if not legacy_portfolio:
            raise current_error
        portfolio = None
    portfolio_schema = None if portfolio is None else int(portfolio[0])
    representation_id = config.search_representation_id
    if representation_id is None:
        if portfolio_schema == SEARCH_PORTFOLIO_V3_SCHEMA_VERSION:
            raise RoundTransactionError(
                "geometry-aware search portfolio schema v3 requires an "
                "explicit known search representation"
            )
        return None
    geometry_contract = geometry_contract_for_representation(
        representation_id,
    )
    if geometry_contract is None:
        if portfolio_schema == SEARCH_PORTFOLIO_V3_SCHEMA_VERSION:
            raise RoundTransactionError(
                "geometry-aware search portfolio schema v3 requires a known "
                "twisted-torus search representation"
            )
        # Existing rectangular representations intentionally remain open-
        # ended.  Their exact legacy invocation has no geometry field; if a
        # future source-bound mapping opts one into a new geometry, changing
        # search_contract.py forces a prepared transaction rebind first.
        return None
    if is_twisted_geometry_contract(geometry_contract):
        if portfolio_schema != SEARCH_PORTFOLIO_V3_SCHEMA_VERSION:
            raise RoundTransactionError(
                "twisted-torus search representation requires geometry-aware "
                "search portfolio schema v3"
            )
        return geometry_contract
    if geometry_contract == LEGACY_GEOMETRY_CONTRACT:
        if portfolio_schema == SEARCH_PORTFOLIO_V3_SCHEMA_VERSION:
            raise RoundTransactionError(
                "geometry-aware search portfolio schema v3 requires the "
                "twisted-torus search representation"
            )
        return None
    raise RoundTransactionError(
        "search representation maps to an unsupported geometry contract"
    )


def _validated_coset_renderer_activation_file(path: Path) -> dict[str, Any]:
    """Replay one activation file through the installed source registries."""

    observed = _read_json_object(path, "coset renderer activation")
    from evolve.coset_search_contract import (
        coset_renderer_activation_document,
        trusted_coset_renderer_activation_from_document,
    )

    try:
        activation = trusted_coset_renderer_activation_from_document(observed)
        replayed = coset_renderer_activation_document(activation)
    except (TypeError, ValueError) as exc:
        raise RoundTransactionError(
            f"coset renderer activation cannot be replayed: {exc}"
        ) from exc
    if observed != replayed:
        raise RoundTransactionError(
            "coset renderer activation is not canonical registry data"
        )
    return replayed


def _materialize_round_renderer_activation(
    config: FlowConfig,
    state: Mapping[str, Any],
    round_dir: Path,
) -> Path | None:
    """Freeze the sole renderer activation authorized for this round."""

    if (
        _flow_evaluator_kind(config) != "coset-two-block"
        or _configured_coset_representation_id(config)
        != COSET_REPRESENTATION_ID_V3
    ):
        return None
    current_round = state.get("current_round")
    if (
        isinstance(current_round, bool)
        or not isinstance(current_round, int)
        or current_round < 0
    ):
        raise RoundTransactionError(
            "renderer activation has an invalid current round"
        )
    target_round = current_round + 1
    expected_round_dir = round_dir.parent / f"round-{target_round:03d}"
    if Path(os.path.abspath(round_dir)) != Path(
        os.path.abspath(expected_round_dir)
    ):
        raise RoundTransactionError(
            "renderer activation target disagrees with the round directory"
        )

    if target_round == 1:
        from evolve.coset_search_contract import (
            coset_renderer_activation_document,
            default_coset_renderer_activation,
        )

        activation_document = coset_renderer_activation_document(
            default_coset_renderer_activation()
        )
    else:
        rounds = state.get("rounds")
        if not isinstance(rounds, list):
            raise RoundTransactionError(
                "renderer activation has no durable round history"
            )
        previous = next((
            row for row in reversed(rounds)
            if isinstance(row, dict) and row.get("round") == current_round
        ), None)
        if previous is None:
            raise RoundTransactionError(
                "renderer activation cannot find the preceding round"
            )
        resolution = _validated_bound_renderer_resolution(
            previous, round_dir.parent
        )
        if resolution is None:
            from evolve.coset_search_contract import (
                coset_renderer_activation_document,
                default_coset_renderer_activation,
            )

            activation_document = coset_renderer_activation_document(
                default_coset_renderer_activation()
            )
        elif resolution["status"] == "activated":
            if resolution["target_round"] != target_round:
                raise RoundTransactionError(
                    "reviewer activation targets a different round"
                )
            activation_document = resolution["renderer_activation"]
        else:
            # A non-executable reviewer proposal is sealed evidence that the
            # requested renderer was *not* authorized.  It is not authority to
            # stop the machine search, nor may any part of that proposal cross
            # into the next invocation.  Continue with the source-owned default
            # v3 activation, which is independently reconstructed from the
            # installed registry on every replay.
            if resolution["target_round"] != target_round:
                raise RoundTransactionError(
                    "reviewer renderer advisory targets a different round"
                )
            handoff = resolution.get("representation_expansion_handoff")
            if (
                not isinstance(handoff, Mapping)
                or handoff.get("execution_permitted") is not False
                or resolution.get("renderer_activation") is not None
            ):
                raise RoundTransactionError(
                    "non-executable renderer advisory is malformed"
                )
            from evolve.coset_search_contract import (
                coset_renderer_activation_document,
                default_coset_renderer_activation,
            )

            activation_document = coset_renderer_activation_document(
                default_coset_renderer_activation()
            )

    activation_path = Path(os.path.abspath(
        round_dir / COSET_RENDERER_ACTIVATION_FILENAME
    ))
    if activation_path.exists() or activation_path.is_symlink():
        if activation_path.is_symlink() or not activation_path.is_file():
            raise RoundTransactionError(
                "coset renderer activation artifact is unsafe"
            )
        if _validated_coset_renderer_activation_file(
            activation_path
        ) != activation_document:
            raise RoundTransactionError(
                "coset renderer activation changed after round prepare"
            )
    else:
        atomic_write_json(activation_path, activation_document)
    return activation_path


def _evolution_launch_binding(
    config: FlowConfig,
    *,
    context_path: Path,
    codex_executable: dict[str, Any] | None = None,
) -> dict[str, dict[str, Any]]:
    binding = {
        "config": _file_descriptor(
            _expected_evolution_config(config), "evolution config"
        ),
        "seed": _file_descriptor(
            _expected_evolution_seed(config), "evolution seed"
        ),
        "launcher": _file_descriptor(
            _expected_evolution_launcher(config), "evolution launcher"
        ),
        "evaluator": _file_descriptor(
            _expected_evolution_evaluator(config), "evolution evaluator"
        ),
        "context": _file_descriptor(
            context_path, "evolution humanize context"
        ),
    }
    for name, relative_path in _evolution_dependencies(config).items():
        binding[name] = _file_descriptor(
            config.repo_dir / relative_path,
            f"evolution evaluator dependency {name}",
        )
    if _flow_evaluator_kind(config) == "coset-two-block":
        _manifest, snapshot, snapshot_manifest = (
            _negative_feedback_epoch_binding(config, context_path.parent)
        )
        binding["coset_negative_feedback_snapshot"] = snapshot
        binding["coset_negative_feedback_snapshot_manifest"] = (
            snapshot_manifest
        )
        if _configured_coset_representation_id(config) == (
            COSET_REPRESENTATION_ID_V3
        ):
            activation_path = Path(os.path.abspath(
                context_path.parent / COSET_RENDERER_ACTIVATION_FILENAME
            ))
            _validated_coset_renderer_activation_file(activation_path)
            binding["coset_renderer_activation"] = _file_descriptor(
                activation_path, "coset renderer activation"
            )
    if config.codex_cli:
        if codex_executable is None:
            raise RoundTransactionError(
                "Codex evolution launch has no frozen executable identity"
            )
        binding["backend"] = _file_descriptor(
            _expected_evolution_backend(config), "evolution model backend"
        )
        observed = _file_descriptor(
            Path(str(codex_executable.get("path", ""))),
            "Codex CLI native executable",
        )
        observed["mode"] = stat.S_IMODE(Path(observed["path"]).stat().st_mode)
        if observed != codex_executable:
            raise RoundTransactionError(
                "Codex CLI native executable changed after transaction prepare"
            )
        binding["codex_executable"] = dict(codex_executable)
        if config.search_representation_id == (
            PUBLISHED_VOLUME_ANSATZ_V3_REPRESENTATION_ID
        ):
            from evolve.ansatz_v3_codex_view import (
                AnsatzV3CodexViewError,
                VIEW_DIRECTORY_NAME,
                validate_sanitized_codex_view,
            )

            try:
                view = validate_sanitized_codex_view(
                    config.repo_dir,
                    context_path.parent / VIEW_DIRECTORY_NAME,
                )
            except (OSError, AnsatzV3CodexViewError) as exc:
                raise RoundTransactionError(
                    f"ansatz-v3 sanitized Codex view failed binding: {exc}"
                ) from exc
            binding[ANSATZ_V3_CODEX_VIEW_LAUNCH_FIELD] = _file_descriptor(
                Path(view["manifest_path"]),
                "ansatz-v3 sanitized Codex view manifest",
            )
    return binding


def _is_ansatz_v3_codex_invocation(config: FlowConfig) -> bool:
    """Return whether Codex must run inside the ansatz-v3 readable view."""

    return (
        config.codex_cli
        and config.search_representation_id
        == PUBLISHED_VOLUME_ANSATZ_V3_REPRESENTATION_ID
    )


def _expected_evolution_invocation_fields(
    config: FlowConfig,
    launch_fields: Collection[str],
    geometry_contract: str | None,
) -> set[str]:
    """Return the one closed invocation schema used by every consumer."""

    expected = set(EVOLUTION_INVOCATION_FIELDS)
    if _flow_evaluator_kind(config) == "coset-two-block":
        expected.update(COSET_EVOLUTION_INVOCATION_FIELDS)
        if set(launch_fields) & set(COSET_NEGATIVE_FEEDBACK_LAUNCH_FIELDS):
            expected.update(COSET_NEGATIVE_FEEDBACK_INVOCATION_FIELDS)
        if _configured_coset_representation_id(config) == (
            COSET_REPRESENTATION_ID_V3
        ):
            expected.add(COSET_RENDERER_ACTIVATION_SHA256_BINDING_FIELD)
    if geometry_contract is not None:
        expected.add(SEARCH_GEOMETRY_CONTRACT_INVOCATION_FIELD)
    if _is_ansatz_v3_codex_invocation(config):
        expected.update(ANSATZ_V3_CODEX_VIEW_INVOCATION_FIELDS)
    return expected


def _validated_codex_cwd(
    config: FlowConfig,
    invocation: Mapping[str, Any],
    launch_binding: Mapping[str, Any],
    *,
    ansatz_v3_codex: bool,
) -> str:
    """Replay the representation-specific Codex cwd and readable-view bind."""

    expected_codex_cwd = str(config.repo_dir.resolve(strict=True))
    if not ansatz_v3_codex:
        return expected_codex_cwd

    from evolve.ansatz_v3_codex_view import (
        AnsatzV3CodexViewError,
        validate_sanitized_codex_view,
    )

    view_descriptor = launch_binding.get(ANSATZ_V3_CODEX_VIEW_LAUNCH_FIELD)
    if not isinstance(view_descriptor, dict):
        raise RoundTransactionError(
            "ansatz-v3 sanitized Codex view launch binding is missing"
        )
    try:
        view = validate_sanitized_codex_view(
            config.repo_dir,
            Path(str(invocation["codex_cwd"])),
        )
    except (KeyError, OSError, AnsatzV3CodexViewError) as exc:
        raise RoundTransactionError(
            f"ansatz-v3 sanitized Codex view changed: {exc}"
        ) from exc
    if (
        _file_descriptor(
            Path(view["manifest_path"]),
            "ansatz-v3 sanitized Codex view manifest",
        )
        != view_descriptor
        or invocation.get("ansatz_v3_codex_view_manifest_path")
        != view["manifest_path"]
        or invocation.get("ansatz_v3_codex_view_manifest_sha256")
        != view["manifest_file_sha256"]
        or invocation.get(
            "ansatz_v3_codex_view_source_fingerprint_sha256"
        ) != view["source_fingerprint_sha256"]
        or invocation.get("ansatz_v3_codex_filesystem_boundary")
        != view["filesystem_boundary"]
    ):
        raise RoundTransactionError(
            "ansatz-v3 sanitized Codex view binding changed"
        )
    return view["view_path"]


def _validate_invocation_binding(
    config: FlowConfig,
    invocation: Any,
    launch_binding: dict[str, dict[str, Any]],
) -> dict[str, Any]:
    geometry_contract = _managed_search_geometry_contract(
        config,
        Path(launch_binding["config"]["path"]),
    )
    launch_fields = set(launch_binding)
    feedback_launch_fields = (
        launch_fields & set(COSET_NEGATIVE_FEEDBACK_LAUNCH_FIELDS)
    )
    if feedback_launch_fields and feedback_launch_fields != set(
        COSET_NEGATIVE_FEEDBACK_LAUNCH_FIELDS
    ):
        raise RoundTransactionError(
            "coset negative-feedback launch binding is incomplete"
        )
    expected_fields = _expected_evolution_invocation_fields(
        config, launch_fields, geometry_contract
    )
    ansatz_v3_codex = _is_ansatz_v3_codex_invocation(config)
    if not isinstance(invocation, dict) or set(invocation) != expected_fields:
        raise RoundTransactionError(
            "evolution invocation binding fields are incomplete"
        )
    if geometry_contract is not None and (
        invocation[SEARCH_GEOMETRY_CONTRACT_INVOCATION_FIELD]
        != geometry_contract
    ):
        raise RoundTransactionError(
            "evolution search geometry contract binding changed"
        )
    if _flow_evaluator_kind(config) == "coset-two-block":
        catalog = launch_binding.get(
            _coset_action_catalog_dependency_key(config)
        )
        if (
            invocation.get("qcode_evaluator_kind") != "coset-two-block"
            or not isinstance(catalog, dict)
            or invocation.get("qcode_action_catalog_sha256")
            != catalog.get("sha256")
        ):
            raise RoundTransactionError(
                "coset evolution evaluator/catalog binding changed"
            )
        if _configured_coset_representation_id(config) == (
            COSET_REPRESENTATION_ID_V3
        ):
            activation_descriptor = launch_binding.get(
                "coset_renderer_activation"
            )
            if not isinstance(activation_descriptor, dict):
                raise RoundTransactionError(
                    "coset renderer activation launch binding is missing"
                )
            activation_path = Path(str(
                activation_descriptor.get("path", "")
            ))
            if _file_descriptor(
                activation_path, "coset renderer activation"
            ) != activation_descriptor:
                raise RoundTransactionError(
                    "coset renderer activation launch binding changed"
                )
            expected_activation = (
                _validated_coset_renderer_activation_file(activation_path)[
                    "activation_sha256"
                ]
            )
            if invocation.get(
                COSET_RENDERER_ACTIVATION_SHA256_BINDING_FIELD
            ) != expected_activation:
                raise RoundTransactionError(
                    "coset renderer activation binding changed"
                )
        if feedback_launch_fields:
            expected_feedback = _negative_feedback_invocation(
                config, launch_binding
            )
            if any(
                invocation.get(name) != value
                for name, value in expected_feedback.items()
            ):
                raise RoundTransactionError(
                    "coset negative-feedback invocation binding changed"
                )
    if invocation["model_names"] != [config.model]:
        raise RoundTransactionError("evolution model binding changed")
    if invocation["reasoning_effort"] != config.reasoning_effort:
        raise RoundTransactionError("evolution reasoning binding changed")
    if invocation["codex_cli"] is not config.codex_cli:
        raise RoundTransactionError("evolution backend selection changed")
    workers = invocation["max_parallel_evaluations"]
    configured_workers = _configured_evolution_workers(
        Path(launch_binding["config"]["path"])
    )
    expected_workers = (
        configured_workers
        if config.max_total_workers is None
        else min(configured_workers, config.max_total_workers)
    )
    if (
        isinstance(workers, bool)
        or not isinstance(workers, int)
        or workers != expected_workers
    ):
        raise RoundTransactionError(
            "evolution worker binding does not match the unified worker budget"
        )
    api_base = invocation["api_base"]
    if not isinstance(api_base, str) or not api_base:
        raise RoundTransactionError("evolution API base binding is invalid")
    if config.api_base is not None and api_base != config.api_base:
        raise RoundTransactionError("evolution API base binding changed")
    if invocation["temperature_disabled"] is not True:
        raise RoundTransactionError(
            "managed evolution must freeze temperature-disabled mode"
        )

    codex_fields = (
        invocation["codex_version"],
        invocation["codex_cwd"],
        invocation["codex_executable_mode"],
    )
    if config.codex_cli:
        if set(("backend", "codex_executable")) - set(launch_binding):
            raise RoundTransactionError("Codex launch binding is incomplete")
        executable = launch_binding["codex_executable"]
        path = Path(str(executable.get("path", "")))
        observed = _file_descriptor(path, "Codex CLI native executable")
        observed["mode"] = stat.S_IMODE(path.stat().st_mode)
        if observed != executable:
            raise RoundTransactionError(
                "Codex CLI native executable changed after transaction prepare"
            )
        expected_codex_cwd = _validated_codex_cwd(
            config,
            invocation,
            launch_binding,
            ansatz_v3_codex=ansatz_v3_codex,
        )
        if (
            invocation["codex_executable_mode"] != executable["mode"]
            or invocation["codex_cwd"]
            != expected_codex_cwd
            or not isinstance(invocation["codex_version"], str)
            or not invocation["codex_version"]
            or _codex_version(path) != invocation["codex_version"]
        ):
            raise RoundTransactionError(
                "Codex execution identity changed after transaction prepare"
            )
    elif any(value is not None for value in codex_fields):
        raise RoundTransactionError(
            "non-Codex invocation contains Codex execution fields"
        )
    return dict(invocation)


def _candidate_support_profile(
    row: dict[str, Any],
) -> tuple[str, str]:
    """Derive support shape from defining terms, never score metadata."""

    construction = row.get("construction")
    if isinstance(construction, dict):
        left = construction.get("left_support", row.get("left_support"))
        right = construction.get("right_support", row.get("right_support"))
        if not isinstance(left, (list, tuple)) or not isinstance(
            right, (list, tuple)
        ):
            return "unclassified", "unclassified"
        if any(not isinstance(item, str) or not item for item in (*left, *right)):
            return f"{len(left)}+{len(right)}", "unclassified"
        return f"{len(left)}+{len(right)}", "nonmixed"

    supports: list[int] = []
    contains_mixed = False
    valid_terms = True
    for field in ("A_terms", "B_terms"):
        terms = row.get(field)
        if not isinstance(terms, (list, tuple)):
            return "unclassified", "unclassified"
        supports.append(len(terms))
        for term in terms:
            if (
                not isinstance(term, (list, tuple))
                or len(term) != 2
                or any(type(coordinate) is not int for coordinate in term)
            ):
                valid_terms = False
                continue
            x, y = term
            if x > 0 and y > 0:
                contains_mixed = True
    split = f"{supports[0]}+{supports[1]}"
    if not valid_terms:
        return split, "unclassified"
    return split, "mixed" if contains_mixed else "nonmixed"


def _candidate_audit_stratum(row: dict[str, Any]) -> tuple[str, str]:
    """Return the advisory mechanism/support stratum for fresh MILP sampling.

    Algebraic mechanism labels are search metadata rather than proof evidence.
    They therefore affect only which otherwise eligible candidates receive a
    scarce exact-audit slot.  Older candidate rows without either label remain
    eligible in a deterministic ``unclassified`` mechanism bucket.
    """

    # ``relation_type`` is the stable human-readable mechanism label.
    # ``algebraic_relation_type`` is a MAP coordinate in current candidate
    # rows and is therefore numeric.  Accept the latter only as a legacy
    # string fallback; never turn its numeric index into a stratum label.
    mechanism: Any = row.get("relation_type")
    if not isinstance(mechanism, str) or not mechanism.strip():
        legacy_mechanism = row.get("algebraic_relation_type")
        mechanism = (
            legacy_mechanism
            if isinstance(legacy_mechanism, str)
            else "unclassified"
        )
    if not isinstance(mechanism, str) or not mechanism.strip():
        mechanism = "unclassified"
    split, _mixed = _candidate_support_profile(row)
    return mechanism.strip(), split


def _candidate_diversity_summary(
    transaction: dict[str, Any],
    batch_rows: list[dict[str, Any]],
) -> dict[str, Any]:
    """Summarize only a transaction-bound raw slice and canonical batch."""

    raw_rows = transaction.get("candidate_source_rows")
    source_sha256 = transaction.get("candidate_source_sha256")
    batch_identity = transaction.get("candidate_batch_identity")
    if (
        isinstance(raw_rows, bool)
        or not isinstance(raw_rows, int)
        or raw_rows < 0
        or not isinstance(source_sha256, str)
        or not re.fullmatch(r"[0-9a-f]{64}", source_sha256)
        or not isinstance(batch_identity, dict)
        or batch_identity.get("rows") != len(batch_rows)
        or not isinstance(batch_identity.get("sha256"), str)
        or not re.fullmatch(r"[0-9a-f]{64}", batch_identity["sha256"])
    ):
        raise RoundTransactionError(
            "candidate diversity received an invalid transaction binding"
        )
    unique_rows = len(batch_rows)
    if unique_rows > raw_rows:
        raise RoundTransactionError(
            "canonical candidate batch is larger than its bound source"
        )

    support_splits: dict[str, int] = {}
    mixed_counts = {
        "mixed": 0,
        "nonmixed": 0,
        "unclassified": 0,
    }
    for row in batch_rows:
        split, mixed_class = _candidate_support_profile(row)
        support_splits[split] = support_splits.get(split, 0) + 1
        mixed_counts[mixed_class] += 1
    support_splits = dict(
        sorted(
            support_splits.items(),
            key=lambda item: (
                item[0] == "unclassified",
                tuple(map(int, item[0].split("+")))
                if item[0] != "unclassified"
                else (),
            ),
        )
    )

    duplicate_count = raw_rows - unique_rows
    return {
        "schema_version": ROUND_CANDIDATE_DIVERSITY_SCHEMA_VERSION,
        "basis": "transaction-bound-source-and-canonical-batch",
        "raw_candidate_source_rows": raw_rows,
        "canonical_unique_batch_rows": unique_rows,
        "duplicate_count": duplicate_count,
        "duplicate_rate": (
            duplicate_count / raw_rows if raw_rows else 0.0
        ),
        "candidate_source_sha256": source_sha256,
        "candidate_batch_sha256": batch_identity["sha256"],
        "support_split_counts": support_splits,
        "mixed_vs_nonmixed_counts": mixed_counts,
    }


def _validate_candidate_diversity_summary(
    value: Any,
) -> dict[str, Any]:
    """Validate the optional state record before rendering fixed advisory text."""

    if not isinstance(value, dict):
        raise RoundTransactionError(
            "previous candidate diversity summary must be an object"
        )
    expected_fields = {
        "schema_version",
        "basis",
        "raw_candidate_source_rows",
        "canonical_unique_batch_rows",
        "duplicate_count",
        "duplicate_rate",
        "candidate_source_sha256",
        "candidate_batch_sha256",
        "support_split_counts",
        "mixed_vs_nonmixed_counts",
    }
    if set(value) != expected_fields:
        raise RoundTransactionError(
            "previous candidate diversity summary fields are invalid"
        )
    if (
        value["schema_version"]
        != ROUND_CANDIDATE_DIVERSITY_SCHEMA_VERSION
        or value["basis"]
        != "transaction-bound-source-and-canonical-batch"
    ):
        raise RoundTransactionError(
            "previous candidate diversity summary schema is invalid"
        )

    integer_fields = (
        "raw_candidate_source_rows",
        "canonical_unique_batch_rows",
        "duplicate_count",
    )
    if any(
        isinstance(value[field], bool)
        or not isinstance(value[field], int)
        or value[field] < 0
        for field in integer_fields
    ):
        raise RoundTransactionError(
            "previous candidate diversity row counts are invalid"
        )
    raw_rows = value["raw_candidate_source_rows"]
    unique_rows = value["canonical_unique_batch_rows"]
    duplicate_count = value["duplicate_count"]
    expected_rate = duplicate_count / raw_rows if raw_rows else 0.0
    if (
        unique_rows > raw_rows
        or duplicate_count != raw_rows - unique_rows
        or isinstance(value["duplicate_rate"], bool)
        or not isinstance(value["duplicate_rate"], (int, float))
        or not 0.0 <= float(value["duplicate_rate"]) <= 1.0
        or abs(float(value["duplicate_rate"]) - expected_rate) > 1e-12
    ):
        raise RoundTransactionError(
            "previous candidate diversity duplicate statistics are invalid"
        )
    if any(
        not isinstance(value[field], str)
        or not re.fullmatch(r"[0-9a-f]{64}", value[field])
        for field in (
            "candidate_source_sha256",
            "candidate_batch_sha256",
        )
    ):
        raise RoundTransactionError(
            "previous candidate diversity bindings are invalid"
        )

    support_splits = value["support_split_counts"]
    if (
        not isinstance(support_splits, dict)
        or any(
            (
                not isinstance(key, str)
                or (
                    key != "unclassified"
                    and not re.fullmatch(r"\d+\+\d+", key)
                )
            )
            or isinstance(count, bool)
            or not isinstance(count, int)
            or count < 0
            for key, count in support_splits.items()
        )
        or sum(support_splits.values()) != unique_rows
    ):
        raise RoundTransactionError(
            "previous candidate support-split distribution is invalid"
        )
    mixed_counts = value["mixed_vs_nonmixed_counts"]
    if (
        not isinstance(mixed_counts, dict)
        or set(mixed_counts) != {"mixed", "nonmixed", "unclassified"}
        or any(
            isinstance(count, bool)
            or not isinstance(count, int)
            or count < 0
            for count in mixed_counts.values()
        )
        or sum(mixed_counts.values()) != unique_rows
    ):
        raise RoundTransactionError(
            "previous mixed-support distribution is invalid"
        )
    return value


def _validate_round_diversity_evidence(
    value: Any, *, round_dir: Path
) -> dict[str, Any]:
    """Replay a diversity summary from its committed manifest and batch."""

    validated = _validate_candidate_diversity_summary(value)
    manifest_path = round_dir / "evolution-transaction.json"
    batch_path = round_dir / "candidate-batch.jsonl"
    if (
        manifest_path.is_symlink()
        or not manifest_path.is_file()
        or batch_path.is_symlink()
        or not batch_path.is_file()
    ):
        raise RoundTransactionError(
            "search-regime diversity transaction evidence is missing"
        )
    transaction = _read_json_object(
        manifest_path, "search-regime evolution transaction"
    )
    if transaction.get("status") != "committed":
        raise RoundTransactionError(
            "search-regime diversity transaction is not committed"
        )
    try:
        batch_rows, end_offset, batch_sha256 = read_jsonl_range(batch_path, 0)
    except ValueError as exc:
        raise RoundTransactionError(str(exc)) from exc
    batch_identity = {
        "sha256": batch_sha256,
        "bytes": end_offset,
        "rows": len(batch_rows),
    }
    if transaction.get("candidate_batch_identity") != batch_identity:
        raise RoundTransactionError(
            "search-regime candidate batch changed after commit"
        )
    expected = _candidate_diversity_summary(transaction, batch_rows)
    if validated != expected:
        raise RoundTransactionError(
            "search-regime diversity summary disagrees with committed batch"
        )
    return validated


def _sealed_exact_distances(
    rows: list[dict[str, Any]], *, round_number: int
) -> list[int]:
    """Extract exact distances only from formal, round-bound audit attempts."""

    distances: list[int] = []
    for row in rows:
        attempt = row.get("audit_attempt")
        if (
            not isinstance(attempt, dict)
            or attempt.get("schema_version") != 2
            or attempt.get("round") != round_number
            or not isinstance(attempt.get("evidence"), dict)
        ):
            # Debug evaluators and legacy/unsealed rows may be useful to tests
            # and review, but they must not vote on a structural regime change.
            continue
        try:
            outcome = classify_evaluation(row)
        except AuditStateError:
            # A corrupt, redirected, stale-implementation, or otherwise
            # unreplayable evidence object is not evidence of exactness.  It
            # remains visible in the durable MILP log for audit/retry, but it
            # must not vote on a search-regime transition.
            continue
        if outcome is not AuditOutcome.EXACT:
            continue
        distance = _positive_distance(row)
        if distance is None:
            raise RoundTransactionError(
                "sealed fully-exact audit has no positive distance"
            )
        distances.append(distance)
    return sorted(distances)


def _sealed_round_exact_summary(
    *,
    round_number: int,
    round_dir: Path,
    failure_feedback: dict[str, Any],
) -> dict[str, Any]:
    """Bind regime input to the durable MILP bytes already sealed this round."""

    milp_path = round_dir / "milp.jsonl"
    if milp_path.is_symlink() or not milp_path.is_file():
        raise RoundTransactionError(
            "search-regime exact evidence requires a regular MILP file"
        )
    payload = milp_path.read_bytes()
    rows = _strict_jsonl_objects(payload, "search-regime round MILP evidence")
    identity = {
        "sha256": hashlib.sha256(payload).hexdigest(),
        "bytes": len(payload),
        "rows": len(rows),
    }
    expected_identity = {
        "sha256": failure_feedback.get("source_milp_sha256"),
        "bytes": failure_feedback.get("source_milp_bytes"),
        "rows": failure_feedback.get("source_milp_rows"),
    }
    if identity != expected_identity:
        raise RoundTransactionError(
            "search-regime exact evidence disagrees with sealed feedback source"
        )
    distances = _sealed_exact_distances(rows, round_number=round_number)
    return {
        "schema_version": SEALED_ROUND_EXACT_SCHEMA_VERSION,
        "basis": "sealed-formal-audit-attempts",
        "source_milp_sha256": identity["sha256"],
        "source_milp_bytes": identity["bytes"],
        "source_milp_rows": identity["rows"],
        "exact_count": len(distances),
        "exact_distances": distances,
    }


def _validate_sealed_round_exact_summary(
    value: Any,
    *,
    round_number: int,
    round_dir: Path | None = None,
) -> dict[str, Any]:
    expected_fields = {
        "schema_version",
        "basis",
        "source_milp_sha256",
        "source_milp_bytes",
        "source_milp_rows",
        "exact_count",
        "exact_distances",
    }
    if not isinstance(value, dict) or set(value) != expected_fields:
        raise RoundTransactionError(
            "sealed round exact summary fields are invalid"
        )
    if (
        value["schema_version"] != SEALED_ROUND_EXACT_SCHEMA_VERSION
        or value["basis"] != "sealed-formal-audit-attempts"
        or not isinstance(value["source_milp_sha256"], str)
        or not re.fullmatch(r"[0-9a-f]{64}", value["source_milp_sha256"])
    ):
        raise RoundTransactionError(
            "sealed round exact summary schema is invalid"
        )
    integer_fields = (
        "source_milp_bytes",
        "source_milp_rows",
        "exact_count",
    )
    if any(
        isinstance(value[field], bool)
        or not isinstance(value[field], int)
        or value[field] < 0
        for field in integer_fields
    ):
        raise RoundTransactionError(
            "sealed round exact summary counts are invalid"
        )
    distances = value["exact_distances"]
    if (
        not isinstance(distances, list)
        or any(
            isinstance(distance, bool)
            or not isinstance(distance, int)
            or distance < 1
            for distance in distances
        )
        or distances != sorted(distances)
        or value["exact_count"] != len(distances)
        or value["exact_count"] > value["source_milp_rows"]
    ):
        raise RoundTransactionError(
            "sealed round exact distances are invalid"
        )
    if round_dir is not None:
        milp_path = round_dir / "milp.jsonl"
        if milp_path.is_symlink() or not milp_path.is_file():
            raise RoundTransactionError(
                "sealed search-regime MILP evidence is missing"
            )
        payload = milp_path.read_bytes()
        rows = _strict_jsonl_objects(
            payload, "sealed search-regime MILP evidence"
        )
        observed_distances = _sealed_exact_distances(
            rows, round_number=round_number
        )
        observed = {
            "source_milp_sha256": hashlib.sha256(payload).hexdigest(),
            "source_milp_bytes": len(payload),
            "source_milp_rows": len(rows),
            "exact_count": len(observed_distances),
            "exact_distances": observed_distances,
        }
        if any(value[field] != observed[field] for field in observed):
            raise RoundTransactionError(
                "sealed round exact summary disagrees with MILP bytes"
            )
    return value


def _normal_search_regime(completed_rounds: int) -> dict[str, Any]:
    return {
        "schema_version": SEARCH_REGIME_SCHEMA_VERSION,
        "kind": SEARCH_REGIME_KIND,
        "status": "normal",
        "reason": "insufficient_trusted_exact_stagnation",
        "evidence": {
            "basis": "durable-sealed-exact-and-diversity",
            "completed_rounds": completed_rounds,
        },
    }


def _advance_search_regime_v1(
    previous: dict[str, Any],
    completed: list[dict[str, Any]],
) -> dict[str, Any]:
    """Replay the historical diversity-collapse policy without reinterpretation."""

    latest = completed[-1]
    exact = latest.get("sealed_exact_audit")
    if not isinstance(exact, dict):
        return (
            copy.deepcopy(previous)
            if previous.get("status") == "expand_required"
            else _normal_search_regime(len(completed))
        )
    latest_distances = exact["exact_distances"]
    if any(distance >= 4 for distance in latest_distances):
        return {
            "schema_version": SEARCH_REGIME_SCHEMA_VERSION,
            "kind": SEARCH_REGIME_KIND,
            "status": "exploit",
            "reason": "trusted_exact_distance_progress",
            "evidence": {
                "basis": "durable-sealed-exact-and-diversity",
                "round": latest["round"],
                "exact_distances": list(latest_distances),
                "source_milp_sha256": exact["source_milp_sha256"],
            },
        }

    low_exact_streak: list[dict[str, Any]] = []
    for summary in reversed(completed):
        item = summary.get("sealed_exact_audit")
        if not isinstance(item, dict):
            break
        distances = item["exact_distances"]
        if not distances or any(distance > 2 for distance in distances):
            break
        low_exact_streak.append(summary)
    low_exact_streak.reverse()
    if len(low_exact_streak) >= SEARCH_REGIME_STAGNATION_ROUNDS:
        recent = low_exact_streak[-SEARCH_REGIME_STAGNATION_ROUNDS:]
        first_diversity = recent[0].get("candidate_diversity")
        latest_diversity = recent[-1].get("candidate_diversity")
        if isinstance(first_diversity, dict) and isinstance(
            latest_diversity, dict
        ):
            first_unique = first_diversity["canonical_unique_batch_rows"]
            latest_unique = latest_diversity["canonical_unique_batch_rows"]
            duplicate_rate = float(latest_diversity["duplicate_rate"])
            high_duplicates = duplicate_rate >= SEARCH_REGIME_DUPLICATE_RATE
            unique_decline = (
                first_unique > 0 and latest_unique * 5 <= first_unique * 4
            )
            if high_duplicates or unique_decline:
                return {
                    "schema_version": SEARCH_REGIME_SCHEMA_VERSION,
                    "kind": SEARCH_REGIME_KIND,
                    "status": "expand_required",
                    "reason": (
                        "trusted_exact_low_distance_with_duplicate_collapse"
                        if high_duplicates
                        else "trusted_exact_low_distance_with_unique_yield_decline"
                    ),
                    "evidence": {
                        "basis": "durable-sealed-exact-and-diversity",
                        "rounds": [item["round"] for item in recent],
                        "exact_distances_by_round": [
                            item["sealed_exact_audit"]["exact_distances"]
                            for item in recent
                        ],
                        "first_canonical_unique_batch_rows": first_unique,
                        "latest_canonical_unique_batch_rows": latest_unique,
                        "latest_duplicate_rate": duplicate_rate,
                    },
                }

    if previous.get("status") == "expand_required":
        return copy.deepcopy(previous)
    return _normal_search_regime(len(completed))


def _advance_search_regime_v2(
    previous: dict[str, Any],
    completed: list[dict[str, Any]],
) -> dict[str, Any]:
    """Advance from exact/diversity facts; unresolved attempts never vote."""

    # Representation replacement is a machine-evidence terminal search mode.
    # It must not be cleared by an unresolved round, reviewer prose, or a later
    # transient exact result; only the outer trusted-win gate ends the search.
    if previous.get("status") == "representation_change_required":
        return copy.deepcopy(previous)

    latest = completed[-1]
    exact = latest.get("sealed_exact_audit")
    if not isinstance(exact, dict):
        return (
            copy.deepcopy(previous)
            if previous.get("status") in {
                "expand_required",
                "representation_change_required",
            }
            else _normal_search_regime(len(completed))
        )
    latest_distances = exact["exact_distances"]
    if any(distance >= 4 for distance in latest_distances):
        return {
            "schema_version": SEARCH_REGIME_SCHEMA_VERSION,
            "kind": SEARCH_REGIME_KIND,
            "status": "exploit",
            "reason": "trusted_exact_distance_progress",
            "evidence": {
                "basis": "durable-sealed-exact-and-diversity",
                "round": latest["round"],
                "exact_distances": list(latest_distances),
                "source_milp_sha256": exact["source_milp_sha256"],
            },
        }

    low_exact_streak: list[dict[str, Any]] = []
    for summary in reversed(completed):
        item = summary.get("sealed_exact_audit")
        if not isinstance(item, dict):
            break
        distances = item["exact_distances"]
        # For the fixed strict target FOM > 12, every valid quantum code has
        # k <= n, hence exact d <= 3 implies k*d^2/n <= 9 and is universally
        # non-winning.  Distance 4 remains the first value that can justify
        # the exploit branch above.  Policy v1 deliberately retains its
        # historical d <= 2 replay boundary.
        if not distances or any(distance >= 4 for distance in distances):
            break
        low_exact_streak.append(summary)
    low_exact_streak.reverse()

    def streak_regime(
        status: str,
        reason: str,
        recent: list[dict[str, Any]],
    ) -> dict[str, Any]:
        return {
            "schema_version": SEARCH_REGIME_SCHEMA_VERSION,
            "kind": SEARCH_REGIME_KIND,
            "status": status,
            "reason": reason,
            "evidence": {
                "basis": "durable-sealed-exact-and-diversity",
                "rounds": [item["round"] for item in recent],
                "exact_distances_by_round": [
                    item["sealed_exact_audit"]["exact_distances"]
                    for item in recent
                ],
            },
        }

    if len(low_exact_streak) >= SEARCH_REGIME_REPRESENTATION_ROUNDS:
        recent = low_exact_streak[-SEARCH_REGIME_REPRESENTATION_ROUNDS:]
        return streak_regime(
            "representation_change_required",
            "trusted_exact_low_distance_streak_requires_representation_change",
            recent,
        )

    if len(low_exact_streak) >= SEARCH_REGIME_EXPANSION_ROUNDS:
        recent = low_exact_streak[-SEARCH_REGIME_EXPANSION_ROUNDS:]
        return streak_regime(
            "expand_required",
            "trusted_exact_low_distance_streak_requires_family_expansion",
            recent,
        )

    if len(low_exact_streak) >= SEARCH_REGIME_STAGNATION_ROUNDS:
        recent = low_exact_streak[-SEARCH_REGIME_STAGNATION_ROUNDS:]
        first_diversity = recent[0].get("candidate_diversity")
        latest_diversity = recent[-1].get("candidate_diversity")
        if isinstance(first_diversity, dict) and isinstance(
            latest_diversity, dict
        ):
            first_unique = first_diversity["canonical_unique_batch_rows"]
            latest_unique = latest_diversity[
                "canonical_unique_batch_rows"
            ]
            duplicate_rate = float(latest_diversity["duplicate_rate"])
            high_duplicates = (
                duplicate_rate >= SEARCH_REGIME_DUPLICATE_RATE
            )
            unique_decline = (
                first_unique > 0 and latest_unique * 5 <= first_unique * 4
            )
            if high_duplicates or unique_decline:
                regime = streak_regime(
                    "expand_required",
                    (
                        "trusted_exact_low_distance_with_duplicate_collapse"
                        if high_duplicates
                        else "trusted_exact_low_distance_with_unique_yield_decline"
                    ),
                    recent,
                )
                regime["evidence"].update({
                    "first_canonical_unique_batch_rows": first_unique,
                    "latest_canonical_unique_batch_rows": latest_unique,
                    "latest_duplicate_rate": duplicate_rate,
                })
                return regime

    if previous.get("status") == "expand_required":
        return copy.deepcopy(previous)
    return _normal_search_regime(len(completed))


def _advance_search_regime_v3(
    previous: dict[str, Any],
    completed: list[dict[str, Any]],
    *,
    max_rounds: int,
) -> dict[str, Any]:
    """Advance without letting empty exact attempts veto structural evidence.

    Policy v2 treated a valid sealed round with no exact distances as a streak
    boundary.  In practice that made a timeout/unresolved attempt cast a
    negative vote against changing representation.  V3 keeps such rounds
    neutral, counts only non-empty exact-low rounds since the latest exact
    distance progress, and closes a fully exhausted expansion budget with a
    representation-change handoff.  V1/V2 remain separate for exact replay.
    """

    if (
        isinstance(max_rounds, bool)
        or not isinstance(max_rounds, int)
        or max_rounds < 1
    ):
        raise RoundTransactionError(
            "search regime policy v3 requires a positive max_rounds"
        )

    latest = completed[-1]
    exact = latest.get("sealed_exact_audit")
    if not isinstance(exact, dict):
        raise RoundTransactionError(
            "search regime policy v3 requires sealed exact evidence per round"
        )
    latest_distances = exact["exact_distances"]
    trusted_win_total = latest.get("trusted_win_total")
    if (
        isinstance(trusted_win_total, bool)
        or not isinstance(trusted_win_total, int)
        or trusted_win_total < 0
    ):
        raise RoundTransactionError(
            "search regime policy v3 requires a trusted_win_total per round"
        )
    # Once authorized, a representation restart is terminal for this search
    # identity.  Validate every subsequently presented sealed round before
    # preserving that decision so malformed post-handoff history cannot hide
    # behind the monotonic fast path.
    if previous.get("status") == "representation_change_required":
        return copy.deepcopy(previous)
    if any(distance >= 4 for distance in latest_distances):
        return {
            "schema_version": SEARCH_REGIME_SCHEMA_VERSION,
            "kind": SEARCH_REGIME_KIND,
            "status": "exploit",
            "reason": "trusted_exact_distance_progress",
            "evidence": {
                "basis": "durable-sealed-exact-and-diversity",
                "round": latest["round"],
                "exact_distances": list(latest_distances),
                "source_milp_sha256": exact["source_milp_sha256"],
            },
        }

    low_exact_evidence: list[dict[str, Any]] = []
    for summary in reversed(completed):
        item = summary.get("sealed_exact_audit")
        if not isinstance(item, dict):
            raise RoundTransactionError(
                "search regime policy v3 requires sealed exact evidence per round"
            )
        distances = item["exact_distances"]
        if not distances:
            # A completed attempt with no exact result is evidence-neutral.  It
            # cannot advance the counter, but it also cannot erase prior exact
            # low-distance evidence from this representation.
            continue
        if any(distance >= 4 for distance in distances):
            break
        low_exact_evidence.append(summary)
    low_exact_evidence.reverse()

    def evidence_regime(
        status: str,
        reason: str,
        recent: list[dict[str, Any]],
    ) -> dict[str, Any]:
        return {
            "schema_version": SEARCH_REGIME_SCHEMA_VERSION,
            "kind": SEARCH_REGIME_KIND,
            "status": status,
            "reason": reason,
            "evidence": {
                "basis": "durable-sealed-exact-and-diversity",
                "rounds": [item["round"] for item in recent],
                "exact_distances_by_round": [
                    item["sealed_exact_audit"]["exact_distances"]
                    for item in recent
                ],
            },
        }

    if len(low_exact_evidence) >= SEARCH_REGIME_REPRESENTATION_ROUNDS:
        recent = low_exact_evidence[-SEARCH_REGIME_REPRESENTATION_ROUNDS:]
        regime = evidence_regime(
            "representation_change_required",
            "trusted_exact_low_distance_evidence_requires_representation_change",
            recent,
        )
    elif len(low_exact_evidence) >= SEARCH_REGIME_EXPANSION_ROUNDS:
        recent = low_exact_evidence[-SEARCH_REGIME_EXPANSION_ROUNDS:]
        regime = evidence_regime(
            "expand_required",
            "trusted_exact_low_distance_evidence_requires_family_expansion",
            recent,
        )
    elif len(low_exact_evidence) >= SEARCH_REGIME_STAGNATION_ROUNDS:
        recent = low_exact_evidence[-SEARCH_REGIME_STAGNATION_ROUNDS:]
        first_diversity = recent[0].get("candidate_diversity")
        latest_diversity = recent[-1].get("candidate_diversity")
        if isinstance(first_diversity, dict) and isinstance(
            latest_diversity, dict
        ):
            first_unique = first_diversity["canonical_unique_batch_rows"]
            latest_unique = latest_diversity[
                "canonical_unique_batch_rows"
            ]
            duplicate_rate = float(latest_diversity["duplicate_rate"])
            high_duplicates = (
                duplicate_rate >= SEARCH_REGIME_DUPLICATE_RATE
            )
            unique_decline = (
                first_unique > 0 and latest_unique * 5 <= first_unique * 4
            )
            if high_duplicates or unique_decline:
                regime = evidence_regime(
                    "expand_required",
                    (
                        "trusted_exact_low_distance_with_duplicate_collapse"
                        if high_duplicates
                        else "trusted_exact_low_distance_with_unique_yield_decline"
                    ),
                    recent,
                )
                regime["evidence"].update({
                    "first_canonical_unique_batch_rows": first_unique,
                    "latest_canonical_unique_batch_rows": latest_unique,
                    "latest_duplicate_rate": duplicate_rate,
                })
            elif previous.get("status") == "expand_required":
                regime = copy.deepcopy(previous)
            else:
                regime = _normal_search_regime(len(completed))
        elif previous.get("status") == "expand_required":
            regime = copy.deepcopy(previous)
        else:
            regime = _normal_search_regime(len(completed))
    elif previous.get("status") == "expand_required":
        regime = copy.deepcopy(previous)
    else:
        regime = _normal_search_regime(len(completed))

    # A run that has already earned an expansion directive must not finish its
    # entire authorized budget in the same representation and then strand the
    # automatic campaign graph.  This is a search-control transition only; it
    # weakens no proof or release gate.  A trusted win always takes precedence.
    if (
        latest["round"] == max_rounds
        and len(completed) == max_rounds
        and trusted_win_total == 0
        and regime.get("status") == "expand_required"
    ):
        return {
            "schema_version": SEARCH_REGIME_SCHEMA_VERSION,
            "kind": SEARCH_REGIME_KIND,
            "status": "representation_change_required",
            "reason": "round_budget_exhausted_after_family_expansion",
            "evidence": {
                "basis": "durable-sealed-exact-and-diversity",
                "round": latest["round"],
                "max_rounds": max_rounds,
                "prior_regime_reason": regime["reason"],
                "prior_regime_evidence": copy.deepcopy(regime["evidence"]),
            },
        }
    return regime


def _advance_search_regime_v4(
    previous: dict[str, Any],
    completed: list[dict[str, Any]],
    *,
    max_rounds: int,
) -> dict[str, Any]:
    """Close a fully used representation budget without a trusted WIN.

    V3 intentionally treats rounds with no Stage-1 exact distance as neutral.
    That is correct for proof credit, but a representation whose exact work is
    deferred to Stage 2 can consequently consume its complete authorized
    search budget without ever reaching the representation-handoff state. V4
    preserves every V3 transition and adds one search-control-only terminal
    rule: after all bound rounds are complete, no trusted WIN authorizes a
    fresh, registry-allowlisted representation. Reviewer advice can shape the
    experiments inside those rounds, but it never enters this decision.
    """

    regime = _advance_search_regime_v3(
        previous,
        completed,
        max_rounds=max_rounds,
    )
    if regime.get("status") == "representation_change_required":
        return regime
    latest = completed[-1]
    if (
        latest["round"] == max_rounds
        and len(completed) == max_rounds
        and latest["trusted_win_total"] == 0
    ):
        return {
            "schema_version": SEARCH_REGIME_SCHEMA_VERSION,
            "kind": SEARCH_REGIME_KIND,
            "status": "representation_change_required",
            "reason": "round_budget_exhausted_without_trusted_win",
            "evidence": {
                "basis": (
                    "durable-authorized-round-budget-and-trusted-win-total"
                ),
                "round": latest["round"],
                "max_rounds": max_rounds,
                "prior_regime_status": regime["status"],
                "prior_regime_reason": regime["reason"],
                "prior_regime_evidence": copy.deepcopy(regime["evidence"]),
            },
        }
    return regime


def _advance_search_regime(
    previous: dict[str, Any],
    completed: list[dict[str, Any]],
    *,
    policy_version: int = 1,
    max_rounds: int | None = None,
) -> dict[str, Any]:
    if policy_version == 1:
        return _advance_search_regime_v1(previous, completed)
    if policy_version == 2:
        return _advance_search_regime_v2(previous, completed)
    if policy_version == 3:
        if (
            isinstance(max_rounds, bool)
            or not isinstance(max_rounds, int)
            or max_rounds < 1
        ):
            raise RoundTransactionError(
                "search regime policy v3 requires a positive max_rounds"
            )
        return _advance_search_regime_v3(
            previous,
            completed,
            max_rounds=max_rounds,
        )
    if policy_version == 4:
        if (
            isinstance(max_rounds, bool)
            or not isinstance(max_rounds, int)
            or max_rounds < 1
        ):
            raise RoundTransactionError(
                "search regime policy v4 requires a positive max_rounds"
            )
        return _advance_search_regime_v4(
            previous,
            completed,
            max_rounds=max_rounds,
        )
    raise RoundTransactionError(
        f"unsupported search regime policy version: {policy_version!r}"
    )


def _replay_search_regime(
    rounds: Any,
    *,
    rounds_root: Path | None = None,
    policy_version: int | None = None,
    max_rounds: int | None = None,
) -> dict[str, Any]:
    """Recompute the versioned regime and reject forged persisted summaries."""

    if not isinstance(rounds, list):
        raise RoundTransactionError("search-regime rounds must be a list")
    recorded_versions = [
        summary.get("search_regime_policy_version")
        for summary in rounds
        if isinstance(summary, dict)
        and "search_regime_policy_version" in summary
    ]
    if recorded_versions and len(recorded_versions) != len(rounds):
        raise RoundTransactionError(
            "search-regime history mixes versioned and legacy rounds"
        )
    if recorded_versions:
        if any(
            isinstance(version, bool)
            or not isinstance(version, int)
            or version not in SEARCH_REGIME_POLICY_VERSIONS
            for version in recorded_versions
        ) or len(set(recorded_versions)) != 1:
            raise RoundTransactionError(
                "search-regime history has inconsistent policy versions"
            )
        recorded_policy_version = recorded_versions[0]
    else:
        recorded_policy_version = 1
    if policy_version is None:
        selected_policy_version = recorded_policy_version
    else:
        if (
            isinstance(policy_version, bool)
            or policy_version not in SEARCH_REGIME_POLICY_VERSIONS
        ):
            raise RoundTransactionError(
                f"unsupported search regime policy version: {policy_version!r}"
            )
        selected_policy_version = policy_version
        if rounds and recorded_policy_version != selected_policy_version:
            raise RoundTransactionError(
                "search-regime history disagrees with configured policy version"
            )
    if (
        selected_policy_version
        in SEARCH_REGIME_BUDGET_BOUND_POLICY_VERSIONS
        and (
            isinstance(max_rounds, bool)
            or not isinstance(max_rounds, int)
            or max_rounds < 1
        )
    ):
        raise RoundTransactionError(
            "budget-bound search regime replay requires a positive max_rounds"
        )
    regime = _normal_search_regime(0)
    completed: list[dict[str, Any]] = []
    previous_number = 0
    previous_trusted_win_total = 0
    for summary in rounds:
        if not isinstance(summary, dict):
            raise RoundTransactionError("search-regime round summary is invalid")
        number = summary.get("round")
        if (
            isinstance(number, bool)
            or not isinstance(number, int)
            or number <= previous_number
        ):
            raise RoundTransactionError(
                "search-regime round numbers are not strictly increasing"
            )
        if (
            selected_policy_version
            in SEARCH_REGIME_BUDGET_BOUND_POLICY_VERSIONS
            and number != previous_number + 1
        ):
            raise RoundTransactionError(
                "budget-bound search regime requires contiguous rounds from one"
            )
        previous_number = number
        if (
            selected_policy_version
            in SEARCH_REGIME_BUDGET_BOUND_POLICY_VERSIONS
            and number > max_rounds
        ):
            raise RoundTransactionError(
                "search-regime round exceeds the bound max_rounds"
            )
        if (
            selected_policy_version
            in SEARCH_REGIME_BUDGET_BOUND_POLICY_VERSIONS
        ):
            trusted_win_total = summary.get("trusted_win_total")
            if (
                isinstance(trusted_win_total, bool)
                or not isinstance(trusted_win_total, int)
                or trusted_win_total < previous_trusted_win_total
            ):
                raise RoundTransactionError(
                    "budget-bound trusted_win_total must be a "
                    "nondecreasing integer"
                )
            previous_trusted_win_total = trusted_win_total
        if "sealed_exact_audit" in summary:
            _validate_sealed_round_exact_summary(
                summary["sealed_exact_audit"],
                round_number=number,
                round_dir=(
                    None
                    if rounds_root is None
                    else rounds_root / f"round-{number:03d}"
                ),
            )
        if "candidate_diversity" in summary:
            if rounds_root is None:
                _validate_candidate_diversity_summary(
                    summary["candidate_diversity"]
                )
            else:
                _validate_round_diversity_evidence(
                    summary["candidate_diversity"],
                    round_dir=rounds_root / f"round-{number:03d}",
                )
        if "search_oracle_feedback" in summary:
            _validate_search_oracle_feedback_summary(
                summary["search_oracle_feedback"]
            )
        completed.append(summary)
        regime = _advance_search_regime(
            regime,
            completed,
            policy_version=selected_policy_version,
            max_rounds=max_rounds,
        )
        recorded = summary.get("search_regime")
        if recorded is not None and recorded != regime:
            raise RoundTransactionError(
                "persisted round search regime disagrees with sealed evidence"
            )
    return regime


def _validated_search_handoff(
    config: FlowConfig,
    state: dict[str, Any],
    *,
    rounds_root: Path,
) -> str | None:
    """Validate a durable Stage-1 regime handoff before honoring it.

    The two marker fields are installed with the completed round in one state
    transaction.  A resumed process must replay the sealed regime rather than
    trusting either marker in isolation, and must never enter the next round
    after a valid terminal representation-change handoff.
    """

    reason_present = "search_handoff_reason" in state
    round_present = "search_handoff_at_round" in state
    if not reason_present and not round_present:
        return None
    if reason_present != round_present:
        raise RoundTransactionError(
            "search handoff has only one of reason/round markers"
        )
    if (
        config.search_regime_policy_version not in {2, 3, 4}
        or not config.stop_on_representation_change
    ):
        raise RoundTransactionError(
            "search handoff is not authorized by the configured policy"
        )
    if state.get("pending_round") is not None or state.get(
        "round_phase"
    ) is not None:
        raise RoundTransactionError(
            "search handoff cannot coexist with a pending round"
        )
    reason = state.get("search_handoff_reason")
    handoff_round = state.get("search_handoff_at_round")
    current_round = state.get("current_round")
    if reason != SEARCH_HANDOFF_REASON_REPRESENTATION_CHANGE:
        raise RoundTransactionError("search handoff reason is invalid")
    if (
        isinstance(handoff_round, bool)
        or not isinstance(handoff_round, int)
        or handoff_round < 1
        or handoff_round != current_round
    ):
        raise RoundTransactionError("search handoff round is invalid")
    status = state.get("status")
    if status not in {"search-complete", "incomplete-unresolved"}:
        raise RoundTransactionError("search handoff status is not terminal")
    rounds = state.get("rounds")
    if (
        not isinstance(rounds, list)
        or not rounds
        or not isinstance(rounds[-1], dict)
        or rounds[-1].get("round") != handoff_round
    ):
        raise RoundTransactionError(
            "search handoff is not bound to the final completed round"
        )
    regime = _replay_search_regime(
        rounds,
        rounds_root=rounds_root,
        policy_version=config.search_regime_policy_version,
        max_rounds=(
            config.max_rounds
            if config.search_regime_policy_version
            in SEARCH_REGIME_BUDGET_BOUND_POLICY_VERSIONS
            else None
        ),
    )
    if (
        regime.get("status")
        != SEARCH_HANDOFF_REASON_REPRESENTATION_CHANGE
        or state.get("search_regime") != regime
        or rounds[-1].get("search_regime") != regime
    ):
        raise RoundTransactionError(
            "search handoff disagrees with replayed regime evidence"
        )
    if (
        config.search_regime_policy_version
        in SEARCH_REGIME_BUDGET_BOUND_POLICY_VERSIONS
    ):
        trusted_win_count = state.get("trusted_win_count")
        final_trusted_win_total = rounds[-1].get("trusted_win_total")
        if (
            isinstance(trusted_win_count, bool)
            or not isinstance(trusted_win_count, int)
            or trusted_win_count != 0
            or isinstance(final_trusted_win_total, bool)
            or not isinstance(final_trusted_win_total, int)
            or final_trusted_win_total != 0
        ):
            raise RoundTransactionError(
                "search handoff cannot coexist with a trusted win"
            )
        prior_regime = _replay_search_regime(
            rounds[:-1],
            rounds_root=rounds_root,
            policy_version=config.search_regime_policy_version,
            max_rounds=config.max_rounds,
        )
        if prior_regime.get("status") == (
            SEARCH_HANDOFF_REASON_REPRESENTATION_CHANGE
        ):
            raise RoundTransactionError(
                "search handoff must bind the first representation-change round"
            )
    return str(status)


def _durable_round_commit_matches(
    state: Any,
    *,
    round_number: int,
) -> bool:
    """Return whether the atomic completed-round state commit is durable.

    Operational mirrors (run metadata and append-only events) are written
    after the scientific state transaction.  If one of those writes fails, an
    exception handler must not roll the already-committed round back to a
    synthetic ``failed`` state.
    """

    rounds = state.get("rounds") if isinstance(state, dict) else None
    return bool(
        isinstance(rounds, list)
        and rounds
        and isinstance(rounds[-1], dict)
        and rounds[-1].get("round") == round_number
        and state.get("current_round") == round_number
        and state.get("pending_round") is None
        and state.get("round_phase") is None
        and state.get("round_transaction_version")
        in ROUND_TRANSACTION_SUPPORTED_PROTOCOL_VERSIONS
    )


def _failure_direction_observation(
    row: dict[str, Any],
    *,
    round_number: int,
) -> dict[str, Any] | None:
    """Extract only a machine-replayed, sealed low-weight logical witness."""

    # Feedback needs only a replayed upper-bound witness.  Suppress the
    # independent exact lower-bound solve here; the canonical audit gate owns
    # that expensive decision separately.
    outcome = classify_evaluation(row, fully_exact=lambda _row: False)
    if outcome is not AuditOutcome.THRESHOLD_REJECTED:
        return None
    attempt = row.get("audit_attempt")
    if (
        not isinstance(attempt, dict)
        or attempt.get("schema_version") != 2
        or attempt.get("round") != round_number
        or not isinstance(attempt.get("evidence"), dict)
    ):
        raise RoundTransactionError(
            "terminal failure-direction evidence is not a sealed formal audit"
        )

    source = "minimum_direction_witness"
    witness: Any = None
    if row.get("threshold_proof_source") == "symplectic_upper_bound":
        source = "symplectic_weight_witness"
        witness = row.get(source)
    else:
        details = row.get("milp_details")
        if isinstance(details, dict):
            witness = details.get(source)
    if not isinstance(witness, dict):
        return None

    side = witness.get("side")
    index = witness.get("index")
    weight = witness.get("weight")
    bits = witness.get("bits")
    n = row.get("n")
    k = row.get("k")
    if (
        side not in {"X", "Z"}
        or isinstance(index, bool)
        or not isinstance(index, int)
        or index < 0
        or isinstance(weight, bool)
        or not isinstance(weight, int)
        or weight < 1
        or isinstance(n, bool)
        or not isinstance(n, int)
        or n < 1
        or isinstance(k, bool)
        or not isinstance(k, int)
        or k < 1
        or not isinstance(bits, list)
        or len(bits) != n
        or any(type(bit) is not int or bit not in {0, 1} for bit in bits)
        or sum(bits) != weight
    ):
        raise RoundTransactionError(
            "sealed failure-direction witness has invalid binary evidence"
        )
    from evaluation.final_gate import minimum_winning_distance

    try:
        required = minimum_winning_distance(n, k)
    except ValueError:
        # This (n, k) cannot win at any physically allowed distance, so its
        # failure direction should not steer mutations of winner-capable codes.
        return None
    if weight >= required:
        return None
    normalized_bits = list(bits)
    observation = {
        "candidate_key": code_key(row),
        "source": source,
        "side": side,
        "index": index,
        "weight": weight,
        "minimum_winning_distance": required,
        "distance_deficit": required - weight,
        "bits": normalized_bits,
        "witness_sha256": _canonical_payload_sha256(witness),
    }
    if row.get("search_representation_id") == (
        PUBLISHED_VOLUME_ANSATZ_V3_REPRESENTATION_ID
    ):
        from evaluation.ansatz_witness_fingerprint import (
            negative_witness_algebraic_fingerprint,
        )

        observation["algebraic_fingerprint"] = (
            negative_witness_algebraic_fingerprint(
                row,
                sector=side,
                weight=weight,
                support=[
                    index for index, bit in enumerate(normalized_bits) if bit
                ],
                witness_sha256=observation["witness_sha256"],
            )
        )
    return observation


def _integer_mutation_weights(
    observations: list[dict[str, Any]],
) -> list[dict[str, Any]]:
    x_count = sum(item["side"] == "X" for item in observations)
    z_count = sum(item["side"] == "Z" for item in observations)
    if not observations:
        weights = (ADAPTIVE_MUTATION_TOTAL_WEIGHT, 0, 0, 0)
    else:
        remaining = (
            ADAPTIVE_MUTATION_TOTAL_WEIGHT
            - ADAPTIVE_MUTATION_EXPLORATION_FLOOR
        )
        votes = (x_count, z_count, min(x_count, z_count))
        denominator = sum(votes)
        allocated = [
            remaining * vote // denominator for vote in votes
        ]
        remainder = remaining - sum(allocated)
        order = sorted(
            range(len(votes)),
            key=lambda offset: (
                -(remaining * votes[offset] % denominator),
                offset,
            ),
        )
        for offset in order[:remainder]:
            allocated[offset] += 1
        weights = (
            ADAPTIVE_MUTATION_EXPLORATION_FLOOR,
            allocated[0],
            allocated[1],
            allocated[2],
        )
    return [
        {"tactic": tactic, "weight": weight}
        for tactic, weight in zip(ADAPTIVE_MUTATION_TACTICS, weights)
    ]


def _build_failure_direction_feedback(
    *,
    round_number: int,
    source_milp: dict[str, Any],
    audited_rows: list[dict[str, Any]],
) -> dict[str, Any]:
    observations_by_identity: dict[str, dict[str, Any]] = {}
    for row in audited_rows:
        observation = _failure_direction_observation(
            row, round_number=round_number
        )
        if observation is None:
            continue
        identity = _canonical_payload_sha256(observation)
        observations_by_identity[identity] = observation
    observations = sorted(
        observations_by_identity.values(),
        key=lambda item: (
            item["candidate_key"],
            0 if item["side"] == "X" else 1,
            item["weight"],
            item["witness_sha256"],
        ),
    )
    policy = {
        "schema_version": ADAPTIVE_MUTATION_POLICY_SCHEMA_VERSION,
        "source_round": round_number,
        "evidence_sha256": _canonical_payload_sha256(observations),
        "exploration_floor": ADAPTIVE_MUTATION_EXPLORATION_FLOOR,
        "total_weight": ADAPTIVE_MUTATION_TOTAL_WEIGHT,
        "tactics": _integer_mutation_weights(observations),
    }
    feedback: dict[str, Any] = {
        "schema_version": FAILURE_DIRECTION_FEEDBACK_SCHEMA_VERSION,
        "kind": FAILURE_DIRECTION_FEEDBACK_KIND,
        "round": round_number,
        "source_milp": source_milp,
        "observations": observations,
        "mutation_policy": policy,
    }
    feedback["payload_sha256"] = _canonical_payload_sha256(feedback)
    return feedback


def _failure_feedback_summary(
    feedback: dict[str, Any],
    artifact_identity: dict[str, Any],
) -> dict[str, Any]:
    source = feedback["source_milp"]
    return {
        "schema_version": FAILURE_DIRECTION_FEEDBACK_SCHEMA_VERSION,
        "artifact_sha256": artifact_identity["sha256"],
        "artifact_bytes": artifact_identity["bytes"],
        "payload_sha256": feedback["payload_sha256"],
        "source_milp_sha256": source["sha256"],
        "source_milp_bytes": source["bytes"],
        "source_milp_rows": source["rows"],
        "trusted_witnesses": len(feedback["observations"]),
    }


def _write_round_failure_direction_feedback(
    *,
    round_number: int,
    round_dir: Path,
    audited_rows: list[dict[str, Any]],
) -> dict[str, Any]:
    milp_path = round_dir / "milp.jsonl"
    if not milp_path.exists() and not audited_rows:
        atomic_write_jsonl(milp_path, [])
    if milp_path.is_symlink() or not milp_path.is_file():
        raise RoundTransactionError(
            "round MILP evidence must be a regular file before feedback"
        )
    milp_payload = milp_path.read_bytes()
    persisted_rows = _strict_jsonl_objects(
        milp_payload, "round MILP evidence"
    )
    persisted_identities = sorted(
        _canonical_payload_sha256(row) for row in persisted_rows
    )
    audited_identities = sorted(
        _canonical_payload_sha256(row) for row in audited_rows
    )
    if persisted_identities != audited_identities:
        raise RoundTransactionError(
            "failure-direction feedback rows disagree with round MILP evidence"
        )
    source = {
        "path": "milp.jsonl",
        "sha256": hashlib.sha256(milp_payload).hexdigest(),
        "bytes": len(milp_payload),
        "rows": len(persisted_rows),
    }
    feedback = _build_failure_direction_feedback(
        round_number=round_number,
        source_milp=source,
        audited_rows=persisted_rows,
    )
    payload = (
        _canonical_compact_json(feedback) + "\n"
    ).encode("utf-8")
    artifact_path = round_dir / "failure-direction-feedback.json"
    if artifact_path.is_symlink():
        raise RoundTransactionError(
            "failure-direction feedback artifact may not be a symlink"
        )
    if artifact_path.exists():
        if not artifact_path.is_file() or artifact_path.read_bytes() != payload:
            raise RoundTransactionError(
                "existing failure-direction feedback disagrees with canonical evidence"
            )
    else:
        atomic_write_bytes(artifact_path, payload)
    observed = _file_descriptor(
        artifact_path, "failure-direction feedback artifact"
    )
    expected_identity = {
        "sha256": hashlib.sha256(payload).hexdigest(),
        "bytes": len(payload),
    }
    if {
        "sha256": observed["sha256"],
        "bytes": observed["bytes"],
    } != expected_identity:
        raise RoundTransactionError(
            "failure-direction feedback identity is inconsistent"
        )
    return _failure_feedback_summary(feedback, expected_identity)


def _previous_round_failure_feedback_advisory(
    state: dict[str, Any],
    previous_number: int,
    previous_round_dir: Path,
) -> str | None:
    rounds = state.get("rounds")
    if not isinstance(rounds, list):
        return None
    previous_summary = next(
        (
            summary
            for summary in reversed(rounds)
            if isinstance(summary, dict)
            and summary.get("round") == previous_number
        ),
        None,
    )
    if (
        previous_summary is None
        or "failure_direction_feedback" not in previous_summary
    ):
        return None
    recorded = previous_summary["failure_direction_feedback"]
    expected_summary_fields = {
        "schema_version",
        "artifact_sha256",
        "artifact_bytes",
        "payload_sha256",
        "source_milp_sha256",
        "source_milp_bytes",
        "source_milp_rows",
        "trusted_witnesses",
    }
    if not isinstance(recorded, dict) or set(recorded) != expected_summary_fields:
        raise RoundTransactionError(
            "previous failure-direction feedback summary is invalid"
        )

    artifact_path = previous_round_dir / "failure-direction-feedback.json"
    if artifact_path.is_symlink() or not artifact_path.is_file():
        raise RoundTransactionError(
            "previous failure-direction feedback artifact is missing"
        )
    artifact_payload = artifact_path.read_bytes()
    artifact = _strict_json_object_bytes(
        artifact_payload, "previous failure-direction feedback"
    )
    unsealed = dict(artifact)
    payload_sha256 = unsealed.pop("payload_sha256", None)
    if (
        not isinstance(payload_sha256, str)
        or payload_sha256 != _canonical_payload_sha256(unsealed)
    ):
        raise RoundTransactionError(
            "previous failure-direction feedback self-hash is invalid"
        )

    milp_path = previous_round_dir / "milp.jsonl"
    if milp_path.is_symlink() or not milp_path.is_file():
        raise RoundTransactionError(
            "previous feedback source MILP evidence is missing"
        )
    milp_payload = milp_path.read_bytes()
    audited_rows = _strict_jsonl_objects(
        milp_payload, "previous round MILP evidence"
    )
    source = {
        "path": "milp.jsonl",
        "sha256": hashlib.sha256(milp_payload).hexdigest(),
        "bytes": len(milp_payload),
        "rows": len(audited_rows),
    }
    expected_artifact = _build_failure_direction_feedback(
        round_number=previous_number,
        source_milp=source,
        audited_rows=audited_rows,
    )
    if artifact != expected_artifact:
        raise RoundTransactionError(
            "previous failure-direction feedback disagrees with sealed evidence"
        )
    artifact_identity = {
        "sha256": hashlib.sha256(artifact_payload).hexdigest(),
        "bytes": len(artifact_payload),
    }
    expected_summary = _failure_feedback_summary(
        expected_artifact, artifact_identity
    )
    if recorded != expected_summary:
        raise RoundTransactionError(
            "previous failure-direction feedback summary was tampered"
        )

    observations = artifact["observations"]
    x_count = sum(item["side"] == "X" for item in observations)
    z_count = sum(item["side"] == "Z" for item in observations)
    weights = ", ".join(
        f"{item['tactic']}={item['weight']}"
        for item in artifact["mutation_policy"]["tactics"]
    )
    policy_mapping = {
        item["tactic"]: item["weight"]
        for item in artifact["mutation_policy"]["tactics"]
    }
    policy_line = (
        "QCODE_ADAPTIVE_MUTATION_POLICY_V1="
        + _canonical_compact_json(policy_mapping)
    )
    definitions_by_key = {
        code_key(row): row
        for row in audited_rows
        if isinstance(row, dict)
    }
    # Preserve the formal artifact schema while finally exposing the compact
    # geometry that the mutation model needs.  The full bit vectors remain in
    # the self-hashed feedback artifact; the prompt receives at most four
    # supports per side, in deterministic order, and can never reinterpret a
    # witness as positive distance evidence.
    bounded_geometry: list[dict[str, Any]] = []
    for side in ("X", "Z"):
        selected = [item for item in observations if item["side"] == side][:4]
        for item in selected:
            definition = definitions_by_key.get(item["candidate_key"], {})
            ell = definition.get("ell")
            m = definition.get("m")
            block_size = (
                ell * m
                if type(ell) is int and type(m) is int and ell > 0 and m > 0
                else None
            )
            support = [
                index
                for index, bit in enumerate(item["bits"])
                if bit == 1
            ]
            bounded_geometry.append({
                "candidate_key": item["candidate_key"],
                "ell": ell,
                "m": m,
                "geometry": definition.get("geometry"),
                "A_terms": definition.get("A_terms"),
                "B_terms": definition.get("B_terms"),
                "side": side,
                "weight": item["weight"],
                "minimum_winning_distance": item[
                    "minimum_winning_distance"
                ],
                "support": support,
                "block_support": [
                    {
                        "qubit": index,
                        "block": (
                            "unknown"
                            if block_size is None
                            else "left" if index < block_size else "right"
                        ),
                        "offset": (
                            index
                            if block_size is None or index < block_size
                            else index - block_size
                        ),
                    }
                    for index in support
                ],
                "witness_sha256": item["witness_sha256"],
                **(
                    {"algebraic_fingerprint": item["algebraic_fingerprint"]}
                    if isinstance(item.get("algebraic_fingerprint"), Mapping)
                    else {}
                ),
                "semantics": "negative_upper_bound_witness",
            })
    geometry_lines: list[str] = []
    if bounded_geometry:
        geometry_lines = [
            "- Concrete replayed supports (two-block BB qubit indices; negative "
            "evidence only):",
            "```json",
            json.dumps(
                bounded_geometry,
                ensure_ascii=False,
                indent=2,
                sort_keys=True,
            ),
            "```",
        ]
    return "\n".join([
        "## Machine-derived previous-round failure-direction advisory",
        (
            f"- Round: {previous_number}; trusted sealed low-weight logical "
            f"witnesses: {len(observations)} (X={x_count}, Z={z_count})."
        ),
        f"- Deterministic mutation weights: {weights}.",
        (
            "- Operational timeouts, unresolved audits, and reviewer text do "
            "not vote in this policy."
        ),
        (
            "- Use X/Z repair tactics to disrupt the corresponding replayed "
            "low-weight logical supports while retaining exploration."
        ),
        *geometry_lines,
        policy_line,
    ])


def _search_oracle_feedback_observation(
    row: dict[str, Any],
) -> dict[str, Any] | None:
    """Replay one Stage-2 SAT witness into negative-only BB geometry."""

    geometry = replay_search_oracle_witness_geometry(row)
    if geometry is None:
        return None
    oracle = row.get("low_weight_oracle")
    witness = oracle.get("witness") if isinstance(oracle, dict) else None
    if not isinstance(oracle, dict) or not isinstance(witness, dict):
        return None
    try:
        candidate_key = code_key(row)
        oracle_sha256 = _canonical_payload_sha256(oracle)
        witness_sha256 = _canonical_payload_sha256(witness)
        from evaluation.final_gate import minimum_winning_distance

        required = minimum_winning_distance(row["n"], row["k"])
    except (KeyError, TypeError, ValueError):
        return None
    weight = geometry["weight"]
    if weight >= required:
        return None
    observation = {
        "candidate_key": candidate_key,
        "oracle_evidence_sha256": oracle_sha256,
        "witness_sha256": witness_sha256,
        "minimum_winning_distance": required,
        "distance_deficit": required - weight,
        **geometry,
    }
    if row.get("search_representation_id") == (
        PUBLISHED_VOLUME_ANSATZ_V3_REPRESENTATION_ID
    ):
        from evaluation.ansatz_witness_fingerprint import (
            negative_witness_algebraic_fingerprint,
        )

        observation["algebraic_fingerprint"] = (
            negative_witness_algebraic_fingerprint(
                row,
                sector=str(geometry["side"]),
                weight=int(weight),
                support=list(geometry["support"]),
                witness_sha256=witness_sha256,
            )
        )
    return observation


def _search_oracle_witness_exceeds_current_cutoff(
    row: dict[str, Any],
    witness: dict[str, Any],
) -> bool:
    """Return a scheduling hint; this alone never authorizes migration."""

    n = row.get("n")
    k = row.get("k")
    weight = witness.get("weight")
    if (
        isinstance(n, bool)
        or not isinstance(n, int)
        or isinstance(k, bool)
        or not isinstance(k, int)
        or isinstance(weight, bool)
        or not isinstance(weight, int)
        or n < 1
        or not 1 <= k <= n
        or weight < 1
    ):
        return False
    try:
        from evaluation.evaluator import compute_challenge_rejection_cutoff

        cutoff = compute_challenge_rejection_cutoff(n, k, 12.0)
    except (ImportError, TypeError, ValueError):
        return False
    return weight > cutoff


def _round_allows_historical_scalar_cutoff_migration(
    round_dir: Path,
) -> bool:
    """Bind the narrow migration to a known committed buggy evaluator."""

    manifest_path = round_dir / "evolution-transaction.json"
    if manifest_path.is_symlink() or not manifest_path.is_file():
        return False
    transaction = _read_json_object(
        manifest_path,
        "historical scalar-cutoff transaction",
    )
    launch = transaction.get("launch_binding")
    evaluator = launch.get("evaluator") if isinstance(launch, dict) else None
    path = evaluator.get("path") if isinstance(evaluator, dict) else None
    sha256 = evaluator.get("sha256") if isinstance(evaluator, dict) else None
    return bool(
        transaction.get("mode") == "openevolve"
        and transaction.get("status") == "committed"
        and isinstance(path, str)
        and Path(path).name == "coset_openevolve_evaluator.py"
        and sha256 in HISTORICAL_SCALAR_ONLY_COSET_EVALUATOR_SHA256
    )


def _build_search_oracle_feedback(
    *,
    round_number: int,
    source_candidate_batch: dict[str, Any],
    candidate_rows: list[dict[str, Any]],
    allow_historical_scalar_cutoff: bool = False,
) -> dict[str, Any]:
    """Build bounded, replayed Stage-2 witness feedback deterministically."""

    queues: dict[str, list[dict[str, Any]]] = {"X": [], "Z": []}
    for row in candidate_rows:
        if not isinstance(row, dict):
            continue
        oracle = row.get("low_weight_oracle")
        witness = oracle.get("witness") if isinstance(oracle, dict) else None
        side = witness.get("sector") if isinstance(witness, dict) else None
        if side not in {"X", "Z"} and isinstance(witness, dict):
            side = witness.get("side")
        if (
            side not in {"X", "Z"}
            or row.get("search_status") != "terminal_negative"
            or row.get("threshold_rejection_proven") is not True
            or row.get("threshold_proof_source") != "low_weight_oracle"
            # Stage 1 may terminate a row against the stricter scalar-FOM
            # target without excluding the official Pareto/final gate.  Such
            # a witness remains durable scalar-negative evidence, but it must
            # not enter the final-gate repair feedback queue.
            or row.get("final_gate_excluded_by_upper_bound") is not True
            or not isinstance(oracle, dict)
            or oracle.get("outcome") != "SAT"
        ):
            continue
        if _search_oracle_witness_exceeds_current_cutoff(row, witness):
            historical_geometry = (
                replay_historical_scalar_only_search_oracle_witness_geometry(
                    row
                )
                if allow_historical_scalar_cutoff
                else None
            )
            if (
                historical_geometry is None
                or historical_geometry.get("side") != side
            ):
                raise RoundTransactionError(
                    "terminal Stage-2 low-weight oracle witness failed replay"
                )
            # The construction, oracle hash, bit vector, logical syndrome and
            # exact old scalar-only contract all replayed.  Omitting this
            # non-rejecting witness is negative-only and consumes no bounded
            # feedback slot; it grants no lower bound or promotion credit.
            continue
        queues[side].append(row)

    observations: list[dict[str, Any]] = []
    per_side = {"X": 0, "Z": 0}
    offsets = {"X": 0, "Z": 0}
    attempts = 0
    while attempts < SEARCH_ORACLE_FEEDBACK_MAX_ATTEMPTS:
        made_progress = False
        for side in ("X", "Z"):
            if per_side[side] >= SEARCH_ORACLE_FEEDBACK_MAX_PER_SIDE:
                continue
            queue = queues[side]
            offset = offsets[side]
            if offset >= len(queue):
                continue
            made_progress = True
            offsets[side] = offset + 1
            attempts += 1
            observation = _search_oracle_feedback_observation(queue[offset])
            if observation is None or observation["side"] != side:
                # A row carrying evaluator-owned terminal oracle markers must
                # replay. Silently consuming the bounded attempt budget would
                # let forged rows starve later genuine witnesses.
                raise RoundTransactionError(
                    "terminal Stage-2 low-weight oracle witness failed replay"
                )
            observations.append(observation)
            per_side[side] += 1
            if attempts >= SEARCH_ORACLE_FEEDBACK_MAX_ATTEMPTS:
                break
        if not made_progress:
            break
    observations.sort(key=lambda item: (
        0 if item["side"] == "X" else 1,
        item["weight"],
        item["candidate_key"],
        item["witness_sha256"],
    ))
    feedback: dict[str, Any] = {
        "schema_version": SEARCH_ORACLE_FEEDBACK_SCHEMA_VERSION,
        "kind": SEARCH_ORACLE_FEEDBACK_KIND,
        "round": round_number,
        "source_candidate_batch": source_candidate_batch,
        "replay_attempts": attempts,
        "observations": observations,
        "semantics": (
            "negative-only upper-bound witnesses; never distance lower-bound "
            "or promotion evidence"
        ),
    }
    feedback["payload_sha256"] = _canonical_payload_sha256(feedback)
    return feedback


def _search_oracle_feedback_summary(
    feedback: dict[str, Any],
    artifact_identity: dict[str, Any],
) -> dict[str, Any]:
    source = feedback["source_candidate_batch"]
    observations = feedback["observations"]
    return {
        "schema_version": SEARCH_ORACLE_FEEDBACK_SCHEMA_VERSION,
        "artifact_sha256": artifact_identity["sha256"],
        "artifact_bytes": artifact_identity["bytes"],
        "payload_sha256": feedback["payload_sha256"],
        "source_candidate_batch_sha256": source["sha256"],
        "source_candidate_batch_bytes": source["bytes"],
        "source_candidate_batch_rows": source["rows"],
        "replay_attempts": feedback["replay_attempts"],
        "replayed_witnesses": len(observations),
        "x_witnesses": sum(item["side"] == "X" for item in observations),
        "z_witnesses": sum(item["side"] == "Z" for item in observations),
    }


def _validate_search_oracle_feedback_summary(value: Any) -> dict[str, Any]:
    expected_fields = {
        "schema_version",
        "artifact_sha256",
        "artifact_bytes",
        "payload_sha256",
        "source_candidate_batch_sha256",
        "source_candidate_batch_bytes",
        "source_candidate_batch_rows",
        "replay_attempts",
        "replayed_witnesses",
        "x_witnesses",
        "z_witnesses",
    }
    if not isinstance(value, dict) or set(value) != expected_fields:
        raise RoundTransactionError(
            "search-oracle feedback summary fields are invalid"
        )
    integer_fields = (
        "artifact_bytes",
        "source_candidate_batch_bytes",
        "source_candidate_batch_rows",
        "replay_attempts",
        "replayed_witnesses",
        "x_witnesses",
        "z_witnesses",
    )
    if (
        value["schema_version"] != SEARCH_ORACLE_FEEDBACK_SCHEMA_VERSION
        or any(
            type(value[field]) is not int or value[field] < 0
            for field in integer_fields
        )
        or value["replay_attempts"] > SEARCH_ORACLE_FEEDBACK_MAX_ATTEMPTS
        or value["replayed_witnesses"]
        != value["x_witnesses"] + value["z_witnesses"]
        or value["x_witnesses"] > SEARCH_ORACLE_FEEDBACK_MAX_PER_SIDE
        or value["z_witnesses"] > SEARCH_ORACLE_FEEDBACK_MAX_PER_SIDE
        or any(
            not isinstance(value[field], str)
            or not re.fullmatch(r"[0-9a-f]{64}", value[field])
            for field in (
                "artifact_sha256",
                "payload_sha256",
                "source_candidate_batch_sha256",
            )
        )
    ):
        raise RoundTransactionError(
            "search-oracle feedback summary values are invalid"
        )
    return value


def _write_round_search_oracle_feedback(
    *,
    round_number: int,
    round_dir: Path,
    candidate_rows: list[dict[str, Any]],
) -> dict[str, Any]:
    batch_path = round_dir / "candidate-batch.jsonl"
    if batch_path.is_symlink() or not batch_path.is_file():
        raise RoundTransactionError(
            "candidate batch must be a regular file before oracle feedback"
        )
    batch_payload = batch_path.read_bytes()
    persisted_rows = _strict_jsonl_objects(
        batch_payload, "round candidate batch"
    )
    if persisted_rows != candidate_rows:
        raise RoundTransactionError(
            "search-oracle feedback rows disagree with committed batch"
        )
    source = {
        "path": "candidate-batch.jsonl",
        "sha256": hashlib.sha256(batch_payload).hexdigest(),
        "bytes": len(batch_payload),
        "rows": len(persisted_rows),
    }
    feedback = _build_search_oracle_feedback(
        round_number=round_number,
        source_candidate_batch=source,
        candidate_rows=persisted_rows,
        allow_historical_scalar_cutoff=(
            _round_allows_historical_scalar_cutoff_migration(round_dir)
        ),
    )
    payload = (_canonical_compact_json(feedback) + "\n").encode("utf-8")
    artifact_path = round_dir / "search-oracle-feedback.json"
    if artifact_path.is_symlink():
        raise RoundTransactionError(
            "search-oracle feedback artifact may not be a symlink"
        )
    if artifact_path.exists():
        if not artifact_path.is_file() or artifact_path.read_bytes() != payload:
            raise RoundTransactionError(
                "existing search-oracle feedback disagrees with replayed evidence"
            )
    else:
        atomic_write_bytes(artifact_path, payload)
    identity = {
        "sha256": hashlib.sha256(payload).hexdigest(),
        "bytes": len(payload),
    }
    observed = _file_descriptor(
        artifact_path, "search-oracle feedback artifact"
    )
    if {
        "sha256": observed["sha256"],
        "bytes": observed["bytes"],
    } != identity:
        raise RoundTransactionError(
            "search-oracle feedback artifact identity is inconsistent"
        )
    return _search_oracle_feedback_summary(feedback, identity)


def _previous_round_search_oracle_advisory(
    state: dict[str, Any],
    previous_number: int,
    previous_round_dir: Path,
) -> str | None:
    rounds = state.get("rounds")
    if not isinstance(rounds, list):
        return None
    previous_summary = next(
        (
            summary
            for summary in reversed(rounds)
            if isinstance(summary, dict)
            and summary.get("round") == previous_number
        ),
        None,
    )
    if previous_summary is None or "search_oracle_feedback" not in previous_summary:
        return None
    recorded = _validate_search_oracle_feedback_summary(
        previous_summary["search_oracle_feedback"]
    )
    if "candidate_diversity" not in previous_summary:
        raise RoundTransactionError(
            "search-oracle feedback lacks its candidate-batch binding"
        )
    _validate_round_diversity_evidence(
        previous_summary["candidate_diversity"],
        round_dir=previous_round_dir,
    )
    batch_path = previous_round_dir / "candidate-batch.jsonl"
    if batch_path.is_symlink() or not batch_path.is_file():
        raise RoundTransactionError(
            "previous search-oracle candidate batch is missing"
        )
    batch_payload = batch_path.read_bytes()
    candidate_rows = _strict_jsonl_objects(
        batch_payload, "previous search-oracle candidate batch"
    )
    source = {
        "path": "candidate-batch.jsonl",
        "sha256": hashlib.sha256(batch_payload).hexdigest(),
        "bytes": len(batch_payload),
        "rows": len(candidate_rows),
    }
    expected = _build_search_oracle_feedback(
        round_number=previous_number,
        source_candidate_batch=source,
        candidate_rows=candidate_rows,
        allow_historical_scalar_cutoff=(
            _round_allows_historical_scalar_cutoff_migration(
                previous_round_dir
            )
        ),
    )
    artifact_path = previous_round_dir / "search-oracle-feedback.json"
    if artifact_path.is_symlink() or not artifact_path.is_file():
        raise RoundTransactionError(
            "previous search-oracle feedback artifact is missing"
        )
    artifact_payload = artifact_path.read_bytes()
    artifact = _strict_json_object_bytes(
        artifact_payload, "previous search-oracle feedback"
    )
    if artifact != expected:
        raise RoundTransactionError(
            "previous search-oracle feedback does not replay"
        )
    identity = {
        "sha256": hashlib.sha256(artifact_payload).hexdigest(),
        "bytes": len(artifact_payload),
    }
    if recorded != _search_oracle_feedback_summary(expected, identity):
        raise RoundTransactionError(
            "previous search-oracle feedback summary was tampered"
        )
    observations = expected["observations"]
    if not observations:
        return None
    return "\n".join([
        "## Machine-replayed Stage-2 low-weight oracle witnesses",
        (
            f"- Round: {previous_number}; concrete witnesses: "
            f"{len(observations)} (X={recorded['x_witnesses']}, "
            f"Z={recorded['z_witnesses']})."
        ),
        (
            "- These are negative-only upper-bound witnesses. Repair or "
            "disrupt their BB support/coset/orbit geometry; never reward "
            "their weight as a distance estimate or lower bound."
        ),
        "```json",
        json.dumps(observations, ensure_ascii=False, indent=2, sort_keys=True),
        "```",
    ])


def _previous_round_diversity_advisory(
    state: dict[str, Any],
    previous_number: int,
) -> str | None:
    """Render fixed guidance only from a machine-derived durable summary."""

    rounds = state.get("rounds")
    if not isinstance(rounds, list):
        return None
    previous_summary = next(
        (
            summary
            for summary in reversed(rounds)
            if (
                isinstance(summary, dict)
                and summary.get("round") == previous_number
            )
        ),
        None,
    )
    if (
        previous_summary is None
        or "candidate_diversity" not in previous_summary
    ):
        # States written before this optional advisory field retain their
        # byte-for-byte context behavior.
        return None
    diversity = _validate_candidate_diversity_summary(
        previous_summary["candidate_diversity"]
    )
    support_splits = diversity["support_split_counts"]
    split_distribution = ", ".join(
        f"{split}={count}" for split, count in support_splits.items()
    ) or "none"
    mixed_counts = diversity["mixed_vs_nonmixed_counts"]
    mixed_distribution = ", ".join(
        f"{name}={mixed_counts[name]}"
        for name in ("mixed", "nonmixed", "unclassified")
    )
    dominant_count = max(support_splits.values(), default=0)
    dominant_splits = (
        ", ".join(
            split
            for split, count in support_splits.items()
            if count == dominant_count
        )
        if dominant_count
        else "none"
    )
    classified_mixed = {
        name: mixed_counts[name] for name in ("mixed", "nonmixed")
    }
    dominant_mixed_count = max(classified_mixed.values(), default=0)
    dominant_mixed = (
        ", ".join(
            name
            for name, count in classified_mixed.items()
            if count == dominant_mixed_count
        )
        if dominant_mixed_count
        else "none"
    )
    return "\n".join([
        "## Machine-derived previous-round diversity advisory",
        (
            f"- Round: {previous_number}; evidence basis: transaction-bound "
            "candidate source and canonical batch."
        ),
        (
            "- Raw source rows: "
            f"{diversity['raw_candidate_source_rows']}; canonical unique "
            f"batch rows: {diversity['canonical_unique_batch_rows']}."
        ),
        (
            f"- Exact duplicate rows: {diversity['duplicate_count']} "
            f"({float(diversity['duplicate_rate']):.2%})."
        ),
        f"- Support-split distribution (|A|+|B|): {split_distribution}.",
        f"- Mixed-vs-nonmixed distribution: {mixed_distribution}.",
        (
            "- Generator action: reduce exact repeats of prior definitions; "
            "spend candidate slots on genuinely distinct A/B supports."
        ),
        (
            "- Generator action: correct structural collapse by exploring "
            f"away from dominant support split(s) [{dominant_splits}] and "
            f"mixed class(es) [{dominant_mixed}]."
        ),
        (
            "- This is search-policy advice only. It is not proof evidence, "
            "a screening gate, or permission to omit the complete candidate "
            "pool from durable handoff."
        ),
    ])


def _review_artifact_binding(
    review_path: Path,
    review: dict[str, Any],
) -> dict[str, Any]:
    """Bind one validated reviewer artifact without granting machine authority."""

    if review_path.is_symlink() or not review_path.is_file():
        raise RoundTransactionError(
            f"review artifact is missing or unsafe: {review_path}"
        )
    payload = review_path.read_bytes()
    try:
        observed = validate_review(json.loads(payload))
    except (
        json.JSONDecodeError,
        OSError,
        UnicodeError,
        ValueError,
        ReviewError,
    ) as exc:
        raise RoundTransactionError(
            f"review artifact cannot be replayed: {review_path}: {exc}"
        ) from exc
    if observed != review:
        raise RoundTransactionError(
            "review artifact bytes disagree with the validated in-memory review"
        )
    is_current = {"schema_version", "search_action"}.issubset(observed)
    return {
        "schema_version": 1,
        "artifact_sha256": hashlib.sha256(payload).hexdigest(),
        "artifact_bytes": len(payload),
        "review_schema_version": 2 if is_current else 1,
        # Historical validation deliberately permits unknown fields.  Neither
        # a lone schema_version nor a lone search_action upgrades that object
        # to the current advisory contract.
        "search_action": (
            copy.deepcopy(observed["search_action"])
            if is_current
            else None
        ),
    }


def _validated_bound_round_review(
    summary: dict[str, Any],
    rounds_root: Path,
) -> dict[str, Any]:
    """Replay a historical review and verify its optional durable binding."""

    number = summary.get("round")
    if isinstance(number, bool) or not isinstance(number, int) or number < 1:
        raise RoundTransactionError("review summary has an invalid round number")
    review_path = rounds_root / f"round-{number:03d}" / "review.json"
    if review_path.is_symlink() or not review_path.is_file():
        raise RoundTransactionError(
            f"historical review artifact is missing or unsafe: {review_path}"
        )
    payload = review_path.read_bytes()
    try:
        review = validate_review(json.loads(payload))
    except (
        json.JSONDecodeError,
        OSError,
        UnicodeError,
        ValueError,
        ReviewError,
    ) as exc:
        raise RoundTransactionError(
            f"historical review artifact cannot be replayed: {review_path}: {exc}"
        ) from exc

    binding = summary.get("review_binding")
    if binding is None:
        # Completed runs created before binding v1 remain readable.  Their
        # free-form focus is consumed only through the legacy immediate-round
        # path and is never presented as a structured v2 search action.
        return review
    expected_fields = {
        "schema_version",
        "artifact_sha256",
        "artifact_bytes",
        "review_schema_version",
        "search_action",
    }
    if not isinstance(binding, dict) or set(binding) != expected_fields:
        raise RoundTransactionError("historical review binding is malformed")
    is_current = {"schema_version", "search_action"}.issubset(review)
    expected = {
        "schema_version": 1,
        "artifact_sha256": hashlib.sha256(payload).hexdigest(),
        "artifact_bytes": len(payload),
        "review_schema_version": 2 if is_current else 1,
        "search_action": (
            copy.deepcopy(review["search_action"])
            if is_current
            else None
        ),
    }
    if binding != expected:
        raise RoundTransactionError(
            "historical review artifact disagrees with its round binding"
        )
    return review


def _bound_executable_search_action(
    summary: Mapping[str, Any],
    rounds_root: Path,
    target_round: int,
) -> dict[str, Any] | None:
    """Return only an authenticated, accepted, in-horizon reviewer action.

    The summary's copied ``search_action`` remains durable audit metadata, but
    it is never execution authority.  Every consumer must replay the exact
    hash-bound ``review.json``, read the verdict from those authenticated
    bytes, and enforce the source action's finite target-round horizon.
    """

    if (
        isinstance(target_round, bool)
        or not isinstance(target_round, int)
        or target_round < 1
    ):
        raise RoundTransactionError(
            "reviewer action target round must be a positive integer"
        )
    review = _validated_bound_round_review(dict(summary), rounds_root)
    binding = summary.get("review_binding")
    if binding is None:
        return None
    if (
        not isinstance(binding, dict)
        or binding.get("review_schema_version") != 2
        or binding.get("search_action") is None
    ):
        return None
    if review.get("verdict") == "reject_round":
        return None
    action = review.get("search_action")
    if not isinstance(action, dict):
        raise RoundTransactionError(
            "bound reviewer-v2 search action is missing"
        )
    source_round = summary.get("round")
    horizon = action.get("horizon_rounds")
    if (
        isinstance(source_round, bool)
        or not isinstance(source_round, int)
        or source_round < 1
        or isinstance(horizon, bool)
        or not isinstance(horizon, int)
        or not 1 <= horizon <= 3
    ):
        raise RoundTransactionError(
            "bound reviewer action has an invalid round horizon"
        )
    if not source_round < target_round <= source_round + horizon:
        return None
    return copy.deepcopy(action)


def _seal_round_renderer_resolution(
    *,
    round_number: int,
    round_dir: Path,
    review: dict[str, Any],
    review_binding: dict[str, Any],
) -> dict[str, Any] | None:
    """Resolve reviewer registry IDs and durably bind the next round."""

    resolution_path = Path(os.path.abspath(
        round_dir / COSET_RENDERER_RESOLUTION_FILENAME
    ))
    search_action = _bound_executable_search_action(
        {
            "round": round_number,
            "review_binding": review_binding,
        },
        round_dir.parent,
        round_number + 1,
    )
    if search_action is None:
        if resolution_path.exists() or resolution_path.is_symlink():
            raise RoundTransactionError(
                "non-executable review has an unexpected renderer resolution "
                "artifact"
            )
        return None
    from humanize.coset_renderer_review import (
        ReviewerRendererResolutionError,
        resolve_reviewer_renderer_action,
        validate_reviewer_renderer_resolution,
    )

    if resolution_path.exists() or resolution_path.is_symlink():
        if resolution_path.is_symlink() or not resolution_path.is_file():
            raise RoundTransactionError(
                "renderer resolution artifact is not a regular file"
            )
        observed = _read_json_object(
            resolution_path, "renderer resolution artifact"
        )
        try:
            resolution = validate_reviewer_renderer_resolution(
                observed,
                search_action=search_action,
            )
        except ReviewerRendererResolutionError as exc:
            raise RoundTransactionError(
                "renderer resolution artifact disagrees after recovery"
            ) from exc
        if (
            resolution.get("source_round") != round_number
            or resolution.get("target_round") != round_number + 1
            or resolution.get("review_artifact_sha256")
            != review_binding["artifact_sha256"]
        ):
            raise RoundTransactionError(
                "renderer resolution recovery binding changed"
            )
    else:
        try:
            resolution = resolve_reviewer_renderer_action(
                search_action,
                source_round=round_number,
                target_round=round_number + 1,
                review_artifact_sha256=review_binding["artifact_sha256"],
            )
        except ReviewerRendererResolutionError as exc:
            raise RoundTransactionError(
                f"reviewer renderer proposal cannot be resolved: {exc}"
            ) from exc
        if resolution is None:
            return None
        atomic_write_json(resolution_path, resolution)
    descriptor = _file_descriptor(
        resolution_path, "reviewer renderer resolution"
    )
    return {
        **descriptor,
        "status": resolution["status"],
        "source_round": round_number,
        "target_round": round_number + 1,
        "activation_sha256": resolution[
            "renderer_activation_sha256"
        ],
        "resolution_sha256": resolution["resolution_sha256"],
    }


def _validated_bound_renderer_resolution(
    summary: Mapping[str, Any],
    rounds_root: Path,
) -> dict[str, Any] | None:
    """Replay a summary's optional reviewer-to-renderer resolution."""

    binding = summary.get(COSET_RENDERER_RESOLUTION_SUMMARY_FIELD)
    if binding is None:
        return None
    expected_fields = {
        "path",
        "sha256",
        "bytes",
        "status",
        "source_round",
        "target_round",
        "activation_sha256",
        "resolution_sha256",
    }
    if type(binding) is not dict or set(binding) != expected_fields:
        raise RoundTransactionError("renderer resolution binding is malformed")
    source_round = summary.get("round")
    expected_path = Path(os.path.abspath(
        rounds_root
        / f"round-{source_round:03d}"
        / COSET_RENDERER_RESOLUTION_FILENAME
    )) if type(source_round) is int and source_round > 0 else None
    if expected_path is None or binding.get("path") != str(expected_path):
        raise RoundTransactionError("renderer resolution path is not round-bound")
    observed_descriptor = _file_descriptor(
        expected_path, "reviewer renderer resolution"
    )
    if any(
        binding.get(name) != observed_descriptor[name]
        for name in ("path", "sha256", "bytes")
    ):
        raise RoundTransactionError("renderer resolution bytes changed")
    review = _validated_bound_round_review(dict(summary), rounds_root)
    review_binding = summary.get("review_binding")
    if not isinstance(review_binding, dict):
        raise RoundTransactionError("renderer resolution has no review binding")
    resolution = _read_json_object(
        expected_path, "reviewer renderer resolution"
    )
    from humanize.coset_renderer_review import (
        ReviewerRendererResolutionError,
        validate_reviewer_renderer_resolution,
    )

    try:
        replayed = validate_reviewer_renderer_resolution(
            resolution,
            search_action=review["search_action"],
        )
    except (KeyError, ReviewerRendererResolutionError) as exc:
        raise RoundTransactionError(
            f"renderer resolution cannot be replayed: {exc}"
        ) from exc
    expected_metadata = {
        "status": replayed["status"],
        "source_round": replayed["source_round"],
        "target_round": replayed["target_round"],
        "activation_sha256": replayed["renderer_activation_sha256"],
        "resolution_sha256": replayed["resolution_sha256"],
    }
    if any(binding.get(name) != value for name, value in expected_metadata.items()):
        raise RoundTransactionError(
            "renderer resolution summary metadata changed"
        )
    if replayed["review_artifact_sha256"] != review_binding.get(
        "artifact_sha256"
    ):
        raise RoundTransactionError(
            "renderer resolution review binding changed"
        )
    executable_action = _bound_executable_search_action(
        summary,
        rounds_root,
        replayed["target_round"],
    )
    if executable_action is None:
        # Old controllers could seal a renderer resolution even when the
        # authenticated reviewer rejected the round.  Keep validating that
        # historical artifact for audit, but never return it to an executable
        # consumer; the next round reconstructs the trusted default renderer.
        return None
    if executable_action != review["search_action"]:
        raise RoundTransactionError(
            "renderer resolution action is outside its executable binding"
        )
    return replayed


def _validated_renderer_expansion_handoff(
    state: Mapping[str, Any],
    rounds_root: Path,
) -> str | None:
    """Validate a legacy terminal reviewer handoff without reinterpreting it.

    New runs retain rejected reviewer proposals as round-bound diagnostics and
    continue under the trusted default renderer.  States committed by the old
    controller remain terminal and replayable through this compatibility gate.
    """

    round_value = state.get("renderer_expansion_handoff_at_round")
    digest_value = state.get("renderer_expansion_handoff_sha256")
    if round_value is None and digest_value is None:
        return None
    if (
        type(round_value) is not int
        or round_value < 1
        or type(digest_value) is not str
        or re.fullmatch(r"[0-9a-f]{64}", digest_value) is None
        or state.get("pending_round") is not None
        or state.get("current_round") != round_value
        or state.get("status") not in {
            "search-complete",
            "incomplete-unresolved",
        }
    ):
        raise RoundTransactionError(
            "renderer expansion handoff state is malformed"
        )
    rounds = state.get("rounds")
    if (
        not isinstance(rounds, list)
        or not rounds
        or not isinstance(rounds[-1], dict)
        or rounds[-1].get("round") != round_value
    ):
        raise RoundTransactionError(
            "renderer expansion handoff is not the final completed round"
        )
    resolution = _validated_bound_renderer_resolution(
        rounds[-1], rounds_root
    )
    if (
        resolution is None
        or resolution.get("status")
        != "representation_expansion_handoff"
        or resolution.get("renderer_activation") is not None
        or resolution.get("resolution_sha256") != digest_value
        or resolution.get("representation_expansion_handoff", {}).get(
            "execution_permitted"
        ) is not False
    ):
        raise RoundTransactionError(
            "renderer expansion handoff does not replay exactly"
        )
    return str(state["status"])


def _v2_evolution_search_action(action: Any) -> dict[str, Any]:
    """Project a replayed reviewer action onto the executable-prompt allowlist.

    ``_validated_bound_round_review`` has already replayed the complete strict
    reviewer-v2 artifact and its byte binding.  The complete object remains in
    ``review.json`` for audit, but only closed enums, bounded integers, and
    evidence identifiers may cross into the prompt that produces executable
    evolved Python.  In particular, free-form rationale is intentionally not
    part of this projection.
    """

    if not isinstance(action, dict):
        raise RoundTransactionError(
            "bound reviewer-v2 search action is not an object"
        )
    required = {
        "schema_version",
        "advisory_only",
        "intent",
        "horizon_rounds",
        "focus",
        "evidence_refs",
        "rationale",
    }
    if set(action) != required:
        raise RoundTransactionError(
            "bound reviewer-v2 search action fields are invalid"
        )
    return {
        "intent": copy.deepcopy(action["intent"]),
        "horizon_rounds": copy.deepcopy(action["horizon_rounds"]),
        "focus": copy.deepcopy(action["focus"]),
        "evidence_refs": copy.deepcopy(action["evidence_refs"]),
    }


def _freeze_round_context(
    config: FlowConfig,
    state: dict[str, Any],
    round_dir: Path,
) -> Path:
    context_path = Path(os.path.abspath(round_dir / "search-context.md"))
    if context_path.is_symlink() or context_path.exists():
        raise RoundTransactionError(
            f"refusing to overwrite an unbound evolution context: {context_path}"
        )
    memory_path = (
        config.repo_dir
        / "results"
        / "humanize"
        / config.run_id
        / "bitlesson.md"
    )
    prompt_safe_reviewer_v2 = config.search_regime_policy_version in {2, 3, 4}
    # Policy-v2 contexts can produce executable evolved Python.  Reviewer
    # lessons and the accumulated BitLesson are deliberately retained on disk
    # for audit but cannot enter that prompt as free text.  Policy v1 keeps its
    # historical byte-for-byte behavior for durable resume compatibility.
    if prompt_safe_reviewer_v2:
        context_parts: list[str] = []
    else:
        context_parts = (
            [memory_path.read_text()] if memory_path.is_file() else []
        )
    failure_advisory: str | None = None
    rounds = state.get("rounds", [])
    if not isinstance(rounds, list) or any(
        not isinstance(summary, dict) for summary in rounds
    ):
        raise RoundTransactionError("durable round history must be a list of objects")
    previous_number = state.get("current_round")
    if (
        not isinstance(previous_number, bool)
        and isinstance(previous_number, int)
        and previous_number > 0
    ):
        previous_review_path = (
            round_dir.parent
            / f"round-{previous_number:03d}"
            / "review.json"
        )
        previous_summary = next(
            (
                summary
                for summary in reversed(rounds)
                if summary.get("round") == previous_number
            ),
            None,
        )
        if not prompt_safe_reviewer_v2:
            if previous_summary is not None and (
                previous_review_path.is_file()
                or previous_summary.get("review_binding") is not None
            ):
                review = _validated_bound_round_review(
                    previous_summary,
                    round_dir.parent,
                )
                focus = review.get("recommended_focus", [])
                if focus:
                    if not isinstance(focus, list):
                        raise RoundTransactionError(
                            "previous reviewer focus must be a list"
                        )
                    context_parts.append(
                        "Previous independent reviewer focus:\n- "
                        + "\n- ".join(map(str, focus))
                    )
            elif previous_review_path.is_file():
                # Pre-summary legacy state: preserve the immediate advisory
                # path, but never promote it into the structured rolling
                # action window.
                review = validate_review(
                    _read_json_object(previous_review_path, "previous review")
                )
                focus = review.get("recommended_focus", [])
                if focus:
                    context_parts.append(
                        "Previous independent reviewer focus:\n- "
                        + "\n- ".join(map(str, focus))
                    )

        # Reviewer actions have finite rolling horizons, but overlapping
        # focus dimensions are not additive. Collect only authenticated,
        # accepted actions here, then project each dimension from its newest
        # source below. This retains older non-conflicting advice without
        # presenting competing support-split or mutation-tactic directives.
        active_structured_actions: list[dict[str, Any]] = []
        for summary in rounds[-3:]:
            binding = summary.get("review_binding")
            if binding is None:
                continue
            search_action = _bound_executable_search_action(
                summary,
                round_dir.parent,
                previous_number + 1,
            )
            if search_action is None:
                continue
            renderer_resolution = _validated_bound_renderer_resolution(
                summary,
                round_dir.parent,
            )
            if (
                renderer_resolution is not None
                and renderer_resolution.get("status")
                == "representation_expansion_handoff"
            ):
                active_structured_actions.append({
                    "round": summary["round"],
                    "renderer_handoff": True,
                    "search_action": search_action,
                })
                continue
            active_structured_actions.append({
                "round": summary["round"],
                "renderer_handoff": False,
                "search_action": search_action,
            })

        from humanize.coset_renderer_review import (
            REVIEWER_RENDERER_FOCUS_DIMENSIONS,
        )

        shadowed_dimensions: set[str] = set()
        newest_first: list[dict[str, Any]] = []
        for active in reversed(active_structured_actions):
            search_action = copy.deepcopy(active["search_action"])
            focus = search_action["focus"]
            if active["renderer_handoff"] is True:
                # Renderer-control focus from the accepted handoff remains
                # sealed audit metadata and cannot enter an executable prompt.
                # It nevertheless supersedes every older renderer-control
                # focus: the machine will use its source-owned default
                # activation, so reviving an older split or registry request
                # would invite guaranteed preflight rejection. The handoff's
                # own non-renderer focus remains executable advisory data and
                # must enter the common newest-first filter below so it also
                # supersedes older advice on those dimensions.
                shadowed_dimensions.update(
                    REVIEWER_RENDERER_FOCUS_DIMENSIONS
                )
                focus = [
                    item for item in focus
                    if item["dimension"]
                    not in REVIEWER_RENDERER_FOCUS_DIMENSIONS
                ]
                if not focus:
                    continue
            focus_dimensions = {
                item["dimension"] for item in focus
            }
            filtered_focus = [
                item for item in focus
                if item["dimension"] not in shadowed_dimensions
            ]
            shadowed_dimensions.update(focus_dimensions)
            if focus and not filtered_focus:
                continue
            search_action["focus"] = filtered_focus
            if prompt_safe_reviewer_v2:
                search_action = _v2_evolution_search_action(search_action)
            newest_first.append({
                "round": active["round"],
                "advisory_only": True,
                "search_action": search_action,
            })
        structured_actions = list(reversed(newest_first))
        if structured_actions:
            context_parts.append("\n".join([
                "## Independent reviewer search advisories",
                (
                    "- For each focus dimension, only the newest authenticated, "
                    "accepted, in-horizon advice is projected; it cannot alter "
                    "machine "
                    "regimes, mutation weights, budgets, proof gates, or stop "
                    "decisions."
                ),
                "```json",
                json.dumps(
                    structured_actions,
                    ensure_ascii=False,
                    indent=2,
                    sort_keys=True,
                ),
                "```",
            ]))
        advisory = _previous_round_diversity_advisory(
            state, previous_number
        )
        if advisory is not None:
            context_parts.append(advisory)
        failure_advisory = _previous_round_failure_feedback_advisory(
            state,
            previous_number,
            round_dir.parent / f"round-{previous_number:03d}",
        )
        if failure_advisory is not None:
            context_parts.append(failure_advisory)
        oracle_advisory = _previous_round_search_oracle_advisory(
            state,
            previous_number,
            round_dir.parent / f"round-{previous_number:03d}",
        )
        if oracle_advisory is not None:
            context_parts.append(oracle_advisory)
    regime_enabled = (
        config.search_regime_policy_version in {2, 3, 4}
        or state.get("search_regime") is not None
        or any(
            isinstance(summary, dict) and "sealed_exact_audit" in summary
            for summary in rounds
        )
    )
    if regime_enabled:
        regime = _replay_search_regime(
            rounds,
            rounds_root=round_dir.parent,
            policy_version=config.search_regime_policy_version,
            max_rounds=(
                config.max_rounds
                if config.search_regime_policy_version
                in SEARCH_REGIME_BUDGET_BOUND_POLICY_VERSIONS
                else None
            ),
        )
        recorded_regime = state.get("search_regime")
        if recorded_regime is not None and recorded_regime != regime:
            raise RoundTransactionError(
                "durable search regime disagrees with sealed round evidence"
            )
        regime_prefix = SEARCH_REGIME_PREFIX_BY_POLICY_VERSION[
            config.search_regime_policy_version
        ]
        regime_marker = regime_prefix + _canonical_compact_json(regime)
        context_parts.append("\n".join([
            "## Machine-derived search regime",
            (
                "- This policy is recomputed only from durable sealed exact "
                "audits and transaction-bound candidate diversity."
            ),
            regime_marker,
        ]))
    context_text = "\n\n".join(context_parts) + "\n"
    policy_token = "QCODE_ADAPTIVE_MUTATION_POLICY_V1"
    policy_marker = policy_token + "="
    expected_policy_lines = 1 if failure_advisory is not None else 0
    observed_policy_lines = sum(
        line.startswith(policy_marker)
        for line in context_text.splitlines()
    )
    if (
        observed_policy_lines != expected_policy_lines
        or context_text.count(policy_marker) != expected_policy_lines
        or context_text.count(policy_token) != expected_policy_lines
    ):
        raise RoundTransactionError(
            "reviewer or memory text contains the reserved adaptive policy marker"
        )
    regime_prefixes = tuple(SEARCH_REGIME_PREFIX_BY_POLICY_VERSION.values())
    regime_tokens = tuple(prefix.removesuffix("=") for prefix in regime_prefixes)
    observed_regime_lines = sum(
        any(line.startswith(prefix) for prefix in regime_prefixes)
        for line in context_text.splitlines()
    )
    expected_regime_lines = int(regime_enabled)
    if (
        observed_regime_lines != expected_regime_lines
        or sum(context_text.count(prefix) for prefix in regime_prefixes)
        != expected_regime_lines
        or sum(context_text.count(token) for token in regime_tokens)
        != expected_regime_lines
    ):
        raise RoundTransactionError(
            "reviewer or memory text contains the reserved search-regime marker"
        )
    payload = context_text.encode("utf-8")
    identity = atomic_write_bytes(context_path, payload)
    observed = _file_descriptor(context_path, "evolution humanize context")
    if (
        observed["sha256"] != identity["sha256"]
        or observed["bytes"] != identity["bytes"]
    ):
        raise RoundTransactionError(
            "frozen evolution context identity is inconsistent"
        )
    return context_path


def _quarantine_orphan_round_context(round_dir: Path) -> Path | None:
    """Preserve a context left by a crash before manifest publication."""
    context_path = Path(os.path.abspath(round_dir / "search-context.md"))
    if not context_path.exists() and not context_path.is_symlink():
        return None
    if context_path.is_symlink() or not context_path.is_file():
        raise RoundTransactionError(
            f"orphan evolution context is not a regular file: {context_path}"
        )
    payload = context_path.read_bytes()
    digest = hashlib.sha256(payload).hexdigest()
    index = 1
    while True:
        destination = round_dir / (
            f"orphan-search-context-{digest[:16]}-{index:03d}.md"
        )
        if not destination.exists() and not destination.is_symlink():
            break
        index += 1
    context_path.replace(destination)
    _fsync_directory(round_dir)
    descriptor = _file_descriptor(
        destination, "orphan evolution context archive"
    )
    if (
        descriptor["sha256"] != digest
        or descriptor["bytes"] != len(payload)
    ):
        raise RoundTransactionError(
            "orphan evolution context archive changed during quarantine"
        )
    return destination


def _fresh_evolution_bindings(
    config: FlowConfig,
    state: dict[str, Any],
    round_dir: Path,
) -> tuple[dict[str, dict[str, Any]], dict[str, Any]]:
    _materialize_round_renderer_activation(config, state, round_dir)
    context_path = _freeze_round_context(config, state, round_dir)
    codex_identity: dict[str, Any] | None = None
    version: str | None = None
    cwd: str | None = None
    if config.codex_cli:
        codex_identity, version, cwd = _fresh_codex_binding(
            config,
            round_dir=round_dir,
        )
    launch = _evolution_launch_binding(
        config,
        context_path=context_path,
        codex_executable=codex_identity,
    )
    invocation = _fresh_invocation_binding(
        config,
        codex_identity=codex_identity,
        codex_version=version,
        codex_cwd=cwd,
        launch_binding=launch,
    )
    _validate_invocation_binding(config, invocation, launch)
    return launch, invocation


def _slice_iterations_sha256(start_iteration: int, count: int) -> str:
    iterations = list(range(start_iteration, start_iteration + count))
    encoded = json.dumps(iterations, separators=(",", ":")).encode("utf-8")
    return hashlib.sha256(encoded).hexdigest()


def _candidate_log_range_identity(
    candidate_log: Path,
    *,
    start_offset: int,
    end_offset: int | None = None,
) -> dict[str, Any]:
    """Recover the shared WAL and snapshot one exact candidate byte range."""
    from evolve.openevolve_evaluator import (
        CandidateLogWriteError,
        candidate_log_range_identity,
    )

    try:
        return candidate_log_range_identity(
            candidate_log.absolute(),
            start_offset=start_offset,
            end_offset=end_offset,
        )
    except (OSError, CandidateLogWriteError) as exc:
        raise RoundTransactionError(
            f"candidate log WAL/range validation failed: {exc}"
        ) from exc


def _search_portfolio_contract_from_config(
    config_path: Path,
) -> tuple[int, tuple[str, ...], dict[str, int]] | None:
    """Return the source-bound v2/v3 portfolio contract, if enabled."""

    try:
        value = yaml.safe_load(config_path.read_text())
    except (OSError, UnicodeError, yaml.YAMLError) as exc:
        raise RoundTransactionError(
            f"cannot inspect search portfolio config: {config_path}: {exc}"
        ) from exc
    if not isinstance(value, dict):
        raise RoundTransactionError(
            "evolution config must contain a YAML object"
        )
    if SEARCH_PORTFOLIO_CONFIG_KEY not in value:
        return None
    marker = value[SEARCH_PORTFOLIO_CONFIG_KEY]
    schema_version = (
        marker.get("schema_version") if isinstance(marker, dict) else None
    )
    if (
        not isinstance(marker, dict)
        or set(marker) != {"enabled", "schema_version"}
        or marker["enabled"] is not True
        or type(schema_version) is not int
        or schema_version not in SEARCH_PORTFOLIO_SPECS
    ):
        raise RoundTransactionError(
            "qcode_search_portfolio marker must be exactly "
            "{enabled: true, schema_version: 2|3}"
        )
    dimensions, bins = SEARCH_PORTFOLIO_SPECS[schema_version]
    database = value.get("database")
    if (
        not isinstance(database, dict)
        or type(database.get("num_islands")) is not int
        or database["num_islands"] != SEARCH_PORTFOLIO_ISLAND_COUNT
        or database.get("feature_dimensions")
        != list(dimensions)
        or not isinstance(database.get("feature_bins"), dict)
        or set(database["feature_bins"]) != set(bins)
        or any(
            type(database["feature_bins"].get(name)) is not int
            or database["feature_bins"][name] != expected
            for name, expected in bins.items()
        )
    ):
        raise RoundTransactionError(
            "search portfolio database geometry must be exactly "
            f"five islands with the schema-v{schema_version} 5/6/3 MAP grid"
        )
    return schema_version, tuple(dimensions), dict(bins)


def _search_portfolio_enabled_from_config(config_path: Path) -> bool:
    return _search_portfolio_contract_from_config(config_path) is not None


def _coset_search_portfolio_contract_from_config(
    config_path: Path,
) -> tuple[int, tuple[str, ...], dict[str, int]] | None:
    """Return the exact typed-coset MAP contract selected by ``config_path``.

    Schema-7 submission witnesses carry the selected parent program and its
    code hash.  Treating this config as an ordinary non-portfolio run drops
    those fields at the Humanize trust boundary, so keep the producer's
    marker and registry-owned geometry mirrored here and fail closed on drift.
    """

    try:
        value = yaml.safe_load(config_path.read_text())
    except (OSError, UnicodeError, yaml.YAMLError) as exc:
        raise RoundTransactionError(
            f"cannot inspect coset search portfolio config: {config_path}: "
            f"{exc}"
        ) from exc
    if not isinstance(value, dict):
        raise RoundTransactionError(
            "evolution config must contain a YAML object"
        )
    if COSET_SEARCH_PORTFOLIO_CONFIG_KEY not in value:
        return None
    marker = value[COSET_SEARCH_PORTFOLIO_CONFIG_KEY]
    if type(marker) is not dict or set(marker) != {
        "enabled",
        "schema_version",
        "representation_id",
        "checkpoint_compatibility_group",
    }:
        raise RoundTransactionError(
            "qcode_coset_search_portfolio fields are not exact"
        )
    representation_id = marker.get("representation_id")
    if type(representation_id) is not str:
        raise RoundTransactionError(
            "coset search portfolio representation_id is invalid"
        )
    try:
        contract = coset_renderer_portfolio_contract(representation_id)
    except (TypeError, ValueError) as exc:
        raise RoundTransactionError(
            "coset search portfolio representation is not registered"
        ) from exc
    expected_marker = {
        "enabled": True,
        "schema_version": contract["map_schema_version"],
        "representation_id": contract["representation_id"],
        "checkpoint_compatibility_group": contract[
            "checkpoint_compatibility_group"
        ],
    }
    if type(marker) is not dict or marker != expected_marker:
        raise RoundTransactionError(
            "qcode_coset_search_portfolio must exactly select the current "
            "representation, descriptor schema, and compatibility group"
        )
    if value.get(COSET_PROOF_LADDER_CONFIG_KEY) != (
        proof_ladder_config_contract()
    ):
        raise RoundTransactionError(
            "qcode_coset_stage1_proof_ladder must exactly match the current "
            "proof ladder and budget contract"
        )
    database = value.get("database")
    if (
        not isinstance(database, dict)
        or type(database.get("num_islands")) is not int
        or database["num_islands"]
        != contract["num_islands"]
        or database.get("feature_dimensions")
        != list(contract["feature_dimensions"])
        or not isinstance(database.get("feature_bins"), dict)
        or set(database["feature_bins"]) != set(contract["feature_bins"])
        or any(
            type(database["feature_bins"].get(name)) is not int
            or database["feature_bins"][name] != expected
            for name, expected in contract["feature_bins"].items()
        )
    ):
        raise RoundTransactionError(
            "coset search portfolio database geometry disagrees with its "
            "registered renderer"
        )
    return (
        int(contract["map_schema_version"]),
        tuple(contract["feature_dimensions"]),
        dict(contract["feature_bins"]),
    )


def _legacy_v4_search_portfolio_enabled_from_config(
    config_path: Path,
) -> bool:
    """Validate the frozen schema-v4 portfolio config without upgrading it."""

    try:
        value = yaml.safe_load(config_path.read_text())
    except (OSError, UnicodeError, yaml.YAMLError) as exc:
        raise RoundTransactionError(
            f"cannot inspect legacy search portfolio config: {config_path}: "
            f"{exc}"
        ) from exc
    if not isinstance(value, dict):
        raise RoundTransactionError(
            "legacy evolution config must contain a YAML object"
        )
    if SEARCH_PORTFOLIO_CONFIG_KEY not in value:
        return False
    marker = value[SEARCH_PORTFOLIO_CONFIG_KEY]
    if (
        not isinstance(marker, dict)
        or set(marker) != {"enabled", "schema_version"}
        or marker.get("enabled") is not True
        or type(marker.get("schema_version")) is not int
        or marker.get("schema_version")
        != LEGACY_V4_SEARCH_PORTFOLIO_SCHEMA_VERSION
    ):
        raise RoundTransactionError(
            "schema-v4 witness requires the frozen legacy portfolio marker"
        )
    database = value.get("database")
    if (
        not isinstance(database, dict)
        or type(database.get("num_islands")) is not int
        or database.get("num_islands") != SEARCH_PORTFOLIO_ISLAND_COUNT
        or database.get("feature_dimensions")
        != list(LEGACY_V4_SEARCH_PORTFOLIO_FEATURE_DIMENSIONS)
        or not isinstance(database.get("feature_bins"), dict)
        or database["feature_bins"]
        != LEGACY_V4_SEARCH_PORTFOLIO_FEATURE_BINS
    ):
        raise RoundTransactionError(
            "schema-v4 witness requires the frozen legacy 6/6/5 MAP grid"
        )
    return True


def _adaptive_mutation_policy_from_context(
    context_path: Path,
) -> dict[str, int]:
    try:
        text = context_path.read_text()
    except (OSError, UnicodeError) as exc:
        raise RoundTransactionError(
            f"cannot read adaptive mutation context: {context_path}: {exc}"
        ) from exc
    marker = ADAPTIVE_MUTATION_POLICY_PREFIX[:-1]
    encoded_policies: list[str] = []
    for line in text.splitlines():
        if marker not in line:
            continue
        if not line.startswith(ADAPTIVE_MUTATION_POLICY_PREFIX):
            raise RoundTransactionError(
                "adaptive mutation policy marker must start a line exactly"
            )
        encoded_policies.append(
            line[len(ADAPTIVE_MUTATION_POLICY_PREFIX):]
        )
    if not encoded_policies:
        return dict(DEFAULT_ADAPTIVE_MUTATION_POLICY)
    if len(encoded_policies) != 1:
        raise RoundTransactionError(
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

    encoded = encoded_policies[0]
    try:
        value = json.loads(
            encoded,
            parse_constant=reject_constant,
            object_pairs_hook=reject_duplicates,
        )
    except (TypeError, json.JSONDecodeError, ValueError) as exc:
        raise RoundTransactionError(
            "adaptive mutation policy is not valid JSON"
        ) from exc
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
        raise RoundTransactionError(
            "adaptive mutation policy must contain the exact tactic "
            "vocabulary, total weight 1000, and exploration floor 250"
        )
    if encoded != _canonical_compact_json(value):
        raise RoundTransactionError(
            "adaptive mutation policy must use canonical compact JSON"
        )
    return {name: value[name] for name in ADAPTIVE_MUTATION_TACTICS}


def _adaptive_mutation_policy_sha256(policy: dict[str, int]) -> str:
    return hashlib.sha256(
        _canonical_compact_json(policy).encode("utf-8")
    ).hexdigest()


def _search_regime_policy_from_context(
    context_path: Path,
) -> dict[str, Any]:
    """Replay the canonical machine regime consumed by the launcher."""

    try:
        text = context_path.read_text()
    except (OSError, UnicodeError) as exc:
        raise RoundTransactionError(
            f"cannot read search regime context: {context_path}: {exc}"
        ) from exc
    marker_specs = tuple(
        (
            version,
            prefix,
            prefix.removesuffix("="),
        )
        for version, prefix in SEARCH_REGIME_PREFIX_BY_POLICY_VERSION.items()
    )
    encoded_values: list[tuple[int, str]] = []
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
            raise RoundTransactionError(
                "search regime marker must start a line exactly"
            )
        version, prefix = exact[0]
        encoded_values.append((version, line[len(prefix):]))
    if not encoded_values:
        return {"schema_version": 1, "status": "normal"}
    if len(encoded_values) != 1 or len(encoded_values[0][1]) > 16_384:
        raise RoundTransactionError(
            "humanize context has an invalid search regime marker"
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

    policy_version, encoded = encoded_values[0]
    try:
        value = json.loads(
            encoded,
            parse_constant=reject_constant,
            object_pairs_hook=reject_duplicates,
        )
    except (TypeError, json.JSONDecodeError, ValueError) as exc:
        raise RoundTransactionError(
            "search regime marker is not valid JSON"
        ) from exc
    if (
        not isinstance(value, dict)
        or value.get("schema_version") != SEARCH_REGIME_SCHEMA_VERSION
        or value.get("status") not in (
            SEARCH_REGIME_V1_STATUSES
            if policy_version == 1
            else SEARCH_REGIME_V2_STATUSES
        )
        or encoded != _canonical_compact_json(value)
    ):
        raise RoundTransactionError(
            "search regime marker has invalid schema/status/canonical form"
        )
    if policy_version == 1:
        # Preserve the historical V1 object exactly.  Old witnesses and
        # artifacts therefore retain their byte-for-byte policy semantics.
        return value
    if "policy_version" in value:
        raise RoundTransactionError(
            "versioned search regime marker must encode its version in the prefix"
        )
    return {**value, "policy_version": policy_version}


def _search_island_schedule(
    iterations: int,
    regime_status: str,
) -> tuple[int, ...]:
    """Mirror the launcher's deterministic mechanism quota schedule."""

    if (
        isinstance(iterations, bool)
        or not isinstance(iterations, int)
        or iterations < 1
        or regime_status not in SEARCH_REGIME_STATUSES
    ):
        raise RoundTransactionError("search island schedule inputs are invalid")
    counts = [iterations // SEARCH_PORTFOLIO_ISLAND_COUNT] * (
        SEARCH_PORTFOLIO_ISLAND_COUNT
    )
    for island in range(iterations % SEARCH_PORTFOLIO_ISLAND_COUNT):
        counts[island] += 1
    order = list(range(SEARCH_PORTFOLIO_ISLAND_COUNT))
    if regime_status == "representation_change_required" and iterations >= 5:
        # A production 25-iteration slice is [3, 3, 3, 3, 13].  Smaller
        # diagnostic slices retain at least one proposal per mechanism while
        # assigning all remaining capacity to representation-changing restart.
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
        raise RoundTransactionError(
            "search island schedule construction was inconsistent"
        )
    return tuple(schedule)


def _adaptive_mutation_tactic_from_parent_hash(
    policy: dict[str, int],
    *,
    parent_code_sha256: str,
    iteration: int,
) -> str:
    policy_sha256 = _adaptive_mutation_policy_sha256(policy)
    digest = hashlib.sha256(
        (
            policy_sha256
            + "\0"
            + parent_code_sha256
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
    raise RoundTransactionError(
        "adaptive mutation tactic selection was inconsistent"
    )


def _portfolio_parent_code_sha256(
    program_id: str,
    *,
    base_checkpoint: dict[str, Any] | None,
    result_checkpoint: dict[str, Any],
    cache: dict[str, str],
) -> str:
    observed = cache.get(program_id)
    if observed is not None:
        return observed
    parent_path: Path | None = None
    for checkpoint in (result_checkpoint, base_checkpoint):
        if checkpoint is None:
            continue
        candidate_path = (
            Path(checkpoint["path"])
            / "programs"
            / f"{program_id}.json"
        )
        if candidate_path.is_file():
            parent_path = candidate_path
            break
    if parent_path is None:
        raise RoundTransactionError(
            "portfolio parent is absent from both slice checkpoints"
        )
    parent = _read_json_object(
        parent_path, "portfolio parent checkpoint program"
    )
    parent_code = parent.get("code")
    if parent.get("id") != program_id or not isinstance(parent_code, str):
        raise RoundTransactionError(
            "portfolio parent checkpoint program is invalid"
        )
    observed = hashlib.sha256(parent_code.encode("utf-8")).hexdigest()
    cache[program_id] = observed
    return observed


def _validated_live_coset_policy_code_identity(
    code: Any,
    *,
    expected_catalog_sha256: Any,
    expected_representation_id: str | None = None,
) -> dict[str, str]:
    """Validate current typed policy text while preserving its raw hash."""

    if (
        not isinstance(code, str)
        or not code
        or not isinstance(expected_catalog_sha256, str)
        or re.fullmatch(r"[0-9a-f]{64}", expected_catalog_sha256) is None
    ):
        raise RoundTransactionError(
            "coset policy code identity is invalid"
        )
    from evolve.coset_policy_dispatch import (
        CosetPolicyDispatchError,
        parse_and_render_registered_policy,
    )

    try:
        rendered = parse_and_render_registered_policy(code)
    except (CosetPolicyDispatchError, UnicodeError, ValueError) as exc:
        raise RoundTransactionError(
            "coset checkpoint policy is invalid"
        ) from exc
    catalog_sha256 = rendered.document.get("action_catalog_sha256")
    representation_id = rendered.descriptor.representation_id
    if catalog_sha256 != expected_catalog_sha256:
        raise RoundTransactionError(
            "coset checkpoint policy catalog binding changed"
        )
    if (
        expected_representation_id is not None
        and representation_id != expected_representation_id
    ):
        raise RoundTransactionError(
            "coset checkpoint policy renderer epoch changed"
        )
    return {
        "code_sha256": hashlib.sha256(code.encode("utf-8")).hexdigest(),
        "policy_sha256": rendered.policy_sha256,
        "policy_catalog_sha256": str(catalog_sha256),
        "representation_id": representation_id,
    }


def _validate_checkpoint_activation_bridge_preflight(
    report: Any,
    *,
    base_checkpoint: dict[str, Any],
    result_checkpoint: dict[str, Any],
    launch_binding: Mapping[str, Any],
    invocation_binding: Mapping[str, Any],
    candidate_log: Path,
    candidate_start_offset: int,
    candidate_end_offset: int,
    expected_representation_id: str | None,
) -> None:
    """Strictly replay one renderer-v3 activation bridge root.

    The bridge is the sole newly evaluated root that replaces a checkpoint
    whose policies are all incompatible with the next round's sealed
    activation.  Its report is intentionally self-contained: replay binds the
    immutable source population, the exact activation and support split, the
    root's canonical policy lineage, and the candidate-log bytes written by
    the fresh evaluation.
    """

    legacy_fields = {
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
    current_fields = (
        legacy_fields
        - {"approved_support_split"}
        | {"approved_support_splits", "root_support_split"}
    )
    report_schema = (
        report.get("schema_version") if isinstance(report, dict) else None
    )
    if report_schema == 3:
        expected_fields = legacy_fields
    elif report_schema == 4:
        expected_fields = current_fields
    else:
        expected_fields = set()
    contract_id = report.get("contract_id") if isinstance(report, dict) else None
    source_programs = (
        report.get("source_programs") if isinstance(report, dict) else None
    )
    if (
        type(report) is not dict
        or set(report) != expected_fields
        or report_schema not in {3, 4}
        or report.get("status") != "completed"
        or report.get("contract_version") != 2
        or type(contract_id) is not int
        or contract_id < 0
        or report.get("mode")
        != "typed-json-dsl-activation-bridge-root"
        or report.get("source_checkpoint") != base_checkpoint
        or type(source_programs) is not int
        or source_programs < 1
        or source_programs != base_checkpoint.get("programs")
        or report.get("target_programs") != 1
        or expected_representation_id != COSET_REPRESENTATION_ID_V3
    ):
        raise RoundTransactionError(
            "checkpoint activation bridge report is invalid"
        )

    hashes = (
        report.get("source_program_set_sha256"),
        report.get("root_policy_sha256"),
        report.get("root_code_sha256"),
        report.get("activation_sha256"),
    )
    if any(
        type(value) is not str
        or re.fullmatch(r"[0-9a-f]{64}", value) is None
        for value in hashes
    ):
        raise RoundTransactionError(
            "checkpoint activation bridge hashes are invalid"
        )

    activation_descriptor = launch_binding.get(
        "coset_renderer_activation"
    )
    if type(activation_descriptor) is not dict:
        raise RoundTransactionError(
            "checkpoint activation bridge has no launch activation"
        )
    activation_path = Path(str(activation_descriptor.get("path", "")))
    if (
        _file_descriptor(
            activation_path, "checkpoint activation bridge renderer activation"
        )
        != activation_descriptor
    ):
        raise RoundTransactionError(
            "checkpoint activation bridge launch activation changed"
        )
    activation_document = _validated_coset_renderer_activation_file(
        activation_path
    )
    invocation_activation = invocation_binding.get(
        COSET_RENDERER_ACTIVATION_SHA256_BINDING_FIELD
    )
    if (
        invocation_activation != activation_document["activation_sha256"]
        or report["activation_sha256"] != invocation_activation
    ):
        raise RoundTransactionError(
            "checkpoint activation bridge activation binding changed"
        )

    if report_schema == 3:
        approved_splits = [report.get("approved_support_split")]
        root_split = report.get("approved_support_split")
    else:
        approved_splits = report.get("approved_support_splits")
        root_split = report.get("root_support_split")
    def valid_split(split: Any) -> bool:
        return (
            type(split) is list
            and len(split) == 2
            and all(type(value) is int and value > 0 for value in split)
        )
    if (
        type(approved_splits) is not list
        or not approved_splits
        or (report_schema == 3 and len(approved_splits) != 1)
        or (report_schema == 4 and len(approved_splits) <= 1)
        or any(not valid_split(split) for split in approved_splits)
        or len({tuple(split) for split in approved_splits})
        != len(approved_splits)
        or not valid_split(root_split)
        or root_split != approved_splits[0]
        or activation_document.get("approved_support_splits")
        != approved_splits
    ):
        raise RoundTransactionError(
            "checkpoint activation bridge support split is invalid"
        )

    bridge_range = report.get("bridge_candidate_range")
    if (
        type(bridge_range) is not dict
        or set(bridge_range)
        != {
            "path",
            "start_offset",
            "end_offset",
            "sha256",
            "bytes",
            "wal_clean",
        }
        or bridge_range.get("path") != str(candidate_log.resolve())
        or type(bridge_range.get("start_offset")) is not int
        or type(bridge_range.get("end_offset")) is not int
        or bridge_range["start_offset"] != candidate_start_offset
        or not (
            candidate_start_offset
            <= bridge_range["end_offset"]
            <= candidate_end_offset
        )
        or bridge_range.get("bytes")
        != bridge_range["end_offset"] - bridge_range["start_offset"]
        or type(bridge_range.get("sha256")) is not str
        or re.fullmatch(r"[0-9a-f]{64}", bridge_range["sha256"])
        is None
        or bridge_range.get("wal_clean") is not True
    ):
        raise RoundTransactionError(
            "checkpoint activation bridge candidate range is invalid"
        )
    observed_range = _candidate_log_range_identity(
        candidate_log,
        start_offset=bridge_range["start_offset"],
        end_offset=bridge_range["end_offset"],
    )
    if any(
        observed_range[name] != bridge_range[name]
        for name in (
            "path",
            "start_offset",
            "end_offset",
            "sha256",
            "bytes",
            "wal_clean",
        )
    ):
        raise RoundTransactionError(
            "checkpoint activation bridge candidate range changed"
        )

    observed_source_program_set_sha256 = _checkpoint_program_set_sha256(
        base_checkpoint
    )
    if observed_source_program_set_sha256 != report[
        "source_program_set_sha256"
    ]:
        raise RoundTransactionError(
            "checkpoint activation bridge source population changed"
        )

    root_program_id = report.get("root_program_id")
    if type(root_program_id) is not str:
        raise RoundTransactionError(
            "checkpoint activation bridge root id is invalid"
        )
    root_program_path = (
        Path(result_checkpoint["path"])
        / "programs"
        / f"{root_program_id}.json"
    )
    if root_program_path.is_symlink() or not root_program_path.is_file():
        raise RoundTransactionError(
            "checkpoint activation bridge root is absent"
        )
    root_program = _read_json_object(
        root_program_path, "checkpoint activation bridge root"
    )
    root_code = root_program.get("code")
    root_identity = _validated_live_coset_policy_code_identity(
        root_code,
        expected_catalog_sha256=invocation_binding.get(
            "qcode_action_catalog_sha256"
        ),
        expected_representation_id=expected_representation_id,
    )

    from evolve.coset_policy_dispatch import (
        CosetPolicyDispatchError,
        parse_and_render_activated_policy,
    )
    from evolve.coset_search_contract import (
        trusted_coset_renderer_activation_from_document,
    )

    try:
        activated_root = parse_and_render_activated_policy(
            root_code,
            trusted_coset_renderer_activation_from_document(
                activation_document
            ),
        )
        observed_split = list(activated_root.policy.support_split)
    except (CosetPolicyDispatchError, TypeError, ValueError) as exc:
        raise RoundTransactionError(
            "checkpoint activation bridge root is not activation-compatible"
        ) from exc

    root_binding = {
        "schema_version": 1 if report_schema == 3 else 2,
        "kind": "qcode-coset-activation-bridge-root",
        "source_checkpoint_sha256": base_checkpoint["sha256"],
        "source_program_set_sha256": observed_source_program_set_sha256,
        "source_last_iteration": base_checkpoint["last_iteration"],
        "activation_sha256": activation_document["activation_sha256"],
        "policy_sha256": root_identity["policy_sha256"],
        "code_sha256": root_identity["code_sha256"],
        "contract_id": contract_id,
    }
    if report_schema == 3:
        root_binding["approved_support_split"] = root_split
    else:
        root_binding["approved_support_splits"] = approved_splits
        root_binding["root_support_split"] = root_split
    expected_root_id = "coset-activation-root-" + hashlib.sha256(
        json.dumps(
            root_binding,
            sort_keys=True,
            separators=(",", ":"),
            allow_nan=False,
        ).encode("utf-8")
    ).hexdigest()[:32]
    root_metadata = root_program.get("metadata")
    if (
        root_program_id != expected_root_id
        or root_program.get("id") != root_program_id
        or root_program.get("parent_id") is not None
        or root_program.get("iteration_found")
        != base_checkpoint["last_iteration"]
        or root_program.get("language") != "json"
        or root_identity["policy_sha256"] != report["root_policy_sha256"]
        or root_identity["code_sha256"] != report["root_code_sha256"]
        or activated_root.policy_sha256 != report["root_policy_sha256"]
        or observed_split != root_split
        or not isinstance(root_metadata, dict)
        or root_metadata.get("checkpoint_activation_bridge") != root_binding
    ):
        raise RoundTransactionError(
            "checkpoint activation bridge lineage is inconsistent"
        )


def _coset_parent_program_identity(
    program_id: str,
    *,
    attempt_iteration: int,
    expected_catalog_sha256: Any,
    expected_representation_id: str,
    base_checkpoint: dict[str, Any] | None,
    result_checkpoint: dict[str, Any],
    cache: dict[str, dict[str, Any]],
) -> dict[str, Any]:
    """Replay one typed-coset parent from the sealed checkpoint lineage."""

    cached = cache.get(program_id)
    if cached is not None:
        if cached["iteration_found"] >= attempt_iteration:
            raise RoundTransactionError(
                "coset submission parent is not older than its child"
            )
        return cached

    identities: list[dict[str, Any]] = []
    for checkpoint in (base_checkpoint, result_checkpoint):
        if checkpoint is None:
            continue
        parent_path = (
            Path(checkpoint["path"])
            / "programs"
            / f"{program_id}.json"
        )
        if parent_path.is_symlink():
            raise RoundTransactionError(
                "coset submission parent may not be a symlink"
            )
        if not parent_path.exists():
            continue
        if not parent_path.is_file():
            raise RoundTransactionError(
                "coset submission parent is not a regular file"
            )
        parent = _read_json_object(
            parent_path, "coset submission parent checkpoint program"
        )
        parent_code = parent.get("code")
        parent_iteration = parent.get("iteration_found")
        if (
            parent.get("id") != program_id
            or not isinstance(parent_code, str)
            or not parent_code
            or parent.get("language") != "json"
            or isinstance(parent_iteration, bool)
            or not isinstance(parent_iteration, int)
            or parent_iteration < 0
        ):
            raise RoundTransactionError(
                "coset submission parent checkpoint program is invalid"
            )
        policy_identity = _validated_live_coset_policy_code_identity(
            parent_code,
            expected_catalog_sha256=expected_catalog_sha256,
            expected_representation_id=expected_representation_id,
        )
        identities.append({
            "code_sha256": policy_identity["code_sha256"],
            "iteration_found": parent_iteration,
            "parent_id": parent.get("parent_id"),
        })

    if not identities:
        raise RoundTransactionError(
            "coset submission parent is absent from both slice checkpoints"
        )
    identity = identities[0]
    if any(candidate != identity for candidate in identities[1:]):
        raise RoundTransactionError(
            "coset submission parent differs between slice checkpoints"
        )
    if identity["iteration_found"] >= attempt_iteration:
        raise RoundTransactionError(
            "coset submission parent is not older than its child"
        )
    cache[program_id] = identity
    return identity


def _validate_coset_search_portfolio_witness(
    attempts: list[dict[str, Any]],
    *,
    invocation_binding: dict[str, Any],
    base_checkpoint: dict[str, Any] | None,
    result_checkpoint: dict[str, Any],
    island_count: int,
    expected_representation_id: str,
) -> None:
    """Validate the schema-7 parent and registered coset submission trace."""

    if type(island_count) is not int or island_count < 1:
        raise RoundTransactionError("coset witness island count is invalid")

    attempt_fields = {
        "iteration",
        "island_id",
        "result",
        "coset_parent_program_id",
        "coset_parent_code_sha256",
    }
    expected_catalog_sha256 = invocation_binding.get(
        "qcode_action_catalog_sha256"
    )
    parent_cache: dict[str, dict[str, Any]] = {}
    for attempt in attempts:
        if set(attempt) != attempt_fields:
            raise RoundTransactionError(
                "coset submission witness fields are not exact"
            )
        iteration = attempt["iteration"]
        parent_program_id = attempt["coset_parent_program_id"]
        parent_code_sha256 = attempt["coset_parent_code_sha256"]
        if (
            type(iteration) is not int
            or not isinstance(parent_program_id, str)
            or re.fullmatch(r"[A-Za-z0-9._-]+", parent_program_id) is None
            or parent_program_id in {".", ".."}
            or not isinstance(parent_code_sha256, str)
            or re.fullmatch(r"[0-9a-f]{64}", parent_code_sha256) is None
        ):
            raise RoundTransactionError(
                "coset submission parent identity is invalid"
            )
        expected_island = (
            iteration - 1
        ) % island_count
        if attempt["island_id"] != expected_island:
            raise RoundTransactionError(
                "coset submission island schedule is inconsistent"
            )
        observed = _coset_parent_program_identity(
            parent_program_id,
            attempt_iteration=iteration,
            expected_catalog_sha256=expected_catalog_sha256,
            expected_representation_id=expected_representation_id,
            base_checkpoint=base_checkpoint,
            result_checkpoint=result_checkpoint,
            cache=parent_cache,
        )
        if observed["code_sha256"] != parent_code_sha256:
            raise RoundTransactionError(
                "coset submission parent code hash changed"
            )


def _validate_coset_result_program_lineage(
    outcome: dict[str, Any],
    attempt: dict[str, Any],
    *,
    result_checkpoint: dict[str, Any],
    expected_catalog_sha256: Any,
    expected_representation_id: str,
) -> None:
    """Bind a successful coset outcome back to its checkpointed parent."""

    program_id = outcome.get("program_id")
    if (
        not isinstance(program_id, str)
        or re.fullmatch(r"[A-Za-z0-9._-]+", program_id) is None
        or program_id in {".", ".."}
    ):
        raise RoundTransactionError(
            "coset result program identity is invalid"
        )
    program_path = (
        Path(result_checkpoint["path"])
        / "programs"
        / f"{program_id}.json"
    )
    if program_path.is_symlink() or not program_path.is_file():
        raise RoundTransactionError(
            "coset result program is absent from the result checkpoint"
        )
    program = _read_json_object(
        program_path, "coset result checkpoint program"
    )
    code = program.get("code")
    if (
        program.get("id") != program_id
        or program.get("iteration_found") != outcome["iteration"]
        or program.get("parent_id")
        != attempt["coset_parent_program_id"]
        or program.get("language") != "json"
        or not isinstance(code, str)
        or not code
    ):
        raise RoundTransactionError(
            "coset result checkpoint lineage is inconsistent"
        )
    _validated_live_coset_policy_code_identity(
        code,
        expected_catalog_sha256=expected_catalog_sha256,
        expected_representation_id=expected_representation_id,
    )


def _validate_legacy_v4_search_portfolio_witness(
    witness: dict[str, Any],
    attempts: list[dict[str, Any]],
    *,
    launch_binding: dict[str, dict[str, Any]],
    base_checkpoint: dict[str, Any] | None,
    result_checkpoint: dict[str, Any],
    start_iteration: int,
    count: int,
) -> None:
    """Validate schema-v4 using only its frozen portfolio-v1 semantics."""

    config_path = Path(launch_binding["config"]["path"])
    context_path = Path(launch_binding["context"]["path"])
    enabled = _legacy_v4_search_portfolio_enabled_from_config(config_path)
    portfolio = witness.get("search_portfolio")
    base_attempt_fields = {"iteration", "island_id", "result"}
    if not enabled:
        if portfolio is not None:
            raise RoundTransactionError(
                "legacy non-portfolio config has a portfolio witness contract"
            )
        if any(set(attempt) != base_attempt_fields for attempt in attempts):
            raise RoundTransactionError(
                "legacy non-portfolio submission fields are not exact"
            )
        return

    policy = _adaptive_mutation_policy_from_context(context_path)
    policy_sha256 = _adaptive_mutation_policy_sha256(policy)
    expected_counts = {
        role: sum(
            (iteration - start_iteration) % SEARCH_PORTFOLIO_ISLAND_COUNT
            == island_id
            for iteration in range(start_iteration, start_iteration + count)
        )
        for island_id, role in enumerate(LEGACY_V4_SEARCH_PORTFOLIO_ROLES)
    }
    expected_portfolio = {
        "schema_version": LEGACY_V4_SEARCH_PORTFOLIO_SCHEMA_VERSION,
        "island_count": SEARCH_PORTFOLIO_ISLAND_COUNT,
        "roles": list(LEGACY_V4_SEARCH_PORTFOLIO_ROLES),
        "policy_sha256": policy_sha256,
        "role_submission_counts": expected_counts,
    }
    if (
        not isinstance(portfolio, dict)
        or set(portfolio) != set(expected_portfolio)
        or type(portfolio.get("schema_version")) is not int
        or type(portfolio.get("island_count")) is not int
        or not isinstance(portfolio.get("roles"), list)
        or not isinstance(portfolio.get("policy_sha256"), str)
        or not isinstance(portfolio.get("role_submission_counts"), dict)
        or set(portfolio["role_submission_counts"])
        != set(LEGACY_V4_SEARCH_PORTFOLIO_ROLES)
        or any(
            type(value) is not int or value < 0
            for value in portfolio["role_submission_counts"].values()
        )
        or portfolio != expected_portfolio
    ):
        raise RoundTransactionError(
            "legacy schema-v4 search portfolio witness is inconsistent"
        )

    portfolio_attempt_fields = base_attempt_fields | {
        "search_portfolio_schema_version",
        "search_policy_sha256",
        "search_role",
        "search_tactic",
        "search_parent_program_id",
        "search_parent_code_sha256",
        "search_role_submission_counts",
    }
    parent_code_hashes: dict[str, str] = {}
    for attempt in attempts:
        if set(attempt) != portfolio_attempt_fields:
            raise RoundTransactionError(
                "legacy portfolio submission witness fields are not exact"
            )
        iteration = attempt["iteration"]
        expected_island = (
            iteration - start_iteration
        ) % SEARCH_PORTFOLIO_ISLAND_COUNT
        expected_role = LEGACY_V4_SEARCH_PORTFOLIO_ROLES[expected_island]
        parent_program_id = attempt["search_parent_program_id"]
        parent_code_sha256 = attempt["search_parent_code_sha256"]
        if (
            not isinstance(parent_program_id, str)
            or not re.fullmatch(r"[A-Za-z0-9._-]+", parent_program_id)
            or parent_program_id in {".", ".."}
            or not isinstance(parent_code_sha256, str)
            or not re.fullmatch(r"[0-9a-f]{64}", parent_code_sha256)
            or type(attempt["search_portfolio_schema_version"]) is not int
            or not isinstance(
                attempt["search_role_submission_counts"], dict
            )
            or any(
                type(value) is not int or value < 0
                for value in attempt[
                    "search_role_submission_counts"
                ].values()
            )
            or attempt["search_role_submission_counts"] != expected_counts
        ):
            raise RoundTransactionError(
                "legacy portfolio submission identity is invalid"
            )
        observed_parent_hash = _portfolio_parent_code_sha256(
            parent_program_id,
            base_checkpoint=base_checkpoint,
            result_checkpoint=result_checkpoint,
            cache=parent_code_hashes,
        )
        expected_tactic = _adaptive_mutation_tactic_from_parent_hash(
            policy,
            parent_code_sha256=parent_code_sha256,
            iteration=iteration,
        )
        if (
            observed_parent_hash != parent_code_sha256
            or attempt["island_id"] != expected_island
            or attempt["search_portfolio_schema_version"]
            != LEGACY_V4_SEARCH_PORTFOLIO_SCHEMA_VERSION
            or attempt["search_policy_sha256"] != policy_sha256
            or attempt["search_role"] != expected_role
            or attempt["search_tactic"] != expected_tactic
        ):
            raise RoundTransactionError(
                "legacy schema-v4 portfolio semantics are inconsistent"
            )


def _validate_search_portfolio_witness(
    witness: dict[str, Any],
    attempts: list[dict[str, Any]],
    *,
    witness_schema: int,
    launch_binding: dict[str, dict[str, Any]],
    invocation_binding: dict[str, Any],
    base_checkpoint: dict[str, Any] | None,
    result_checkpoint: dict[str, Any],
    start_iteration: int,
    count: int,
) -> bool:
    config_path = Path(launch_binding["config"]["path"])
    coset_contract = _coset_search_portfolio_contract_from_config(
        config_path
    )
    if coset_contract is not None:
        if (
            witness_schema != EVOLUTION_SLICE_WITNESS_SCHEMA_VERSION
            or invocation_binding.get("qcode_evaluator_kind")
            != "coset-two-block"
        ):
            raise RoundTransactionError(
                "coset search portfolio requires a schema-7 coset witness"
            )
        if _search_portfolio_contract_from_config(config_path) is not None:
            raise RoundTransactionError(
                "BB and coset search portfolios cannot both be enabled"
            )
        if witness.get("search_portfolio") is not None:
            raise RoundTransactionError(
                "coset search portfolio cannot carry a BB portfolio witness"
            )
        config_document = yaml.safe_load(config_path.read_text())
        coset_marker = config_document[COSET_SEARCH_PORTFOLIO_CONFIG_KEY]
        representation_id = coset_marker["representation_id"]
        renderer_contract = coset_renderer_portfolio_contract(
            representation_id
        )
        _validate_coset_search_portfolio_witness(
            attempts,
            invocation_binding=invocation_binding,
            base_checkpoint=base_checkpoint,
            result_checkpoint=result_checkpoint,
            island_count=int(renderer_contract["num_islands"]),
            expected_representation_id=representation_id,
        )
        return True
    if witness_schema == EVOLUTION_SLICE_WITNESS_PREVIOUS_SCHEMA_VERSION:
        _validate_legacy_v4_search_portfolio_witness(
            witness,
            attempts,
            launch_binding=launch_binding,
            base_checkpoint=base_checkpoint,
            result_checkpoint=result_checkpoint,
            start_iteration=start_iteration,
            count=count,
        )
        return False
    if witness_schema not in EVOLUTION_SLICE_WITNESS_MECHANISM_SCHEMA_VERSIONS:
        if "search_portfolio" in witness:
            raise RoundTransactionError(
                "pre-v4 witness cannot contain a portfolio contract"
            )
        base_attempt_fields = {"iteration", "island_id", "result"}
        if any(set(attempt) != base_attempt_fields for attempt in attempts):
            raise RoundTransactionError(
                "legacy submission witness fields are not exact"
            )
        return False
    context_path = Path(launch_binding["context"]["path"])
    portfolio_contract = _search_portfolio_contract_from_config(config_path)
    enabled = portfolio_contract is not None
    portfolio = witness.get("search_portfolio")
    base_attempt_fields = {"iteration", "island_id", "result"}
    if not enabled:
        if portfolio is not None:
            raise RoundTransactionError(
                "non-portfolio config has a portfolio witness contract"
            )
        if any(set(attempt) != base_attempt_fields for attempt in attempts):
            raise RoundTransactionError(
                "non-portfolio submission witness fields are not exact"
            )
        return False
    assert portfolio_contract is not None
    portfolio_schema, feature_dimensions, _feature_bins = portfolio_contract

    policy = _adaptive_mutation_policy_from_context(context_path)
    policy_sha256 = _adaptive_mutation_policy_sha256(policy)
    regime = _search_regime_policy_from_context(context_path)
    regime_status = str(regime["status"])
    schedule = _search_island_schedule(count, regime_status)
    expected_counts = {
        role: schedule.count(island_id)
        for island_id, role in enumerate(SEARCH_PORTFOLIO_ROLES)
    }
    expected_portfolio = {
        "schema_version": portfolio_schema,
        "island_count": SEARCH_PORTFOLIO_ISLAND_COUNT,
        "roles": list(SEARCH_PORTFOLIO_ROLES),
        "feature_dimensions": list(feature_dimensions),
        "regime_status": regime_status,
        "policy_sha256": policy_sha256,
        "role_submission_counts": expected_counts,
    }
    if (
        not isinstance(portfolio, dict)
        or set(portfolio) != set(expected_portfolio)
        or type(portfolio.get("schema_version")) is not int
        or type(portfolio.get("island_count")) is not int
        or not isinstance(portfolio.get("roles"), list)
        or not isinstance(portfolio.get("feature_dimensions"), list)
        or not isinstance(portfolio.get("regime_status"), str)
        or not isinstance(portfolio.get("policy_sha256"), str)
        or not isinstance(portfolio.get("role_submission_counts"), dict)
        or set(portfolio["role_submission_counts"])
        != set(SEARCH_PORTFOLIO_ROLES)
        or any(
            type(value) is not int or value < 0
            for value in portfolio["role_submission_counts"].values()
        )
    ):
        raise RoundTransactionError(
            "OpenEvolve search portfolio witness contract is invalid"
        )
    if portfolio != expected_portfolio:
        raise RoundTransactionError(
            "OpenEvolve search portfolio witness contract is inconsistent"
        )
    portfolio_attempt_fields = base_attempt_fields | {
        "search_portfolio_schema_version",
        "search_policy_sha256",
        "search_regime_status",
        "search_role",
        "search_tactic",
        "search_parent_program_id",
        "search_parent_code_sha256",
        "search_role_submission_counts",
    }
    parent_code_hashes: dict[str, str] = {}
    for attempt in attempts:
        if set(attempt) != portfolio_attempt_fields:
            raise RoundTransactionError(
                "portfolio submission witness fields are not exact"
            )
        iteration = attempt["iteration"]
        offset = iteration - start_iteration
        if not 0 <= offset < len(schedule):
            raise RoundTransactionError(
                "portfolio submission iteration is outside the slice"
            )
        expected_island = schedule[offset]
        expected_role = SEARCH_PORTFOLIO_ROLES[expected_island]
        parent_program_id = attempt["search_parent_program_id"]
        parent_code_sha256 = attempt["search_parent_code_sha256"]
        if (
            not isinstance(parent_program_id, str)
            or not re.fullmatch(r"[A-Za-z0-9._-]+", parent_program_id)
            or parent_program_id in {".", ".."}
            or type(attempt["search_portfolio_schema_version"]) is not int
            or not isinstance(attempt["search_role_submission_counts"], dict)
            or set(attempt["search_role_submission_counts"])
            != set(SEARCH_PORTFOLIO_ROLES)
            or any(
                type(value) is not int or value < 0
                for value in attempt[
                    "search_role_submission_counts"
                ].values()
            )
            or not isinstance(parent_code_sha256, str)
            or len(parent_code_sha256) != 64
            or any(
                character not in "0123456789abcdef"
                for character in parent_code_sha256
            )
        ):
            raise RoundTransactionError(
                "portfolio submission parent code hash is invalid"
            )
        observed_parent_hash = parent_code_hashes.get(parent_program_id)
        if observed_parent_hash is None:
            parent_path: Path | None = None
            for checkpoint in (
                result_checkpoint,
                base_checkpoint,
            ):
                if checkpoint is None:
                    continue
                candidate_path = (
                    Path(checkpoint["path"])
                    / "programs"
                    / f"{parent_program_id}.json"
                )
                if candidate_path.is_file():
                    parent_path = candidate_path
                    break
            if parent_path is None:
                raise RoundTransactionError(
                    "portfolio parent is absent from both slice checkpoints"
                )
            parent = _read_json_object(
                parent_path, "portfolio parent checkpoint program"
            )
            parent_code = parent.get("code")
            if (
                parent.get("id") != parent_program_id
                or not isinstance(parent_code, str)
            ):
                raise RoundTransactionError(
                    "portfolio parent checkpoint program is invalid"
                )
            observed_parent_hash = hashlib.sha256(
                parent_code.encode("utf-8")
            ).hexdigest()
            parent_code_hashes[parent_program_id] = observed_parent_hash
        if observed_parent_hash != parent_code_sha256:
            raise RoundTransactionError(
                "portfolio submission parent code hash changed"
            )
        expected_tactic = _adaptive_mutation_tactic_from_parent_hash(
            policy,
            parent_code_sha256=parent_code_sha256,
            iteration=iteration,
        )
        if (
            attempt["island_id"] != expected_island
            or attempt["search_portfolio_schema_version"]
            != portfolio_schema
            or attempt["search_policy_sha256"] != policy_sha256
            or attempt["search_regime_status"] != regime_status
            or attempt["search_role"] != expected_role
            or attempt["search_tactic"] != expected_tactic
            or attempt["search_role_submission_counts"] != expected_counts
        ):
            raise RoundTransactionError(
                "portfolio submission witness semantics are inconsistent"
            )
    return False


def _validate_slice_witness(
    witness_path: Path,
    config: FlowConfig,
    base_checkpoint: dict[str, Any] | None,
    result_checkpoint: dict[str, Any],
    launch_binding: dict[str, dict[str, Any]],
    invocation_binding: dict[str, Any],
    candidate_log: Path,
    candidate_start_offset: int,
    legacy_candidate_source: dict[str, Any] | None = None,
    require_candidate_end_of_file: bool = False,
    allow_historical_candidate_inode_change: bool = False,
) -> dict[str, Any]:
    witness = _read_json_object(witness_path, "OpenEvolve slice witness")
    witness_schema = witness.get("schema_version")
    legacy_witness = witness_schema == 2
    if legacy_witness and legacy_candidate_source is None:
        raise LegacySliceWitnessUpgradeRequired(
            "prepared legacy OpenEvolve witness has no candidate-range "
            "binding and must be quarantined and replayed"
        )
    if witness_schema not in (
        EVOLUTION_SLICE_WITNESS_LEGACY_SCHEMA_VERSIONS
        | {EVOLUTION_SLICE_WITNESS_SCHEMA_VERSION}
    ):
        raise RoundTransactionError(
            f"unsupported OpenEvolve witness schema: {witness_schema!r}"
        )
    binding = launch_binding
    invocation = _validate_invocation_binding(
        config, invocation_binding, binding
    )
    base_iteration = (
        0 if base_checkpoint is None else int(base_checkpoint["last_iteration"])
    )
    start_iteration = base_iteration + 1
    count = config.iterations_per_round
    end_iteration = base_iteration + count
    expected: dict[str, Any] = {
        "schema_version": witness_schema,
        "status": "completed",
        "output_dir": str(
            (
                config.repo_dir
                / "results"
                / "evolution"
                / f"humanize_{config.run_id}"
            ).resolve()
        ),
        "resume_checkpoint": (
            None if base_checkpoint is None else base_checkpoint["path"]
        ),
        "base_last_iteration": base_iteration,
        "iterations_requested": count,
        "slice_start_iteration": start_iteration,
        "slice_end_iteration": end_iteration,
        "slice_iteration_count": count,
        "slice_iterations_sha256": _slice_iterations_sha256(
            start_iteration, count
        ),
        "result_checkpoint": result_checkpoint["path"],
        "result_last_iteration": result_checkpoint["last_iteration"],
        "result_checkpoint_sha256": result_checkpoint["sha256"],
        "result_checkpoint_programs": result_checkpoint["programs"],
    }
    if not legacy_witness:
        expected.update({
            "candidate_log_path": str(candidate_log.resolve()),
            "candidate_start_offset": candidate_start_offset,
            "candidate_wal_clean": True,
        })
    for name, descriptor in binding.items():
        for field in ("path", "sha256", "bytes"):
            expected[f"{name}_{field}"] = descriptor[field]
    expected.update(invocation)
    for key, value in expected.items():
        if witness.get(key) != value:
            raise RoundTransactionError(
                f"OpenEvolve slice witness mismatch for {key}: "
                f"expected {value!r}, got {witness.get(key)!r}"
            )

    if legacy_witness:
        assert legacy_candidate_source is not None
        candidate_end_offset = legacy_candidate_source.get(
            "candidate_end_offset"
        )
        candidate_range_sha256 = legacy_candidate_source.get(
            "candidate_source_sha256"
        )
        if (
            legacy_candidate_source.get("candidate_start_offset")
            != candidate_start_offset
            or isinstance(candidate_end_offset, bool)
            or not isinstance(candidate_end_offset, int)
            or candidate_end_offset < candidate_start_offset
            or not isinstance(candidate_range_sha256, str)
            or len(candidate_range_sha256) != 64
            or any(
                character not in "0123456789abcdef"
                for character in candidate_range_sha256
            )
        ):
            raise RoundTransactionError(
                "legacy transaction candidate source identity is invalid"
            )
        observed_candidate = _candidate_log_range_identity(
            candidate_log,
            start_offset=candidate_start_offset,
            end_offset=(
                None
                if require_candidate_end_of_file
                else candidate_end_offset
            ),
        )
        if (
            observed_candidate["end_offset"] != candidate_end_offset
            or observed_candidate["sha256"] != candidate_range_sha256
        ):
            raise RoundTransactionError(
                "legacy transaction candidate source range changed"
            )
    else:
        candidate_end_offset = witness.get("candidate_end_offset")
        candidate_device = witness.get("candidate_log_device")
        candidate_inode = witness.get("candidate_log_inode")
        candidate_range_bytes = witness.get("candidate_range_bytes")
        candidate_range_sha256 = witness.get("candidate_range_sha256")
        if (
            isinstance(candidate_end_offset, bool)
            or not isinstance(candidate_end_offset, int)
            or candidate_end_offset < candidate_start_offset
            or isinstance(candidate_device, bool)
            or not isinstance(candidate_device, int)
            or candidate_device < 0
            or isinstance(candidate_inode, bool)
            or not isinstance(candidate_inode, int)
            or candidate_inode < 1
            or isinstance(candidate_range_bytes, bool)
            or not isinstance(candidate_range_bytes, int)
            or candidate_range_bytes
            != candidate_end_offset - candidate_start_offset
            or not isinstance(candidate_range_sha256, str)
            or len(candidate_range_sha256) != 64
            or any(
                character not in "0123456789abcdef"
                for character in candidate_range_sha256
            )
        ):
            raise RoundTransactionError(
                "OpenEvolve slice witness candidate range identity is invalid"
            )
        observed_candidate = _candidate_log_range_identity(
            candidate_log,
            start_offset=candidate_start_offset,
            end_offset=(
                None
                if require_candidate_end_of_file
                else candidate_end_offset
            ),
        )
        candidate_expected = {
            "candidate_log_path": observed_candidate["path"],
            "candidate_log_device": observed_candidate["device"],
            "candidate_log_inode": observed_candidate["inode"],
            "candidate_start_offset": observed_candidate["start_offset"],
            "candidate_end_offset": observed_candidate["end_offset"],
            "candidate_range_sha256": observed_candidate["sha256"],
            "candidate_range_bytes": observed_candidate["bytes"],
            "candidate_wal_clean": observed_candidate["wal_clean"],
        }
        # A committed slice is replayed by its immutable byte range and proof
        # chain.  Recovery may atomically replace the aggregate candidate log
        # while preserving those bytes, which necessarily changes its inode.
        # Live/pre-commit validation must retain the inode lease so a file
        # replacement cannot be mistaken for the process-owned append target.
        if allow_historical_candidate_inode_change:
            candidate_expected.pop("candidate_log_inode")
        for key, value in candidate_expected.items():
            if witness.get(key) != value:
                raise RoundTransactionError(
                    f"OpenEvolve slice witness mismatch for {key}: "
                    f"expected {value!r}, got {witness.get(key)!r}"
                )

    expected_iterations = list(range(start_iteration, end_iteration + 1))
    attempts = witness.get("submission_attempts")
    if not isinstance(attempts, list) or len(attempts) != count:
        raise RoundTransactionError(
            "OpenEvolve slice witness has incomplete submission attempts"
        )
    if [attempt.get("iteration") for attempt in attempts if isinstance(attempt, dict)] != expected_iterations:
        raise RoundTransactionError(
            "OpenEvolve slice witness submission iterations are not exact"
        )
    for attempt in attempts:
        if (
            not isinstance(attempt, dict)
            or type(attempt.get("iteration")) is not int
            or isinstance(attempt.get("island_id"), bool)
            or not isinstance(attempt.get("island_id"), int)
            or attempt.get("result") != "future"
        ):
            raise RoundTransactionError(
                "OpenEvolve slice witness contains an invalid submission"
            )
    coset_portfolio_witness = _validate_search_portfolio_witness(
        witness,
        attempts,
        witness_schema=witness_schema,
        launch_binding=binding,
        invocation_binding=invocation_binding,
        base_checkpoint=base_checkpoint,
        result_checkpoint=result_checkpoint,
        start_iteration=start_iteration,
        count=count,
    )
    coset_representation_id: str | None = None
    if coset_portfolio_witness:
        config_document = yaml.safe_load(
            Path(binding["config"]["path"]).read_text()
        )
        coset_marker = config_document.get(
            COSET_SEARCH_PORTFOLIO_CONFIG_KEY
        )
        if not isinstance(coset_marker, dict) or not isinstance(
            coset_marker.get("representation_id"), str
        ):
            raise RoundTransactionError(
                "coset witness config representation is invalid"
            )
        coset_representation_id = coset_marker["representation_id"]
    checkpoint_preflight = witness.get("checkpoint_preflight")
    if witness_schema == EVOLUTION_SLICE_WITNESS_SCHEMA_VERSION:
        if base_checkpoint is None:
            if checkpoint_preflight is not None:
                raise RoundTransactionError(
                    "fresh evolution witness contains a checkpoint preflight"
                )
        else:
            if not isinstance(checkpoint_preflight, dict):
                raise RoundTransactionError(
                    "resumed evolution witness has no checkpoint preflight"
                )
            report_schema = checkpoint_preflight.get("schema_version")
            common_valid = (
                checkpoint_preflight.get("status") == "completed"
                and checkpoint_preflight.get("contract_version") == 2
                and type(checkpoint_preflight.get("contract_id")) is int
                and checkpoint_preflight["contract_id"] >= 0
            )
            if not common_valid or report_schema not in {1, 2, 3, 4}:
                raise RoundTransactionError(
                    "checkpoint preflight report is invalid"
                )
            if report_schema == 1:
                expected_report_fields = {
                    "schema_version",
                    "status",
                    "contract_version",
                    "contract_id",
                    "programs",
                    "unique_program_codes",
                    "programs_already_complete",
                    "unique_program_codes_evaluated",
                    "programs_updated",
                    "worker_cap",
                }
                counts = [
                    checkpoint_preflight.get(field)
                    for field in (
                        "programs",
                        "unique_program_codes",
                        "programs_already_complete",
                        "unique_program_codes_evaluated",
                        "programs_updated",
                        "worker_cap",
                    )
                ]
                if (
                    set(checkpoint_preflight) != expected_report_fields
                    or any(type(value) is not int or value < 0 for value in counts)
                    or checkpoint_preflight["programs"] < 1
                    or checkpoint_preflight["unique_program_codes"] < 1
                    or checkpoint_preflight["worker_cap"] < 1
                ):
                    raise RoundTransactionError(
                        "checkpoint backfill report is invalid"
                    )
            elif report_schema == 2:
                expected_report_fields = {
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
                    "migration_candidate_range",
                }
                range_value = checkpoint_preflight.get(
                    "migration_candidate_range"
                )
                hashes = (
                    checkpoint_preflight.get("source_program_set_sha256"),
                    checkpoint_preflight.get("root_policy_sha256"),
                    checkpoint_preflight.get("root_code_sha256"),
                )
                if (
                    set(checkpoint_preflight) != expected_report_fields
                    or checkpoint_preflight.get("mode")
                    != "legacy-python-to-typed-json-dsl-root"
                    or checkpoint_preflight.get("source_checkpoint")
                    != base_checkpoint
                    or checkpoint_preflight.get("source_programs")
                    != base_checkpoint["programs"]
                    or checkpoint_preflight.get("target_programs") != 1
                    or not isinstance(
                        checkpoint_preflight.get("root_program_id"), str
                    )
                    or not checkpoint_preflight["root_program_id"].startswith(
                        "coset-dsl-root-"
                    )
                    or any(
                        not isinstance(value, str)
                        or re.fullmatch(r"[0-9a-f]{64}", value) is None
                        for value in hashes
                    )
                    or not isinstance(range_value, dict)
                    or set(range_value)
                    != {
                        "path",
                        "start_offset",
                        "end_offset",
                        "sha256",
                        "bytes",
                        "wal_clean",
                    }
                    or range_value.get("path") != str(candidate_log.resolve())
                    or type(range_value.get("start_offset")) is not int
                    or type(range_value.get("end_offset")) is not int
                    or range_value["start_offset"] != candidate_start_offset
                    or not (
                        candidate_start_offset
                        <= range_value["end_offset"]
                        <= int(witness["candidate_end_offset"])
                    )
                    or range_value.get("bytes")
                    != range_value["end_offset"] - range_value["start_offset"]
                    or not isinstance(range_value.get("sha256"), str)
                    or re.fullmatch(r"[0-9a-f]{64}", range_value["sha256"])
                    is None
                    or range_value.get("wal_clean") is not True
                ):
                    raise RoundTransactionError(
                        "checkpoint DSL migration report is invalid"
                    )
                observed_migration = _candidate_log_range_identity(
                    candidate_log,
                    start_offset=range_value["start_offset"],
                    end_offset=range_value["end_offset"],
                )
                root_program_path = (
                    Path(result_checkpoint["path"])
                    / "programs"
                    / f"{checkpoint_preflight['root_program_id']}.json"
                )
                if (
                    root_program_path.is_symlink()
                    or not root_program_path.is_file()
                ):
                    raise RoundTransactionError(
                        "checkpoint DSL migration root is absent"
                    )
                root_program = _read_json_object(
                    root_program_path,
                    "checkpoint DSL migration root",
                )
                root_code = root_program.get("code")
                if coset_representation_id is None:
                    raise RoundTransactionError(
                        "checkpoint DSL migration has no renderer epoch"
                    )
                root_policy = _validated_live_coset_policy_code_identity(
                    root_code,
                    expected_catalog_sha256=invocation_binding.get(
                        "qcode_action_catalog_sha256"
                    ),
                    expected_representation_id=coset_representation_id,
                )
                root_policy_sha256 = root_policy["policy_sha256"]
                observed_source_program_set_sha256 = (
                    _checkpoint_program_set_sha256(base_checkpoint)
                )
                root_binding = {
                    "schema_version": 1,
                    "kind": "qcode-coset-checkpoint-dsl-epoch",
                    "source_checkpoint_sha256": base_checkpoint["sha256"],
                    "source_program_set_sha256": (
                        observed_source_program_set_sha256
                    ),
                    "source_last_iteration": base_checkpoint["last_iteration"],
                    "policy_sha256": root_policy_sha256,
                    "code_sha256": root_policy["code_sha256"],
                    "contract_id": checkpoint_preflight["contract_id"],
                }
                expected_root_id = "coset-dsl-root-" + hashlib.sha256(
                    json.dumps(
                        root_binding,
                        sort_keys=True,
                        separators=(",", ":"),
                        allow_nan=False,
                    ).encode("utf-8")
                ).hexdigest()[:32]
                root_metadata = root_program.get("metadata")
                if (
                    observed_migration["sha256"] != range_value["sha256"]
                    or observed_migration["bytes"] != range_value["bytes"]
                    or observed_source_program_set_sha256
                    != checkpoint_preflight["source_program_set_sha256"]
                    or checkpoint_preflight["root_program_id"]
                    != expected_root_id
                    or root_program.get("id")
                    != checkpoint_preflight["root_program_id"]
                    or root_program.get("parent_id") is not None
                    or root_program.get("iteration_found")
                    != base_checkpoint["last_iteration"]
                    or root_program.get("language") != "json"
                    or root_policy_sha256
                    != checkpoint_preflight["root_policy_sha256"]
                    or root_policy["code_sha256"]
                    != checkpoint_preflight["root_code_sha256"]
                    or not isinstance(root_metadata, dict)
                    or root_metadata.get("checkpoint_genome_epoch")
                    != root_binding
                ):
                    raise RoundTransactionError(
                        "checkpoint DSL migration lineage is inconsistent"
                    )
            else:
                _validate_checkpoint_activation_bridge_preflight(
                    checkpoint_preflight,
                    base_checkpoint=base_checkpoint,
                    result_checkpoint=result_checkpoint,
                    launch_binding=binding,
                    invocation_binding=invocation_binding,
                    candidate_log=candidate_log,
                    candidate_start_offset=candidate_start_offset,
                    candidate_end_offset=int(witness["candidate_end_offset"]),
                    expected_representation_id=coset_representation_id,
                )

    outcomes = witness.get("outcomes")
    if not isinstance(outcomes, list) or len(outcomes) != count:
        raise RoundTransactionError(
            "OpenEvolve slice witness has incomplete future outcomes"
        )
    if any(
        not isinstance(outcome, dict)
        or type(outcome.get("iteration")) is not int
        for outcome in outcomes
    ):
        raise RoundTransactionError(
            "OpenEvolve slice witness outcome iteration is invalid"
        )
    if [outcome.get("iteration") for outcome in outcomes if isinstance(outcome, dict)] != expected_iterations:
        raise RoundTransactionError(
            "OpenEvolve slice witness outcome iterations are not exact"
        )
    successful = 0
    worker_errors = 0
    controlled_mutation_rejections = 0
    controlled_error_kinds = (
        {"invalid_mutation", "no_effect_mutation"}
        if coset_portfolio_witness
        else set()
    )
    attempts_by_iteration = {
        attempt["iteration"]: attempt for attempt in attempts
    }
    witnessed_program_ids: set[str] = set()
    for outcome in outcomes:
        if not isinstance(outcome, dict):
            raise RoundTransactionError(
                "OpenEvolve slice witness outcome is not an object"
            )
        iteration = int(outcome["iteration"])
        status = outcome.get("status")
        if status == "worker_error":
            worker_errors += 1
            digest = outcome.get("error_sha256")
            size = outcome.get("error_bytes")
            error_kind = outcome.get("error_kind")
            if (
                not isinstance(digest, str)
                or len(digest) != 64
                or any(
                    character not in "0123456789abcdef"
                    for character in digest
                )
                or isinstance(size, bool)
                or not isinstance(size, int)
                or size < 1
                or (
                    error_kind is not None
                    and error_kind not in controlled_error_kinds
                )
            ):
                raise RoundTransactionError(
                    "OpenEvolve slice witness worker error identity is invalid"
                )
            if error_kind in controlled_error_kinds:
                controlled_mutation_rejections += 1
        elif status == "program_added":
            successful += 1
            program_id = outcome.get("program_id")
            program_sha256 = outcome.get("program_sha256")
            program_bytes = outcome.get("program_bytes")
            if (
                not isinstance(program_id, str)
                or not program_id
                or program_id in witnessed_program_ids
                or not isinstance(program_sha256, str)
                or len(program_sha256) != 64
                or any(
                    character not in "0123456789abcdef"
                    for character in program_sha256
                )
                or isinstance(program_bytes, bool)
                or not isinstance(program_bytes, int)
                or program_bytes < 1
            ):
                raise RoundTransactionError(
                    "OpenEvolve slice witness program identity is invalid"
                )
            if coset_portfolio_witness:
                assert coset_representation_id is not None
                _validate_coset_result_program_lineage(
                    outcome,
                    attempts_by_iteration[iteration],
                    result_checkpoint=result_checkpoint,
                    expected_catalog_sha256=invocation_binding.get(
                        "qcode_action_catalog_sha256"
                    ),
                    expected_representation_id=coset_representation_id,
                )
            witnessed_program_ids.add(program_id)
        else:
            raise RoundTransactionError(
                f"OpenEvolve slice witness has invalid outcome status: {status!r}"
            )
    if successful < 1 and not (
        coset_portfolio_witness
        and controlled_mutation_rejections == count
    ):
        raise RoundTransactionError(
            "OpenEvolve slice witness has no successful program"
        )
    if (
        witness.get("successful_evaluations") != successful
        or witness.get("worker_errors") != worker_errors
        or successful + worker_errors != count
    ):
        raise RoundTransactionError(
            "OpenEvolve slice witness outcome counts are inconsistent"
        )

    saves = witness.get("checkpoint_saves")
    if not isinstance(saves, list) or not any(
        isinstance(save, dict)
        and save.get("iteration") == end_iteration
        and save.get("accounting_complete") is True
        and save.get("checkpoint_sha256") == result_checkpoint["sha256"]
        and save.get("checkpoint_programs") == result_checkpoint["programs"]
        for save in saves
    ):
        raise RoundTransactionError(
            "OpenEvolve slice witness has no post-accounting final checkpoint save"
        )

    if witness.get("openevolve_version") != "0.2.26":
        raise RoundTransactionError("unsupported OpenEvolve witness version")
    openevolve_sources = (
        OPENEVOLVE_EVALUATOR_BOUND_WITNESS_SOURCES
        if witness_schema in {6, EVOLUTION_SLICE_WITNESS_SCHEMA_VERSION}
        else OPENEVOLVE_BASE_WITNESS_SOURCES
    )
    for name in openevolve_sources:
        source_path = witness.get(f"{name}_path")
        if not isinstance(source_path, str):
            raise RoundTransactionError(
                f"OpenEvolve slice witness is missing {name} source path"
            )
        observed = _file_descriptor(Path(source_path), f"{name} source")
        for field in ("path", "sha256", "bytes"):
            if witness.get(f"{name}_{field}") != observed[field]:
                raise RoundTransactionError(
                    f"OpenEvolve slice witness source mismatch for {name}_{field}"
                )
    if not isinstance(witness.get("completed_at"), str):
        raise RoundTransactionError(
            "OpenEvolve slice witness has no completion timestamp"
        )
    allowed_fields = set(expected) | {
        "submission_attempts",
        "outcomes",
        "successful_evaluations",
        "worker_errors",
        "checkpoint_saves",
        "openevolve_version",
        "completed_at",
    }
    if (
        witness_schema == EVOLUTION_SLICE_WITNESS_SCHEMA_VERSION
        and base_checkpoint is not None
    ):
        allowed_fields.add("checkpoint_preflight")
    if witness_schema in EVOLUTION_SLICE_WITNESS_PORTFOLIO_SCHEMA_VERSIONS:
        allowed_fields.add("search_portfolio")
    if not legacy_witness:
        allowed_fields.update({
            "candidate_log_device",
            "candidate_log_inode",
            "candidate_end_offset",
            "candidate_range_sha256",
            "candidate_range_bytes",
        })
    for name in openevolve_sources:
        allowed_fields.update(
            f"{name}_{field}" for field in ("path", "sha256", "bytes")
        )
    if set(witness) != allowed_fields:
        raise RoundTransactionError(
            "OpenEvolve slice witness fields are not exact"
        )
    witness["sha256"] = _file_sha256(witness_path)
    witness["bytes"] = witness_path.stat().st_size
    return witness


def _completion_marker_expected(
    config: FlowConfig,
    base_checkpoint: dict[str, Any] | None,
    result_checkpoint: dict[str, Any],
    launch_binding: dict[str, dict[str, Any]],
    invocation_binding: dict[str, Any],
    slice_witness: dict[str, Any],
) -> dict[str, Any]:
    base_iteration = (
        0 if base_checkpoint is None else int(base_checkpoint["last_iteration"])
    )
    witness_schema = slice_witness.get("schema_version")
    if witness_schema not in (
        EVOLUTION_SLICE_WITNESS_LEGACY_SCHEMA_VERSIONS
        | {EVOLUTION_SLICE_WITNESS_SCHEMA_VERSION}
    ):
        raise RoundTransactionError(
            "completion marker received an unsupported witness schema"
        )
    expected: dict[str, Any] = {
        "schema_version": witness_schema,
        "status": "completed",
        "output_dir": str(
            (
                config.repo_dir
                / "results"
                / "evolution"
                / f"humanize_{config.run_id}"
            ).resolve()
        ),
        "resume_checkpoint": (
            None if base_checkpoint is None else base_checkpoint["path"]
        ),
        "base_last_iteration": base_iteration,
        "iterations_requested": config.iterations_per_round,
        "result_checkpoint": result_checkpoint["path"],
        "result_last_iteration": result_checkpoint["last_iteration"],
        "result_checkpoint_sha256": result_checkpoint["sha256"],
        "result_checkpoint_programs": result_checkpoint["programs"],
        "slice_witness_path": slice_witness["path"],
        "slice_witness_sha256": slice_witness["sha256"],
        "slice_witness_bytes": slice_witness["bytes"],
    }
    if witness_schema != 2:
        for field in CANDIDATE_WITNESS_FIELDS:
            expected[field] = slice_witness[field]
    for name, descriptor in launch_binding.items():
        for field in ("path", "sha256", "bytes"):
            expected[f"{name}_{field}"] = descriptor[field]
    expected.update(invocation_binding)
    return expected


def _validate_completion_marker(
    marker_path: Path,
    config: FlowConfig,
    base_checkpoint: dict[str, Any] | None,
    result_checkpoint: dict[str, Any],
    launch_binding: dict[str, dict[str, Any]],
    invocation_binding: dict[str, Any],
    slice_witness: dict[str, Any],
) -> dict[str, Any]:
    marker = _read_json_object(marker_path, "OpenEvolve completion marker")
    witness_with_path = dict(slice_witness)
    witness_with_path["path"] = str(_slice_witness_path(marker_path.parent).resolve())
    expected = _completion_marker_expected(
        config,
        base_checkpoint,
        result_checkpoint,
        launch_binding,
        _validate_invocation_binding(
            config, invocation_binding, launch_binding
        ),
        witness_with_path,
    )
    for key, value in expected.items():
        if marker.get(key) != value:
            raise RoundTransactionError(
                f"OpenEvolve completion marker mismatch for {key}: "
                f"expected {value!r}, got {marker.get(key)!r}"
            )
    if (
        set(marker) != set(expected) | {"completed_at"}
        or not isinstance(marker.get("completed_at"), str)
    ):
        raise RoundTransactionError(
            "OpenEvolve completion marker fields are not exact"
        )
    marker["sha256"] = _file_sha256(marker_path)
    marker["bytes"] = marker_path.stat().st_size
    return marker


def _revalidate_frozen_bindings(
    config: FlowConfig,
    launch: Any,
    invocation: Any,
    round_dir: Path,
) -> tuple[dict[str, dict[str, Any]], dict[str, Any]]:
    if not isinstance(launch, dict):
        raise RoundTransactionError(
            "managed OpenEvolve launch is missing its frozen launch binding"
        )
    expected_context = str(
        Path(os.path.abspath(round_dir / "search-context.md"))
    )
    context = launch.get("context")
    if (
        not isinstance(context, dict)
        or context.get("path") != expected_context
    ):
        raise RoundTransactionError(
            "managed OpenEvolve launch has the wrong frozen context"
        )
    codex_executable = (
        launch.get("codex_executable") if config.codex_cli else None
    )
    observed = _evolution_launch_binding(
        config,
        context_path=Path(expected_context),
        codex_executable=codex_executable,
    )
    if observed != launch:
        raise RoundTransactionError(
            "evolution launch inputs changed after transaction prepare"
        )
    validated_invocation = _validate_invocation_binding(
        config, invocation, observed
    )
    return observed, validated_invocation


def _current_evolution_bindings(
    config: FlowConfig,
    round_dir: Path,
) -> tuple[dict[str, dict[str, Any]], dict[str, Any]]:
    """Describe current launch inputs without replacing the frozen context."""
    context_path = Path(os.path.abspath(round_dir / "search-context.md"))
    codex_identity: dict[str, Any] | None = None
    codex_version: str | None = None
    codex_cwd: str | None = None
    if config.codex_cli:
        codex_identity, codex_version, codex_cwd = _fresh_codex_binding(
            config,
            round_dir=round_dir,
        )
    launch = _evolution_launch_binding(
        config,
        context_path=context_path,
        codex_executable=codex_identity,
    )
    invocation = _fresh_invocation_binding(
        config,
        codex_identity=codex_identity,
        codex_version=codex_version,
        codex_cwd=codex_cwd,
        launch_binding=launch,
    )
    _validate_invocation_binding(config, invocation, launch)
    return launch, invocation


def _binding_identity_sha256(
    launch: dict[str, dict[str, Any]],
    invocation: dict[str, Any],
) -> str:
    encoded = json.dumps(
        {"launch": launch, "invocation": invocation},
        sort_keys=True,
        separators=(",", ":"),
        allow_nan=False,
    ).encode("utf-8")
    return hashlib.sha256(encoded).hexdigest()


def _evolution_launch_shape_rank(
    launch: Any,
    current_launch: dict[str, dict[str, Any]],
) -> int | None:
    """Return the append-only dependency-schema rank for a launch binding."""

    if not isinstance(launch, dict):
        return None
    launch_fields = set(launch)
    current_fields = set(current_launch)
    if launch_fields == current_fields:
        return len(LEGACY_EVOLUTION_LAUNCH_MISSING_FIELDS)
    for rank, missing in enumerate(
        LEGACY_EVOLUTION_LAUNCH_MISSING_FIELDS
    ):
        # Coset-only dependencies are absent from the current launch schema of
        # every other evaluator.  Project each append-only historical shape
        # onto the active evaluator's fields so adding the typed-DSL bindings
        # does not invalidate the existing default-evaluator rebind chain.
        effective_missing = missing & current_fields
        if (
            effective_missing
            and launch_fields == current_fields - effective_missing
        ):
            return rank
    return None


def _is_legacy_evolution_launch_shape(
    launch: Any,
    current_launch: dict[str, dict[str, Any]],
) -> bool:
    rank = _evolution_launch_shape_rank(launch, current_launch)
    return (
        rank is not None
        and rank < len(LEGACY_EVOLUTION_LAUNCH_MISSING_FIELDS)
    )


def _validate_stored_binding_shape(
    config: FlowConfig,
    launch: Any,
    invocation: Any,
    round_dir: Path,
    current_launch: dict[str, dict[str, Any]],
    *,
    allow_legacy: bool = False,
    allow_previous_committed: bool = False,
) -> tuple[dict[str, dict[str, Any]], dict[str, Any]]:
    """Validate an old identity without requiring old source bytes to exist.

    A prepared transaction may safely replay after source files at the same
    canonical paths are upgraded.  The old descriptors must still be exact,
    and the round context (which is transaction data rather than source code)
    must remain byte-identical.
    """
    if not isinstance(launch, dict):
        raise RoundTransactionError(
            "managed OpenEvolve launch binding fields are incomplete"
        )
    launch_fields = set(launch)
    current_fields = set(current_launch)
    legacy_shape = _is_legacy_evolution_launch_shape(
        launch, current_launch
    )
    previous_committed_shape = any(
        (missing & current_fields)
        and launch_fields == current_fields - (missing & current_fields)
        for missing in COMMITTED_PREVIOUS_EVOLUTION_LAUNCH_MISSING_FIELDS
    )
    if launch_fields != current_fields and not (
        allow_legacy and legacy_shape
        or allow_previous_committed and previous_committed_shape
    ):
        raise RoundTransactionError(
            "managed OpenEvolve launch binding fields are incomplete"
        )
    for name in launch_fields:
        current = current_launch[name]
        descriptor = launch[name]
        expected_fields = {"path", "sha256", "bytes"}
        if name == "codex_executable":
            expected_fields.add("mode")
        if (
            not isinstance(descriptor, dict)
            or set(descriptor) != expected_fields
            or descriptor.get("path") != current["path"]
            or not isinstance(descriptor.get("sha256"), str)
            or re.fullmatch(r"[0-9a-f]{64}", descriptor["sha256"]) is None
            or isinstance(descriptor.get("bytes"), bool)
            or not isinstance(descriptor.get("bytes"), int)
            or descriptor["bytes"] < 0
        ):
            raise RoundTransactionError(
                f"managed OpenEvolve {name} identity is malformed or redirected"
            )
        if name == "codex_executable" and (
            isinstance(descriptor.get("mode"), bool)
            or not isinstance(descriptor.get("mode"), int)
            or descriptor["mode"] < 0
        ):
            raise RoundTransactionError(
                "managed OpenEvolve Codex executable mode is invalid"
            )
    if launch["context"] != current_launch["context"]:
        raise RoundTransactionError(
            "evolution launch inputs changed after transaction prepare: "
            "the frozen context is not byte-identical"
        )

    geometry_contract = _managed_search_geometry_contract(
        config,
        Path(launch["config"]["path"]),
    )
    feedback_launch_fields = (
        launch_fields & set(COSET_NEGATIVE_FEEDBACK_LAUNCH_FIELDS)
    )
    if feedback_launch_fields and feedback_launch_fields != set(
        COSET_NEGATIVE_FEEDBACK_LAUNCH_FIELDS
    ):
        raise RoundTransactionError(
            "coset negative-feedback launch binding is incomplete"
        )
    expected_invocation_fields = _expected_evolution_invocation_fields(
        config, launch_fields, geometry_contract
    )
    ansatz_v3_codex = _is_ansatz_v3_codex_invocation(config)
    if (
        not isinstance(invocation, dict)
        or set(invocation) != expected_invocation_fields
    ):
        raise RoundTransactionError(
            "evolution invocation binding fields are incomplete"
        )
    if geometry_contract is not None and (
        invocation[SEARCH_GEOMETRY_CONTRACT_INVOCATION_FIELD]
        != geometry_contract
    ):
        raise RoundTransactionError(
            "evolution search geometry contract binding changed"
        )
    if _flow_evaluator_kind(config) == "coset-two-block":
        catalog = launch.get(_coset_action_catalog_dependency_key(config))
        if (
            invocation.get("qcode_evaluator_kind") != "coset-two-block"
            or not isinstance(catalog, dict)
            or invocation.get("qcode_action_catalog_sha256")
            != catalog.get("sha256")
        ):
            raise RoundTransactionError(
                "coset evolution evaluator/catalog binding changed"
            )
        if feedback_launch_fields:
            expected_feedback = _negative_feedback_invocation(config, launch)
            if any(
                invocation.get(name) != value
                for name, value in expected_feedback.items()
            ):
                raise RoundTransactionError(
                    "coset negative-feedback invocation binding changed"
                )
    if invocation["model_names"] != [config.model]:
        raise RoundTransactionError("evolution model binding changed")
    if invocation["reasoning_effort"] != config.reasoning_effort:
        raise RoundTransactionError("evolution reasoning binding changed")
    if invocation["codex_cli"] is not config.codex_cli:
        raise RoundTransactionError("evolution backend selection changed")
    workers = invocation["max_parallel_evaluations"]
    if (
        isinstance(workers, bool)
        or not isinstance(workers, int)
        or workers < 1
    ):
        raise RoundTransactionError(
            "evolution worker binding identity is invalid"
        )
    api_base = invocation["api_base"]
    if (
        not isinstance(api_base, str)
        or not api_base
        or (config.api_base is not None and api_base != config.api_base)
    ):
        raise RoundTransactionError("evolution API base binding changed")
    if invocation["temperature_disabled"] is not True:
        raise RoundTransactionError(
            "managed evolution must freeze temperature-disabled mode"
        )
    if config.codex_cli:
        executable = launch["codex_executable"]
        expected_codex_cwd = _validated_codex_cwd(
            config,
            invocation,
            launch,
            ansatz_v3_codex=ansatz_v3_codex,
        )
        if (
            invocation["codex_executable_mode"] != executable["mode"]
            or invocation["codex_cwd"] != expected_codex_cwd
            or not isinstance(invocation["codex_version"], str)
            or not invocation["codex_version"]
        ):
            raise RoundTransactionError(
                "Codex execution identity is malformed"
            )
    elif any(
        invocation[field] is not None
        for field in (
            "codex_version",
            "codex_cwd",
            "codex_executable_mode",
        )
    ):
        raise RoundTransactionError(
            "non-Codex invocation contains Codex execution fields"
        )
    return copy.deepcopy(launch), copy.deepcopy(invocation)


def _binding_change_reason(
    old_launch: dict[str, dict[str, Any]],
    old_invocation: dict[str, Any],
    current_launch: dict[str, dict[str, Any]],
    current_invocation: dict[str, Any],
) -> str:
    changed = [
        f"launch:{name}"
        for name in sorted(current_launch)
        if old_launch.get(name) != current_launch[name]
    ]
    changed.extend(
        f"invocation:{name}"
        for name in sorted(current_invocation)
        if old_invocation.get(name) != current_invocation[name]
    )
    return (
        "prepared OpenEvolve binding changed before source-ready: "
        + ", ".join(changed)
    )


def _frozen_bindings_from_state(
    config: FlowConfig,
    state: dict[str, Any],
    round_dir: Path,
) -> tuple[dict[str, dict[str, Any]], dict[str, Any]]:
    return _revalidate_frozen_bindings(
        config,
        state.get("_evolution_launch_binding"),
        state.get("_evolution_invocation_binding"),
        round_dir,
    )


def run_openevolve(config: FlowConfig, state: dict[str, Any], round_dir: Path) -> Path:
    """Run one exact OpenEvolve increment and require a durable success marker."""
    evolution_name = f"humanize_{config.run_id}"
    output_dir = config.repo_dir / "results" / "evolution" / evolution_name
    iterations_this_round = config.iterations_per_round
    if "_evolution_base_checkpoint" not in state:
        raise RoundTransactionError(
            "managed OpenEvolve launch is missing its frozen base checkpoint"
        )
    frozen_base = state["_evolution_base_checkpoint"]
    if frozen_base is None:
        expected_base_path = None
    elif isinstance(frozen_base, dict) and isinstance(
        frozen_base.get("path"), str
    ):
        expected_base_path = frozen_base["path"]
    else:
        raise RoundTransactionError(
            "managed OpenEvolve frozen base checkpoint is invalid"
        )
    if state.get("last_checkpoint") != expected_base_path:
        raise RoundTransactionError(
            "managed OpenEvolve state disagrees with its frozen base checkpoint"
        )
    if frozen_base is None:
        base_checkpoint = None
    else:
        base_checkpoint = _checkpoint_descriptor(
            output_dir,
            Path(frozen_base["path"]),
            expected_iteration=frozen_base.get("last_iteration"),
        )
        if base_checkpoint != frozen_base:
            raise RoundTransactionError(
                "managed OpenEvolve base checkpoint changed after prepare"
            )
    base_iteration = (
        0 if base_checkpoint is None else int(base_checkpoint["last_iteration"])
    )
    expected_iteration = base_iteration + iterations_this_round
    marker_path = _completion_marker_path(round_dir)
    witness_path = _slice_witness_path(round_dir)
    for artifact in (marker_path, witness_path):
        if artifact.is_symlink() or artifact.exists():
            raise RoundTransactionError(
                f"refusing to overwrite an existing completion artifact: {artifact}"
            )

    lease_fd = state.get("_round_lifecycle_lease_fd")
    lease_path_value = state.get("_round_lifecycle_lease_path")
    expected_lease_path = _round_lifecycle_lock_path(round_dir.absolute()).absolute()
    if (
        isinstance(lease_fd, bool)
        or not isinstance(lease_fd, int)
        or lease_fd < 0
        or not isinstance(lease_path_value, str)
        or Path(lease_path_value).absolute() != expected_lease_path
    ):
        raise RoundTransactionError(
            "managed OpenEvolve launch is missing its inherited lifecycle lease"
        )
    _validate_round_lifecycle_inode(lease_fd, expected_lease_path)
    try:
        fcntl.flock(lease_fd, fcntl.LOCK_EX | fcntl.LOCK_NB)
    except BlockingIOError as exc:
        raise RoundTransactionError(
            "managed OpenEvolve lifecycle lease is not held"
        ) from exc

    launch_binding, invocation_binding = _frozen_bindings_from_state(
        config, state, round_dir
    )
    candidate_start_offset = state.get("candidate_offset")
    if (
        isinstance(candidate_start_offset, bool)
        or not isinstance(candidate_start_offset, int)
        or candidate_start_offset < 0
    ):
        raise RoundTransactionError(
            "managed OpenEvolve candidate start offset is invalid"
        )
    candidate_log = output_dir / "all_codes.jsonl"
    context_path = Path(launch_binding["context"]["path"])
    command = [
        sys.executable,
        launch_binding["launcher"]["path"],
        "--run-name", evolution_name,
        "--iterations", str(iterations_this_round),
        "--models", *invocation_binding["model_names"],
        "--humanize-context", str(context_path),
        "--completion-marker", str(marker_path),
        "--slice-witness", str(witness_path),
        "--candidate-start-offset", str(candidate_start_offset),
        "--lifecycle-lease-fd", str(lease_fd),
        "--lifecycle-lease-path", str(expected_lease_path),
        "--config", launch_binding["config"]["path"],
        "--seed", launch_binding["seed"]["path"],
        "--max-parallel-evaluations",
        str(invocation_binding["max_parallel_evaluations"]),
        "--api-base", invocation_binding["api_base"],
    ]
    evaluator_kind = _flow_evaluator_kind(config)
    if evaluator_kind != "default":
        command.extend(["--evaluator", evaluator_kind])
    if invocation_binding["reasoning_effort"] is not None:
        command.extend([
            "--reasoning-effort",
            invocation_binding["reasoning_effort"],
        ])
    if invocation_binding["temperature_disabled"]:
        command.append("--no-temperature")
    if base_checkpoint is not None:
        command.extend(["--resume", base_checkpoint["path"]])
    if invocation_binding["codex_cli"]:
        command.append("--codex-cli")
    if COSET_NEGATIVE_FEEDBACK_INVOCATION_FIELDS.issubset(invocation_binding):
        command.extend([
            "--negative-feedback-live-archive",
            invocation_binding["qcode_negative_feedback_live_archive_path"],
            "--negative-feedback-snapshot",
            invocation_binding["qcode_negative_feedback_snapshot_path"],
            "--negative-feedback-snapshot-sha256",
            invocation_binding["qcode_negative_feedback_snapshot_sha256"],
            "--negative-feedback-archive-sha256",
            invocation_binding["qcode_negative_feedback_archive_sha256"],
            "--negative-feedback-manifest",
            invocation_binding["qcode_negative_feedback_manifest_path"],
            "--negative-feedback-manifest-sha256",
            invocation_binding["qcode_negative_feedback_manifest_sha256"],
            "--negative-feedback-epoch",
            str(invocation_binding["qcode_negative_feedback_epoch"]),
        ])
    renderer_activation_descriptor = launch_binding.get(
        "coset_renderer_activation"
    )
    if renderer_activation_descriptor is not None:
        command.extend([
            "--coset-renderer-activation",
            renderer_activation_descriptor["path"],
        ])

    child_environment = os.environ.copy()
    child_environment.pop("QCODE_COSET_RENDERER_ACTIVATION_JSON", None)
    geometry_contract = invocation_binding.get(
        SEARCH_GEOMETRY_CONTRACT_INVOCATION_FIELD,
    )
    if geometry_contract is None:
        child_environment.pop(SEARCH_GEOMETRY_CONTRACT_ENV, None)
    else:
        child_environment[SEARCH_GEOMETRY_CONTRACT_ENV] = geometry_contract
    if invocation_binding["codex_cli"]:
        child_environment["QCODE_CODEX_BIN"] = launch_binding[
            "codex_executable"
        ]["path"]
        child_environment["QCODE_CODEX_CWD"] = invocation_binding["codex_cwd"]
        if ANSATZ_V3_CODEX_VIEW_INVOCATION_FIELDS.issubset(
            invocation_binding
        ):
            child_environment[
                "QCODE_ANSATZ_V3_CODEX_VIEW_MANIFEST"
            ] = invocation_binding["ansatz_v3_codex_view_manifest_path"]
            child_environment[
                "QCODE_ANSATZ_V3_CODEX_VIEW_MANIFEST_SHA256"
            ] = invocation_binding[
                "ansatz_v3_codex_view_manifest_sha256"
            ]
            child_environment[
                "QCODE_ANSATZ_V3_CODEX_VIEW_SOURCE_FINGERPRINT_SHA256"
            ] = invocation_binding[
                "ansatz_v3_codex_view_source_fingerprint_sha256"
            ]
            child_environment[
                "QCODE_ANSATZ_V3_CODEX_FILESYSTEM_BOUNDARY"
            ] = invocation_binding["ansatz_v3_codex_filesystem_boundary"]
    else:
        child_environment.pop("QCODE_CODEX_BIN", None)
        child_environment.pop("QCODE_CODEX_CWD", None)
    if not ANSATZ_V3_CODEX_VIEW_INVOCATION_FIELDS.issubset(invocation_binding):
        child_environment.pop("QCODE_ANSATZ_V3_CODEX_VIEW_MANIFEST", None)
        child_environment.pop(
            "QCODE_ANSATZ_V3_CODEX_VIEW_MANIFEST_SHA256", None
        )
        child_environment.pop(
            "QCODE_ANSATZ_V3_CODEX_VIEW_SOURCE_FINGERPRINT_SHA256", None
        )
        child_environment.pop(
            "QCODE_ANSATZ_V3_CODEX_FILESYSTEM_BOUNDARY", None
        )
    if COSET_NEGATIVE_FEEDBACK_INVOCATION_FIELDS.issubset(invocation_binding):
        child_environment["QCODE_COSET_NEGATIVE_ARCHIVE_PATH"] = (
            invocation_binding["qcode_negative_feedback_live_archive_path"]
        )
        child_environment["QCODE_COSET_NEGATIVE_ARCHIVE_SNAPSHOT_PATH"] = (
            invocation_binding["qcode_negative_feedback_snapshot_path"]
        )
    log_path = round_dir / "evolution.log"
    with tempfile.TemporaryDirectory(
        prefix="qcode-openevolve-pycache-"
    ) as cache:
        child_environment["PYTHONPYCACHEPREFIX"] = cache
        with log_path.open("w", encoding="utf-8") as stream:
            process = subprocess.Popen(
                command,
                cwd=config.repo_dir,
                stdout=stream,
                stderr=subprocess.STDOUT,
                pass_fds=(lease_fd,),
                start_new_session=True,
                env=child_environment,
            )
            _wait_for_managed_process(process, command)

    result_checkpoint = _checkpoint_descriptor(
        output_dir,
        output_dir / "checkpoints" / f"checkpoint_{expected_iteration}",
        expected_iteration=expected_iteration,
    )
    witness = _validate_slice_witness(
        witness_path,
        config,
        base_checkpoint,
        result_checkpoint,
        launch_binding,
        invocation_binding,
        candidate_log,
        candidate_start_offset,
        require_candidate_end_of_file=True,
    )
    _validate_completion_marker(
        marker_path,
        config,
        base_checkpoint,
        result_checkpoint,
        launch_binding,
        invocation_binding,
        witness,
    )
    return Path(result_checkpoint["path"])


_milp_is_fully_exact = is_fully_exact


def evaluate_with_milp(
    candidate: dict[str, Any],
    config: FlowConfig,
    *,
    checkpoint_path: str | Path | None = None,
    resume: bool = True,
    hard_timeout_per_logical: float | None = None,
) -> dict[str, Any]:
    """Use qcode's evaluator with durable, killable per-direction solves."""
    from evaluation.evaluator import evaluate_candidate_milp
    from evaluation.final_gate import FOM_THRESHOLD
    from main import merge_bp_milp_result

    normalized_candidate = dict(candidate)
    geometry = candidate_geometry(candidate)
    if geometry is None:
        normalized_candidate.pop("geometry", None)
    else:
        normalized_candidate["geometry"] = geometry
    result = evaluate_candidate_milp(
        int(candidate["ell"]),
        int(candidate["m"]),
        [tuple(map(int, term)) for term in candidate["A_terms"]],
        [tuple(map(int, term)) for term in candidate["B_terms"]],
        geometry=geometry,
        milp_timeout_per_logical=config.milp_timeout_per_logical,
        milp_total_timeout=config.milp_total_timeout,
        milp_early_stop=(config.milp_early_stop or None),
        milp_target_fom=FOM_THRESHOLD,
        milp_checkpoint_path=checkpoint_path,
        milp_resume=resume,
        milp_hard_timeout_per_logical=hard_timeout_per_logical,
    )
    merged = merge_bp_milp_result(normalized_candidate, result)
    # Preserve pre-MILP machine gates when an exact result replaces the BP row;
    # final acceptance requires this replayable evidence.
    for field in ("static_eligibility", "structural_novelty"):
        if field in normalized_candidate:
            merged[field] = normalized_candidate[field]
    merged["candidate_key"] = code_key(normalized_candidate)
    if "threshold_proof_witness" in result:
        merged["threshold_proof_witness"] = copy.deepcopy(
            result["threshold_proof_witness"]
        )
    merged["milp_attempted"] = True
    # A reviewer must never be able to alter this machine-derived field.
    merged["d_is_exact"] = is_fully_exact(merged)
    return merged


def _positive_distance(row: dict[str, Any]) -> int | None:
    value = row.get("d")
    if isinstance(value, bool):
        return None
    try:
        distance = int(value)
    except (TypeError, ValueError):
        return None
    return distance if distance > 0 else None


def _distance_evidence_rank(row: dict[str, Any]) -> int:
    """Rank evidence kind before comparing stochastic upper bounds."""
    try:
        fully_exact = is_fully_exact(row)
    except AuditStateError:
        # Discovery JSONL is an input pool, not trusted audit evidence.
        # Malformed exactness metadata must never grant a stronger rank.
        fully_exact = False
    if fully_exact:
        return 3
    if row.get("milp_attempted") is True and _positive_distance(row) is not None:
        return 2
    if _positive_distance(row) is not None:
        return 1
    return 0


def _zero_distance_persistence_rank(row: dict[str, Any]) -> int:
    """Rank retry urgency for zero-distance rows, never mathematical evidence.

    Every row here remains rank zero in ``_distance_evidence_rank``.  An error
    runs first because its allocated distance attempt failed before returning
    evidence, not because it proves more than a completed unresolved attempt.
    """
    return {
        "quick_distance_budget": 0,
        "selected_distance_pending": 1,
        "selected_distance_unresolved": 2,
        "selected_distance_error": 3,
    }.get(str(row.get("candidate_persistence_reason", "")), 0)


def _bp_observation_summary(row: dict[str, Any]) -> tuple[int, int, int] | None:
    """Return count/min/max for replayable BP-style observations in one row."""
    if _distance_evidence_rank(row) != 1:
        return None
    existing = row.get("bp_upper_bound_observations")
    if isinstance(existing, dict):
        count = existing.get("count")
        minimum = existing.get("minimum_distance")
        maximum = existing.get("maximum_distance")
        if (
            isinstance(count, int)
            and not isinstance(count, bool)
            and count > 0
            and isinstance(minimum, int)
            and not isinstance(minimum, bool)
            and minimum > 0
            and isinstance(maximum, int)
            and not isinstance(maximum, bool)
            and maximum >= minimum
        ):
            return count, minimum, maximum
    distance = _positive_distance(row)
    assert distance is not None
    return 1, distance, distance


def _search_lower_bound_persistence_rank(
    row: dict[str, Any],
) -> tuple[int, int] | None:
    """Rank internally sealed search lower bounds for duplicate retention.

    This rank selects which copy of the *same construction* survives the
    candidate pool; it grants no exact-distance or final-gate credit.  Require
    the complete source-bound evidence and proof-ledger hashes so a truncated
    or casually forged status string cannot displace a durable retry record.
    """

    lower_bound = row.get("distance_lower_bound")
    evidence = row.get("distance_lower_bound_evidence")
    ledger = row.get("proof_ledger")
    candidate_sha256 = row.get("candidate_sha256")
    if (
        isinstance(lower_bound, bool)
        or not isinstance(lower_bound, int)
        or lower_bound < 1
        or row.get("distance_lower_bound_proven") is not True
        or row.get("distance_lower_bound_status") != "search_oracle_proven"
        or not isinstance(evidence, dict)
        or not isinstance(ledger, dict)
        or not isinstance(candidate_sha256, str)
        or len(candidate_sha256) != 64
    ):
        return None
    unsigned_evidence = dict(evidence)
    evidence_sha256 = unsigned_evidence.pop("evidence_sha256", None)
    threshold = evidence.get("max_weight")
    try:
        evidence_hash_valid = (
            evidence_sha256 == _canonical_payload_sha256(unsigned_evidence)
        )
    except (TypeError, ValueError):
        return None
    if (
        not isinstance(evidence_sha256, str)
        or not evidence_hash_valid
        or row.get("distance_lower_bound_evidence_sha256")
        != evidence_sha256
        or evidence.get("outcome") != "UNSAT"
        or evidence.get("decision_complete") is not True
        or evidence.get("retryable") is not False
        or evidence.get("witness") is not None
        or isinstance(threshold, bool)
        or not isinstance(threshold, int)
        or threshold < 0
        or lower_bound != threshold + 1
        or evidence.get("distance_lower_bound") != lower_bound
    ):
        return None
    unsigned_ledger = dict(ledger)
    ledger_root = unsigned_ledger.pop("root_sha256", None)
    entries = ledger.get("entries")
    try:
        ledger_hash_valid = (
            ledger_root == _canonical_payload_sha256(unsigned_ledger)
        )
    except (TypeError, ValueError):
        return None
    if (
        not ledger_hash_valid
        or ledger.get("candidate_sha256") != candidate_sha256
        or not isinstance(entries, list)
        or not any(
            isinstance(entry, dict)
            and entry.get("threshold") == threshold
            and entry.get("outcome") == "UNSAT"
            and entry.get("evidence_sha256") == evidence_sha256
            for entry in entries
        )
    ):
        return None
    complete = int(
        row.get("oracle_ladder_complete") is True
        and row.get("challenge_target_lower_bound_proven") is True
    )
    return lower_bound, complete


def _prefer_duplicate_evidence(
    current: dict[str, Any],
    proposed: dict[str, Any],
    *,
    policy_version: int = CANDIDATE_BATCH_POLICY_VERSION,
) -> dict[str, Any]:
    """Choose the strongest evidence, then the tightest observed upper bound."""

    if (
        isinstance(policy_version, bool)
        or policy_version not in CANDIDATE_BATCH_POLICY_VERSIONS
    ):
        raise ValueError(
            f"unsupported candidate batch policy version: {policy_version!r}"
        )
    current_rank = _distance_evidence_rank(current)
    proposed_rank = _distance_evidence_rank(proposed)
    if proposed_rank != current_rank:
        if (
            policy_version >= 2
            and current_rank < 2
            and proposed_rank < 2
        ):
            current_lower = _search_lower_bound_persistence_rank(current)
            proposed_lower = _search_lower_bound_persistence_rank(proposed)
            if current_lower != proposed_lower:
                if current_lower is None:
                    return proposed
                if proposed_lower is None:
                    return current
                return proposed if proposed_lower > current_lower else current
        return proposed if proposed_rank > current_rank else current
    if policy_version >= 2:
        current_lower = _search_lower_bound_persistence_rank(current)
        proposed_lower = _search_lower_bound_persistence_rank(proposed)
        if current_lower != proposed_lower:
            if current_lower is None:
                return proposed
            if proposed_lower is None:
                return current
            return proposed if proposed_lower > current_lower else current
    current_distance = _positive_distance(current)
    proposed_distance = _positive_distance(proposed)
    if current_distance is not None and proposed_distance is not None:
        # BP-OSD produces feasible logicals and therefore distance *upper*
        # bounds. The minimum observation is the informative conservative
        # value; taking max selected the loosest/noisiest run.
        if proposed_distance != current_distance:
            return proposed if proposed_distance < current_distance else current
    if proposed_rank == 0:
        current_lane = current.get("candidate_persistence_lane")
        proposed_lane = proposed.get("candidate_persistence_lane")
        current_persistence = _zero_distance_persistence_rank(current)
        proposed_persistence = _zero_distance_persistence_rank(proposed)
        if proposed_persistence != current_persistence:
            return (
                proposed
                if proposed_persistence > current_persistence
                else current
            )
        if proposed_lane and not current_lane:
            return proposed
        if current_lane and not proposed_lane:
            return current
    if (
        policy_version
        >= CANDIDATE_BATCH_POLICY_COMPOSITE_PROVENANCE_VERSION
    ):
        # Every evidence/lifecycle tie must have a content-addressed winner;
        # otherwise reversing raw occurrence order changes the primary row
        # beneath an otherwise canonical composite proof bundle.
        return (
            proposed
            if _canonical_payload_sha256(proposed)
            > _canonical_payload_sha256(current)
            else current
        )
    return current


def _valid_candidate_sha256(row: Mapping[str, Any]) -> str | None:
    value = row.get("candidate_sha256")
    if (
        isinstance(value, str)
        and re.fullmatch(r"[0-9a-f]{64}", value) is not None
    ):
        return value
    return None


def _trusted_search_upper_bound(
    row: dict[str, Any],
) -> tuple[int, dict[str, Any], dict[str, Any]] | None:
    """Replay one SAT oracle artifact and return its mathematical UB.

    Reported ``d``/upper-bound/status fields are deliberately ignored.  The
    returned weight comes only from the self-hashed oracle witness after the
    candidate matrices and logical action have been independently rebuilt.
    """

    geometry = replay_search_oracle_upper_bound_geometry(row)
    oracle = row.get("low_weight_oracle")
    witness = oracle.get("witness") if isinstance(oracle, dict) else None
    if (
        geometry is None
        or not isinstance(oracle, dict)
        or not isinstance(witness, dict)
        or type(geometry.get("weight")) is not int
        or geometry["weight"] < 1
        or witness.get("weight") != geometry["weight"]
        or not isinstance(oracle.get("evidence_sha256"), str)
        or re.fullmatch(
            r"[0-9a-f]{64}", str(oracle.get("evidence_sha256"))
        ) is None
    ):
        return None
    return (
        geometry["weight"],
        copy.deepcopy(oracle),
        copy.deepcopy(witness),
    )


_COMPOSITE_LEDGER_KIND = "qcode-coset-stage1-proof-ledger-v1"
_COMPOSITE_LEDGER_ENTRY_FIELDS = (
    "threshold",
    "outcome",
    "evidence_sha256",
    "attempt_sha256",
    "cache_sha256",
)
_COMPOSITE_HISTORY_ENTRY_FIELDS = frozenset({
    *_COMPOSITE_LEDGER_ENTRY_FIELDS,
    "attempts",
    "cache_hit",
})
_COMPOSITE_GENERATION_BINDING_FIELDS = (
    "threshold",
    "outcome",
    "attempts",
    "evidence_sha256",
    "attempt_sha256",
    "cache_sha256",
)
_COMPOSITE_STAGE1_SEARCH_STATUSES = frozenset({
    "challenge_threshold_survivor",
    "fom_threshold_survivor",
    "partial_lower_bound",
    "partial_lower_bound_budget",
    "partial_lower_bound_retry",
    "terminal_negative",
    "unresolved",
    "unresolved_budget",
})


def _sealed_oracle_provenance(
    row: Mapping[str, Any],
    *,
    candidate_sha256: str,
) -> tuple[list[dict[str, Any]], int] | None:
    """Return one internally coherent v3 attempt history and ledger.

    Policy-v5 may combine generations only after each source occurrence proves
    that its occurrence-local history, last-attempt triple, and self-hashed
    ledger describe the same cache generations.  Older ladder schemas remain
    opaque so historical policy bytes can still be replayed unchanged.
    """

    history = row.get("oracle_ladder_history")
    ledger = row.get("proof_ledger")
    declared_v3 = bool(
        row.get("oracle_ladder_schema_version") == 3
        or isinstance(ledger, dict)
        and ledger.get("proof_ladder_version") == 3
    )
    if not declared_v3:
        return None
    if not isinstance(history, list) or not isinstance(ledger, dict):
        raise RoundTransactionError(
            "policy-v5 declared v3 provenance is incomplete"
        )
    proof_ladder_version = ledger.get("proof_ladder_version")
    if type(proof_ladder_version) is not int or proof_ladder_version != 3:
        raise RoundTransactionError(
            "policy-v5 oracle/ledger schema versions disagree"
        )
    row_ladder_version = row.get("oracle_ladder_schema_version")
    if row_ladder_version is not None and (
        type(row_ladder_version) is not int or row_ladder_version != 3
    ):
        raise RoundTransactionError(
            "policy-v5 oracle/ledger schema versions disagree"
        )
    if (
        ledger.get("kind") != _COMPOSITE_LEDGER_KIND
        or type(ledger.get("schema_version")) is not int
        or ledger.get("schema_version") != 1
        or ledger.get("candidate_sha256") != candidate_sha256
        or not isinstance(ledger.get("entries"), list)
    ):
        raise RoundTransactionError(
            "policy-v5 source proof ledger is malformed"
        )
    entries: list[dict[str, Any]] = []
    thresholds: list[int] = []
    for raw in history:
        if not isinstance(raw, dict):
            raise RoundTransactionError(
                "policy-v5 source oracle history is malformed"
            )
        if set(raw) != _COMPOSITE_HISTORY_ENTRY_FIELDS:
            raise RoundTransactionError(
                "policy-v5 source oracle history fields are malformed"
            )
        threshold = raw.get("threshold")
        outcome = raw.get("outcome")
        attempts = raw.get("attempts")
        if (
            isinstance(threshold, bool)
            or not isinstance(threshold, int)
            or threshold < 1
            or outcome not in {"SAT", "UNSAT", "UNKNOWN"}
            or isinstance(attempts, bool)
            or not isinstance(attempts, int)
            or attempts < 1
            or not isinstance(raw.get("cache_hit"), bool)
        ):
            raise RoundTransactionError(
                "policy-v5 source oracle history entry is malformed"
            )
        for field in ("attempt_sha256", "cache_sha256"):
            value = raw.get(field)
            if (
                not isinstance(value, str)
                or re.fullmatch(r"[0-9a-f]{64}", value) is None
            ):
                raise RoundTransactionError(
                    "policy-v5 source oracle history digest is malformed"
                )
        evidence_sha256 = raw.get("evidence_sha256")
        if (
            evidence_sha256 is not None
            and (
                not isinstance(evidence_sha256, str)
                or re.fullmatch(r"[0-9a-f]{64}", evidence_sha256) is None
            )
        ):
            raise RoundTransactionError(
                "policy-v5 source oracle evidence digest is malformed"
            )
        if (
            (
                outcome in {"SAT", "UNSAT"}
                and evidence_sha256 is None
            )
            or (
                outcome == "UNKNOWN"
                and evidence_sha256 is not None
            )
        ):
            raise RoundTransactionError(
                "policy-v5 source oracle outcome/evidence binding is invalid"
            )
        thresholds.append(threshold)
        entries.append({
            field: copy.deepcopy(raw.get(field))
            for field in _COMPOSITE_LEDGER_ENTRY_FIELDS
        })
    if thresholds != sorted(set(thresholds)):
        raise RoundTransactionError(
            "policy-v5 source oracle history is not threshold-unique"
        )
    ladder = row.get("oracle_ladder_thresholds")
    if (
        not isinstance(ladder, list)
        or not ladder
        or any(
            isinstance(value, bool)
            or not isinstance(value, int)
            or value < 1
            for value in ladder
        )
        or ladder != sorted(set(ladder))
        or thresholds != ladder[:len(thresholds)]
        or any(
            entry["outcome"] != "UNSAT"
            for entry in history[:-1]
        )
    ):
        raise RoundTransactionError(
            "policy-v5 source oracle history is not a valid ladder prefix"
        )
    ladder_cutoff = row.get("oracle_ladder_cutoff")
    if (
        type(ladder_cutoff) is not int
        or ladder_cutoff != ladder[-1]
    ):
        raise RoundTransactionError(
            "policy-v5 source oracle ladder cutoff is malformed"
        )
    expected_ledger = {
        "kind": _COMPOSITE_LEDGER_KIND,
        "schema_version": 1,
        "proof_ladder_version": proof_ladder_version,
        "candidate_sha256": candidate_sha256,
        "entries": entries,
    }
    expected_ledger["root_sha256"] = _canonical_payload_sha256(
        expected_ledger
    )
    try:
        ledger_matches = (
            _canonical_compact_json(ledger)
            == _canonical_compact_json(expected_ledger)
        )
    except RoundTransactionError:
        ledger_matches = False
    if not ledger_matches:
        raise RoundTransactionError(
            "policy-v5 source oracle history disagrees with its proof ledger"
        )

    last_attempt = row.get("oracle_last_attempt")
    if not history:
        if (
            last_attempt is not None
            or "oracle_last_attempt_outcome" in row
            or "oracle_last_attempt_threshold" in row
        ):
            raise RoundTransactionError(
                "policy-v5 source contains a phantom last-attempt triple"
            )
    else:
        tail = history[-1]
        last_attempt_threshold = row.get("oracle_last_attempt_threshold")
        unsigned_last_attempt = (
            dict(last_attempt) if isinstance(last_attempt, dict) else {}
        )
        claimed_attempt_sha256 = unsigned_last_attempt.pop(
            "attempt_sha256", None
        )
        try:
            last_attempt_hash_valid = bool(
                isinstance(last_attempt, dict)
                and claimed_attempt_sha256
                == _canonical_payload_sha256(unsigned_last_attempt)
            )
        except (RoundTransactionError, TypeError, ValueError):
            last_attempt_hash_valid = False
        if (
            not isinstance(last_attempt, dict)
            or not last_attempt_hash_valid
            or last_attempt.get("attempt_sha256")
            != tail.get("attempt_sha256")
            or last_attempt.get("outcome") != tail.get("outcome")
            or row.get("oracle_last_attempt_outcome")
            != tail.get("outcome")
            or type(last_attempt_threshold) is not int
            or last_attempt_threshold != tail.get("threshold")
        ):
            raise RoundTransactionError(
                "policy-v5 source last-attempt triple disagrees with history"
            )
    return copy.deepcopy(history), proof_ladder_version


def _canonicalize_composite_oracle_provenance(
    merged: dict[str, Any],
    occurrences: list[dict[str, Any]],
    *,
    required_lower_evidence_sha256: str | None,
    required_upper_evidence_sha256: str | None,
    normalize_stage1_lifecycle: bool,
) -> dict[str, Any]:
    """Build an order-independent proof ladder from sealed occurrences."""

    candidate_sha256 = _valid_candidate_sha256(merged)
    if candidate_sha256 is None:
        return merged
    sources: list[tuple[dict[str, Any], list[dict[str, Any]]]] = []
    ladder_versions: set[int] = set()
    declared_v3 = False
    for row in occurrences:
        ledger = row.get("proof_ledger")
        if (
            row.get("oracle_ladder_schema_version") == 3
            or isinstance(ledger, dict)
            and ledger.get("proof_ladder_version") == 3
        ):
            declared_v3 = True
        sealed = _sealed_oracle_provenance(
            row,
            candidate_sha256=candidate_sha256,
        )
        if sealed is None:
            continue
        history, version = sealed
        ladder_versions.add(version)
        sources.append((row, history))
    if not declared_v3:
        # Pre-v3 synthetic/unit-test rows are outside this migration.
        return merged
    if not sources or ladder_versions != {3}:
        raise RoundTransactionError(
            "policy-v5 has no coherent v3 oracle provenance source"
        )

    ladders = {
        tuple(row.get("oracle_ladder_thresholds", ()))
        for row, _history in sources
    }
    if (
        len(ladders) != 1
        or not ladders
        or not all(
            isinstance(value, int) and not isinstance(value, bool) and value > 0
            for value in next(iter(ladders))
        )
    ):
        raise RoundTransactionError(
            "policy-v5 source oracle ladders disagree"
        )
    ladder = next(iter(ladders))

    cache_bindings: dict[str, tuple[Any, ...]] = {}
    by_threshold: dict[
        int, list[tuple[dict[str, Any], dict[str, Any]]]
    ] = {}
    for row, history in sources:
        for entry in history:
            binding = tuple(
                entry[field]
                for field in _COMPOSITE_GENERATION_BINDING_FIELDS
            )
            cache_sha256 = str(entry["cache_sha256"])
            previous_cache_binding = cache_bindings.setdefault(
                cache_sha256, binding
            )
            if previous_cache_binding != binding:
                raise RoundTransactionError(
                    "policy-v5 cache SHA binds conflicting generation metadata"
                )
            by_threshold.setdefault(int(entry["threshold"]), []).append(
                (row, entry)
            )

    chosen: list[
        tuple[dict[str, Any], list[tuple[dict[str, Any], dict[str, Any]]]]
    ] = []
    for threshold in sorted(by_threshold):
        candidates = by_threshold[threshold]
        terminal_outcomes = {
            entry["outcome"]
            for _row, entry in candidates
            if entry["outcome"] in {"SAT", "UNSAT"}
        }
        if len(terminal_outcomes) > 1:
            raise RoundTransactionError(
                "policy-v5 found conflicting SAT/UNSAT cache generations"
            )
        outcome = (
            next(iter(terminal_outcomes))
            if terminal_outcomes else "UNKNOWN"
        )
        candidates = [
            item for item in candidates if item[1]["outcome"] == outcome
        ]
        generation = max(
            (int(entry["attempts"]), str(entry["cache_sha256"]))
            for _row, entry in candidates
        )
        generation_sources = [
            item for item in candidates
            if (
                int(item[1]["attempts"]),
                str(item[1]["cache_sha256"]),
            ) == generation
        ]
        immutable_fields = {
            tuple(entry.get(field) for field in _COMPOSITE_LEDGER_ENTRY_FIELDS)
            for _row, entry in generation_sources
        }
        if len(immutable_fields) != 1:
            raise RoundTransactionError(
                "policy-v5 cache generation metadata conflicts"
            )
        entry = copy.deepcopy(generation_sources[0][1])
        # Cache-hit is occurrence-local.  The composite records whether this
        # exact immutable generation was ever hydrated, deterministically.
        entry["cache_hit"] = any(
            bool(source_entry["cache_hit"])
            for _row, source_entry in generation_sources
        )
        chosen.append((entry, generation_sources))

    thresholds = [entry["threshold"] for entry, _sources in chosen]
    if thresholds != list(ladder[:len(thresholds)]):
        raise RoundTransactionError(
            "policy-v5 composite oracle history is not a ladder prefix"
        )
    non_unsat = [
        index for index, (entry, _sources) in enumerate(chosen)
        if entry["outcome"] != "UNSAT"
    ]
    if non_unsat and non_unsat != [len(chosen) - 1]:
        raise RoundTransactionError(
            "policy-v5 composite ladder advances beyond a terminal/UNKNOWN rung"
        )

    history = [copy.deepcopy(entry) for entry, _sources in chosen]
    composite_ledger = {
        "kind": _COMPOSITE_LEDGER_KIND,
        "schema_version": 1,
        "proof_ladder_version": 3,
        "candidate_sha256": candidate_sha256,
        "entries": [{
            field: copy.deepcopy(entry.get(field))
            for field in _COMPOSITE_LEDGER_ENTRY_FIELDS
        } for entry in history],
    }
    composite_ledger["root_sha256"] = _canonical_payload_sha256(
        composite_ledger
    )
    if (
        any(entry["outcome"] == "UNSAT" for entry in composite_ledger["entries"])
        and required_lower_evidence_sha256 is None
    ):
        raise RoundTransactionError(
            "policy-v5 UNSAT history has no selected lower-bound artifact"
        )
    if (
        any(entry["outcome"] == "SAT" for entry in composite_ledger["entries"])
        and required_upper_evidence_sha256 is None
    ):
        raise RoundTransactionError(
            "policy-v5 SAT history has no replayed upper-bound artifact"
        )
    if required_lower_evidence_sha256 is not None and not any(
        entry["outcome"] == "UNSAT"
        and entry["evidence_sha256"] == required_lower_evidence_sha256
        for entry in composite_ledger["entries"]
    ):
        raise RoundTransactionError(
            "policy-v5 composite ledger dropped the selected lower bound"
        )
    if required_upper_evidence_sha256 is not None and not any(
        entry["outcome"] == "SAT"
        and entry["evidence_sha256"] == required_upper_evidence_sha256
        for entry in composite_ledger["entries"]
    ):
        raise RoundTransactionError(
            "policy-v5 composite ledger dropped the selected upper bound"
        )

    merged.update({
        "oracle_ladder_schema_version": 3,
        "oracle_ladder_cutoff": ladder[-1],
        "oracle_ladder_thresholds": list(ladder),
        "oracle_ladder_history": history,
        "proof_ledger": composite_ledger,
    })
    injected_sequences = [
        int(row["global_proof_frontier_first_seen_sequence"])
        for row, _history in sources
        if row.get("global_proof_frontier_injected") is True
        and isinstance(
            row.get("global_proof_frontier_first_seen_sequence"), int
        )
        and not isinstance(
            row.get("global_proof_frontier_first_seen_sequence"), bool
        )
    ]
    if injected_sequences:
        merged["global_proof_frontier_injected"] = True
        merged["global_proof_frontier_first_seen_sequence"] = min(
            injected_sequences
        )
    else:
        merged.pop("global_proof_frontier_injected", None)
        merged.pop("global_proof_frontier_first_seen_sequence", None)
    if not chosen:
        merged["oracle_last_attempt"] = None
        merged.pop("oracle_last_attempt_outcome", None)
        merged.pop("oracle_last_attempt_threshold", None)
    else:
        tail, tail_sources = chosen[-1]
        authorities: list[
            tuple[str, str, dict[str, Any], dict[str, Any]]
        ] = []
        for row, source_entry in tail_sources:
            last_attempt = row.get("oracle_last_attempt")
            if (
                isinstance(last_attempt, dict)
                and row.get("oracle_last_attempt_threshold")
                == tail["threshold"]
                and row.get("oracle_last_attempt_outcome")
                == tail["outcome"]
                and last_attempt.get("attempt_sha256")
                == tail["attempt_sha256"]
            ):
                authorities.append((
                    _canonical_payload_sha256(last_attempt),
                    _canonical_payload_sha256(row),
                    row,
                    last_attempt,
                ))
        if not authorities:
            raise RoundTransactionError(
                "policy-v5 composite tail has no last-attempt authority"
            )
        _attempt_tie_break, _row_tie_break, authority, last_attempt = max(
            authorities,
            key=lambda item: (item[0], item[1]),
        )
        merged["oracle_last_attempt"] = copy.deepcopy(last_attempt)
        merged["oracle_last_attempt_outcome"] = tail["outcome"]
        merged["oracle_last_attempt_threshold"] = tail["threshold"]
        for field in (
            "oracle_frontier_selected",
            "oracle_batch_budget_exhausted",
        ):
            if field in authority:
                merged[field] = copy.deepcopy(authority[field])
            else:
                merged.pop(field, None)

    if normalize_stage1_lifecycle:
        tail_outcome = None if not history else history[-1]["outcome"]
        complete = bool(
            tail_outcome == "SAT"
            or history
            and tail_outcome == "UNSAT"
            and len(history) == len(ladder)
        )
        deferred = bool(
            not complete
            and (
                not history
                or tail_outcome == "UNSAT"
                or tail_outcome == "UNKNOWN"
                and history[-1]["cache_hit"] is True
            )
        )
        merged.update({
            "low_weight_oracle_outcome": (
                "NOT_RUN" if tail_outcome is None else tail_outcome
            ),
            "oracle_ladder_complete": complete,
            "oracle_retryable": not complete,
            "distance_retry_required": not complete,
            "oracle_deferred": deferred,
            "oracle_ladder_next_threshold": (
                None
                if complete
                else history[-1]["threshold"]
                if tail_outcome == "UNKNOWN"
                else ladder[len(history)]
            ),
        })
        if required_upper_evidence_sha256 is not None:
            # The trusted upper-bound merge above decides whether this is a
            # selected-target rejection.  It is always terminal with respect
            # to the Stage-1 proof ladder itself.
            merged.update({
                "oracle_ladder_complete": True,
                "oracle_retryable": False,
                "distance_retry_required": False,
                "oracle_deferred": False,
                "oracle_ladder_next_threshold": None,
            })
        elif complete:
            merged["search_status"] = (
                "fom_threshold_survivor"
                if merged.get("fom_target_lower_bound_proven") is True
                else "challenge_threshold_survivor"
                if merged.get("challenge_target_lower_bound_proven") is True
                else "partial_lower_bound"
            )
        elif required_lower_evidence_sha256 is not None:
            merged["search_status"] = (
                "partial_lower_bound_budget"
                if deferred else "partial_lower_bound_retry"
            )
        else:
            merged["search_status"] = (
                "unresolved_budget" if deferred else "unresolved"
            )

    proof = merged.get("search_distance_interval_proof")
    if isinstance(proof, dict) and required_lower_evidence_sha256 is not None:
        proof = copy.deepcopy(proof)
        proof["lower_bound_ledger_root_sha256"] = composite_ledger[
            "root_sha256"
        ]
        proof.pop("proof_sha256", None)
        proof["proof_sha256"] = _canonical_payload_sha256(proof)
        merged["search_distance_interval_proof"] = proof
    return merged


def _merge_duplicate_search_evidence(
    selected: dict[str, Any],
    occurrences: list[dict[str, Any]],
    *,
    policy_version: int = CANDIDATE_BATCH_POLICY_VERSION,
) -> dict[str, Any]:
    """Merge independently replayable LB/UB evidence for one definition.

    Policy-v3+ canonicalization is evidence-preserving rather than row-
    preserving: a Stage-1 UNSAT lower bound and a later SAT upper witness may
    live on different raw occurrences of the same candidate.  Only rows with
    the selected candidate's exact SHA-256 identity participate.  The merged
    interval remains a search artifact and never impersonates a formal
    release/MILP exact proof.
    """

    if (
        isinstance(policy_version, bool)
        or policy_version not in CANDIDATE_BATCH_POLICY_VERSIONS
    ):
        raise ValueError(
            f"unsupported candidate batch policy version: {policy_version!r}"
        )

    candidate_sha256 = _valid_candidate_sha256(selected)
    merged = copy.deepcopy(selected)
    for field in (
        "search_distance_interval_exact",
        "search_distance_interval_proof",
        "search_distance_interval_status",
        "search_exact_distance",
    ):
        # Never carry a self-declared interval through policy-v3.  It is
        # rebuilt below only from evidence replayed in this invocation.
        merged.pop(field, None)
    if candidate_sha256 is None:
        return merged
    same_candidate = [
        row
        for row in occurrences
        if _valid_candidate_sha256(row) == candidate_sha256
    ]
    if not same_candidate:
        return merged

    lower_candidates: list[
        tuple[tuple[int, int], str, dict[str, Any]]
    ] = []
    upper_candidates: list[
        tuple[int, str, dict[str, Any], dict[str, Any], dict[str, Any]]
    ] = []
    for row in same_candidate:
        lower_rank = _search_lower_bound_persistence_rank(row)
        if lower_rank is not None:
            lower_candidates.append(
                (lower_rank, _canonical_payload_sha256(row), row)
            )
        upper = _trusted_search_upper_bound(row)
        if upper is not None:
            weight, oracle, witness = upper
            upper_candidates.append(
                (
                    weight,
                    _canonical_payload_sha256(row),
                    row,
                    oracle,
                    witness,
                )
            )

    lower_row: dict[str, Any] | None = None
    lower_bound: int | None = None
    lower_complete = False
    if lower_candidates:
        lower_rank, _tie_break, lower_row = max(
            lower_candidates,
            key=lambda item: (item[0], item[1]),
        )
        lower_bound, complete_rank = lower_rank
        lower_complete = bool(complete_rank)
        for field in (
            "distance_lower_bound_evidence",
            "proof_ledger",
        ):
            merged[field] = copy.deepcopy(lower_row[field])
        merged.update({
            "distance_lower_bound": lower_bound,
            "distance_lower_bound_proven": True,
            "distance_lower_bound_status": "search_oracle_proven",
            "distance_lower_bound_evidence_sha256": lower_row[
                "distance_lower_bound_evidence_sha256"
            ],
            "oracle_ladder_complete": lower_complete,
        })

    upper_bound: int | None = None
    upper_oracle: dict[str, Any] | None = None
    upper_witness: dict[str, Any] | None = None
    if upper_candidates:
        (
            upper_bound,
            _tie_break,
            _upper_row,
            upper_oracle,
            upper_witness,
        ) = min(upper_candidates, key=lambda item: (item[0], item[1]))
        if policy_version >= CANDIDATE_BATCH_POLICY_WITNESS_METADATA_VERSION:
            # These annotations form one archive-snapshot-dependent bundle.
            # Once the SAT row supplies the canonical witness, retaining any
            # member from the selected LB row would bind penalty provenance to
            # the wrong occurrence.  Missing fields are cleared rather than
            # silently falling back to stale LB metadata.
            for field in (
                "negative_archive_match_counts",
                "negative_archive_coordinate_sha256",
                "negative_archive_penalty",
                "negative_archive_penalty_components",
                "negative_archive_witness_match_counts",
                "negative_archive_witness_motif_sha256",
            ):
                if field in _upper_row:
                    merged[field] = copy.deepcopy(_upper_row[field])
                else:
                    merged.pop(field, None)
            # Attempt history is likewise occurrence-local.  The evidence
            # digest itself is normalized from the replayed oracle rather than
            # trusted from either row's scalar metadata.
            for field in (
                "oracle_ladder_history",
                "oracle_last_attempt",
                "oracle_last_attempt_outcome",
                "oracle_last_attempt_threshold",
                "oracle_frontier_selected",
                "oracle_batch_budget_exhausted",
            ):
                if field in _upper_row:
                    merged[field] = copy.deepcopy(_upper_row[field])
                else:
                    merged.pop(field, None)
            merged["oracle_evidence_sha256"] = upper_oracle[
                "evidence_sha256"
            ]
        merged.update({
            "d": upper_bound,
            "d_is_exact": False,
            "distance_trusted": False,
            "distance_status": "upper_bound",
            "distance_upper_bound": upper_bound,
            "distance_upper_bound_source": "low_weight_oracle",
            "low_weight_oracle": upper_oracle,
            "low_weight_oracle_outcome": "SAT",
            "low_weight_oracle_threshold": upper_oracle["max_weight"],
            "low_weight_witness": upper_witness,
            "threshold_proof_distance": upper_bound,
            "threshold_proof_source": "low_weight_oracle",
            "threshold_proof_witness": upper_witness,
            # A replayed feasible logical is an upper bound only, so it never
            # earns positive search fitness even when paired with an LB.
            "score": 0.0,
        })

    def finalize_provenance(
        value: dict[str, Any],
        *,
        normalize_stage1_lifecycle: bool | None = None,
    ) -> dict[str, Any]:
        if (
            policy_version
            < CANDIDATE_BATCH_POLICY_COMPOSITE_PROVENANCE_VERSION
        ):
            return value
        if normalize_stage1_lifecycle is None:
            evidence_rank = _distance_evidence_rank(value)
            n = value.get("n")
            k = value.get("k")
            normalize_stage1_lifecycle = bool(
                evidence_rank < 2
                and (
                    lower_row is not None
                    or upper_oracle is not None
                    or evidence_rank == 0
                )
                and type(n) is int
                and type(k) is int
                and n >= 1
                and 1 <= k <= n
                and value.get("static_legal") is not False
                and value.get("target_binding_status") != "conflict"
                and value.get("search_status")
                in _COMPOSITE_STAGE1_SEARCH_STATUSES
            )
        return _canonicalize_composite_oracle_provenance(
            value,
            same_candidate,
            required_lower_evidence_sha256=(
                None
                if lower_row is None
                else str(lower_row["distance_lower_bound_evidence_sha256"])
            ),
            required_upper_evidence_sha256=(
                None
                if upper_oracle is None
                else str(upper_oracle["evidence_sha256"])
            ),
            normalize_stage1_lifecycle=normalize_stage1_lifecycle,
        )

    if lower_bound is None and upper_bound is None:
        return finalize_provenance(merged)
    n = merged.get("n")
    k = merged.get("k")
    if (
        type(n) is not int
        or type(k) is not int
        or n < 1
        or not 1 <= k <= n
    ):
        return finalize_provenance(
            merged,
            normalize_stage1_lifecycle=False,
        )
    from evaluation.evaluator import compute_challenge_rejection_cutoff
    from evaluation.target_policy import (
        DEFAULT_TARGET_MODE,
        TARGET_MODE_SCALAR,
        target_binding,
        validate_target_mode,
    )

    explicit_modes: set[str] = set()
    invalid_target_binding = False
    prior_target_conflict = False
    for occurrence in same_candidate:
        if occurrence.get("target_binding_status") == "conflict":
            prior_target_conflict = True
            carried_modes = occurrence.get("target_mode_conflict")
            if isinstance(carried_modes, list):
                for carried_mode in carried_modes:
                    try:
                        explicit_modes.add(validate_target_mode(carried_mode))
                    except ValueError:
                        invalid_target_binding = True
            invalid_target_binding = bool(
                invalid_target_binding
                or occurrence.get("target_binding_invalid") is True
            )
        occurrence_modes: set[str] = set()
        for field in ("target_mode", "proof_target_mode"):
            raw_mode = occurrence.get(field)
            if raw_mode is None:
                continue
            try:
                occurrence_modes.add(validate_target_mode(raw_mode))
            except ValueError:
                invalid_target_binding = True
        explicit_modes.update(occurrence_modes)
        supplied_target = occurrence.get("target")
        if supplied_target is not None:
            try:
                normalized_target = validate_target_binding(
                    supplied_target,
                    n,
                    k,
                    (
                        next(iter(occurrence_modes))
                        if len(occurrence_modes) == 1
                        else None
                    ),
                )
                explicit_modes.add(normalized_target["mode"])
            except ValueError:
                invalid_target_binding = True
    if (
        prior_target_conflict
        or invalid_target_binding
        or len(explicit_modes) > 1
    ):
        # Mathematical LB/UB evidence remains useful, but evidence produced
        # under conflicting target contracts must never be converted into a
        # terminal rejection, exact search result, or implicit legacy-gist
        # decision.  Stage 2 may later rebind and replay it under its
        # authoritative campaign target.
        for field in (
            "target",
            "target_mode",
            "proof_target_mode",
            "target_required_distance",
            "target_binding_sha256",
            "selected_target_lower_bound_proven",
            "selected_target_excluded_by_upper_bound",
            "threshold_rejected",
            "threshold_rejection_proven",
            "search_exact_distance",
            "search_distance_interval_proof",
        ):
            merged.pop(field, None)
        merged.update({
            "target_binding_status": "conflict",
            "target_mode_conflict": sorted(explicit_modes),
            "target_binding_invalid": invalid_target_binding,
            "search_status": "unresolved_target_conflict",
            "search_distance_interval_status": "target_mode_conflict",
            "search_distance_interval_exact": False,
            "distance_retry_required": False,
            "oracle_retryable": False,
            "score": 0.0,
        })
        return finalize_provenance(
            merged,
            normalize_stage1_lifecycle=False,
        )
    selected_mode = (
        next(iter(explicit_modes))
        if len(explicit_modes) == 1
        else DEFAULT_TARGET_MODE
    )
    selected_target = target_binding(n, k, selected_mode)
    scalar_target = target_binding(n, k, TARGET_MODE_SCALAR)
    selected_minimum_distance = int(selected_target["required_distance"])
    selected_cutoff = int(selected_target["rejection_cutoff"])
    strict_minimum_distance = int(scalar_target["required_distance"])
    strict_cutoff = int(scalar_target["rejection_cutoff"])
    challenge_cutoff = compute_challenge_rejection_cutoff(n, k, 12.0)
    merged.update({
        "target_mode": selected_mode,
        "proof_target_mode": selected_mode,
        "target": selected_target,
        "target_required_distance": selected_minimum_distance,
        "target_binding_sha256": selected_target["binding_sha256"],
        "minimum_scalar_fom_distance": strict_minimum_distance,
        "fom_rejection_cutoff": strict_cutoff,
        "challenge_rejection_cutoff": challenge_cutoff,
    })
    if lower_bound is not None:
        merged["fom_lower_bound"] = k * lower_bound * lower_bound / n
        merged["challenge_target_lower_bound_proven"] = bool(
            lower_bound > challenge_cutoff
        )
        merged["fom_target_lower_bound_proven"] = bool(
            lower_bound >= strict_minimum_distance
        )
        merged["selected_target_lower_bound_proven"] = bool(
            lower_bound >= selected_minimum_distance
        )
    if upper_bound is not None:
        upper_fom = k * upper_bound * upper_bound / n
        merged["fom"] = upper_fom
        merged["fom_upper_bound"] = upper_fom

    if lower_bound is not None and upper_bound is not None:
        if lower_bound == upper_bound:
            interval_status = "exact"
        elif lower_bound < upper_bound:
            interval_status = "bounded"
        else:
            interval_status = "inconsistent_evidence"
    elif lower_bound is not None:
        interval_status = "lower_bound_only"
    else:
        interval_status = "upper_bound_only"
    interval_exact = interval_status == "exact"
    selected_target_excluded = bool(
        upper_bound is not None and upper_bound <= selected_cutoff
    )
    scalar_excluded = bool(
        upper_bound is not None and upper_bound <= strict_cutoff
    )
    proof = {
        "schema_version": SEARCH_DISTANCE_INTERVAL_PROOF_SCHEMA_VERSION,
        "kind": SEARCH_DISTANCE_INTERVAL_PROOF_KIND,
        "candidate_sha256": candidate_sha256,
        "lower_bound": lower_bound,
        "lower_bound_evidence_sha256": (
            lower_row["distance_lower_bound_evidence_sha256"]
            if lower_row is not None
            else None
        ),
        "lower_bound_ledger_root_sha256": (
            lower_row["proof_ledger"]["root_sha256"]
            if lower_row is not None
            else None
        ),
        "upper_bound": upper_bound,
        "upper_bound_oracle_evidence_sha256": (
            upper_oracle["evidence_sha256"]
            if upper_oracle is not None
            else None
        ),
        "upper_bound_oracle_payload_sha256": (
            _canonical_payload_sha256(upper_oracle)
            if upper_oracle is not None
            else None
        ),
        "upper_bound_witness_sha256": (
            _canonical_payload_sha256(upper_witness)
            if upper_witness is not None
            else None
        ),
        "strict_fom_target": 12.0,
        "strict_fom_target_numerator": 12,
        "strict_fom_target_denominator": 1,
        "strict_fom_rejection_cutoff": strict_cutoff,
        "strict_fom_minimum_distance": strict_minimum_distance,
        "interval_status": interval_status,
        "interval_exact": interval_exact,
        "selected_target_mode": selected_mode,
        "selected_target_rejection_cutoff": selected_cutoff,
        "selected_target_minimum_distance": selected_minimum_distance,
        "terminal_excluded": selected_target_excluded,
    }
    proof["proof_sha256"] = _canonical_payload_sha256(proof)
    merged.update({
        "search_distance_interval_status": interval_status,
        "search_distance_interval_exact": interval_exact,
        "search_distance_interval_proof": proof,
        "strict_fom_minimum_distance": strict_minimum_distance,
    })
    if interval_exact:
        merged["search_exact_distance"] = upper_bound
    if upper_bound is not None:
        challenge_excluded = bool(
            upper_bound <= challenge_cutoff
        )
        merged.update({
            "selected_target_excluded_by_upper_bound": (
                selected_target_excluded
            ),
            "scalar_fom_excluded_by_upper_bound": scalar_excluded,
            "gist_challenge_excluded_by_upper_bound": challenge_excluded,
            "challenge_target_excluded_by_upper_bound": challenge_excluded,
            "fom_target_excluded_by_upper_bound": scalar_excluded,
            "final_gate_excluded_by_upper_bound": challenge_excluded,
            "search_final_gate_excluded_by_upper_bound": challenge_excluded,
            "gist_challenge_possible_despite_selected_target_exclusion": bool(
                selected_target_excluded and not challenge_excluded
            ),
        })
    if selected_target_excluded:
        merged.update({
            "search_status": "terminal_negative",
            "threshold_rejected": True,
            "threshold_rejection_proven": True,
            "distance_retry_required": False,
            "oracle_retryable": False,
            "oracle_deferred": False,
            "oracle_ladder_complete": True,
            "oracle_ladder_next_threshold": None,
            "candidate_persistence_lane": "negative_search_feedback",
            "candidate_persistence_reason": (
                "replayed_scalar_fom_excluding_logical_witness"
            ),
        })
        if policy_version >= CANDIDATE_BATCH_POLICY_WITNESS_METADATA_VERSION:
            # A replayed excluding witness is terminal and earns no search or
            # evolutionary credit, regardless of which LB row was initially
            # selected as the canonical occurrence.
            merged.update({
                "stage": "low_weight_oracle_rejected",
                "score": 0.0,
                "fitness": 0.0,
                "fitness_distance_credit": 0.0,
            })
    return finalize_provenance(merged)


def _deduplicate(
    rows: list[dict[str, Any]],
    *,
    policy_version: int = CANDIDATE_BATCH_POLICY_VERSION,
) -> list[dict[str, Any]]:
    if (
        isinstance(policy_version, bool)
        or policy_version not in CANDIDATE_BATCH_POLICY_VERSIONS
    ):
        raise ValueError(
            f"unsupported candidate batch policy version: {policy_version!r}"
        )
    best: dict[str, dict[str, Any]] = {}
    observations: dict[str, tuple[int, int, int]] = {}
    occurrences: dict[str, list[dict[str, Any]]] = {}
    for row in rows:
        key = code_key(row)
        occurrences.setdefault(key, []).append(row)
        summary = _bp_observation_summary(row)
        if summary is not None:
            previous = observations.get(key)
            if previous is None:
                observations[key] = summary
            else:
                observations[key] = (
                    previous[0] + summary[0],
                    min(previous[1], summary[1]),
                    max(previous[2], summary[2]),
                )
        current = best.get(key)
        if current is None:
            best[key] = row
        else:
            best[key] = _prefer_duplicate_evidence(
                current,
                row,
                policy_version=policy_version,
            )

    if policy_version >= CANDIDATE_BATCH_POLICY_EVIDENCE_MERGE_VERSION:
        for key, selected in list(best.items()):
            best[key] = _merge_duplicate_search_evidence(
                selected,
                occurrences[key],
                policy_version=policy_version,
            )

    for key, summary in observations.items():
        selected = best[key]
        if (
            len(occurrences[key]) > 1
            and _distance_evidence_rank(selected) == 1
        ):
            count, minimum, maximum = summary
            selected = copy.deepcopy(selected)
            best[key] = selected
            selected["bp_upper_bound_observations"] = {
                "count": count,
                "minimum_distance": minimum,
                "maximum_distance": maximum,
                "selected_distance": _positive_distance(selected),
                "selection_policy": "tightest_observed_upper_bound",
            }
    return list(best.values())


def _quick_exploration_priority(
    row: dict[str, Any],
) -> tuple[int, float, str] | None:
    """Validate an explicit quick-only marker and return its stable priority."""
    if (
        row.get("candidate_persistence_lane")
        != "winner_capable_quick_exploration"
        or row.get("winner_capable_parameters") is not True
        or _positive_distance(row) is not None
    ):
        return None
    required = row.get("minimum_winning_distance")
    singleton_upper = row.get("singleton_distance_upper_bound")
    if (
        isinstance(required, bool)
        or not isinstance(required, int)
        or required < 1
        or isinstance(singleton_upper, bool)
        or not isinstance(singleton_upper, int)
        or singleton_upper < required
    ):
        return None
    selected_distance_rank = _zero_distance_persistence_rank(row)
    return selected_distance_rank, singleton_upper / required, code_key(row)


def _search_lower_bound_audit_priority(
    row: dict[str, Any],
    lower_bound: int,
    *,
    target_mode: str,
) -> tuple[int, float, float, float, str] | None:
    """Rank one already-replayed lower bound for scarce exact-audit work."""

    n = row.get("n")
    k = row.get("k")
    if (
        isinstance(lower_bound, bool)
        or not isinstance(lower_bound, int)
        or lower_bound < 1
        or isinstance(n, bool)
        or not isinstance(n, int)
        or n < 1
        or isinstance(k, bool)
        or not isinstance(k, int)
        or not 1 <= k <= n
        or lower_bound > n
    ):
        return None
    try:
        required = int(
            target_binding(n, k, target_mode)["required_distance"]
        )
    except (KeyError, TypeError, ValueError):
        return None
    lower_fom = k * lower_bound * lower_bound / n
    return (
        int(lower_bound >= required),
        lower_bound / required,
        lower_fom,
        k / n,
        code_key(row),
    )


def _search_lower_bound_claim_priority(
    row: dict[str, Any],
    *,
    target_mode: str,
) -> tuple[int, float, float, float, str] | None:
    """Return an audit-only priority for a claimed positive search bound.

    This helper deliberately does not grant mathematical credit.  It only
    orders the small set of claims that :func:`select_for_milp` will replay
    before spending an exact-audit slot.  BP/OSD ``d`` and FOM magnitudes are
    absent: the ordering uses the claimed lower bound, the authoritative
    campaign target derived from ``(n, k)``, and the exact encoding rate.
    """

    lower_bound = row.get("distance_lower_bound")
    if (
        isinstance(lower_bound, bool)
        or not isinstance(lower_bound, int)
        or lower_bound < 1
        or row.get("distance_lower_bound_proven") is not True
        or row.get("distance_lower_bound_status")
        != "search_oracle_proven"
    ):
        return None
    return _search_lower_bound_audit_priority(
        row,
        lower_bound,
        target_mode=target_mode,
    )


def _replayable_search_lower_bound_for_audit(
    row: dict[str, Any],
) -> int | None:
    """Replay a positive search bound for scheduling, never final acceptance.

    Compact coset rows carry a source-bound proof-ledger contract checked by
    ``_search_lower_bound_persistence_rank`` and then receive a fresh matrix /
    two-sector oracle replay here.  Legacy/default BB rows reuse the
    evaluator's independent matrix/oracle replay.  Neither path changes exact-
    distance or final-gate semantics: the returned value is consumed solely
    by the scarce Stage-1 audit scheduler.
    """

    ledger_rank = _search_lower_bound_persistence_rank(row)
    if ledger_rank is not None:
        # A proof-ledger self-hash is durable provenance, but is not by itself
        # mathematical authority.  Rebuild the claimed construction and rerun
        # the deterministic two-sector UNSAT verifier before this row can gain
        # even audit-scheduling priority.
        try:
            from evaluation.construction import build_css_code_from_claim
            from evaluation.distance_milp import get_code_matrices
            from evaluation.low_weight_oracle import (
                verify_css_low_weight_oracle,
            )

            code = build_css_code_from_claim(row)
            n = row.get("n")
            k = row.get("k")
            if (
                isinstance(n, bool)
                or not isinstance(n, int)
                or isinstance(k, bool)
                or not isinstance(k, int)
                or int(code.num_qudits) != n
                or int(code.dimension) != k
            ):
                return None
            hx, hz, lx, lz = get_code_matrices(code)
            evidence = row.get("distance_lower_bound_evidence")
            if not isinstance(evidence, Mapping) or (
                verify_css_low_weight_oracle(evidence, hx, hz, lx, lz)
            ):
                return None
        except Exception:
            return None
        return ledger_rank[0]
    try:
        from evolve.openevolve_evaluator import (
            _normalized_stage2_lower_bound_row,
        )

        normalized = _normalized_stage2_lower_bound_row(row)
    except Exception:
        return None
    if normalized is None:
        return None
    lower_bound = normalized.get("distance_lower_bound")
    if isinstance(lower_bound, bool) or not isinstance(lower_bound, int):
        return None
    return lower_bound if lower_bound >= 1 else None


class _VerifiedStructuralDigestIndex:
    """Ephemeral capability produced only by one verified structural screen.

    The index is deliberately kept out of candidate rows and durable state.
    Each entry is bound to both the strict authoritative digest definition and
    the exact structural-screen input, while the whole index is bound to the
    structural-screen runtime fingerprint.  Any mismatch falls back to the
    existing independent Tanner canonicalization path.
    """

    __slots__ = ("_bindings", "_runtime_sha256")

    def __init__(
        self,
        screened_rows: list[dict[str, Any]],
        *,
        runtime_sha256_before_screen: str,
    ) -> None:
        from evaluation.structural_dedup import (
            StructuralScreenCacheError,
            structural_screen_input_sha256,
            structural_screen_runtime_fingerprint,
        )

        runtime_sha256_after_screen = (
            structural_screen_runtime_fingerprint()["sha256"]
        )
        if runtime_sha256_after_screen != runtime_sha256_before_screen:
            raise AuditStateError(
                "structural-screen runtime changed while building selector index"
            )
        bindings: dict[tuple[str, str], str] = {}
        invalid_bindings: set[tuple[str, str]] = set()
        for row in screened_rows:
            if isinstance(row.get("construction"), Mapping):
                # The structural screen dispatches these rows through their
                # construction schema, whereas authoritative_candidate_digest
                # deliberately rebuilds the legacy BB fields.  Never use one
                # representation as authority for the other.
                continue
            static = row.get("static_eligibility")
            novelty = row.get("structural_novelty")
            if (
                not isinstance(static, Mapping)
                or static.get("eligible") is not True
                or not isinstance(novelty, Mapping)
                or novelty.get("checked") is not True
                or novelty.get("novel") is not True
            ):
                # A test double or a future non-BB screen may return a row
                # outside this capability's closed schema.  Preserve the old
                # selector semantics by withholding reuse for that row.
                continue
            digest = novelty.get("canonical_digest")
            if (
                not isinstance(digest, str)
                or len(digest) != 64
                or any(character not in "0123456789abcdef" for character in digest)
            ):
                continue
            try:
                binding = (
                    candidate_digest_definition_sha256(row),
                    structural_screen_input_sha256(row),
                )
            except (
                AuditStateError,
                KeyError,
                OverflowError,
                StructuralScreenCacheError,
                TypeError,
                ValueError,
            ):
                # Some non-BB construction rows do not use the legacy
                # authoritative digest path.  Withhold the capability so the
                # selector preserves its existing independent behavior.
                continue
            if binding in invalid_bindings:
                continue
            previous = bindings.get(binding)
            if previous is not None and previous != digest:
                bindings.pop(binding, None)
                invalid_bindings.add(binding)
                continue
            bindings[binding] = digest
        self._bindings = bindings
        self._runtime_sha256 = runtime_sha256_after_screen

    @property
    def entry_count(self) -> int:
        return len(self._bindings)

    def require_current_runtime(self) -> None:
        from evaluation.structural_dedup import (
            structural_screen_runtime_fingerprint,
        )

        current = structural_screen_runtime_fingerprint()["sha256"]
        if current != self._runtime_sha256:
            raise AuditStateError(
                "verified structural-screen selector index is stale"
            )

    def digest_for(self, row: dict[str, Any]) -> str | None:
        from evaluation.structural_dedup import (
            StructuralScreenCacheError,
            structural_screen_input_sha256,
        )

        if isinstance(row.get("construction"), Mapping):
            return None
        try:
            binding = (
                candidate_digest_definition_sha256(row),
                structural_screen_input_sha256(row),
            )
        except (
            AuditStateError,
            KeyError,
            OverflowError,
            StructuralScreenCacheError,
            TypeError,
            ValueError,
        ):
            return None
        digest = self._bindings.get(binding)
        if digest is None:
            return None
        novelty = row.get("structural_novelty")
        if (
            not isinstance(novelty, Mapping)
            or novelty.get("canonical_digest") != digest
        ):
            return None
        return digest


def select_for_milp(
    new_elites: list[dict[str, Any]],
    archive: EliteArchive | None,
    audited_keys: set[str],
    limit: int,
    audited_digests: set[str] | None = None,
    *,
    policy_version: int = CANDIDATE_BATCH_POLICY_VERSION,
    target_mode: str = DEFAULT_TARGET_MODE,
    replay_structural_negatives: bool = True,
    formal_audit_slots: list[Mapping[str, int]] | None = None,
    prior_audit_rows: list[Mapping[str, Any]] | None = None,
    verified_structural_digests: _VerifiedStructuralDigestIndex | None = None,
) -> list[dict[str, Any]]:
    """Select diverse candidates without rewarding BP upper-bound magnitude."""
    selected_target_mode = validate_target_mode(target_mode)
    if not isinstance(replay_structural_negatives, bool):
        raise ValueError("replay_structural_negatives must be boolean")
    if (
        verified_structural_digests is not None
        and not isinstance(
            verified_structural_digests,
            _VerifiedStructuralDigestIndex,
        )
    ):
        raise TypeError("verified structural digests have an invalid type")
    if limit <= 0:
        return []
    if audited_digests and verified_structural_digests is not None:
        verified_structural_digests.require_current_runtime()
    archive_rows = [] if archive is None else archive.ranked()
    pool = _deduplicate(
        new_elites + archive_rows,
        policy_version=policy_version,
    )
    quick_ranked: list[
        tuple[tuple[int, float, str], dict[str, Any]]
    ] = []
    evidence_candidates: list[dict[str, Any]] = []
    for row in pool:
        if code_key(row) in audited_keys:
            continue
        static = row.get("static_eligibility") or {}
        novelty = row.get("structural_novelty") or {}
        if static and static.get("eligible") is not True:
            continue
        if novelty and novelty.get("novel") is not True:
            continue
        digest = None
        if audited_digests:
            if verified_structural_digests is not None:
                digest = verified_structural_digests.digest_for(row)
            if digest is None:
                digest = authoritative_candidate_digest(row)
        if audited_digests and digest and digest in audited_digests:
            continue
        quick_priority = _quick_exploration_priority(row)
        if (
            row.get("candidate_persistence_lane")
            == "winner_capable_quick_exploration"
            and quick_priority is None
        ):
            # A forged/partial marker is neither a valid exploration object
            # nor ordinary BP evidence; fail closed instead of laundering it
            # into the generic exploratory lane.
            continue
        if candidate_terminal_negative(row):
            # Only internally exact rejection evidence crosses this boundary.
            # Scalar or unreplayed upper bounds remain eligible for audit.
            continue
        if quick_priority is None:
            evidence_candidates.append(row)
        else:
            quick_ranked.append((quick_priority, row))
    quick_ranked.sort(key=lambda item: item[0], reverse=True)
    quick_exploration = [row for _priority, row in quick_ranked]
    structural_replay_limit = 4 * limit
    structural_attempted_keys: set[str] = set()
    lower_bound_replay_limit = 4 * limit
    lower_bound_replay_attempts = 0
    structural_negative_keys: set[str] = set()
    structural_nonnegative_keys: set[str] = set()

    def reserve_structural_replay(row: dict[str, Any]) -> bool:
        """Bound negative-witness rebuilds independently of LB replays."""

        key = code_key(row)
        if key in structural_attempted_keys:
            return True
        if len(structural_attempted_keys) >= structural_replay_limit:
            return False
        structural_attempted_keys.add(key)
        return True

    def has_replayed_structural_rejection(row: dict[str, Any]) -> bool:
        """Return only a rebuilt negative witness; failures keep the row."""

        if (
            policy_version < CANDIDATE_BATCH_POLICY_AUDIT_FUNNEL_VERSION
            or not replay_structural_negatives
        ):
            return False
        # Internally exact evidence is handled by the historical proof-aware
        # order.  A conflicting basis report must reach the formal audit
        # rather than silently overriding stronger evidence here.
        if candidate_evidence_priority(row)[0] > 0:
            return False
        key = code_key(row)
        if key in structural_negative_keys:
            return True
        if key in structural_nonnegative_keys:
            return False
        static = row.get("static_eligibility")
        report = (
            static.get("logical_basis_upper_bound")
            if isinstance(static, Mapping) else None
        )
        if not isinstance(report, Mapping):
            return False
        if not reserve_structural_replay(row):
            # The replay budget is operational, never mathematical.  Once it
            # is exhausted an unchecked row remains eligible for formal audit.
            return False
        from .negative_evidence import (
            replay_structural_logical_basis_rejection,
        )

        rejection = replay_structural_logical_basis_rejection(
            row,
            target_mode=selected_target_mode,
        )
        if rejection is None:
            structural_nonnegative_keys.add(key)
            return False
        structural_negative_keys.add(key)
        return True

    if policy_version < CANDIDATE_BATCH_POLICY_AUDIT_FUNNEL_VERSION:
        # Preserve the immutable selector semantics of committed v1-v5
        # transactions.  Only a fresh policy-v6 transaction opts into the
        # lower-bound replay funnel below.
        evidence_candidates.sort(
            key=candidate_evidence_priority,
            reverse=True,
        )
    else:
        # Exact/certified evidence keeps the historical lead.  Among the
        # remaining rows, replay a bounded proof-funnel (at most four
        # candidates per audit slot) and put validated positive lower bounds
        # ahead of rate-only rows.  This fixes the previous funnel inversion
        # in which every d>=5 survivor tied at zero and top-k selection was
        # effectively rate-first.
        exact_candidates: list[dict[str, Any]] = []
        lower_bound_claims: list[dict[str, Any]] = []
        ordinary_candidates: list[dict[str, Any]] = []
        for row in evidence_candidates:
            if candidate_evidence_priority(row)[0] > 0:
                exact_candidates.append(row)
            elif _search_lower_bound_claim_priority(
                row,
                target_mode=selected_target_mode,
            ) is not None:
                lower_bound_claims.append(row)
            else:
                ordinary_candidates.append(row)
        exact_candidates.sort(key=candidate_evidence_priority, reverse=True)
        lower_bound_claims.sort(
            key=lambda row: _search_lower_bound_claim_priority(
                row,
                target_mode=selected_target_mode,
            ),
            reverse=True,
        )
        verified_lower_bounds: list[tuple[dict[str, Any], int]] = []
        unverified_claims: list[dict[str, Any]] = []
        for index, row in enumerate(lower_bound_claims):
            if lower_bound_replay_attempts >= lower_bound_replay_limit:
                unverified_claims.extend(lower_bound_claims[index:])
                break
            if has_replayed_structural_rejection(row):
                # This is negative-only scheduling evidence.  The candidate
                # remains in the immutable source history, but cannot consume
                # one of this round's scarce exact-audit slots.
                continue
            lower_bound_replay_attempts += 1
            replayed_lower_bound = (
                _replayable_search_lower_bound_for_audit(row)
            )
            claimed_lower_bound = row.get("distance_lower_bound")
            if (
                isinstance(replayed_lower_bound, bool)
                or not isinstance(replayed_lower_bound, int)
                or replayed_lower_bound != claimed_lower_bound
            ):
                unverified_claims.append(row)
                continue
            verified_lower_bounds.append((row, replayed_lower_bound))
        verified_lower_bounds.sort(
            key=lambda item: _search_lower_bound_audit_priority(
                item[0],
                item[1],
                target_mode=selected_target_mode,
            ),
            reverse=True,
        )
        ordinary_candidates.extend(unverified_claims)
        ordinary_candidates.sort(
            key=candidate_evidence_priority,
            reverse=True,
        )
        evidence_candidates = (
            exact_candidates
            + [row for row, _lower_bound in verified_lower_bounds]
            + ordinary_candidates
        )
    if formal_audit_slots is not None:
        from evaluation.formal_audit_quota import (
            assigned_candidate,
            candidate_audit_strata,
            observe_strata,
            strata_sets,
            stratum_novelty_key,
        )

        if (
            not isinstance(formal_audit_slots, list)
            or len(formal_audit_slots) > limit
            or any(
                not isinstance(slot, Mapping)
                or type(slot.get("slot_index")) is not int
                or type(slot.get("volume")) is not int
                for slot in formal_audit_slots
            )
        ):
            raise ValueError("formal-audit slots are malformed")
        observed = strata_sets(prior_audit_rows or [])
        ordered_pool = [*evidence_candidates, *quick_exploration]
        quick_identities = {id(row) for row in quick_exploration}
        selected_rows: list[dict[str, Any]] = []
        selected_ids: set[int] = set()
        quick_selected = 0
        for slot in formal_audit_slots:
            ranked_slot: list[
                tuple[tuple[int, int, int, int], int, dict[str, Any], dict[str, Any]]
            ] = []
            for position, row in enumerate(ordered_pool):
                if id(row) in selected_ids:
                    continue
                if id(row) in quick_identities and quick_selected >= 1:
                    continue
                strata = candidate_audit_strata(row)
                if strata is None or strata["published_volume"] != slot["volume"]:
                    continue
                ranked_slot.append((
                    stratum_novelty_key(strata, observed),
                    -position,
                    row,
                    strata,
                ))
            ranked_slot.sort(key=lambda item: (item[0], item[1]), reverse=True)
            for _novelty, _position, row, strata in ranked_slot:
                if has_replayed_structural_rejection(row):
                    continue
                selected_rows.append(assigned_candidate(
                    row,
                    slot=slot,
                    strata=strata,
                ))
                selected_ids.add(id(row))
                if id(row) in quick_identities:
                    quick_selected += 1
                observe_strata(strata, observed)
                break
        return selected_rows

    selected: list[dict[str, Any]] = []
    used_cells: set[str] = set()
    used_strata: set[tuple[str, str]] = set()

    def add_new_strata(rows: list[dict[str, Any]], target: int) -> None:
        # ``rows`` is already in the existing evidence-priority order.  Take
        # the best representative of each mechanism x support-split stratum
        # before allowing a second representative of an already-covered one.
        for row in rows:
            if len(selected) >= target or len(selected) >= limit:
                return
            if has_replayed_structural_rejection(row):
                continue
            stratum = _candidate_audit_stratum(row)
            if stratum in used_strata:
                continue
            selected.append(row)
            used_strata.add(stratum)
            cell = str(row.get("archive_cell", ""))
            if cell:
                used_cells.add(cell)

    def add_from(rows: list[dict[str, Any]], target: int) -> None:
        for require_new_cell in (True, False):
            for row in rows:
                if len(selected) >= target or len(selected) >= limit:
                    return
                if row in selected:
                    continue
                if has_replayed_structural_rejection(row):
                    continue
                cell = str(row.get("archive_cell", ""))
                if require_new_cell and cell and cell in used_cells:
                    continue
                selected.append(row)
                used_strata.add(_candidate_audit_stratum(row))
                if cell:
                    used_cells.add(cell)

    reserve_quick = bool(quick_exploration) and limit > 1
    add_new_strata(
        evidence_candidates,
        limit - int(reserve_quick),
    )
    add_from(
        evidence_candidates,
        limit - int(reserve_quick),
    )
    if reserve_quick:
        add_from(quick_exploration, len(selected) + 1)
    # Keep this lane deliberately sparse: a quick-only row has no distance
    # evidence yet, so at most one may consume a round's MILP budget.
    add_from(evidence_candidates, limit)
    if not selected and quick_exploration:
        add_from(quick_exploration, 1)
    return selected


def _stage1_milp_worker_count(config: FlowConfig, pending_count: int) -> int:
    """Return the Stage 1 candidate lanes allowed by the shared worker cap."""
    if pending_count < 1:
        return 0
    budget = config.max_total_workers
    if budget is None:
        budget = 3
    return min(3, budget, pending_count)


class HumanizeFlow:
    """One-build/one-review qcode loop with durable evidence and hard gates."""

    def __init__(
        self,
        config: FlowConfig,
        *,
        reviewer: Reviewer | None = None,
        evolution_runner: EvolutionRunner = run_openevolve,
        milp_evaluator: MilpEvaluator = evaluate_with_milp,
    ):
        config.validate()
        self.config = config
        self.store = RunStore.create(config.repo_dir / "results", config.run_id)
        self.archive = EliteArchive(self.store.archive_path)
        self.reviewer = reviewer or CodexReviewer(
            repo_dir=config.repo_dir,
            model=config.review_model,
            effort=config.review_effort,
        )
        self.evolution_runner = evolution_runner
        self.milp_evaluator = milp_evaluator
        self.run_dir = config.repo_dir / "results" / "runs" / self.store.run_id
        self.run_dir.mkdir(parents=True, exist_ok=True)

    @property
    def evolution_output(self) -> Path:
        return self.config.repo_dir / "results" / "evolution" / f"humanize_{self.store.run_id}"

    @property
    def candidate_log(self) -> Path:
        return self.config.candidate_file or self.evolution_output / "all_codes.jsonl"

    def _recover_candidate_log_wal(self) -> bool:
        """Finish any evaluator append before Flow reads or rewrites its log."""
        if self.config.candidate_file is not None:
            return False
        from evolve.openevolve_evaluator import (
            CandidateLogWriteError,
            recover_candidate_log_wal,
        )

        try:
            return recover_candidate_log_wal(
                self.candidate_log.absolute()
            )
        except (OSError, CandidateLogWriteError) as exc:
            raise RoundTransactionError(
                f"candidate log WAL recovery failed: {exc}"
            ) from exc

    @staticmethod
    def _read_jsonl(path: Path) -> list[dict[str, Any]]:
        if not path.is_file():
            return []
        return [
            json.loads(line)
            for line in path.read_text().splitlines()
            if line.strip()
        ]

    @staticmethod
    def _write_jsonl(path: Path, rows: list[dict[str, Any]]) -> None:
        atomic_write_jsonl(path, rows)

    @property
    def evaluations_path(self) -> Path:
        return self.run_dir / "evaluations.jsonl"

    def _milp_checkpoint_path(self, candidate_key: str) -> Path:
        if not candidate_key or any(
            character not in "0123456789abcdef" for character in candidate_key
        ):
            raise AuditStateError("candidate_key is unsafe for a checkpoint path")
        repo_root = self.config.repo_dir
        results_root = repo_root / "results"
        runs_root = results_root / "runs"
        for label, path in (
            ("repository", repo_root),
            ("results", results_root),
            ("runs", runs_root),
            ("run directory", self.run_dir),
        ):
            if path.is_symlink():
                raise AuditStateError(
                    f"MILP {label} may not be a symlink: {path}"
                )
            if not path.is_dir():
                raise AuditStateError(
                    f"MILP {label} is not a directory: {path}"
                )
        resolved_repo = repo_root.resolve(strict=True)
        resolved_runs = runs_root.resolve(strict=True)
        resolved_run = self.run_dir.resolve(strict=True)
        try:
            resolved_runs.relative_to(resolved_repo)
        except ValueError as exc:
            raise AuditStateError(
                f"MILP runs root escapes the repository: {resolved_runs}"
            ) from exc
        expected_run = resolved_runs / self.store.run_id
        if resolved_run != expected_run:
            raise AuditStateError(
                "MILP run directory is outside the fixed results/runs root"
            )
        checkpoint_root = self.run_dir / "milp-checkpoints"
        if checkpoint_root.is_symlink():
            raise AuditStateError(
                f"MILP checkpoint root may not be a symlink: {checkpoint_root}"
            )
        checkpoint_root.mkdir(parents=True, exist_ok=True)
        if not checkpoint_root.is_dir():
            raise AuditStateError(
                f"MILP checkpoint root is not a directory: {checkpoint_root}"
            )
        resolved_root = checkpoint_root.resolve(strict=True)
        if resolved_root.parent != resolved_run:
            raise AuditStateError(
                "MILP checkpoint root is outside the fixed run directory"
            )
        checkpoint = resolved_root / f"{candidate_key}.json"
        if checkpoint.is_symlink():
            raise AuditStateError(
                f"MILP checkpoint may not be a symlink: {checkpoint}"
            )
        if checkpoint.exists() and not checkpoint.is_file():
            raise AuditStateError(
                f"MILP checkpoint is not a regular file: {checkpoint}"
            )
        try:
            checkpoint.relative_to(resolved_root)
        except ValueError as exc:
            raise AuditStateError(
                f"MILP checkpoint escapes its root: {checkpoint}"
            ) from exc
        return checkpoint

    @staticmethod
    def _decode_canonical_jsonl(payload: bytes, path: Path) -> list[dict[str, Any]]:
        rows: list[dict[str, Any]] = []

        def reject_constant(value: str) -> None:
            raise ValueError(f"non-finite JSON number: {value}")

        def reject_duplicates(pairs: list[tuple[str, Any]]) -> dict[str, Any]:
            value: dict[str, Any] = {}
            for key, item in pairs:
                if key in value:
                    raise ValueError(f"duplicate JSON key: {key}")
                value[key] = item
            return value

        for line_number, raw in enumerate(payload.splitlines(keepends=True), 1):
            if not raw.endswith(b"\n"):
                raise AuditStateError(
                    f"canonical evaluation line {line_number} is not terminated"
                )
            try:
                row = json.loads(
                    raw.decode("utf-8"),
                    parse_constant=reject_constant,
                    object_pairs_hook=reject_duplicates,
                )
            except (UnicodeDecodeError, json.JSONDecodeError, ValueError) as exc:
                raise AuditStateError(
                    f"invalid canonical evaluation {path}:{line_number}: {exc}"
                ) from exc
            if not isinstance(row, dict):
                raise AuditStateError(
                    f"canonical evaluation {path}:{line_number} is not an object"
                )
            rows.append(row)
        return rows

    def _read_canonical_evaluations(
        self,
        *,
        recover_final_partial: bool,
    ) -> list[dict[str, Any]]:
        path = self.evaluations_path
        if path.is_symlink():
            raise AuditStateError(
                f"canonical evaluations may not be a symlink: {path}"
            )
        if not path.exists():
            return []
        if not path.is_file():
            raise AuditStateError(
                f"canonical evaluations must be a regular file: {path}"
            )
        payload = path.read_bytes()
        if payload and not payload.endswith(b"\n"):
            split = payload.rfind(b"\n") + 1
            prefix, tail = payload[:split], payload[split:]
            # A bad complete row before the final fragment is never repairable.
            rows = self._decode_canonical_jsonl(prefix, path)
            if not recover_final_partial:
                raise AuditStateError(
                    f"canonical evaluations end in a partial row: {path}"
                )
            digest = hashlib.sha256(tail).hexdigest()
            archive = (
                self.run_dir
                / "recovery"
                / f"evaluations-final-partial-{digest[:16]}.bin"
            )
            if archive.exists():
                if archive.is_symlink() or archive.read_bytes() != tail:
                    raise AuditStateError(
                        f"evaluation partial-row archive is inconsistent: {archive}"
                    )
            else:
                atomic_write_bytes(archive, tail)
            atomic_write_bytes(path, prefix)
            self.store.event(
                "evaluation_partial_row_recovered",
                archive=str(archive),
                bytes=len(tail),
                sha256=digest,
            )
            return rows
        return self._decode_canonical_jsonl(payload, path)

    def _rebuild_global_audit_state(
        self,
        state: dict[str, Any],
        *,
        recover_final_partial: bool,
    ) -> tuple[list[dict[str, Any]], Any]:
        rows = self._read_canonical_evaluations(
            recover_final_partial=recover_final_partial
        )
        rebuilt = rebuild_audit_state(
            rows,
            fully_exact=is_fully_exact,
            checkpoint_path_for=lambda key: self._milp_checkpoint_path(key),
        )
        state.update(rebuilt.as_state_fields())
        state["audit_evaluations_seen"] = rebuilt.evaluations_seen
        state["unresolved_count"] = len(rebuilt.unresolved)
        self.store.write_state(state)
        return rows, rebuilt

    def _trusted_exact_audit_view(
        self,
        rows: list[dict[str, Any]],
    ) -> tuple[list[dict[str, Any]], list[dict[str, Any]]]:
        """Return exact evidence and registry-replayed selected-target WINs.

        Exact distance evidence is necessary but not sufficient to terminate
        discovery.  The candidate construction is rebuilt here and replayed
        against the registry belonging to *this* repository.  A known code or
        any unavailable, incomplete, or contradictory registry replay remains
        exact evidence for review, but can never enter ``trusted_wins``.
        """
        from evaluation.final_gate import classify_win
        from evaluation.registry import check_code_novelty, load_registry

        campaign_target_mode = validate_target_mode(self.config.target_mode)

        # Validate the whole append-only history before promoting any one row.
        rebuild_audit_state(
            rows,
            fully_exact=is_fully_exact,
            checkpoint_path_for=lambda key: self._milp_checkpoint_path(key),
        )
        exact_by_key: dict[str, dict[str, Any]] = {}
        for row in rows:
            if (
                classify_evaluation(
                    row,
                    fully_exact=is_fully_exact,
                )
                is AuditOutcome.EXACT
            ):
                exact_by_key[code_key(row)] = copy.deepcopy(row)

        # ``load_registry`` caches validated immutable snapshots by path.
        # Invalidate that process cache at each authoritative audit view so a
        # registry replacement between rounds cannot leave Stage 1 consulting
        # stale contents under the same repository path.
        load_registry.cache_clear()
        registry_path = (
            self.config.repo_dir / "results" / "known_code_registry.json"
        )
        wins_by_key: dict[str, dict[str, Any]] = {}
        for key, row in exact_by_key.items():
            try:
                ell = int(row["ell"])
                m = int(row["m"])
                a_terms = [
                    tuple(map(int, term)) for term in row["A_terms"]
                ]
                b_terms = [
                    tuple(map(int, term)) for term in row["B_terms"]
                ]
                c_terms = [
                    tuple(map(int, term))
                    for term in (row.get("C_terms") or [])
                ]
                d_terms = [
                    tuple(map(int, term))
                    for term in (row.get("D_terms") or [])
                ]
                if c_terms or d_terms:
                    from evaluation.pbb_code import build_pbb_code

                    rebuilt_code = build_pbb_code(
                        ell,
                        m,
                        a_terms,
                        b_terms,
                        c_terms,
                        d_terms,
                    )
                    code_type = "noncss"
                else:
                    from evaluation.bb_code import build_bb_code

                    rebuilt_code = build_bb_code(
                        ell,
                        m,
                        a_terms,
                        b_terms,
                        geometry=row.get("geometry"),
                    )
                    code_type = "css"
                rebuilt_n = int(rebuilt_code.num_qudits)
                rebuilt_k = int(rebuilt_code.dimension)
                reported_n = int(row["n"])
                reported_k = int(row["k"])
                distance = int(row["d"])
                if (
                    rebuilt_n <= 0
                    or rebuilt_k <= 0
                    or reported_n != rebuilt_n
                    or reported_k != rebuilt_k
                ):
                    raise ValueError(
                        "exact row n/k disagree with the rebuilt construction"
                    )
                selected_target = target_binding(
                    rebuilt_n,
                    rebuilt_k,
                    campaign_target_mode,
                )
                reported_modes = {
                    validate_target_mode(row[name])
                    for name in ("target_mode", "proof_target_mode")
                    if row.get(name) is not None
                }
                if reported_modes and reported_modes != {
                    campaign_target_mode
                }:
                    raise ValueError(
                        "exact row target mode conflicts with the Stage-1 "
                        "campaign target"
                    )
                if row.get("target") is not None:
                    validate_target_binding(
                        row["target"],
                        rebuilt_n,
                        rebuilt_k,
                        campaign_target_mode,
                    )
                for name in (
                    "required_distance",
                    "target_required_distance",
                ):
                    if row.get(name) is not None and (
                        type(row[name]) is not int
                        or row[name] != selected_target["required_distance"]
                    ):
                        raise ValueError(
                            f"exact row {name} conflicts with the selected "
                            "target"
                        )
                # Preserve the historical monkeypatchable gist helper for
                # legacy Humanize unit/API users.  Scalar campaigns use the
                # integer target-policy decision and cannot be stopped by a
                # merely Pareto-compatible gist result.
                selected_result = (
                    classify_win(rebuilt_n, rebuilt_k, distance)
                    if campaign_target_mode == TARGET_MODE_GIST
                    else classify_target_win(
                        rebuilt_n,
                        rebuilt_k,
                        distance,
                        campaign_target_mode,
                    )
                )
                challenge_result = classify_win(
                    rebuilt_n,
                    rebuilt_k,
                    distance,
                )
            except Exception as exc:
                row["trusted_win_gate"] = {
                    "schema_version": 1,
                    "trusted": False,
                    "target_mode": campaign_target_mode,
                    "selected_target_win": None,
                    "challenge_win": None,
                    "registry_novelty": {
                        "status": "INCOMPLETE",
                        "checked": False,
                        "novel": None,
                        "registry_path": str(registry_path),
                        "failure": {
                            "domain": "candidate",
                            "code": "EXACT_CONSTRUCTION_REBUILD_FAILED",
                            "detail": str(exc),
                            "retryable": False,
                            "terminal_candidate_rejection": False,
                        },
                    },
                }
                continue

            if selected_result.get("passed") is not True:
                row["trusted_win_gate"] = {
                    "schema_version": 1,
                    "trusted": False,
                    "target_mode": campaign_target_mode,
                    "target": selected_target,
                    "selected_target_win": selected_result,
                    "challenge_win": challenge_result,
                    "registry_novelty": {
                        "status": "NOT_APPLICABLE",
                        "checked": False,
                        "novel": None,
                        "registry_path": str(registry_path),
                    },
                }
                continue

            novelty = check_code_novelty(
                rebuilt_code,
                code_type=code_type,
                registry_path=registry_path,
            )
            trusted = novelty.get("novel") is True
            row["trusted_win_gate"] = {
                "schema_version": 1,
                "trusted": trusted,
                "target_mode": campaign_target_mode,
                "target": selected_target,
                "selected_target_win": selected_result,
                "challenge_win": challenge_result,
                "registry_novelty": novelty,
            }
            if trusted:
                wins_by_key[key] = row

        exact = sorted(
            exact_by_key.values(),
            key=lambda row: (
                code_key(row) in wins_by_key,
                candidate_fom(row),
                code_key(row),
            ),
            reverse=True,
        )
        wins = [row for row in exact if code_key(row) in wins_by_key]
        return exact, wins

    @staticmethod
    def _record_trusted_audit_view(
        state: dict[str, Any],
        exact: list[dict[str, Any]],
        wins: list[dict[str, Any]],
    ) -> None:
        state["trusted_exact_count"] = len(exact)
        state["trusted_win_count"] = len(wins)
        state["best_exact_fom"] = max(
            (candidate_fom(row) for row in exact),
            default=0.0,
        )
        challenge_win_gates = [
            row["trusted_win_gate"]
            for row in exact
            if isinstance(row.get("trusted_win_gate"), dict)
            and isinstance(
                row["trusted_win_gate"].get("challenge_win"),
                dict,
            )
            and row["trusted_win_gate"]["challenge_win"].get("passed") is True
        ]
        state["challenge_win_registry_novel_count"] = sum(
            gate.get("registry_novelty", {}).get("novel") is True
            for gate in challenge_win_gates
        )
        state["challenge_win_registry_known_count"] = sum(
            gate.get("registry_novelty", {}).get("novel") is False
            for gate in challenge_win_gates
        )
        state["challenge_win_registry_unresolved_count"] = sum(
            gate.get("registry_novelty", {}).get("novel") is None
            for gate in challenge_win_gates
        )

    @staticmethod
    def _canonical_row_identity(row: dict[str, Any]) -> str:
        try:
            payload = json.dumps(
                row,
                sort_keys=True,
                separators=(",", ":"),
                ensure_ascii=False,
                allow_nan=False,
            ).encode("utf-8")
        except (TypeError, ValueError) as exc:
            raise AuditStateError(
                "evaluation row must be strict JSON data"
            ) from exc
        return hashlib.sha256(payload).hexdigest()

    def _reconcile_round_evaluations(
        self,
        selected: list[dict[str, Any]],
        *,
        round_number: int,
        milp_path: Path,
        global_rows: list[dict[str, Any]],
    ) -> list[dict[str, Any]]:
        selected_keys = [code_key(row) for row in selected]
        selected_key_set = set(selected_keys)
        current: dict[str, dict[str, Any]] = {}
        global_identities = {
            self._canonical_row_identity(row) for row in global_rows
        }
        for row in global_rows:
            attempt = row.get("audit_attempt")
            if not isinstance(attempt, dict) or attempt.get("round") != round_number:
                continue
            key = code_key(row)
            if key not in selected_key_set:
                continue
            if key in current:
                raise AuditStateError(
                    f"candidate {key} has duplicate attempts in round {round_number}"
                )
            current[key] = row

        # Legacy round rows may not have audit_attempt. Trust them only if the
        # byte-equivalent logical row is already present in the global log. A
        # malformed or partial round file is evidence, so archive its exact
        # bytes before replacing it from the canonical global log.
        legacy_round_rows: list[dict[str, Any]] = []
        if milp_path.is_symlink():
            raise AuditStateError(
                f"round evaluations may not be a symlink: {milp_path}"
            )
        if milp_path.exists():
            if not milp_path.is_file():
                raise AuditStateError(
                    f"round evaluations must be a regular file: {milp_path}"
                )
            raw_round = milp_path.read_bytes()
            try:
                legacy_round_rows = self._decode_canonical_jsonl(
                    raw_round, milp_path
                )
            except AuditStateError:
                digest = hashlib.sha256(raw_round).hexdigest()
                archive = (
                    milp_path.parent
                    / f"milp-malformed-{digest[:16]}.bin"
                )
                if archive.is_symlink():
                    raise AuditStateError(
                        f"round evaluation archive may not be a symlink: {archive}"
                    )
                if archive.exists():
                    if not archive.is_file() or archive.read_bytes() != raw_round:
                        raise AuditStateError(
                            "round evaluation archive is inconsistent: "
                            f"{archive}"
                        )
                else:
                    atomic_write_bytes(archive, raw_round)
                self.store.event(
                    "round_evaluations_archived",
                    round=round_number,
                    archive=str(archive),
                    bytes=len(raw_round),
                    sha256=digest,
                )
        for row in legacy_round_rows:
            key = code_key(row)
            if (
                key in selected_key_set
                and key not in current
                and self._canonical_row_identity(row) in global_identities
            ):
                current[key] = row

        ordered = [current[key] for key in selected_keys if key in current]
        atomic_write_jsonl(milp_path, ordered)
        return ordered

    def _select_audit_candidates(
        self,
        candidates: list[dict[str, Any]],
        state: dict[str, Any],
        *,
        screened_history: list[dict[str, Any]] | None = None,
        policy_version: int = CANDIDATE_BATCH_POLICY_VERSION,
        verified_structural_digests: (
            _VerifiedStructuralDigestIndex | None
        ) = None,
    ) -> list[dict[str, Any]]:
        if self.config.milp_top <= 0:
            return []
        unresolved = state.get("unresolved_candidates", {})
        if not isinstance(unresolved, dict):
            raise AuditStateError("unresolved_candidates must be an object")
        blocked_keys = set(state.get("audited_keys", [])) | set(unresolved)
        blocked_digests = set(state.get("audited_structural_digests", []))
        blocked_digests.update(
            str(entry["canonical_digest"])
            for entry in unresolved.values()
            if entry.get("canonical_digest")
        )
        if screened_history is None:
            (
                screened_history,
                _rejected,
                verified_structural_digests,
            ) = self._replay_screened_candidate_pool_indexed(
                candidates,
                policy_version=policy_version,
            )

        quota_contract: dict[str, Any] | None = None
        quota_slots: list[Mapping[str, int]] | None = None
        prior_audit_rows: list[Mapping[str, Any]] | None = None
        quota_round = int(state.get("current_round", 0)) + 1
        if self.config.formal_audit_quota_contract is not None:
            from evaluation.formal_audit_quota import (
                load_quota_contract,
                round_quota_slots,
            )

            quota_contract = load_quota_contract(
                self.config.formal_audit_quota_contract,
                representation_id=self.config.search_representation_id,
                rounds=self.config.max_rounds,
                slots_per_round=self.config.milp_top,
            )
            quota_slots = list(round_quota_slots(quota_contract, quota_round))
            prior_audit_rows = self._read_canonical_evaluations(
                recover_final_partial=False
            )

        # An unresolved solver call is evidence that the candidate needs more
        # budget, not permission to monopolize every future discovery round.
        # With two or more lanes, reserve one for a never-audited candidate and
        # use the remainder for least-recently-attempted retries.  A one-lane
        # campaign alternates retry/fresh turns using the durable completed
        # round number.  Selection itself is written transactionally by the
        # caller, so a resumed pending round cannot change sides of the
        # alternation.
        retry_capacity = 0
        if unresolved:
            if self.config.milp_top == 1:
                current_round = state.get("current_round", 0)
                if (
                    isinstance(current_round, bool)
                    or not isinstance(current_round, int)
                    or current_round < 0
                ):
                    raise AuditStateError(
                        "current_round must be a non-negative integer"
                    )
                next_round = current_round + 1
                retry_capacity = int(next_round % 2 == 1)
            else:
                retry_capacity = self.config.milp_top - 1
        retry_entries = select_retry_lane(
            unresolved,
            limit=retry_capacity,
        )
        retry_candidates = [
            dict(entry["candidate"]) for entry in retry_entries
        ]
        fresh_capacity = self.config.milp_top - len(retry_candidates)
        new_candidates = select_for_milp(
            screened_history,
            None,
            blocked_keys,
            fresh_capacity,
            blocked_digests,
            policy_version=policy_version,
            target_mode=self.config.target_mode,
            replay_structural_negatives=(
                not self.config.allow_debug_audit_evaluator
            ),
            formal_audit_slots=(
                None
                if quota_slots is None
                else quota_slots[:fresh_capacity]
            ),
            prior_audit_rows=prior_audit_rows,
            verified_structural_digests=verified_structural_digests,
        )

        # Do not leave compute idle when the fresh pool is empty (including a
        # one-lane fresh turn).  Filling only the unused capacity preserves
        # retry fairness without taking away the reserved fresh slot when one
        # exists.
        remaining = self.config.milp_top - (
            len(retry_candidates) + len(new_candidates)
        )
        if remaining > 0 and unresolved and quota_contract is None:
            selected_retry_keys = {
                str(entry["candidate_key"]) for entry in retry_entries
            }
            for entry in select_retry_lane(
                unresolved,
                limit=self.config.milp_top,
            ):
                if entry["candidate_key"] in selected_retry_keys:
                    continue
                retry_candidates.append(dict(entry["candidate"]))
                selected_retry_keys.add(str(entry["candidate_key"]))
                remaining -= 1
                if remaining == 0:
                    break
        if quota_contract is not None:
            from evaluation.formal_audit_quota import (
                selection_report,
                validate_selection_report,
            )

            report = selection_report(
                contract=quota_contract,
                round_number=quota_round,
                selected_fresh=new_candidates,
                retry_candidate_keys=[
                    code_key(candidate) for candidate in retry_candidates
                ],
                candidate_key_fn=code_key,
            )
            report_path = (
                self.store.root
                / "rounds"
                / f"round-{quota_round:03d}"
                / "formal-audit-quota-selection.json"
            )
            if report_path.is_symlink():
                raise AuditStateError(
                    "formal-audit quota selection report may not be a symlink"
                )
            if report_path.exists():
                existing = _read_json_object(
                    report_path,
                    "formal-audit quota selection report",
                )
                validate_selection_report(
                    existing,
                    contract=quota_contract,
                    round_number=quota_round,
                )
                if existing != report:
                    raise AuditStateError(
                        "formal-audit quota selection changed during resume"
                    )
            else:
                atomic_write_json(report_path, report)
        return retry_candidates + new_candidates

    def _attempt_plan(
        self,
        candidate: dict[str, Any],
        state: dict[str, Any],
        *,
        round_number: int,
    ) -> tuple[FlowConfig, dict[str, Any], dict[str, Any]]:
        key = code_key(candidate)
        unresolved = state.get("unresolved_candidates", {})
        entry = unresolved.get(key) if isinstance(unresolved, dict) else None
        completed = 0 if entry is None else int(entry["attempts_completed"])
        base_hard_timeout = max(
            float(self.config.milp_timeout_per_logical) * 1.1,
            float(self.config.milp_timeout_per_logical) + 30.0,
        )
        budget = retry_budget(
            timeout_per_logical=self.config.milp_timeout_per_logical,
            total_timeout=self.config.milp_total_timeout,
            completed_attempts=completed,
            hard_timeout_per_logical=base_hard_timeout,
        )
        assert budget.hard_timeout_per_logical is not None
        checkpoint = self._milp_checkpoint_path(key)
        checkpoint.parent.mkdir(parents=True, exist_ok=True)
        attempt = {
            "schema_version": 1,
            "round": round_number,
            "kind": "new" if completed == 0 else "retry",
            "attempt": completed + 1,
            "multiplier": budget.multiplier,
            "soft": budget.timeout_per_logical,
            "total": budget.total_timeout,
            "hard": budget.hard_timeout_per_logical,
            "checkpoint": str(checkpoint),
        }
        attempt_config = replace(
            self.config,
            milp_timeout_per_logical=budget.timeout_per_logical,
            milp_total_timeout=budget.total_timeout,
        )
        invocation = {
            "checkpoint_path": str(checkpoint),
            "resume": True,
            "hard_timeout_per_logical": budget.hard_timeout_per_logical,
        }
        return attempt_config, attempt, invocation

    def _evaluate_audit_attempt(
        self,
        candidate: dict[str, Any],
        attempt_config: FlowConfig,
        invocation: dict[str, Any],
    ) -> dict[str, Any]:
        formal_contract = False
        try:
            signature = inspect.signature(self.milp_evaluator)
            signature.bind(candidate, attempt_config, **invocation)
        except TypeError:
            try:
                signature.bind(candidate, attempt_config)
            except TypeError as exc:
                raise AuditStateError(
                    "MILP evaluator accepts neither the production invocation "
                    "nor the legacy two-argument contract"
                ) from exc
            if not self.config.allow_debug_audit_evaluator:
                raise AuditStateError(
                    "legacy two-argument MILP evaluator is disabled; set "
                    "allow_debug_audit_evaluator only for explicit debug runs"
                )
            result = self.milp_evaluator(candidate, attempt_config)
        else:
            result = self.milp_evaluator(
                candidate,
                attempt_config,
                **invocation,
            )
            formal_contract = True
        if not isinstance(result, dict):
            raise AuditStateError("MILP evaluator must return an object")
        returned = dict(result)
        formal_result = (
            formal_contract
            and "audit_evaluator_invocation" in returned
        )
        if (
            not formal_result
            and not self.config.allow_debug_audit_evaluator
        ):
            raise AuditStateError(
                "MILP evaluator did not return the formal schema-v2 audit "
                "invocation contract; debug downgrade is disabled"
            )
        returned["_humanize_formal_audit_contract"] = formal_result
        if not formal_contract:
            returned.pop("audit_evaluator_invocation", None)
        return returned

    @staticmethod
    def _transaction_paths(round_dir: Path) -> dict[str, Path]:
        return {
            "manifest": round_dir / "evolution-transaction.json",
            "batch": round_dir / "candidate-batch.jsonl",
            "completion": _completion_marker_path(round_dir),
            "witness": _slice_witness_path(round_dir),
        }

    @staticmethod
    def _prepared_transaction_has_no_bound_source(
        transaction: dict[str, Any],
    ) -> bool:
        return (
            transaction.get("status") == "prepared"
            and transaction.get("result_checkpoint") is None
            and transaction.get("candidate_end_offset") is None
            and transaction.get("candidate_source_sha256") is None
            and transaction.get("candidate_source_rows") is None
            and transaction.get("candidate_batch_identity") is None
            and transaction.get("completion_marker_sha256") is None
            and transaction.get("completion_witness_sha256") is None
            and "source_ready_at" not in transaction
            and "batch_ready_at" not in transaction
            and "committed_at" not in transaction
        )

    @staticmethod
    def _candidate_batch_policy_version(
        transaction: dict[str, Any],
    ) -> int:
        """Return the immutable selector version bound to this transaction.

        Protocol-v2/schema-v2 manifests created before selector versioning did
        not carry this field.  Their batches were all derived with policy v1,
        so absence is the exact historical v1 encoding.  Protocol v3 requires
        an explicit binding and accepts immutable v2/v3 batches as well as
        v4 witness-metadata-canonicalizing, v5 composite-provenance, and v6
        lower-bound audit-funnel batches; deleting it cannot silently
        downgrade a transaction.
        """

        value = transaction.get("candidate_batch_policy_version")
        identity = (
            transaction.get("schema_version"),
            transaction.get("protocol_version"),
        )
        if identity == (
            ROUND_TRANSACTION_LEGACY_SCHEMA_VERSION,
            ROUND_TRANSACTION_LEGACY_PROTOCOL_VERSION,
        ):
            if value is None:
                return CANDIDATE_BATCH_POLICY_LEGACY_VERSION
            if (
                isinstance(value, bool)
                or not isinstance(value, int)
                or value != CANDIDATE_BATCH_POLICY_LEGACY_VERSION
            ):
                raise RoundTransactionError(
                    "legacy transaction has an invalid candidate batch policy"
                )
            return CANDIDATE_BATCH_POLICY_LEGACY_VERSION
        if identity != (
            ROUND_TRANSACTION_SCHEMA_VERSION,
            ROUND_TRANSACTION_PROTOCOL_VERSION,
        ):
            raise RoundTransactionError(
                "candidate batch policy has an unsupported transaction identity"
            )
        if (
            isinstance(value, bool)
            or not isinstance(value, int)
            or value not in {
                CANDIDATE_BATCH_POLICY_LOWER_BOUND_VERSION,
                CANDIDATE_BATCH_POLICY_EVIDENCE_MERGE_VERSION,
                CANDIDATE_BATCH_POLICY_WITNESS_METADATA_VERSION,
                CANDIDATE_BATCH_POLICY_COMPOSITE_PROVENANCE_VERSION,
                CANDIDATE_BATCH_POLICY_VERSION,
            }
        ):
            raise RoundTransactionError(
                f"unsupported candidate batch policy version: {value!r}"
            )
        return value

    def _validate_binding_rebind_history(
        self,
        transaction: dict[str, Any],
        round_dir: Path,
        current_launch: dict[str, dict[str, Any]],
    ) -> list[dict[str, Any]]:
        history = transaction.setdefault("evolution_binding_rebinds", [])
        if not isinstance(history, list):
            raise RoundTransactionError(
                "transaction evolution binding rebind history is invalid"
            )
        if transaction["mode"] != "openevolve":
            if history:
                raise RoundTransactionError(
                    "candidate-file transaction contains binding rebind history"
                )
            return history

        pending_seen = False
        previous_launch: dict[str, dict[str, Any]] | None = None
        previous_invocation: dict[str, Any] | None = None
        previous_schema_rank: int | None = None
        required = {
            "attempt",
            "status",
            "reason",
            "old_launch_binding",
            "old_invocation_binding",
            "old_binding_sha256",
            "candidate_start_offset",
            "evolution_attempts_before",
            "abandoned_ranges_before",
            "abandoned_checkpoints_before",
            "planned_at",
        }
        completed_only = {
            "new_launch_binding",
            "new_invocation_binding",
            "new_binding_sha256",
            "evolution_attempts_after",
            "abandoned_ranges_after",
            "abandoned_checkpoints_after",
            "rebound_at",
        }
        for index, record in enumerate(history, 1):
            if not isinstance(record, dict):
                raise RoundTransactionError(
                    "evolution binding rebind record is not an object"
                )
            status = record.get("status")
            expected_fields = (
                required
                if status == "rebinding"
                else required | completed_only
                if status == "rebound"
                else set()
            )
            if not expected_fields or set(record) != expected_fields:
                raise RoundTransactionError(
                    "evolution binding rebind record fields are invalid"
                )
            if (
                record["attempt"] != index
                or not isinstance(record["reason"], str)
                or not record["reason"]
                or record["candidate_start_offset"]
                != transaction["candidate_start_offset"]
                or not isinstance(record["planned_at"], str)
                or any(
                    isinstance(record[field], bool)
                    or not isinstance(record[field], int)
                    or record[field] < 0
                    for field in (
                        "evolution_attempts_before",
                        "abandoned_ranges_before",
                        "abandoned_checkpoints_before",
                    )
                )
            ):
                raise RoundTransactionError(
                    "evolution binding rebind record identity is invalid"
                )
            old_launch, old_invocation = _validate_stored_binding_shape(
                self.config,
                record["old_launch_binding"],
                record["old_invocation_binding"],
                round_dir,
                current_launch,
                allow_legacy=True,
            )
            old_schema_rank = _evolution_launch_shape_rank(
                old_launch, current_launch
            )
            if old_schema_rank is None:
                raise RoundTransactionError(
                    "evolution binding rebind history has unknown schema"
                )
            if record["old_binding_sha256"] != _binding_identity_sha256(
                old_launch, old_invocation
            ):
                raise RoundTransactionError(
                    "old evolution binding rebind identity changed"
                )
            if previous_launch is not None and (
                old_launch != previous_launch
                or old_invocation != previous_invocation
            ):
                raise RoundTransactionError(
                    "evolution binding rebind history is not a continuous chain"
                )
            if (
                previous_schema_rank is not None
                and old_schema_rank < previous_schema_rank
            ):
                raise RoundTransactionError(
                    "evolution binding rebind history downgrades its schema"
                )

            if status == "rebinding":
                if pending_seen or index != len(history):
                    raise RoundTransactionError(
                        "pending evolution binding rebind must be last"
                    )
                pending_seen = True
                previous_launch = old_launch
                previous_invocation = old_invocation
                previous_schema_rank = old_schema_rank
            else:
                new_launch, new_invocation = _validate_stored_binding_shape(
                    self.config,
                    record["new_launch_binding"],
                    record["new_invocation_binding"],
                    round_dir,
                    current_launch,
                    allow_legacy=True,
                )
                new_schema_rank = _evolution_launch_shape_rank(
                    new_launch, current_launch
                )
                if new_schema_rank is None:
                    raise RoundTransactionError(
                        "evolution binding rebind history has unknown schema"
                    )
                if new_schema_rank < old_schema_rank:
                    raise RoundTransactionError(
                        "evolution binding rebind history downgrades its schema"
                    )
                if record["new_binding_sha256"] != _binding_identity_sha256(
                    new_launch, new_invocation
                ):
                    raise RoundTransactionError(
                        "new evolution binding rebind identity changed"
                    )
                if (
                    not isinstance(record["rebound_at"], str)
                    or any(
                        isinstance(record[field], bool)
                        or not isinstance(record[field], int)
                        or record[field] < record[before]
                        for field, before in (
                            (
                                "evolution_attempts_after",
                                "evolution_attempts_before",
                            ),
                            (
                                "abandoned_ranges_after",
                                "abandoned_ranges_before",
                            ),
                            (
                                "abandoned_checkpoints_after",
                                "abandoned_checkpoints_before",
                            ),
                        )
                    )
                ):
                    raise RoundTransactionError(
                        "completed evolution binding rebind record is invalid"
                    )
                previous_launch = new_launch
                previous_invocation = new_invocation
                previous_schema_rank = new_schema_rank

        if history and (
            transaction.get("launch_binding") != previous_launch
            or transaction.get("invocation_binding") != previous_invocation
        ):
            raise RoundTransactionError(
                "transaction binding disagrees with its rebind history"
            )
        if pending_seen and (
            transaction["status"] != "prepared"
            or not self._prepared_transaction_has_no_bound_source(transaction)
        ):
            raise RoundTransactionError(
                "pending evolution binding rebind crossed source-ready"
            )
        return history

    def _rebind_prepared_evolution_transaction(
        self,
        transaction: dict[str, Any],
        round_dir: Path,
        current_launch: dict[str, dict[str, Any]],
        current_invocation: dict[str, Any],
    ) -> None:
        """Replayably abandon an unfinished slice and bind current sources."""
        if not self._prepared_transaction_has_no_bound_source(transaction):
            raise RoundTransactionError(
                "only an unbound prepared OpenEvolve transaction may rebind"
            )
        batch_path = Path(transaction["candidate_batch"])
        if batch_path.is_symlink() or batch_path.exists():
            raise RoundTransactionError(
                "prepared OpenEvolve transaction contains an unbound "
                "candidate batch"
            )
        history = transaction["evolution_binding_rebinds"]
        pending = (
            history[-1]
            if history and history[-1].get("status") == "rebinding"
            else None
        )
        if pending is None:
            old_launch = copy.deepcopy(transaction["launch_binding"])
            old_invocation = copy.deepcopy(transaction["invocation_binding"])
            pending = {
                "attempt": len(history) + 1,
                "status": "rebinding",
                "reason": _binding_change_reason(
                    old_launch,
                    old_invocation,
                    current_launch,
                    current_invocation,
                ),
                "old_launch_binding": old_launch,
                "old_invocation_binding": old_invocation,
                "old_binding_sha256": _binding_identity_sha256(
                    old_launch, old_invocation
                ),
                "candidate_start_offset": transaction[
                    "candidate_start_offset"
                ],
                "evolution_attempts_before": len(
                    transaction["evolution_attempts"]
                ),
                "abandoned_ranges_before": len(
                    transaction["abandoned_ranges"]
                ),
                "abandoned_checkpoints_before": len(
                    transaction["abandoned_checkpoints"]
                ),
                "planned_at": utc_now(),
            }
            history.append(pending)
            atomic_write_json(
                self._transaction_paths(round_dir)["manifest"], transaction
            )

        self._abandon_uncommitted_tail(transaction, round_dir)
        expected_path = (
            self.evolution_output
            / "checkpoints"
            / f"checkpoint_{int(transaction['expected_result_iteration'])}"
        )
        self._resume_checkpoint_quarantine(
            transaction, round_dir, expected_path
        )
        self._quarantine_untrusted_evolution_attempt(
            transaction,
            round_dir,
            expected_path,
            reason=pending["reason"],
        )

        new_launch, new_invocation = _current_evolution_bindings(
            self.config, round_dir
        )
        pending.update({
            "status": "rebound",
            "new_launch_binding": copy.deepcopy(new_launch),
            "new_invocation_binding": copy.deepcopy(new_invocation),
            "new_binding_sha256": _binding_identity_sha256(
                new_launch, new_invocation
            ),
            "evolution_attempts_after": len(
                transaction["evolution_attempts"]
            ),
            "abandoned_ranges_after": len(
                transaction["abandoned_ranges"]
            ),
            "abandoned_checkpoints_after": len(
                transaction["abandoned_checkpoints"]
            ),
            "rebound_at": utc_now(),
        })
        transaction["launch_binding"] = copy.deepcopy(new_launch)
        transaction["invocation_binding"] = copy.deepcopy(new_invocation)
        atomic_write_json(
            self._transaction_paths(round_dir)["manifest"], transaction
        )

    def _load_transaction(
        self,
        state: dict[str, Any],
        number: int,
        round_dir: Path,
        *,
        allow_prepared_rebind: bool = False,
    ) -> dict[str, Any] | None:
        paths = self._transaction_paths(round_dir)
        if not paths["manifest"].exists():
            return None
        transaction = _read_json_object(
            paths["manifest"], "round transaction manifest"
        )
        expected_mode = (
            "candidate-file" if self.config.candidate_file is not None
            else "openevolve"
        )
        transaction_identity = (
            transaction.get("schema_version"),
            transaction.get("protocol_version"),
        )
        if transaction_identity not in ROUND_TRANSACTION_SUPPORTED_IDENTITIES:
            raise RoundTransactionError(
                "round transaction schema/protocol identity is unsupported: "
                f"{transaction_identity!r}"
            )
        identity = {
            "run_id": self.store.run_id,
            "round": number,
            "mode": expected_mode,
            "candidate_log": str(self.candidate_log.resolve()),
            "candidate_batch": str(paths["batch"].resolve()),
            "completion_marker": (
                None
                if expected_mode == "candidate-file"
                else str(paths["completion"].resolve())
            ),
            "completion_witness": (
                None
                if expected_mode == "candidate-file"
                else str(paths["witness"].resolve())
            ),
        }
        for key, expected in identity.items():
            if transaction.get(key) != expected:
                raise RoundTransactionError(
                    f"round transaction identity mismatch for {key}: "
                    f"expected {expected!r}, got {transaction.get(key)!r}"
                )
        status = transaction.get("status")
        if status not in {"prepared", "source-ready", "batch-ready", "committed"}:
            raise RoundTransactionError(
                f"invalid round transaction status: {status!r}"
            )
        self._candidate_batch_policy_version(transaction)
        start_offset = transaction.get("candidate_start_offset")
        initial_offset = transaction.get("initial_candidate_offset")
        if (
            isinstance(start_offset, bool)
            or not isinstance(start_offset, int)
            or start_offset < 0
            or isinstance(initial_offset, bool)
            or not isinstance(initial_offset, int)
            or initial_offset < 0
            or start_offset != initial_offset
        ):
            raise RoundTransactionError("transaction candidate offsets are invalid")
        if not isinstance(transaction.get("abandoned_ranges"), list):
            raise RoundTransactionError("transaction abandoned_ranges is invalid")
        partial_recoveries = transaction.setdefault(
            "candidate_partial_recoveries", []
        )
        if not isinstance(partial_recoveries, list):
            raise RoundTransactionError(
                "transaction candidate_partial_recoveries is invalid"
            )
        if not isinstance(transaction.get("evolution_attempts"), list):
            raise RoundTransactionError("transaction evolution_attempts is invalid")
        if not isinstance(transaction.get("abandoned_checkpoints"), list):
            raise RoundTransactionError("transaction abandoned_checkpoints is invalid")
        rebinds = transaction.setdefault("evolution_binding_rebinds", [])
        if not isinstance(rebinds, list):
            raise RoundTransactionError(
                "transaction evolution binding rebind history is invalid"
            )
        if int(state.get("current_round", -1)) != number - 1:
            raise RoundTransactionError(
                "round transaction does not follow the durable current_round"
            )

        base = transaction.get("base_checkpoint")
        if expected_mode == "candidate-file":
            if (
                base is not None
                or transaction.get("expected_result_iteration") is not None
                or transaction.get("launch_binding") is not None
                or transaction.get("invocation_binding") is not None
                or rebinds
            ):
                raise RoundTransactionError(
                    "candidate-file transaction may not contain evolution bindings"
                )
        else:
            if base is not None:
                if not isinstance(base, dict) or "path" not in base:
                    raise RoundTransactionError("transaction base checkpoint is invalid")
                observed = _checkpoint_descriptor(
                    self.evolution_output,
                    Path(base["path"]),
                    expected_iteration=base.get("last_iteration"),
                )
                if observed != base:
                    raise RoundTransactionError("base checkpoint changed after prepare")
        expected_iteration = transaction.get("expected_result_iteration")
        if expected_mode == "openevolve":
            base_iteration = 0 if base is None else int(base["last_iteration"])
            if (
                transaction.get("iterations_per_round")
                != self.config.iterations_per_round
                or expected_iteration
                != base_iteration + self.config.iterations_per_round
            ):
                raise RoundTransactionError(
                    "transaction does not request one exact iteration increment"
                )
            current_launch, current_invocation = _current_evolution_bindings(
                self.config, round_dir
            )
            stored_launch, stored_invocation = (
                _validate_stored_binding_shape(
                    self.config,
                    transaction.get("launch_binding"),
                    transaction.get("invocation_binding"),
                    round_dir,
                    current_launch,
                    allow_legacy=(
                        status == "prepared"
                        and allow_prepared_rebind
                        and self._prepared_transaction_has_no_bound_source(
                            transaction
                        )
                    ),
                    allow_previous_committed=(status == "committed"),
                )
            )
            history = self._validate_binding_rebind_history(
                transaction, round_dir, current_launch
            )
            pending_rebind = bool(
                history and history[-1].get("status") == "rebinding"
            )
            launch_changed = stored_launch != current_launch
            if pending_rebind or launch_changed:
                if status == "committed":
                    if pending_rebind:
                        raise RoundTransactionError(
                            "committed evolution transaction has an unfinished "
                            "binding rebind"
                        )
                    # The current launch belongs to a future slice.  Preserve
                    # this committed transaction's historical identity.
                elif (
                    status != "prepared"
                    or not allow_prepared_rebind
                ):
                    _revalidate_frozen_bindings(
                        self.config,
                        stored_launch,
                        stored_invocation,
                        round_dir,
                    )
                    raise RoundTransactionError(
                        "pending prepared evolution binding rebind requires "
                        "its lifecycle lease"
                    )
                else:
                    self._rebind_prepared_evolution_transaction(
                        transaction,
                        round_dir,
                        current_launch,
                        current_invocation,
                    )
            # A committed slice is historical evidence: its checkpoint,
            # candidate source/batch, completion marker, and exact witness are
            # all replayed below against the launch identities frozen in this
            # manifest.  Requiring those historical source files to retain
            # their old bytes at their live repository paths would make any
            # later evaluator fix render an otherwise valid checkpoint
            # permanently unresumable.  Only a slice that can still execute
            # (prepared/source-ready/batch-ready) must match the current live
            # launch bytes.  Committed bindings are never rewritten or
            # rebound.
            if status != "committed":
                _revalidate_frozen_bindings(
                    self.config,
                    transaction.get("launch_binding"),
                    transaction.get("invocation_binding"),
                    round_dir,
                )
        return transaction

    def _prepare_transaction(
        self,
        state: dict[str, Any],
        number: int,
        round_dir: Path,
    ) -> dict[str, Any]:
        paths = self._transaction_paths(round_dir)
        if paths["manifest"].is_symlink() or paths["manifest"].exists():
            raise RoundTransactionError(
                "cannot prepare a transaction over an existing manifest"
            )
        for label in ("batch", "completion", "witness"):
            if paths[label].is_symlink() or paths[label].exists():
                raise RoundTransactionError(
                    f"transaction artifact exists without manifest: {paths[label]}"
                )
        start_offset = state.get("candidate_offset", 0)
        if (
            isinstance(start_offset, bool)
            or not isinstance(start_offset, int)
            or start_offset < 0
        ):
            raise RoundTransactionError("state candidate_offset is invalid")
        self._recover_candidate_log_wal()
        if self.candidate_log.is_file():
            source_size = self.candidate_log.stat().st_size
            if start_offset > source_size:
                raise RoundTransactionError(
                    "candidate log is shorter than the durable offset"
                )
        elif start_offset:
            raise RoundTransactionError(
                "candidate log is missing at a non-zero durable offset"
            )

        mode = (
            "candidate-file" if self.config.candidate_file is not None
            else "openevolve"
        )
        base_checkpoint = None
        launch_binding = None
        invocation_binding = None
        expected_iteration = None
        if mode == "openevolve":
            checkpoint_value = state.get("last_checkpoint")
            if checkpoint_value:
                base_checkpoint = _checkpoint_descriptor(
                    self.evolution_output, Path(checkpoint_value)
                )
            base_iteration = (
                0
                if base_checkpoint is None
                else int(base_checkpoint["last_iteration"])
            )
            expected_iteration = base_iteration + self.config.iterations_per_round
            expected_path = (
                self.evolution_output
                / "checkpoints"
                / f"checkpoint_{expected_iteration}"
            )
            _assert_checkpoint_frontier(
                self.evolution_output,
                base_iteration,
            )
            _quarantine_orphan_round_context(round_dir)
            launch_binding, invocation_binding = _fresh_evolution_bindings(
                self.config, state, round_dir
            )
        elif state.get("last_checkpoint") is not None:
            raise RoundTransactionError(
                "candidate-file transaction inherited an evolution checkpoint"
            )

        transaction: dict[str, Any] = {
            "schema_version": ROUND_TRANSACTION_SCHEMA_VERSION,
            "protocol_version": ROUND_TRANSACTION_PROTOCOL_VERSION,
            "run_id": self.store.run_id,
            "round": number,
            "mode": mode,
            "status": "prepared",
            "iterations_per_round": (
                self.config.iterations_per_round if mode == "openevolve" else 0
            ),
            "base_checkpoint": base_checkpoint,
            "expected_result_iteration": expected_iteration,
            "result_checkpoint": None,
            "launch_binding": launch_binding,
            "invocation_binding": invocation_binding,
            "candidate_log": str(self.candidate_log.resolve()),
            "initial_candidate_offset": start_offset,
            "candidate_start_offset": start_offset,
            "candidate_end_offset": None,
            "abandoned_ranges": [],
            "candidate_partial_recoveries": [],
            "abandoned_checkpoints": [],
            "evolution_attempts": [],
            "evolution_binding_rebinds": [],
            "candidate_source_sha256": None,
            "candidate_source_rows": None,
            "candidate_batch": str(paths["batch"].resolve()),
            "candidate_batch_policy_version": CANDIDATE_BATCH_POLICY_VERSION,
            "candidate_batch_identity": None,
            "completion_marker": (
                None if mode == "candidate-file" else str(paths["completion"].resolve())
            ),
            "completion_marker_sha256": None,
            "completion_witness": (
                None if mode == "candidate-file" else str(paths["witness"].resolve())
            ),
            "completion_witness_sha256": None,
            "prepared_at": utc_now(),
        }
        if mode == "candidate-file":
            source_end = (
                self.candidate_log.stat().st_size
                if self.candidate_log.is_file()
                else 0
            )
            try:
                source_rows, observed_end, source_sha256 = read_jsonl_range(
                    self.candidate_log, start_offset, source_end
                )
            except ValueError as exc:
                raise RoundTransactionError(str(exc)) from exc
            transaction["candidate_end_offset"] = observed_end
            transaction["candidate_source_sha256"] = source_sha256
            transaction["candidate_source_rows"] = len(source_rows)
            transaction["status"] = "source-ready"
            transaction["source_ready_at"] = utc_now()

        atomic_write_json(paths["manifest"], transaction)
        return transaction

    def _validate_transaction_source(
        self,
        transaction: dict[str, Any],
    ) -> list[dict[str, Any]]:
        end_offset = transaction.get("candidate_end_offset")
        if (
            isinstance(end_offset, bool)
            or not isinstance(end_offset, int)
            or end_offset < int(transaction["candidate_start_offset"])
        ):
            raise RoundTransactionError("transaction end offset is invalid")
        self._recover_candidate_log_wal()
        try:
            rows, observed_end, source_sha256 = read_jsonl_range(
                self.candidate_log,
                int(transaction["candidate_start_offset"]),
                end_offset,
            )
        except ValueError as exc:
            raise RoundTransactionError(str(exc)) from exc
        if (
            observed_end != end_offset
            or source_sha256 != transaction.get("candidate_source_sha256")
            or len(rows) != transaction.get("candidate_source_rows")
        ):
            raise RoundTransactionError(
                "candidate source slice changed after transaction prepare"
            )
        return rows

    def _validate_transaction_checkpoint(
        self,
        transaction: dict[str, Any],
        round_dir: Path,
        *,
        allow_historical_candidate_inode_change: bool = False,
    ) -> dict[str, Any] | None:
        if transaction["mode"] == "candidate-file":
            return None
        result = transaction.get("result_checkpoint")
        if not isinstance(result, dict) or "path" not in result:
            raise RoundTransactionError("transaction result checkpoint is missing")
        observed = _checkpoint_descriptor(
            self.evolution_output,
            Path(result["path"]),
            expected_iteration=transaction["expected_result_iteration"],
        )
        if observed != result:
            raise RoundTransactionError("result checkpoint changed after completion")
        witness_path = _slice_witness_path(round_dir)
        witness = _validate_slice_witness(
            witness_path,
            self.config,
            transaction.get("base_checkpoint"),
            observed,
            transaction.get("launch_binding"),
            transaction.get("invocation_binding"),
            self.candidate_log,
            int(transaction["candidate_start_offset"]),
            legacy_candidate_source=transaction,
            allow_historical_candidate_inode_change=(
                allow_historical_candidate_inode_change
            ),
        )
        if witness["sha256"] != transaction.get("completion_witness_sha256"):
            raise RoundTransactionError("completion witness changed after prepare")
        marker_path = _completion_marker_path(round_dir)
        marker = _validate_completion_marker(
            marker_path,
            self.config,
            transaction.get("base_checkpoint"),
            observed,
            transaction.get("launch_binding"),
            transaction.get("invocation_binding"),
            witness,
        )
        if marker["sha256"] != transaction.get("completion_marker_sha256"):
            raise RoundTransactionError("completion marker changed after prepare")
        return observed

    def _validate_candidate_batch(
        self,
        transaction: dict[str, Any],
    ) -> list[dict[str, Any]]:
        identity = transaction.get("candidate_batch_identity")
        batch_path = Path(transaction["candidate_batch"])
        if (
            not isinstance(identity, dict)
            or batch_path.is_symlink()
            or not batch_path.is_file()
        ):
            raise RoundTransactionError("candidate batch is missing")
        observed = {
            "sha256": _file_sha256(batch_path),
            "bytes": batch_path.stat().st_size,
            "rows": identity.get("rows"),
        }
        try:
            rows, end_offset, source_sha256 = read_jsonl_range(batch_path, 0)
        except ValueError as exc:
            raise RoundTransactionError(str(exc)) from exc
        observed["rows"] = len(rows)
        if end_offset != observed["bytes"] or source_sha256 != observed["sha256"]:
            raise RoundTransactionError("candidate batch byte identity is invalid")
        if observed != {
            "sha256": identity.get("sha256"),
            "bytes": identity.get("bytes"),
            "rows": identity.get("rows"),
        }:
            raise RoundTransactionError("candidate batch changed after commit")
        return rows

    @staticmethod
    def _candidate_rows_identity(rows: list[dict[str, Any]]) -> dict[str, Any]:
        payload = "".join(
            json.dumps(row, ensure_ascii=False, default=str) + "\n"
            for row in rows
        ).encode("utf-8")
        return {
            "sha256": hashlib.sha256(payload).hexdigest(),
            "bytes": len(payload),
            "rows": len(rows),
        }

    def _candidate_log_size(self, *, start_offset: int) -> int:
        self._recover_candidate_log_wal()
        path = self.candidate_log
        if path.is_symlink():
            raise RoundTransactionError(f"candidate log may not be a symlink: {path}")
        if not path.exists():
            if start_offset == 0:
                return 0
            raise RoundTransactionError(
                "candidate log is missing at a non-zero transaction offset"
            )
        if not path.is_file():
            raise RoundTransactionError(f"candidate log is not a regular file: {path}")
        size = path.stat().st_size
        if size < start_offset:
            raise RoundTransactionError(
                "candidate log is shorter than the transaction start offset"
            )
        return size

    @staticmethod
    def _inspect_abandoned_payload(
        payload: bytes,
        *,
        start_offset: int,
    ) -> dict[str, Any]:
        complete_length = payload.rfind(b"\n") + 1
        complete_rows = 0
        for raw in payload[:complete_length].splitlines(keepends=True):
            try:
                row = json.loads(raw.decode("utf-8"))
            except (UnicodeDecodeError, json.JSONDecodeError) as exc:
                raise RoundTransactionError(
                    f"invalid complete JSONL record in abandoned tail: {exc}"
                ) from exc
            if not isinstance(row, dict):
                raise RoundTransactionError(
                    "non-object JSONL record in abandoned candidate tail"
                )
            complete_rows += 1
        return {
            "start_offset": start_offset,
            "end_offset": start_offset + len(payload),
            "last_complete_offset": start_offset + complete_length,
            "sha256": hashlib.sha256(payload).hexdigest(),
            "bytes": len(payload),
            "complete_rows": complete_rows,
            "partial_bytes": len(payload) - complete_length,
        }

    @staticmethod
    def _abandoned_candidate_batch_path(
        round_dir: Path,
        attempt_number: int,
    ) -> Path:
        return (
            round_dir
            / f"abandoned-candidate-complete-{attempt_number:03d}.jsonl"
        )

    def _materialize_abandoned_candidate_batch(
        self,
        round_dir: Path,
        attempt_number: int,
        payload: bytes,
        tail: dict[str, Any],
    ) -> tuple[Path, dict[str, Any]]:
        """Materialize the complete JSONL prefix of an abandoned raw tail."""
        complete_length = (
            int(tail["last_complete_offset"]) - int(tail["start_offset"])
        )
        complete_payload = payload[:complete_length]
        batch_path = self._abandoned_candidate_batch_path(
            round_dir, attempt_number
        )
        if batch_path.is_symlink():
            raise RoundTransactionError(
                f"abandoned candidate batch may not be a symlink: {batch_path}"
            )
        expected = {
            "path": str(batch_path.resolve()),
            "sha256": hashlib.sha256(complete_payload).hexdigest(),
            "bytes": len(complete_payload),
            "rows": int(tail["complete_rows"]),
        }
        if batch_path.exists():
            descriptor = _file_descriptor(
                batch_path, "abandoned complete candidate batch"
            )
            observed = {
                **descriptor,
                "rows": int(tail["complete_rows"]),
            }
            if observed != expected or batch_path.read_bytes() != complete_payload:
                raise RoundTransactionError(
                    "abandoned complete candidate batch changed"
                )
        else:
            descriptor = atomic_write_bytes(batch_path, complete_payload)
            observed = {
                "path": str(batch_path.resolve()),
                **descriptor,
                "rows": int(tail["complete_rows"]),
            }
            if observed != expected:
                raise RoundTransactionError(
                    "abandoned complete candidate batch identity is inconsistent"
                )
        try:
            rows, end_offset, source_sha256 = read_jsonl_range(batch_path, 0)
        except ValueError as exc:
            raise RoundTransactionError(str(exc)) from exc
        if (
            len(rows) != expected["rows"]
            or end_offset != expected["bytes"]
            or source_sha256 != expected["sha256"]
        ):
            raise RoundTransactionError(
                "abandoned complete candidate batch is not valid bound JSONL"
            )
        return batch_path, expected

    def _abandoned_candidate_inputs(
        self,
        transaction: dict[str, Any],
        round_dir: Path,
    ) -> tuple[Path, ...]:
        """Validate and return salvaged complete rows in attempt order.

        Pre-hotfix manifests did not record the derived batch descriptor.  Their
        immutable raw archive already binds the exact bytes, so materializing
        the complete prefix remains a safe, backward-compatible migration.
        """
        inputs: list[Path] = []
        abandoned = transaction.get("abandoned_ranges", [])
        if not isinstance(abandoned, list):
            raise RoundTransactionError("transaction abandoned_ranges is invalid")
        start_offset = int(transaction["candidate_start_offset"])
        for attempt_number, record in enumerate(abandoned, 1):
            if not isinstance(record, dict):
                raise RoundTransactionError(
                    "abandoned-tail record is not an object"
                )
            archive_path = (
                round_dir
                / f"abandoned-candidate-tail-{attempt_number:03d}.bin"
            )
            descriptor = _file_descriptor(
                archive_path, "abandoned candidate-tail archive"
            )
            payload = archive_path.read_bytes()
            tail = self._inspect_abandoned_payload(
                payload, start_offset=start_offset
            )
            expected_archive = {
                **tail,
                "archive_path": descriptor["path"],
                "archive_sha256": descriptor["sha256"],
                "archive_bytes": descriptor["bytes"],
            }
            for key, value in expected_archive.items():
                if record.get(key) != value:
                    raise RoundTransactionError(
                        f"abandoned-tail record mismatch for {key}"
                    )
            batch_path, batch_identity = (
                self._materialize_abandoned_candidate_batch(
                    round_dir,
                    attempt_number,
                    payload,
                    tail,
                )
            )
            recorded_identity = record.get("complete_candidate_batch")
            if (
                recorded_identity is not None
                and recorded_identity != batch_identity
            ):
                raise RoundTransactionError(
                    "abandoned complete candidate batch binding mismatch"
                )
            if batch_identity["rows"]:
                inputs.append(batch_path)
        return tuple(inputs)

    def _atomic_restore_candidate_prefix(self, start_offset: int) -> None:
        self._recover_candidate_log_wal()
        path = self.candidate_log
        if start_offset == 0 and not path.exists():
            return
        try:
            _rows, observed, _sha256 = read_jsonl_range(path, 0, start_offset)
        except ValueError as exc:
            raise RoundTransactionError(
                "durable candidate prefix is not valid JSONL"
            ) from exc
        if observed != start_offset:
            raise RoundTransactionError("candidate prefix length changed during recovery")
        with path.open("rb") as stream:
            prefix = stream.read(start_offset)
            if len(prefix) != start_offset:
                raise RoundTransactionError(
                    "candidate log changed while restoring its durable prefix"
                )
        atomic_write_bytes(path, prefix)
        if path.stat().st_size != start_offset:
            raise RoundTransactionError("candidate log prefix restore was not durable")

    def _validate_candidate_partial_recoveries(
        self,
        transaction: dict[str, Any],
        round_dir: Path,
    ) -> None:
        history = transaction.get("candidate_partial_recoveries", [])
        if not isinstance(history, list):
            raise RoundTransactionError(
                "transaction candidate_partial_recoveries is invalid"
            )
        start_offset = int(transaction["candidate_start_offset"])
        for recovery_number, record in enumerate(history, 1):
            if not isinstance(record, dict):
                raise RoundTransactionError(
                    "candidate partial recovery record is not an object"
                )
            archive_path = (
                round_dir
                / f"candidate-final-partial-{recovery_number:03d}.bin"
            )
            descriptor = _file_descriptor(
                archive_path, "candidate partial-tail archive"
            )
            payload = archive_path.read_bytes()
            tail = self._inspect_abandoned_payload(
                payload, start_offset=start_offset
            )
            if tail["partial_bytes"] < 1:
                raise RoundTransactionError(
                    "candidate partial-tail archive has no partial record"
                )
            expected = {
                **tail,
                "archive_path": descriptor["path"],
                "archive_sha256": descriptor["sha256"],
                "archive_bytes": descriptor["bytes"],
            }
            for key, value in expected.items():
                if record.get(key) != value:
                    raise RoundTransactionError(
                        f"candidate partial recovery mismatch for {key}"
                    )

    def _recover_final_partial_candidate_tail(
        self,
        transaction: dict[str, Any],
        round_dir: Path,
    ) -> int:
        """Archive and remove only an unterminated final candidate record.

        The archive contains the entire transaction tail, not just the fragment.
        This makes an interruption between archive creation, atomic truncation,
        and manifest publication unambiguous on the next resume.
        """
        self._validate_candidate_partial_recoveries(transaction, round_dir)
        history = transaction.setdefault("candidate_partial_recoveries", [])
        start_offset = int(transaction["candidate_start_offset"])
        recovery_number = len(history) + 1
        archive_path = (
            round_dir / f"candidate-final-partial-{recovery_number:03d}.bin"
        )
        if archive_path.is_symlink():
            raise RoundTransactionError(
                f"candidate partial-tail archive may not be a symlink: {archive_path}"
            )
        source_size = self._candidate_log_size(start_offset=start_offset)

        if archive_path.exists():
            descriptor = _file_descriptor(
                archive_path, "orphan candidate partial-tail archive"
            )
            payload = archive_path.read_bytes()
            tail = self._inspect_abandoned_payload(
                payload, start_offset=start_offset
            )
            if tail["partial_bytes"] < 1:
                raise RoundTransactionError(
                    "orphan candidate partial-tail archive has no fragment"
                )
            complete_length = (
                int(tail["last_complete_offset"]) - start_offset
            )
            if source_size == tail["end_offset"]:
                with self.candidate_log.open("rb") as stream:
                    stream.seek(start_offset)
                    observed = stream.read()
                if observed != payload:
                    raise RoundTransactionError(
                        "orphan candidate partial-tail archive disagrees "
                        "with candidate log"
                    )
                self._atomic_restore_candidate_prefix(
                    int(tail["last_complete_offset"])
                )
            elif source_size == tail["last_complete_offset"]:
                with self.candidate_log.open("rb") as stream:
                    stream.seek(start_offset)
                    observed = stream.read(complete_length)
                if observed != payload[:complete_length]:
                    raise RoundTransactionError(
                        "recovered candidate prefix disagrees with its "
                        "partial-tail archive"
                    )
            else:
                raise RoundTransactionError(
                    "cannot reconcile orphan candidate partial-tail archive "
                    "with candidate log"
                )
        else:
            if source_size == start_offset:
                return source_size
            with self.candidate_log.open("rb") as stream:
                observed_size = os.fstat(stream.fileno()).st_size
                stream.seek(start_offset)
                payload = stream.read()
                final_size = os.fstat(stream.fileno()).st_size
            if observed_size != source_size or final_size != source_size:
                raise RoundTransactionError(
                    "candidate log changed while inspecting its final record"
                )
            tail = self._inspect_abandoned_payload(
                payload, start_offset=start_offset
            )
            if tail["partial_bytes"] == 0:
                return source_size
            descriptor = atomic_write_bytes(archive_path, payload)
            descriptor["path"] = str(archive_path.resolve())
            self._atomic_restore_candidate_prefix(
                int(tail["last_complete_offset"])
            )

        if (
            descriptor["sha256"] != tail["sha256"]
            or descriptor["bytes"] != tail["bytes"]
        ):
            raise RoundTransactionError(
                "candidate partial-tail archive identity mismatch"
            )
        record = {
            **tail,
            "archive_path": descriptor["path"],
            "archive_sha256": descriptor["sha256"],
            "archive_bytes": descriptor["bytes"],
            "reason": "unterminated final candidate JSONL record",
            "recovered_at": utc_now(),
        }
        history.append(record)
        atomic_write_json(
            self._transaction_paths(round_dir)["manifest"], transaction
        )
        return int(tail["last_complete_offset"])

    def _abandon_uncommitted_tail(
        self,
        transaction: dict[str, Any],
        round_dir: Path,
    ) -> None:
        """Archive and atomically remove raw rows not bound to a checkpoint."""
        start_offset = int(transaction["candidate_start_offset"])
        abandoned = transaction["abandoned_ranges"]
        attempt_number = len(abandoned) + 1
        archive_path = (
            round_dir / f"abandoned-candidate-tail-{attempt_number:03d}.bin"
        )
        if archive_path.is_symlink():
            raise RoundTransactionError(
                f"abandoned-tail archive may not be a symlink: {archive_path}"
            )
        source_size = self._candidate_log_size(start_offset=start_offset)

        if archive_path.exists():
            descriptor = _file_descriptor(
                archive_path, "orphan abandoned-tail archive"
            )
            payload = archive_path.read_bytes()
            if not payload:
                raise RoundTransactionError(
                    "orphan abandoned-tail archive is unexpectedly empty"
                )
            if source_size == start_offset:
                pass
            elif source_size == start_offset + len(payload):
                with self.candidate_log.open("rb") as stream:
                    stream.seek(start_offset)
                    observed = stream.read()
                if observed != payload:
                    raise RoundTransactionError(
                        "orphan abandoned-tail archive disagrees with candidate log"
                    )
                self._atomic_restore_candidate_prefix(start_offset)
            else:
                raise RoundTransactionError(
                    "cannot reconcile orphan abandoned-tail archive with candidate log"
                )
        else:
            if source_size == start_offset:
                return
            with self.candidate_log.open("rb") as stream:
                observed_size = os.fstat(stream.fileno()).st_size
                stream.seek(start_offset)
                payload = stream.read()
                final_size = os.fstat(stream.fileno()).st_size
            if observed_size != source_size or final_size != source_size:
                raise RoundTransactionError(
                    "candidate log changed while archiving its abandoned tail"
                )
            descriptor = atomic_write_bytes(archive_path, payload)
            descriptor["path"] = str(archive_path.resolve())
            self._atomic_restore_candidate_prefix(start_offset)

        tail = self._inspect_abandoned_payload(
            payload,
            start_offset=start_offset,
        )
        if descriptor["sha256"] != tail["sha256"] or descriptor["bytes"] != tail["bytes"]:
            raise RoundTransactionError("abandoned-tail archive identity mismatch")
        _batch_path, batch_identity = self._materialize_abandoned_candidate_batch(
            round_dir,
            attempt_number,
            payload,
            tail,
        )
        tail.update({
            "archive_path": descriptor["path"],
            "archive_sha256": descriptor["sha256"],
            "archive_bytes": descriptor["bytes"],
            "complete_candidate_batch": batch_identity,
            "reason": "expected checkpoint absent before safe replay",
            "abandoned_at": utc_now(),
        })
        abandoned.append(tail)
        atomic_write_json(self._transaction_paths(round_dir)["manifest"], transaction)

    @staticmethod
    def _checkpoint_quarantine_paths(
        round_dir: Path,
        expected_checkpoint: Path,
        attempt: int,
    ) -> tuple[dict[str, Path], dict[str, Path]]:
        sources = {
            "checkpoint": expected_checkpoint,
            "completion_marker": _completion_marker_path(round_dir),
            "slice_witness": _slice_witness_path(round_dir),
        }
        destinations = {
            "checkpoint": round_dir / f"abandoned-checkpoint-attempt-{attempt:03d}",
            "completion_marker": round_dir / (
                f"abandoned-completion-marker-attempt-{attempt:03d}.json"
            ),
            "slice_witness": round_dir / (
                f"abandoned-slice-witness-attempt-{attempt:03d}.json"
            ),
        }
        return sources, destinations

    def _resume_checkpoint_quarantine(
        self,
        transaction: dict[str, Any],
        round_dir: Path,
        expected_checkpoint: Path,
    ) -> None:
        """Finish a content-bound write-ahead quarantine after interruption."""
        records = transaction["abandoned_checkpoints"]
        pending = [
            index
            for index, record in enumerate(records)
            if isinstance(record, dict)
            and record.get("status") == "quarantining"
        ]
        last_is_pending = bool(
            records
            and isinstance(records[-1], dict)
            and records[-1].get("status") == "quarantining"
        )
        attempt = len(records) if last_is_pending else len(records) + 1
        _sources, destinations = self._checkpoint_quarantine_paths(
            round_dir, expected_checkpoint, attempt
        )
        orphan_destination = any(
            path.is_symlink() or path.exists()
            for path in destinations.values()
        )
        if orphan_destination and not pending:
            raise RoundTransactionError(
                "checkpoint quarantine destination exists without a "
                "write-ahead record"
            )
        if pending:
            self._quarantine_untrusted_evolution_attempt(
                transaction,
                round_dir,
                expected_checkpoint,
                reason="recovered interrupted checkpoint quarantine",
            )

    def _quarantine_untrusted_evolution_attempt(
        self,
        transaction: dict[str, Any],
        round_dir: Path,
        expected_checkpoint: Path,
        *,
        reason: str,
    ) -> None:
        """Durably quarantine one attempt using a replayable write-ahead record."""
        records = transaction["abandoned_checkpoints"]
        artifact_order = ("checkpoint", "completion_marker", "slice_witness")
        pending_indexes = [
            index
            for index, record in enumerate(records)
            if isinstance(record, dict)
            and record.get("status") == "quarantining"
        ]
        if pending_indexes:
            if pending_indexes != [len(records) - 1]:
                raise RoundTransactionError(
                    "checkpoint quarantine write-ahead record is not last"
                )
            plan = records[-1]
            attempt = len(records)
            if (
                plan.get("attempt") != attempt
                or not isinstance(plan.get("reason"), str)
                or not isinstance(plan.get("planned_at"), str)
                or plan.get("expected_checkpoint")
                != str(expected_checkpoint.absolute())
            ):
                raise RoundTransactionError(
                    "checkpoint quarantine write-ahead record is invalid"
                )
            names = plan.get("artifact_names")
            identities = plan.get("artifact_identities")
            if (
                not isinstance(names, list)
                or not names
                or any(name not in artifact_order for name in names)
                or any(not isinstance(name, str) for name in names)
                or len(names) != len(set(names))
                or names
                != [name for name in artifact_order if name in set(names)]
                or not isinstance(identities, dict)
                or set(identities) != set(names)
                or any(
                    not isinstance(identity, dict)
                    for identity in identities.values()
                )
            ):
                raise RoundTransactionError(
                    "checkpoint quarantine artifact plan is invalid"
                )
        else:
            if any(
                isinstance(record, dict) and "status" in record
                for record in records
            ):
                raise RoundTransactionError(
                    "checkpoint quarantine record has an invalid status"
                )
            attempt = len(records) + 1
            plan = None

        sources, destinations = self._checkpoint_quarantine_paths(
            round_dir, expected_checkpoint, attempt
        )
        for name in artifact_order:
            if sources[name].is_symlink() or destinations[name].is_symlink():
                raise RoundTransactionError(
                    f"refusing to quarantine symlinked OpenEvolve {name} artifact"
                )

        observed_names = [
            name
            for name in artifact_order
            if sources[name].exists() or destinations[name].exists()
        ]
        if plan is None:
            if not observed_names:
                return
            if any(destinations[name].exists() for name in artifact_order):
                raise RoundTransactionError(
                    "checkpoint quarantine destination exists without a "
                    "write-ahead record"
                )
            identities: dict[str, dict[str, Any]] = {}
            for name in observed_names:
                identity = _quarantined_artifact_descriptor(
                    sources[name], f"planned OpenEvolve {name}"
                )
                identity["path"] = str(destinations[name].resolve())
                identities[name] = identity
            plan = {
                "attempt": attempt,
                "status": "quarantining",
                "reason": reason,
                "expected_checkpoint": str(expected_checkpoint.absolute()),
                "artifact_names": observed_names,
                "artifact_identities": identities,
                "planned_at": utc_now(),
            }
            records.append(plan)
            atomic_write_json(
                self._transaction_paths(round_dir)["manifest"], transaction
            )
        else:
            planned_names = list(plan["artifact_names"])
            unexpected_names = [
                name for name in observed_names if name not in planned_names
            ]
            if unexpected_names:
                raise RoundTransactionError(
                    "unexpected OpenEvolve artifacts appeared during "
                    "checkpoint quarantine: " + ", ".join(unexpected_names)
                )

        artifacts: dict[str, dict[str, Any]] = {}
        for name in plan["artifact_names"]:
            source = sources[name]
            destination = destinations[name]
            source_present = source.exists()
            destination_present = destination.exists()
            if source_present and destination_present:
                raise RoundTransactionError(
                    f"cannot reconcile source and quarantined {name} artifacts"
                )
            if not source_present and not destination_present:
                raise RoundTransactionError(
                    f"planned OpenEvolve {name} artifact disappeared during quarantine"
                )
            observed_path = source if source_present else destination
            observed_identity = _quarantined_artifact_descriptor(
                observed_path, f"replayed OpenEvolve {name}"
            )
            observed_identity["path"] = str(destination.resolve())
            expected_identity = plan["artifact_identities"][name]
            if observed_identity != expected_identity:
                raise RoundTransactionError(
                    f"planned OpenEvolve {name} artifact identity changed "
                    "during quarantine"
                )
            if source_present:
                source_parent = source.parent
                source.replace(destination)
                _fsync_directory(source_parent)
                if destination.parent != source_parent:
                    _fsync_directory(destination.parent)
                destination_present = True
            if destination_present:
                destination_identity = _quarantined_artifact_descriptor(
                    destination, f"quarantined OpenEvolve {name}"
                )
                if destination_identity != expected_identity:
                    raise RoundTransactionError(
                        f"quarantined OpenEvolve {name} artifact identity "
                        "does not match its write-ahead record"
                    )
                artifacts[name] = destination_identity
        records[-1] = {
            "attempt": attempt,
            "reason": plan["reason"],
            "artifacts": artifacts,
            "abandoned_at": utc_now(),
        }
        atomic_write_json(
            self._transaction_paths(round_dir)["manifest"], transaction
        )

    def _complete_prepared_evolution(
        self,
        state: dict[str, Any],
        transaction: dict[str, Any],
        round_dir: Path,
        lease: _RoundLifecycleLease,
    ) -> None:
        expected_iteration = int(transaction["expected_result_iteration"])
        expected_path = (
            self.evolution_output
            / "checkpoints"
            / f"checkpoint_{expected_iteration}"
        )
        marker_path = _completion_marker_path(round_dir)
        witness_path = _slice_witness_path(round_dir)
        base = transaction.get("base_checkpoint")
        base_iteration = 0 if base is None else int(base["last_iteration"])
        self._resume_checkpoint_quarantine(
            transaction, round_dir, expected_path
        )
        _assert_checkpoint_frontier(
            self.evolution_output,
            base_iteration,
            allowed_iterations=frozenset({expected_iteration}),
        )
        checkpoint_present = expected_path.is_symlink() or expected_path.exists()
        marker_present = marker_path.is_symlink() or marker_path.exists()
        witness_present = witness_path.is_symlink() or witness_path.exists()

        for artifact in (expected_path, marker_path, witness_path):
            if artifact.is_symlink():
                raise RoundTransactionError(
                    f"OpenEvolve completion artifact may not be a symlink: {artifact}"
                )

        if checkpoint_present and marker_present and witness_present:
            result_checkpoint = _checkpoint_descriptor(
                self.evolution_output,
                expected_path,
                expected_iteration=expected_iteration,
            )
            try:
                witness = _validate_slice_witness(
                    witness_path,
                    self.config,
                    transaction.get("base_checkpoint"),
                    result_checkpoint,
                    transaction["launch_binding"],
                    transaction["invocation_binding"],
                    self.candidate_log,
                    int(transaction["candidate_start_offset"]),
                    require_candidate_end_of_file=True,
                )
                marker = _validate_completion_marker(
                    marker_path,
                    self.config,
                    transaction.get("base_checkpoint"),
                    result_checkpoint,
                    transaction["launch_binding"],
                    transaction["invocation_binding"],
                    witness,
                )
            except LegacySliceWitnessUpgradeRequired:
                self._quarantine_untrusted_evolution_attempt(
                    transaction,
                    round_dir,
                    expected_path,
                    reason=(
                        "legacy completion proof has no candidate-range "
                        "binding after source upgrade"
                    ),
                )
                checkpoint_present = False
                marker_present = False
                witness_present = False
            else:
                transaction["result_checkpoint"] = result_checkpoint
                transaction["completion_witness_sha256"] = witness["sha256"]
                transaction["completion_marker_sha256"] = marker["sha256"]
                return
        if any((checkpoint_present, marker_present, witness_present)):
            self._quarantine_untrusted_evolution_attempt(
                transaction,
                round_dir,
                expected_path,
                reason=(
                    "incomplete OpenEvolve checkpoint/marker/witness artifact set"
                ),
            )

        self._abandon_uncommitted_tail(transaction, round_dir)
        transaction["evolution_attempts"].append({
            "attempt": len(transaction["evolution_attempts"]) + 1,
            "candidate_start_offset": transaction["candidate_start_offset"],
            "started_at": utc_now(),
        })
        atomic_write_json(
            self._transaction_paths(round_dir)["manifest"], transaction
        )
        runner_state = dict(state)
        runner_state["_round_lifecycle_lease_fd"] = lease.fd
        runner_state["_round_lifecycle_lease_path"] = str(lease.path)
        runner_state["_evolution_launch_binding"] = copy.deepcopy(
            transaction["launch_binding"]
        )
        runner_state["_evolution_invocation_binding"] = copy.deepcopy(
            transaction["invocation_binding"]
        )
        runner_state["_evolution_base_checkpoint"] = copy.deepcopy(
            transaction["base_checkpoint"]
        )
        returned = self.evolution_runner(
            self.config, runner_state, round_dir
        )
        _assert_checkpoint_frontier(
            self.evolution_output,
            base_iteration,
            allowed_iterations=frozenset({expected_iteration}),
        )
        result_checkpoint = _checkpoint_descriptor(
            self.evolution_output,
            expected_path,
            expected_iteration=expected_iteration,
        )
        if returned is not None and Path(returned).resolve() != Path(
            result_checkpoint["path"]
        ):
            raise RoundTransactionError(
                "evolution runner returned the wrong checkpoint"
            )
        witness = _validate_slice_witness(
            witness_path,
            self.config,
            transaction.get("base_checkpoint"),
            result_checkpoint,
            transaction["launch_binding"],
            transaction["invocation_binding"],
            self.candidate_log,
            int(transaction["candidate_start_offset"]),
            require_candidate_end_of_file=True,
        )
        marker = _validate_completion_marker(
            marker_path,
            self.config,
            transaction.get("base_checkpoint"),
            result_checkpoint,
            transaction["launch_binding"],
            transaction["invocation_binding"],
            witness,
        )
        transaction["result_checkpoint"] = result_checkpoint
        transaction["completion_witness_sha256"] = witness["sha256"]
        transaction["completion_marker_sha256"] = marker["sha256"]

    def _capture_round_candidates(
        self,
        state: dict[str, Any],
        number: int,
        round_dir: Path,
    ) -> list[dict[str, Any]]:
        if self.config.candidate_file is not None:
            return self._capture_round_candidates_locked(
                state, number, round_dir, None
            )
        with _acquire_round_lifecycle_lease(round_dir) as lease:
            return self._capture_round_candidates_locked(
                state, number, round_dir, lease
            )

    def _capture_round_candidates_locked(
        self,
        state: dict[str, Any],
        number: int,
        round_dir: Path,
        lease: _RoundLifecycleLease | None,
    ) -> list[dict[str, Any]]:
        paths = self._transaction_paths(round_dir)
        transaction = self._load_transaction(
            state,
            number,
            round_dir,
            allow_prepared_rebind=lease is not None,
        )
        if transaction is None:
            transaction = self._prepare_transaction(state, number, round_dir)

        if transaction["status"] == "prepared":
            if transaction["mode"] == "openevolve":
                if lease is None:
                    raise RoundTransactionError(
                        "OpenEvolve transaction recovery requires its lifecycle lease"
                    )
                self._complete_prepared_evolution(
                    state, transaction, round_dir, lease
                )

            source_end = (
                self._recover_final_partial_candidate_tail(
                    transaction, round_dir
                )
                if transaction["mode"] == "openevolve"
                else self._candidate_log_size(
                    start_offset=int(transaction["candidate_start_offset"])
                )
            )
            try:
                source_rows, observed_end, source_sha256 = read_jsonl_range(
                    self.candidate_log,
                    int(transaction["candidate_start_offset"]),
                    source_end,
                )
            except ValueError as exc:
                raise RoundTransactionError(str(exc)) from exc
            transaction["candidate_end_offset"] = observed_end
            transaction["candidate_source_sha256"] = source_sha256
            transaction["candidate_source_rows"] = len(source_rows)
            transaction["status"] = "source-ready"
            transaction["source_ready_at"] = utc_now()
            atomic_write_json(paths["manifest"], transaction)

        if transaction["status"] in {"source-ready", "batch-ready", "committed"}:
            self._validate_transaction_checkpoint(
                transaction,
                round_dir,
                allow_historical_candidate_inode_change=(
                    transaction["status"] == "committed"
                ),
            )
            source_rows = self._validate_transaction_source(transaction)
        else:
            raise RoundTransactionError(
                f"transaction did not reach source-ready: {transaction['status']!r}"
            )

        batch_policy_version = self._candidate_batch_policy_version(transaction)
        batch_rows = _deduplicate(
            source_rows,
            policy_version=batch_policy_version,
        )
        expected_batch_identity = self._candidate_rows_identity(batch_rows)
        if transaction["status"] == "source-ready":
            batch_path = paths["batch"]
            if batch_path.is_symlink():
                raise RoundTransactionError(
                    f"candidate batch may not be a symlink: {batch_path}"
                )
            if batch_path.exists():
                try:
                    observed_rows, observed_end, observed_sha256 = read_jsonl_range(
                        batch_path, 0
                    )
                except ValueError as exc:
                    raise RoundTransactionError(str(exc)) from exc
                observed_identity = {
                    "sha256": observed_sha256,
                    "bytes": observed_end,
                    "rows": len(observed_rows),
                }
                if (
                    observed_identity != expected_batch_identity
                    or observed_rows != batch_rows
                ):
                    raise RoundTransactionError(
                        "unbound candidate batch disagrees with source snapshot"
                    )
                batch_identity = observed_identity
            else:
                batch_identity = atomic_write_jsonl(batch_path, batch_rows)
                if batch_identity != expected_batch_identity:
                    raise RoundTransactionError(
                        "atomic candidate batch identity is inconsistent"
                    )
            transaction["candidate_batch_identity"] = batch_identity
            transaction["status"] = "batch-ready"
            transaction["batch_ready_at"] = utc_now()
            atomic_write_json(paths["manifest"], transaction)

        if transaction["status"] in {"batch-ready", "committed"}:
            self._validate_transaction_checkpoint(
                transaction,
                round_dir,
                allow_historical_candidate_inode_change=(
                    transaction["status"] == "committed"
                ),
            )
            self._validate_transaction_source(transaction)
            observed_batch = self._validate_candidate_batch(transaction)
            if observed_batch != batch_rows:
                raise RoundTransactionError(
                    "candidate batch no longer matches its bound source"
                )

        initial_offset = int(transaction["initial_candidate_offset"])
        end_offset = int(transaction["candidate_end_offset"])
        base = transaction.get("base_checkpoint")
        result = transaction.get("result_checkpoint")
        expected_base = None if base is None else base["path"]
        expected_result = None if result is None else result["path"]
        precommit = (
            state.get("candidate_offset") == initial_offset
            and state.get("last_checkpoint") == expected_base
            and state.get("pending_round") is None
            and state.get("round_phase") is None
        )
        postcommit = (
            state.get("candidate_offset") == end_offset
            and state.get("last_checkpoint") == expected_result
            and state.get("pending_round") == number
            and state.get("round_phase")
            in {"screen", "audit", "review", "finalize"}
            and state.get("round_transaction_version")
            == transaction["protocol_version"]
        )

        if transaction["status"] == "batch-ready":
            if precommit:
                state["candidate_offset"] = end_offset
                state["last_checkpoint"] = expected_result
                state["pending_round"] = number
                state["round_phase"] = "screen"
                state["round_transaction_version"] = transaction[
                    "protocol_version"
                ]
                self.store.write_state(state)
                postcommit = True
            elif not postcommit:
                raise RoundTransactionError(
                    "durable state is neither before nor after transaction commit"
                )
            transaction["status"] = "committed"
            transaction["committed_at"] = utc_now()
            atomic_write_json(paths["manifest"], transaction)
        elif transaction["status"] == "committed" and not postcommit:
            raise RoundTransactionError(
                "committed manifest disagrees with durable round state"
            )

        return self._validate_candidate_batch(transaction)

    def _validate_completed_transaction(
        self,
        number: int,
        round_dir: Path,
    ) -> tuple[dict[str, Any], list[dict[str, Any]]]:
        """Replay every binding of a supported committed transaction."""
        paths = self._transaction_paths(round_dir)
        transaction = _read_json_object(
            paths["manifest"], "completed round transaction"
        )
        expected_mode = (
            "candidate-file" if self.config.candidate_file is not None
            else "openevolve"
        )
        transaction_identity = (
            transaction.get("schema_version"),
            transaction.get("protocol_version"),
        )
        if transaction_identity not in ROUND_TRANSACTION_SUPPORTED_IDENTITIES:
            raise RoundTransactionError(
                "completed transaction schema/protocol identity is unsupported"
            )
        fixed_identity = {
            "run_id": self.store.run_id,
            "round": number,
            "mode": expected_mode,
            "status": "committed",
            "candidate_log": str(self.candidate_log.resolve()),
            "candidate_batch": str(paths["batch"].resolve()),
            "completion_marker": (
                None
                if expected_mode == "candidate-file"
                else str(paths["completion"].resolve())
            ),
            "completion_witness": (
                None
                if expected_mode == "candidate-file"
                else str(paths["witness"].resolve())
            ),
        }
        for key, value in fixed_identity.items():
            if transaction.get(key) != value:
                raise RoundTransactionError(
                    f"completed transaction identity mismatch for {key}"
                )

        initial_offset = transaction.get("initial_candidate_offset")
        start_offset = transaction.get("candidate_start_offset")
        end_offset = transaction.get("candidate_end_offset")
        if (
            isinstance(initial_offset, bool)
            or not isinstance(initial_offset, int)
            or initial_offset < 0
            or start_offset != initial_offset
            or isinstance(end_offset, bool)
            or not isinstance(end_offset, int)
            or end_offset < initial_offset
        ):
            raise RoundTransactionError(
                "completed transaction candidate offsets are invalid"
            )
        if (
            isinstance(transaction.get("candidate_source_rows"), bool)
            or not isinstance(transaction.get("candidate_source_rows"), int)
            or transaction["candidate_source_rows"] < 0
            or not isinstance(transaction.get("candidate_source_sha256"), str)
            or len(transaction["candidate_source_sha256"]) != 64
        ):
            raise RoundTransactionError(
                "completed transaction source identity is invalid"
            )

        abandoned = transaction.get("abandoned_ranges")
        partial_recoveries = transaction.get(
            "candidate_partial_recoveries", []
        )
        quarantined = transaction.get("abandoned_checkpoints")
        attempts = transaction.get("evolution_attempts")
        rebinds = transaction.setdefault("evolution_binding_rebinds", [])
        if (
            not isinstance(abandoned, list)
            or not isinstance(partial_recoveries, list)
            or not isinstance(quarantined, list)
            or not isinstance(attempts, list)
            or not isinstance(rebinds, list)
        ):
            raise RoundTransactionError(
                "completed transaction recovery history is invalid"
            )
        self._abandoned_candidate_inputs(transaction, round_dir)
        self._validate_candidate_partial_recoveries(transaction, round_dir)
        for index, record in enumerate(quarantined, 1):
            if (
                not isinstance(record, dict)
                or record.get("attempt") != index
                or not isinstance(record.get("reason"), str)
                or not isinstance(record.get("abandoned_at"), str)
                or not isinstance(record.get("artifacts"), dict)
            ):
                raise RoundTransactionError(
                    "quarantined checkpoint record is invalid"
                )
            destinations = {
                "checkpoint": round_dir / f"abandoned-checkpoint-attempt-{index:03d}",
                "completion_marker": round_dir / (
                    f"abandoned-completion-marker-attempt-{index:03d}.json"
                ),
                "slice_witness": round_dir / (
                    f"abandoned-slice-witness-attempt-{index:03d}.json"
                ),
            }
            artifacts = record["artifacts"]
            if not artifacts or not set(artifacts).issubset(destinations):
                raise RoundTransactionError(
                    "quarantined checkpoint artifact set is invalid"
                )
            for name, expected_descriptor in artifacts.items():
                observed_descriptor = _quarantined_artifact_descriptor(
                    destinations[name], f"quarantined OpenEvolve {name}"
                )
                if observed_descriptor != expected_descriptor:
                    raise RoundTransactionError(
                        f"quarantined checkpoint artifact changed: {name}"
                    )
        for index, attempt in enumerate(attempts, 1):
            if (
                not isinstance(attempt, dict)
                or attempt.get("attempt") != index
                or attempt.get("candidate_start_offset") != initial_offset
                or not isinstance(attempt.get("started_at"), str)
            ):
                raise RoundTransactionError(
                    "completed transaction evolution attempt history is invalid"
                )

        base = transaction.get("base_checkpoint")
        result = transaction.get("result_checkpoint")
        if expected_mode == "candidate-file":
            if (
                transaction.get("iterations_per_round") != 0
                or base is not None
                or result is not None
                or transaction.get("expected_result_iteration") is not None
                or transaction.get("launch_binding") is not None
                or transaction.get("invocation_binding") is not None
                or transaction.get("completion_marker_sha256") is not None
                or transaction.get("completion_witness_sha256") is not None
                or abandoned
                or partial_recoveries
                or quarantined
                or attempts
                or rebinds
            ):
                raise RoundTransactionError(
                    "completed candidate-file transaction has evolution fields"
                )
        else:
            current_launch, _current_invocation = (
                _current_evolution_bindings(self.config, round_dir)
            )
            _validate_stored_binding_shape(
                self.config,
                transaction.get("launch_binding"),
                transaction.get("invocation_binding"),
                round_dir,
                current_launch,
                allow_previous_committed=True,
            )
            self._validate_binding_rebind_history(
                transaction, round_dir, current_launch
            )
            # Completed rounds retain the exact historical launch hashes in
            # their manifest/witness.  Replay those immutable artifacts, but
            # do not require the live repository to keep obsolete evaluator
            # bytes forever; the next prepared slice separately freezes and
            # validates the current source tree.
            if base is not None:
                if not isinstance(base, dict) or "path" not in base:
                    raise RoundTransactionError(
                        "completed transaction base checkpoint is invalid"
                    )
                observed_base = _checkpoint_descriptor(
                    self.evolution_output,
                    Path(base["path"]),
                    expected_iteration=base.get("last_iteration"),
                )
                if observed_base != base:
                    raise RoundTransactionError(
                        "completed transaction base checkpoint changed"
                    )
            base_iteration = 0 if base is None else int(base["last_iteration"])
            expected_iteration = base_iteration + self.config.iterations_per_round
            if (
                transaction.get("iterations_per_round")
                != self.config.iterations_per_round
                or transaction.get("expected_result_iteration")
                != expected_iteration
                or not isinstance(result, dict)
                or result.get("last_iteration") != expected_iteration
            ):
                raise RoundTransactionError(
                    "completed transaction iteration binding is invalid"
                )
            self._validate_transaction_checkpoint(
                transaction,
                round_dir,
                allow_historical_candidate_inode_change=True,
            )

        source_rows = self._validate_transaction_source(transaction)
        batch_rows = self._validate_candidate_batch(transaction)
        batch_policy_version = self._candidate_batch_policy_version(transaction)
        if batch_rows != _deduplicate(
            source_rows,
            policy_version=batch_policy_version,
        ):
            raise RoundTransactionError(
                "completed candidate batch disagrees with its source slice"
            )
        return transaction, batch_rows

    @staticmethod
    def _legacy_batch_paths(round_dir: Path) -> dict[str, Path]:
        return {
            "batch": round_dir / "legacy-candidate-batch.jsonl",
            "sidecar": round_dir / "legacy-candidate-batch.json",
        }

    def _validate_legacy_batch_sidecar(
        self,
        number: int,
        round_dir: Path,
    ) -> Path:
        paths = self._legacy_batch_paths(round_dir)
        sidecar = _read_json_object(
            paths["sidecar"], "legacy candidate-batch sidecar"
        )
        expected = {
            "schema_version": LEGACY_BATCH_SCHEMA_VERSION,
            "protocol": "legacy-materialized-v1",
            "status": "committed",
            "run_id": self.store.run_id,
            "round": number,
            "candidate_batch": str(paths["batch"].resolve()),
        }
        for key, value in expected.items():
            if sidecar.get(key) != value:
                raise RoundTransactionError(
                    f"legacy candidate-batch sidecar mismatch for {key}"
                )
        identity = sidecar.get("candidate_batch_identity")
        pseudo_transaction = {
            "candidate_batch": sidecar["candidate_batch"],
            "candidate_batch_identity": identity,
        }
        self._validate_candidate_batch(pseudo_transaction)
        return paths["batch"]

    def _materialize_legacy_batch(
        self,
        number: int,
        round_dir: Path,
        candidate_path: Path,
        *,
        binding: dict[str, Any],
    ) -> Path:
        paths = self._legacy_batch_paths(round_dir)
        if paths["sidecar"].is_symlink():
            raise RoundTransactionError(
                f"legacy batch sidecar may not be a symlink: {paths['sidecar']}"
            )
        if paths["sidecar"].exists():
            return self._validate_legacy_batch_sidecar(number, round_dir)
        if candidate_path.is_symlink() or not candidate_path.is_file():
            raise RoundTransactionError(
                f"legacy round candidates are missing: {candidate_path}"
            )
        try:
            rows, source_bytes, source_sha256 = read_jsonl_range(candidate_path, 0)
        except ValueError as exc:
            raise RoundTransactionError(str(exc)) from exc
        source_identity = {
            "path": str(candidate_path.resolve()),
            "sha256": source_sha256,
            "bytes": source_bytes,
            "rows": len(rows),
        }
        expected_batch_identity = self._candidate_rows_identity(rows)
        if paths["batch"].is_symlink():
            raise RoundTransactionError(
                f"legacy candidate batch may not be a symlink: {paths['batch']}"
            )
        if paths["batch"].exists():
            try:
                observed_rows, observed_bytes, observed_sha256 = read_jsonl_range(
                    paths["batch"], 0
                )
            except ValueError as exc:
                raise RoundTransactionError(str(exc)) from exc
            batch_identity = {
                "sha256": observed_sha256,
                "bytes": observed_bytes,
                "rows": len(observed_rows),
            }
            if batch_identity != expected_batch_identity or observed_rows != rows:
                raise RoundTransactionError(
                    "orphan legacy candidate batch disagrees with candidates"
                )
        else:
            batch_identity = atomic_write_jsonl(paths["batch"], rows)
            if batch_identity != expected_batch_identity:
                raise RoundTransactionError(
                    "legacy candidate batch identity is inconsistent"
                )
        sidecar = {
            "schema_version": LEGACY_BATCH_SCHEMA_VERSION,
            "protocol": "legacy-materialized-v1",
            "status": "committed",
            "run_id": self.store.run_id,
            "round": number,
            "candidate_source": source_identity,
            "candidate_batch": str(paths["batch"].resolve()),
            "candidate_batch_identity": batch_identity,
            "legacy_binding": binding,
            "materialized_at": utc_now(),
        }
        atomic_write_json(paths["sidecar"], sidecar)
        return self._validate_legacy_batch_sidecar(number, round_dir)

    def _migrate_legacy_completed_rounds(self, state: dict[str, Any]) -> None:
        for number in range(1, int(state.get("current_round", 0)) + 1):
            round_dir = self.store.round_dir(number)
            manifest = self._transaction_paths(round_dir)["manifest"]
            legacy_sidecar = self._legacy_batch_paths(round_dir)["sidecar"]
            if manifest.exists():
                self._validate_completed_transaction(number, round_dir)
                continue
            if legacy_sidecar.exists():
                self._validate_legacy_batch_sidecar(number, round_dir)
                continue
            self._materialize_legacy_batch(
                number,
                round_dir,
                round_dir / "candidates.jsonl",
                binding={
                    "kind": "completed-pre-transaction-round",
                    "migrated_from_state_round": state.get("current_round"),
                },
            )

    def _validate_legacy_pending_round(
        self,
        state: dict[str, Any],
        number: int,
        candidate_path: Path,
        milp_path: Path,
    ) -> None:
        phase = state.get("round_phase")
        if phase not in {"screen", "audit", "review", "finalize"}:
            raise RoundTransactionError(
                f"legacy pending round has invalid phase: {phase!r}"
            )
        offset = state.get("candidate_offset")
        if isinstance(offset, bool) or not isinstance(offset, int) or offset < 0:
            raise RoundTransactionError("legacy candidate_offset is invalid")
        self._recover_candidate_log_wal()
        try:
            _rows, observed_offset, _sha256 = read_jsonl_range(
                self.candidate_log, 0, offset
            )
        except ValueError as exc:
            raise RoundTransactionError(
                "legacy candidate offset does not bind a valid source prefix"
            ) from exc
        if observed_offset != offset:
            raise RoundTransactionError("legacy candidate offset changed")

        checkpoint_binding = None
        if self.config.candidate_file is None:
            checkpoint_value = state.get("last_checkpoint")
            if not checkpoint_value:
                raise RoundTransactionError(
                    "legacy pending evolution round has no checkpoint"
                )
            checkpoint_binding = _checkpoint_descriptor(
                self.evolution_output,
                Path(checkpoint_value),
                expected_iteration=number * self.config.iterations_per_round,
            )
        elif state.get("last_checkpoint") is not None:
            raise RoundTransactionError(
                "legacy candidate-file round unexpectedly has a checkpoint"
            )

        if phase in {"audit", "review", "finalize"}:
            selected_path = candidate_path.parent / "selected.jsonl"
            for label, path in (
                ("selection", selected_path),
                ("MILP evidence", milp_path),
            ):
                if path.is_symlink() or not path.is_file():
                    raise RoundTransactionError(
                        f"legacy pending round is missing {label}: {path}"
                    )
                try:
                    read_jsonl_range(path, 0)
                except ValueError as exc:
                    raise RoundTransactionError(
                        f"legacy pending round has invalid {label}"
                    ) from exc

        batch_path = self._materialize_legacy_batch(
            number,
            candidate_path.parent,
            candidate_path,
            binding={
                "kind": "pending-pre-transaction-round",
                "phase": phase,
                "candidate_offset": offset,
                "result_checkpoint": checkpoint_binding,
            },
        )
        state["legacy_round_transaction"] = {
            "round": number,
            "candidate_batch": str(batch_path.resolve()),
        }
        self.store.write_state(state)

    @staticmethod
    def _read_validated_candidate_input(path: Path) -> list[dict[str, Any]]:
        try:
            rows, end_offset, _source_sha256 = read_jsonl_range(path, 0)
        except ValueError as exc:
            raise RoundTransactionError(str(exc)) from exc
        if end_offset != path.stat().st_size:
            raise RoundTransactionError(
                f"candidate input is not complete bound JSONL: {path}"
            )
        return rows

    def _validated_committed_candidate_history(
        self,
    ) -> tuple[tuple[Path, ...], list[dict[str, Any]]]:
        """Return transaction-replayed candidate inputs and all of their rows.

        ``archive.json`` is only a disposable MAP-Elites cache.  Scheduling
        must instead be rebuilt from the immutable per-round transactions so a
        high BP upper bound cannot permanently hide a runner-up in the same
        archive cell.
        """
        state = self.store.load_state()
        if state is None:
            return (), []
        paths: list[Path] = []
        rows: list[dict[str, Any]] = []
        previous: dict[str, Any] | None = None
        legacy_boundary = False
        seen_v2 = False
        for number in range(1, int(state.get("current_round", 0)) + 1):
            round_dir = self.store.root / "rounds" / f"round-{number:03d}"
            transaction_path = self._transaction_paths(round_dir)["manifest"]
            legacy_sidecar = self._legacy_batch_paths(round_dir)["sidecar"]
            if transaction_path.exists() and legacy_sidecar.exists():
                raise RoundTransactionError(
                    f"round {number} has both legacy and v2 candidate batches"
                )
            if transaction_path.exists():
                transaction, batch_rows = self._validate_completed_transaction(
                    number, round_dir
                )
                start_offset = int(transaction["candidate_start_offset"])
                if previous is None:
                    if not legacy_boundary and start_offset != 0:
                        raise RoundTransactionError(
                            "first pure-v2 transaction must start at candidate offset zero"
                        )
                    if (
                        not legacy_boundary
                        and transaction["mode"] == "openevolve"
                        and transaction.get("base_checkpoint") is not None
                    ):
                        raise RoundTransactionError(
                            "first pure-v2 transaction may not resume an unbound checkpoint"
                        )
                else:
                    if int(previous["candidate_end_offset"]) != start_offset:
                        raise RoundTransactionError(
                            "completed transaction candidate offsets are not contiguous"
                        )
                    if previous.get("result_checkpoint") != transaction.get(
                        "base_checkpoint"
                    ):
                        raise RoundTransactionError(
                            "completed transaction checkpoint chain is broken"
                        )
                if transaction["mode"] == "openevolve":
                    result = transaction["result_checkpoint"]
                    expected_result = (
                        self.evolution_output
                        / "checkpoints"
                        / f"checkpoint_{transaction['expected_result_iteration']}"
                    ).resolve()
                    if Path(result["path"]) != expected_result:
                        raise RoundTransactionError(
                            "completed transaction result checkpoint path is non-canonical"
                        )
                abandoned_inputs = self._abandoned_candidate_inputs(
                    transaction, round_dir
                )
                for path in abandoned_inputs:
                    paths.append(path)
                    rows.extend(self._read_validated_candidate_input(path))
                paths.append(Path(transaction["candidate_batch"]))
                rows.extend(batch_rows)
                previous = transaction
                legacy_boundary = False
                seen_v2 = True
            elif legacy_sidecar.exists():
                if seen_v2:
                    raise RoundTransactionError(
                        "legacy candidate batch may not follow a v2 transaction"
                    )
                path = self._validate_legacy_batch_sidecar(number, round_dir)
                paths.append(path)
                rows.extend(self._read_validated_candidate_input(path))
                previous = None
                legacy_boundary = True
            else:
                raise RoundTransactionError(
                    f"round {number} has no canonical committed candidate batch"
                )
        return tuple(paths), rows

    def _validated_canonical_evaluations(
        self,
        state: dict[str, Any],
    ) -> list[dict[str, Any]]:
        """Strictly replay the canonical Stage 1 audit log for handoff."""
        rows = self._read_canonical_evaluations(
            recover_final_partial=False
        )
        rebuilt = rebuild_audit_state(
            rows,
            fully_exact=is_fully_exact,
            checkpoint_path_for=lambda key: self._milp_checkpoint_path(key),
        )
        recorded_count = state.get("audit_evaluations_seen")
        if (
            recorded_count is not None
            and recorded_count != rebuilt.evaluations_seen
        ):
            raise AuditStateError(
                "canonical evaluation count disagrees with durable state"
            )
        for name, expected in rebuilt.as_state_fields().items():
            recorded = state.get(name)
            if recorded is not None and recorded != expected:
                raise AuditStateError(
                    f"canonical evaluation state disagrees for {name}"
                )
        return rows

    @property
    def pipeline_candidate_inputs(self) -> tuple[Path, ...]:
        state = self.store.load_state()
        if state is None:
            return ()
        candidate_paths, _rows = (
            self._validated_committed_candidate_history()
        )
        paths = list(candidate_paths)
        if self.evaluations_path.exists():
            self._validated_canonical_evaluations(state)
            paths.append(self.evaluations_path.resolve())
        return tuple(paths)

    def _replay_screened_candidate_pool_impl(
        self,
        current: list[dict[str, Any]],
        *,
        policy_version: int = CANDIDATE_BATCH_POLICY_VERSION,
        build_digest_index: bool,
    ) -> tuple[
        list[dict[str, Any]],
        list[dict[str, Any]],
        _VerifiedStructuralDigestIndex | None,
    ]:
        """Rebuild the eligible pool from bound history with verified cache."""
        from evaluation.structural_dedup import (
            screen_css_results_with_deferred_cache,
            structural_screen_runtime_fingerprint,
        )

        runtime_before = (
            structural_screen_runtime_fingerprint()["sha256"]
            if build_digest_index
            else None
        )
        _paths, historical = self._validated_committed_candidate_history()
        combined = _deduplicate(
            historical + current,
            policy_version=policy_version,
        )
        combined.sort(key=candidate_evidence_priority, reverse=True)
        worker_budget = self.config.max_total_workers or 1
        kept, rejected, unresolved = (
            screen_css_results_with_deferred_cache(
                combined,
                cache_dir=self.store.root / "structural-screen-cache-v1",
                max_workers=worker_budget,
            )
        )
        if unresolved:
            self.store.event(
                "structural_screen_deferred",
                retryable=True,
                unresolved=len(unresolved),
                candidates=unresolved,
                max_total_workers=worker_budget,
            )
        digest_index = (
            _VerifiedStructuralDigestIndex(
                kept,
                runtime_sha256_before_screen=runtime_before,
            )
            if runtime_before is not None
            else None
        )
        return kept, rejected, digest_index

    def _replay_screened_candidate_pool(
        self,
        current: list[dict[str, Any]],
        *,
        policy_version: int = CANDIDATE_BATCH_POLICY_VERSION,
    ) -> tuple[list[dict[str, Any]], list[dict[str, Any]]]:
        """Compatibility wrapper that does not retain selector sidecars."""

        kept, rejected, _digest_index = (
            self._replay_screened_candidate_pool_impl(
                current,
                policy_version=policy_version,
                build_digest_index=False,
            )
        )
        return kept, rejected

    def _replay_screened_candidate_pool_indexed(
        self,
        current: list[dict[str, Any]],
        *,
        policy_version: int = CANDIDATE_BATCH_POLICY_VERSION,
    ) -> tuple[
        list[dict[str, Any]],
        list[dict[str, Any]],
        _VerifiedStructuralDigestIndex,
    ]:
        """Replay screening and retain its verified digests in memory."""

        kept, rejected, digest_index = (
            self._replay_screened_candidate_pool_impl(
                current,
                policy_version=policy_version,
                build_digest_index=True,
            )
        )
        if digest_index is None:
            raise AuditStateError(
                "verified structural-screen selector index was not built"
            )
        return kept, rejected, digest_index

    def _screen_candidates_with_pool(
        self,
        rows: list[dict[str, Any]],
        *,
        policy_version: int = CANDIDATE_BATCH_POLICY_VERSION,
    ) -> tuple[
        list[dict[str, Any]],
        list[dict[str, Any]],
        list[dict[str, Any]],
    ]:
        """Apply static and BLISS gates before archive ranking or MILP.

        The persistent archive is regenerated only as an advisory cache.
        Selection separately replays all transaction-bound history, retaining
        same-cell runners-up that MAP-Elites intentionally omits.
        """
        current = _deduplicate(rows, policy_version=policy_version)
        current_keys = {code_key(row) for row in current}
        kept, rejected = self._replay_screened_candidate_pool(
            current,
            policy_version=policy_version,
        )
        self.archive.replace(kept)
        accepted = [row for row in kept if code_key(row) in current_keys]
        return accepted, rejected, kept

    def _screen_candidates_with_pool_indexed(
        self,
        rows: list[dict[str, Any]],
        *,
        policy_version: int = CANDIDATE_BATCH_POLICY_VERSION,
    ) -> tuple[
        list[dict[str, Any]],
        list[dict[str, Any]],
        list[dict[str, Any]],
        _VerifiedStructuralDigestIndex,
    ]:
        """Screen one pool and keep an ephemeral digest capability."""

        current = _deduplicate(rows, policy_version=policy_version)
        current_keys = {code_key(row) for row in current}
        kept, rejected, digest_index = (
            self._replay_screened_candidate_pool_indexed(
                current,
                policy_version=policy_version,
            )
        )
        self.archive.replace(kept)
        accepted = [row for row in kept if code_key(row) in current_keys]
        return accepted, rejected, kept, digest_index

    def _screen_candidates(
        self,
        rows: list[dict[str, Any]],
        *,
        policy_version: int = CANDIDATE_BATCH_POLICY_VERSION,
    ) -> tuple[list[dict[str, Any]], list[dict[str, Any]]]:
        accepted, rejected, _pool = self._screen_candidates_with_pool(
            rows,
            policy_version=policy_version,
        )
        return accepted, rejected

    def _audit_selected(
        self,
        selected: list[dict[str, Any]],
        *,
        state: dict[str, Any],
        milp_path: Path,
        round_number: int,
    ) -> list[dict[str, Any]]:
        """Audit one ordered selection with a global canonical commit log."""
        global_rows = self._read_canonical_evaluations(
            recover_final_partial=False
        )
        existing = self._reconcile_round_evaluations(
            selected,
            round_number=round_number,
            milp_path=milp_path,
            global_rows=global_rows,
        )
        by_key = {code_key(row): row for row in existing}
        pending = [row for row in selected if code_key(row) not in by_key]
        failures: list[tuple[str, Exception]] = []

        def run_one(
            candidate: dict[str, Any],
        ) -> tuple[dict[str, Any], dict[str, Any]]:
            attempt_config, attempt, invocation = self._attempt_plan(
                candidate,
                state,
                round_number=round_number,
            )
            return (
                self._evaluate_audit_attempt(
                    candidate,
                    attempt_config,
                    invocation,
                ),
                attempt,
            )

        def persist(
            candidate: dict[str, Any],
            result: dict[str, Any],
            attempt: dict[str, Any],
        ) -> None:
            normalized_candidate = dict(candidate)
            geometry = candidate_geometry(candidate)
            if geometry is None:
                normalized_candidate.pop("geometry", None)
            else:
                normalized_candidate["geometry"] = geometry
            key = code_key(normalized_candidate)
            formal_contract = result.pop(
                "_humanize_formal_audit_contract", False
            )
            if not isinstance(formal_contract, bool):
                raise AuditStateError(
                    "internal formal evaluator marker is invalid"
                )
            defining_fields = (
                "construction", "geometry", "ell", "m", "A_terms", "B_terms",
            )
            provenance_fields = (
                "static_eligibility",
                "structural_novelty",
                "search_representation_id",
                "formal_audit_quota_assignment",
            )
            proposed_identity = dict(result)
            for field in defining_fields:
                if (
                    field not in proposed_identity
                    and field in normalized_candidate
                ):
                    proposed_identity[field] = normalized_candidate[field]
            observed_key = code_key(proposed_identity)
            if observed_key != key:
                raise AuditStateError(
                    "MILP evaluator returned defining fields for a different "
                    f"candidate: expected {key}, got {observed_key}"
                )
            returned_key = result.get("candidate_key")
            if returned_key is not None and returned_key != key:
                raise AuditStateError(
                    "MILP evaluator returned a mismatched candidate_key"
                )
            for field in defining_fields + provenance_fields:
                if field in normalized_candidate:
                    result[field] = normalized_candidate[field]
                else:
                    result.pop(field, None)
            result["candidate_key"] = key
            result["milp_attempted"] = True
            result["d_is_exact"] = is_fully_exact(result)
            if formal_contract:
                result["audit_attempt"] = seal_audit_attempt_evidence(
                    result,
                    attempt,
                    run_dir=self.run_dir,
                    evidence_root=(
                        self.run_dir / "milp-checkpoints" / "evidence"
                    ),
                )
            else:
                result.pop("audit_evaluator_invocation", None)
                debug_attempt = dict(attempt)
                debug_attempt["schema_version"] = 1
                result["audit_attempt"] = debug_attempt

            # Validate the row and the entire proposed history before changing
            # the canonical log. This rejects non-finite JSON, identity drift,
            # invalid retry metadata, and inconsistent checkpoint history.
            self._canonical_row_identity(result)
            proposed_rows = [*global_rows, result]
            rebuild_audit_state(
                proposed_rows,
                fully_exact=is_fully_exact,
                checkpoint_path_for=lambda candidate_key: (
                    self._milp_checkpoint_path(candidate_key)
                ),
            )

            # The global log is canonical. If the process dies after this
            # rename, the next start reconstructs both state and round output.
            global_rows[:] = proposed_rows
            atomic_write_jsonl(self.evaluations_path, global_rows)
            by_key[key] = result
            atomic_write_jsonl(
                milp_path,
                [
                    by_key[selected_key]
                    for selected_key in (code_key(row) for row in selected)
                    if selected_key in by_key
                ],
            )
            self._rebuild_global_audit_state(
                state,
                recover_final_partial=False,
            )
            state["round_phase"] = "audit"
            self.store.write_state(state)

        if len(pending) == 1:
            candidate = pending[0]
            result, attempt = run_one(candidate)
            persist(candidate, result, attempt)
        elif pending:
            workers = _stage1_milp_worker_count(self.config, len(pending))
            with ThreadPoolExecutor(max_workers=workers) as pool:
                futures = {
                    pool.submit(run_one, candidate): candidate
                    for candidate in pending
                }
                for future in as_completed(futures):
                    candidate = futures[future]
                    try:
                        result, attempt = future.result()
                    except Exception as exc:
                        failures.append((code_key(candidate), exc))
                    else:
                        persist(candidate, result, attempt)

        if failures:
            key, exc = failures[0]
            raise RuntimeError(
                f"MILP audit failed for {key}: {type(exc).__name__}: {exc}"
            ) from exc

        # Reviewer input follows selection order, independent of worker finish
        # order and canonical-log order.
        return [
            by_key[code_key(row)]
            for row in selected
            if code_key(row) in by_key
        ]

    def _write_run_meta(self, state: dict[str, Any]) -> None:
        meta = {
            "run_id": self.store.run_id,
            "status": state["status"],
            "humanize": True,
            "rounds_completed": state["current_round"],
            "total_evaluations": int(state.get("audit_evaluations_seen", 0)),
            "unresolved": len(state.get("unresolved_candidates", {})),
            "best_fom": state.get("best_fom", 0.0),
            "best_bp_fom_upper_bound": state.get(
                "best_bp_fom_upper_bound",
                0.0,
            ),
            "best_exact_fom": state.get("best_exact_fom", 0.0),
            "trusted_exact": int(state.get("trusted_exact_count", 0)),
            "trusted_wins": int(state.get("trusted_win_count", 0)),
            "search_regime": copy.deepcopy(
                state.get("search_regime", _normal_search_regime(0))
            ),
            "max_total_workers": self.config.max_total_workers,
            "config": state["config"],
            "state_path": str(self.store.state_path),
            "updated_at": utc_now(),
        }
        path = self.run_dir / "run_meta.json"
        temporary = path.with_suffix(".json.tmp")
        temporary.write_text(json.dumps(meta, ensure_ascii=False, indent=2) + "\n")
        temporary.replace(path)

    def _write_contract(self, round_number: int, round_dir: Path) -> dict[str, Any]:
        contract = {
            "round": round_number,
            "build": {
                "openevolve_iterations_this_round": self.config.iterations_per_round,
                "openevolve_target_iterations": round_number * self.config.iterations_per_round,
                "model": self.config.model,
                "reasoning_effort": self.config.reasoning_effort,
                "max_total_workers": self.config.max_total_workers,
            },
            "promotion_gates": {
                "static": "commuting, weight/degree <= 6, connected Tanner graph",
                "novelty": "BLISS match plus explicit H_X/H_Z replay",
                "bp_osd": "upper-bound candidate only",
                "milp_top": self.config.milp_top,
                "milp_exact": "all logical directions proven optimal",
                "lean": "performed by archon after search promotion",
            },
            "review": {
                "model": self.config.review_model,
                "reasoning_effort": self.config.review_effort,
                "independent_fresh_session": True,
            },
        }
        (round_dir / "contract.json").write_text(
            json.dumps(contract, ensure_ascii=False, indent=2) + "\n"
        )
        return contract

    def _finish_round(
        self,
        state: dict[str, Any],
        number: int,
        candidates: list[dict[str, Any]],
        audited: list[dict[str, Any]],
        review: dict[str, Any],
        round_dir: Path,
    ) -> None:
        exact = sum(1 for row in audited if row.get("d_is_exact"))
        failure_direction_feedback = (
            _write_round_failure_direction_feedback(
                round_number=number,
                round_dir=round_dir,
                audited_rows=audited,
            )
        )
        sealed_exact_audit = _sealed_round_exact_summary(
            round_number=number,
            round_dir=round_dir,
            failure_feedback=failure_direction_feedback,
        )
        candidate_diversity: dict[str, Any] | None = None
        search_oracle_feedback: dict[str, Any] | None = None
        transaction_path = self._transaction_paths(round_dir)["manifest"]
        if transaction_path.is_file():
            transaction, batch_rows = self._validate_completed_transaction(
                number, round_dir
            )
            candidate_diversity = _candidate_diversity_summary(
                transaction, batch_rows
            )
            search_oracle_feedback = _write_round_search_oracle_feedback(
                round_number=number,
                round_dir=round_dir,
                candidate_rows=batch_rows,
            )
        review_binding = _review_artifact_binding(
            round_dir / "review.json",
            review,
        )
        renderer_resolution_binding = None
        if (
            _flow_evaluator_kind(self.config) == "coset-two-block"
            and _configured_coset_representation_id(self.config)
            == COSET_REPRESENTATION_ID_V3
        ):
            renderer_resolution_binding = _seal_round_renderer_resolution(
                round_number=number,
                round_dir=round_dir,
                review=review,
                review_binding=review_binding,
            )
        formal_audit_quota_summary: dict[str, Any] | None = None
        if self.config.formal_audit_quota_contract is not None:
            from evaluation.formal_audit_quota import (
                load_quota_contract,
                validate_selection_report,
            )

            quota_contract = load_quota_contract(
                self.config.formal_audit_quota_contract,
                representation_id=self.config.search_representation_id,
                rounds=self.config.max_rounds,
                slots_per_round=self.config.milp_top,
            )
            quota_path = round_dir / "formal-audit-quota-selection.json"
            quota_report = validate_selection_report(
                _read_json_object(
                    quota_path,
                    "formal-audit quota selection report",
                ),
                contract=quota_contract,
                round_number=number,
            )
            audited_keys = {code_key(row) for row in audited}
            scheduled_keys = {
                row["candidate_key"]
                for row in quota_report["slots"]
                if row["status"] == "FILLED"
            }.union(quota_report["retry_candidate_keys"])
            if audited_keys != scheduled_keys:
                raise RoundTransactionError(
                    "formal-audit quota report disagrees with sealed audits"
                )
            volume_counts: dict[str, int] = {}
            for row in quota_report["slots"]:
                if row["status"] != "FILLED":
                    continue
                volume = str(row["volume"])
                volume_counts[volume] = volume_counts.get(volume, 0) + 1
            formal_audit_quota_summary = {
                "schema_version": 1,
                "contract_sha256": quota_contract["contract_sha256"],
                "report_sha256": quota_report["report_sha256"],
                "filled_fresh_slots": quota_report["filled_fresh_slots"],
                "unfilled_fresh_slots": quota_report["unfilled_fresh_slots"],
                "retry_slots": len(quota_report["retry_candidate_keys"]),
                "volume_counts": dict(sorted(volume_counts.items())),
            }
        summary = {
            "round": number,
            "new_candidates": len(candidates),
            "milp_audited": len(audited),
            "milp_exact": exact,
            "best_fom": max(
                (
                    candidate_proven_fom(r)
                    for r in [*candidates, *audited]
                ),
                default=0.0,
            ),
            "best_bp_fom_upper_bound": max(
                (candidate_fom(r) for r in candidates),
                default=0.0,
            ),
            "trusted_exact_total": int(
                state.get("trusted_exact_count", 0)
            ),
            "trusted_win_total": int(state.get("trusted_win_count", 0)),
            "best_exact_fom": float(state.get("best_exact_fom", 0.0)),
            "review_verdict": review["verdict"],
            "review_summary": review["summary"],
            "review_binding": review_binding,
            "failure_direction_feedback": failure_direction_feedback,
            "sealed_exact_audit": sealed_exact_audit,
        }
        if self.config.search_regime_policy_version in {2, 3, 4}:
            summary["search_regime_policy_version"] = (
                self.config.search_regime_policy_version
            )
        if candidate_diversity is not None:
            summary["candidate_diversity"] = candidate_diversity
        if search_oracle_feedback is not None:
            summary["search_oracle_feedback"] = search_oracle_feedback
        if formal_audit_quota_summary is not None:
            summary["formal_audit_quota"] = formal_audit_quota_summary
        if renderer_resolution_binding is not None:
            summary[COSET_RENDERER_RESOLUTION_SUMMARY_FIELD] = (
                renderer_resolution_binding
            )
        regime = _replay_search_regime(
            [*state["rounds"], summary],
            rounds_root=round_dir.parent,
            policy_version=self.config.search_regime_policy_version,
            max_rounds=(
                self.config.max_rounds
                if self.config.search_regime_policy_version
                in SEARCH_REGIME_BUDGET_BOUND_POLICY_VERSIONS
                else None
            ),
        )
        summary["search_regime"] = copy.deepcopy(regime)
        state["search_regime"] = copy.deepcopy(regime)
        summary_payload = (
            "\n".join([
                f"# Humanize qcode round {number}", "",
                f"- New candidates: {len(candidates)}",
                f"- MILP audited: {len(audited)}",
                f"- Fully exact MILP: {exact}",
                (
                    "- Trusted exact history: "
                    f"{int(state.get('trusted_exact_count', 0))}"
                ),
                (
                    "- Trusted exact WINs: "
                    f"{int(state.get('trusted_win_count', 0))}"
                ),
                (
                    "- Trusted low-weight failure witnesses: "
                    f"{failure_direction_feedback['trusted_witnesses']}"
                ),
                (
                    "- Replayed Stage-2 oracle witnesses: "
                    f"{0 if search_oracle_feedback is None else search_oracle_feedback['replayed_witnesses']}"
                ),
                f"- Search regime: `{regime['status']}`",
                f"- Reviewer verdict: `{review['verdict']}`", "",
                "## Review", "", review["summary"], "",
                "## BitLesson Delta", "",
                f"- Action: {'add' if review['lessons'] else 'none'}",
                f"- Lesson count: {len(review['lessons'])}",
            ]) + "\n"
        ).encode("utf-8")
        atomic_write_bytes(
            round_dir / "summary.md",
            summary_payload,
        )
        # Install the logical commit in the caller-owned state only after all
        # round artifacts exist.  The outer finalize path applies this method
        # to a private state copy and persists that copy as one commit.
        state["rounds"].append(summary)
        state["current_round"] = number

    def run(
        self,
        *,
        inherited_run_lease: _HumanizeRunLease | None = None,
    ) -> dict[str, Any]:
        # The direct Humanize CLI and candidate-file mode do not necessarily
        # have an outer owner. The five-stage pipeline, however, holds the same
        # lease through Stages 1-5 and passes its exact active lease here so
        # Stage 1 does not deadlock by attempting a second flock.
        if inherited_run_lease is not None:
            _validate_inherited_humanize_run_lease(
                self.store,
                inherited_run_lease,
            )
            return self._run_with_active_lease()
        with _acquire_humanize_run_lease(self.store):
            return self._run_with_active_lease()

    def _run_with_active_lease(self) -> dict[str, Any]:
        # __init__ may have happened before a previous owner completed. Reload
        # the archive only after this run is known to own (or inherit) its lease.
        self.archive = EliteArchive(self.store.archive_path)
        return self._run_locked()

    def _run_locked(self) -> dict[str, Any]:
        serialized_config = self.config.serializable()
        existing = self.store.load_state()
        if existing is not None:
            durable_config = existing.get("config")
            if durable_config != serialized_config:
                compatible_extension = False
                previous_max_rounds: int | None = None
                requested_max_rounds = serialized_config.get("max_rounds")
                current_round = existing.get("current_round")
                if isinstance(durable_config, dict):
                    previous_max_rounds = durable_config.get("max_rounds")
                    durable_policy_version = durable_config.get(
                        "search_regime_policy_version", 1
                    )
                    durable_context = dict(durable_config)
                    requested_context = dict(serialized_config)
                    durable_context.pop("max_rounds", None)
                    requested_context.pop("max_rounds", None)
                    compatible_extension = (
                        isinstance(previous_max_rounds, int)
                        and not isinstance(previous_max_rounds, bool)
                        and isinstance(requested_max_rounds, int)
                        and not isinstance(requested_max_rounds, bool)
                        and isinstance(current_round, int)
                        and not isinstance(current_round, bool)
                        and 0 <= current_round <= previous_max_rounds
                        # V3 binds max_rounds into replay and terminal handoff
                        # evidence.  Rebinding that value under the same run_id
                        # would reinterpret already-sealed rounds.
                        and durable_policy_version
                        not in SEARCH_REGIME_BUDGET_BOUND_POLICY_VERSIONS
                        and requested_max_rounds > previous_max_rounds
                        and durable_context == requested_context
                    )
                if not compatible_extension:
                    raise ValueError(
                        "Refusing to resume a Humanize run with different "
                        "configuration"
                    )

                extension_history = existing.get(
                    "config_extension_events", []
                )
                if not isinstance(extension_history, list):
                    raise ValueError(
                        "Refusing to resume a Humanize run with malformed "
                        "configuration extension history"
                    )
                assert previous_max_rounds is not None
                extended_at = utc_now()
                extension_event = {
                    "schema_version": 1,
                    "event": "max_rounds_extended",
                    "sequence": len(extension_history) + 1,
                    "from_max_rounds": previous_max_rounds,
                    "to_max_rounds": requested_max_rounds,
                    "current_round": current_round,
                    "extended_at": extended_at,
                }
                extended = copy.deepcopy(existing)
                extended["config"] = copy.deepcopy(serialized_config)
                extended["config_extension_events"] = [
                    *copy.deepcopy(extension_history),
                    extension_event,
                ]
                # The authoritative config update and its extension event are
                # one atomic state-file transaction. The append-only event log
                # below is an operational mirror of this durable record.
                self.store.write_state(extended)
                self.store.event(
                    "max_rounds_extended",
                    sequence=extension_event["sequence"],
                    from_max_rounds=previous_max_rounds,
                    to_max_rounds=requested_max_rounds,
                    current_round=current_round,
                    extended_at=extended_at,
                )
        state = self.store.initialize(serialized_config)
        state["runtime_worker_budget"] = self.config.max_total_workers
        global_rows, rebuilt = self._rebuild_global_audit_state(
            state,
            recover_final_partial=True,
        )
        trusted_exact, trusted_wins = self._trusted_exact_audit_view(
            global_rows
        )
        self._record_trusted_audit_view(
            state, trusted_exact, trusted_wins
        )
        self.store.write_state(state)
        transaction_version = state.get("round_transaction_version")
        if transaction_version is None:
            self._migrate_legacy_completed_rounds(state)
            if state.get("pending_round") is None:
                state["round_transaction_version"] = (
                    ROUND_TRANSACTION_PROTOCOL_VERSION
                )
                transaction_version = ROUND_TRANSACTION_PROTOCOL_VERSION
                self.store.write_state(state)
        if (
            transaction_version is not None
            and transaction_version
            not in ROUND_TRANSACTION_SUPPORTED_PROTOCOL_VERSIONS
        ):
            raise RoundTransactionError(
                f"unsupported round transaction version: {transaction_version!r}"
            )
        handoff_status = _validated_search_handoff(
            self.config,
            state,
            rounds_root=self.store.root / "rounds",
        )
        if handoff_status is not None:
            self._write_run_meta(state)
            if handoff_status == "incomplete-unresolved":
                raise UnresolvedAuditError(
                    "Stage 1 previously committed a representation-change "
                    "handoff with unresolved MILP candidate(s)"
                )
            return state
        renderer_handoff_status = _validated_renderer_expansion_handoff(
            state,
            self.store.root / "rounds",
        )
        if renderer_handoff_status is not None:
            self._write_run_meta(state)
            if renderer_handoff_status == "incomplete-unresolved":
                raise UnresolvedAuditError(
                    "Stage 1 previously committed a non-executable renderer "
                    "expansion handoff with unresolved candidate(s)"
                )
            return state
        if trusted_wins and state.get("pending_round") is None:
            already_complete = state.get("status") == "search-complete"
            state["status"] = "search-complete"
            self.store.write_state(state)
            self._write_run_meta(state)
            if not already_complete:
                self.store.event(
                    "search_completed_from_trusted_history",
                    rounds=state["current_round"],
                    trusted_exact=len(trusted_exact),
                    trusted_wins=len(trusted_wins),
                    unresolved_handed_off=len(rebuilt.unresolved),
                )
            return state
        if (
            state["status"] in {"completed", "search-complete"}
            and state.get("pending_round") is None
            # A no-WIN completion is terminal only for the round budget that
            # produced it.  A strict max_rounds extension must enter the loop
            # below; otherwise the newly authorized rounds are silently
            # skipped forever after the old search-complete checkpoint.
            and int(state["current_round"]) >= self.config.max_rounds
            and (not rebuilt.unresolved or trusted_wins)
        ):
            self._write_run_meta(state)
            return state

        state.pop("failure", None)
        state["status"] = "running"
        self.store.write_state(state)
        self._write_run_meta(state)

        for number in range(int(state["current_round"]) + 1, self.config.max_rounds + 1):
            round_dir = self.store.round_dir(number)
            contract = self._write_contract(number, round_dir)
            self.store.event("round_started", round_number=number)

            try:
                rejected_path = round_dir / "rejected-candidates.jsonl"
                selected_path = round_dir / "selected.jsonl"
                candidate_path = round_dir / "candidates.jsonl"
                milp_path = round_dir / "milp.jsonl"
                review_path = round_dir / "review.json"
                pending = state.get("pending_round") == number
                phase = state.get("round_phase")
                legacy_pending = (
                    pending
                    and state.get("round_transaction_version") is None
                )
                if state.get("pending_round") not in (None, number):
                    raise RoundTransactionError(
                        "durable state refers to a different pending round"
                    )
                if legacy_pending:
                    self._validate_legacy_pending_round(
                        state, number, candidate_path, milp_path
                    )

                resume_review = pending and phase in {"review", "finalize"}
                if resume_review:
                    if not legacy_pending:
                        self._capture_round_candidates(state, number, round_dir)
                    if (
                        not candidate_path.is_file()
                        or not selected_path.is_file()
                        or not milp_path.is_file()
                    ):
                        raise RoundTransactionError(
                            "review phase is missing candidates, selection, or MILP evidence"
                        )
                    candidates = self._read_jsonl(candidate_path)
                    selected = self._read_jsonl(selected_path)
                    global_rows = self._read_canonical_evaluations(
                        recover_final_partial=False
                    )
                    audited = self._reconcile_round_evaluations(
                        selected,
                        round_number=number,
                        milp_path=milp_path,
                        global_rows=global_rows,
                    )
                    if len(audited) != len(selected):
                        raise RoundTransactionError(
                            "review phase lacks canonical global MILP evidence"
                        )
                    self.store.event(
                        "round_resumed", round_number=number,
                        phase=phase,
                    )
                else:
                    screened_history: list[dict[str, Any]] | None = None
                    verified_structural_digests: (
                        _VerifiedStructuralDigestIndex | None
                    ) = None
                    batch_policy_version = CANDIDATE_BATCH_POLICY_VERSION
                    if pending and phase not in {"screen", "audit"}:
                        raise RoundTransactionError(
                            f"cannot resume pending round phase {phase!r}"
                        )
                    if legacy_pending:
                        candidates = self._read_jsonl(candidate_path)
                    elif pending:
                        raw_candidates = self._capture_round_candidates(
                            state, number, round_dir
                        )
                        candidates = (
                            raw_candidates
                            if phase == "screen"
                            else self._read_jsonl(candidate_path)
                        )
                    else:
                        candidates = self._capture_round_candidates(
                            state, number, round_dir
                        )

                    if legacy_pending:
                        batch_policy_version = (
                            CANDIDATE_BATCH_POLICY_LEGACY_VERSION
                        )
                    else:
                        screen_transaction = self._load_transaction(
                            state,
                            number,
                            round_dir,
                        )
                        if (
                            screen_transaction is None
                            or screen_transaction.get("status") != "committed"
                        ):
                            raise RoundTransactionError(
                                "screen phase has no committed candidate batch"
                            )
                        batch_policy_version = (
                            self._candidate_batch_policy_version(
                                screen_transaction
                            )
                        )

                    if state.get("round_phase") == "screen":
                        (
                            candidates,
                            rejected,
                            screened_history,
                            verified_structural_digests,
                        ) = self._screen_candidates_with_pool_indexed(
                            candidates,
                            policy_version=batch_policy_version,
                        )
                        self._write_jsonl(candidate_path, candidates)
                        self._write_jsonl(rejected_path, rejected)
                    elif state.get("round_phase") == "audit":
                        if not candidate_path.is_file():
                            raise RoundTransactionError(
                                "audit phase is missing screened candidates"
                            )
                        candidates = self._read_jsonl(candidate_path)
                    else:
                        raise RoundTransactionError(
                            "round transaction did not reach screen/audit"
                        )

                    if selected_path.is_file():
                        selected = self._read_jsonl(selected_path)
                    elif state.get("round_phase") == "screen":
                        selected = self._select_audit_candidates(
                            candidates,
                            state,
                            screened_history=screened_history,
                            policy_version=batch_policy_version,
                            verified_structural_digests=(
                                verified_structural_digests
                            ),
                        )
                        self._write_jsonl(selected_path, selected)
                    else:
                        raise RoundTransactionError(
                            "audit phase is missing the durable selection"
                        )
                    if not milp_path.exists():
                        self._write_jsonl(milp_path, [])
                    state["pending_round"] = number
                    state["round_phase"] = "audit"
                    self.store.write_state(state)
                    self.store.event(
                        "round_resumed" if pending else "round_batch_committed",
                        round_number=number,
                        phase="audit",
                    )
                    audited = self._audit_selected(
                        selected,
                        state=state,
                        milp_path=milp_path,
                        round_number=number,
                    )
                    state["round_phase"] = "review"
                    self.store.write_state(state)

                current_candidate_diversity: dict[str, Any] | None = None
                transaction_manifest = self._transaction_paths(
                    round_dir
                )["manifest"]
                if transaction_manifest.is_file():
                    transaction, transaction_batch_rows = (
                        self._validate_completed_transaction(
                            number, round_dir
                        )
                    )
                    current_candidate_diversity = (
                        _candidate_diversity_summary(
                            transaction,
                            transaction_batch_rows,
                        )
                    )
                elif not legacy_pending:
                    raise RoundTransactionError(
                        "review phase has no committed evolution transaction"
                    )

                canonical_rows = self._read_canonical_evaluations(
                    recover_final_partial=False
                )
                trusted_exact, trusted_wins = (
                    self._trusted_exact_audit_view(canonical_rows)
                )
                memory = self.store.memory_path.read_text() if self.store.memory_path.exists() else ""
                prompt = build_review_prompt(
                    round_number=number,
                    contract=contract,
                    candidates=candidates,
                    audited=audited,
                    archive_top=self.archive.ranked(),
                    trusted_exact_history=trusted_exact,
                    trusted_exact_wins=trusted_wins,
                    memory=memory,
                    round_history=state.get("rounds", []),
                    current_candidate_diversity=(
                        current_candidate_diversity
                    ),
                )
                (round_dir / "review-request.md").write_text(prompt)
                if state.get("round_phase") == "finalize" and review_path.is_file():
                    review = validate_review(json.loads(review_path.read_text()))
                else:
                    try:
                        review = validate_review(
                            self.reviewer.review(prompt, round_dir)
                        )
                    except Exception as exc:
                        if not trusted_wins:
                            raise
                        # Reviewer feedback guides later search rounds; it is
                        # not part of the machine proof. Once the canonical
                        # audit log already contains a replayed exact WIN, a
                        # transient reviewer/API failure must not strand that
                        # proof in a pending round forever.
                        failure = {
                            "schema_version": 1,
                            "gate": "qcode-humanize-review-advisory-failure",
                            "round": number,
                            "classification": type(exc).__name__,
                            "message": str(exc),
                            "trusted_win_count": len(trusted_wins),
                            "recorded_at": utc_now(),
                        }
                        atomic_write_json(
                            round_dir / "review-advisory-failure.json",
                            failure,
                        )
                        self.store.event(
                            "trusted_win_review_failed_advisory",
                            round_number=number,
                            classification=type(exc).__name__,
                            trusted_wins=len(trusted_wins),
                        )
                        review = validate_review({
                            "verdict": "promote",
                            "summary": (
                                "The canonical audit log already contains a "
                                "machine-replayed exact WIN; independent review "
                                "failed and is recorded as advisory."
                            ),
                            "risks": [{
                                "severity": "P2",
                                "finding": (
                                    "Independent round review was unavailable "
                                    "after the exact WIN was established."
                                ),
                                "evidence": (
                                    f"{type(exc).__name__}: {exc}"
                                ),
                            }],
                            "recommended_focus": [
                                "Proceed to deterministic certificate and "
                                "strict-gate replay.",
                            ],
                            "lessons": [],
                        })
                    # Always bind the durable artifact to the validated object
                    # returned above. A failed reviewer may have left a partial
                    # or malformed review.json at the same path.
                    atomic_write_json(review_path, review)
                    state["round_phase"] = "finalize"
                    self.store.write_state(state)

                if review["verdict"] != "reject_round":
                    self.store.add_lessons(review["lessons"], number)

                final_state = copy.deepcopy(state)
                round_best = max(
                    (
                        candidate_proven_fom(r)
                        for r in [*candidates, *audited]
                    ),
                    default=0.0,
                )
                round_bp_upper = max(
                    (candidate_fom(r) for r in candidates),
                    default=0.0,
                )
                final_state["best_bp_fom_upper_bound"] = max(
                    float(
                        final_state.get(
                            "best_bp_fom_upper_bound",
                            0.0,
                        )
                    ),
                    round_bp_upper,
                )
                previous_best = float(final_state.get("best_fom", 0.0))
                if round_best > previous_best + self.config.min_improvement:
                    final_state["best_fom"] = round_best
                    final_state["no_improvement_rounds"] = 0
                else:
                    final_state["no_improvement_rounds"] = int(
                        final_state.get("no_improvement_rounds", 0)
                    ) + 1

                self._record_trusted_audit_view(
                    final_state, trusted_exact, trusted_wins
                )
                self._finish_round(
                    final_state,
                    number,
                    candidates,
                    audited,
                    review,
                    round_dir,
                )
                unresolved_count = len(
                    final_state.get("unresolved_candidates", {})
                )
                # Search termination is a machine decision.  Reviewer advice
                # and BP-based patience can never stop a no-WIN run.  A
                # formally replayed exact WIN, however, is enough to hand off
                # immediately even if unrelated candidates remain unresolved.
                representation_handoff = bool(
                    not trusted_wins
                    and self.config.stop_on_representation_change
                    and self.config.search_regime_policy_version in {2, 3, 4}
                    and isinstance(final_state.get("search_regime"), dict)
                    and final_state["search_regime"].get("status")
                    == SEARCH_HANDOFF_REASON_REPRESENTATION_CHANGE
                )
                renderer_resolution = _validated_bound_renderer_resolution(
                    final_state["rounds"][-1], round_dir.parent
                )
                renderer_advisory = bool(
                    renderer_resolution is not None
                    and renderer_resolution.get("status")
                    == "representation_expansion_handoff"
                )
                should_stop = bool(
                    trusted_wins
                    or representation_handoff
                )
                if representation_handoff:
                    # These fields, the completed round summary, current_round,
                    # and removal of pending state are persisted below as one
                    # atomic final_state transaction.  Never install a marker
                    # in a follow-up write that could be lost independently.
                    final_state["search_handoff_reason"] = (
                        SEARCH_HANDOFF_REASON_REPRESENTATION_CHANGE
                    )
                    final_state["search_handoff_at_round"] = number
                    final_state["status"] = (
                        "incomplete-unresolved"
                        if unresolved_count
                        else "search-complete"
                    )
                self.store.event(
                    "round_completed",
                    round_number=number,
                    reviewer_verdict=review["verdict"],
                    exact_total=len(trusted_exact),
                    trusted_win_total=len(trusted_wins),
                    unresolved=unresolved_count,
                    stop=should_stop,
                )
                completed_transaction_version = state.get(
                    "round_transaction_version"
                )
                if (
                    completed_transaction_version
                    not in ROUND_TRANSACTION_SUPPORTED_PROTOCOL_VERSIONS
                ):
                    completed_transaction_version = (
                        ROUND_TRANSACTION_PROTOCOL_VERSION
                    )
                final_state["round_transaction_version"] = (
                    completed_transaction_version
                )
                final_state.pop("pending_round", None)
                final_state.pop("round_phase", None)
                final_state.pop("legacy_round_transaction", None)
                self.store.write_state(final_state)
                state.clear()
                state.update(final_state)
                self._write_run_meta(final_state)
                if representation_handoff:
                    self.store.event(
                        "search_representation_change_handoff",
                        round_number=number,
                        status=final_state["status"],
                        unresolved=unresolved_count,
                    )
                if renderer_advisory:
                    assert renderer_resolution is not None
                    handoff = renderer_resolution.get(
                        "representation_expansion_handoff"
                    )
                    assert isinstance(handoff, Mapping)
                    self.store.event(
                        "search_renderer_expansion_deferred",
                        round_number=number,
                        status=final_state["status"],
                        unresolved=unresolved_count,
                        reason=handoff.get("reason"),
                        execution_permitted=False,
                        resolution_sha256=renderer_resolution[
                            "resolution_sha256"
                        ],
                    )
                if should_stop:
                    break
            except (Exception, KeyboardInterrupt) as exc:
                # ``write_state(final_state)`` above is the scientific commit.
                # Run metadata and events that follow it are operational
                # mirrors.  An exception (including SIGINT) in that
                # post-commit window must preserve the durable round and its
                # atomic representation-change handoff instead of rewriting it
                # as failed.  A subsequent resume can regenerate the mirrors.
                try:
                    durable_state = self.store.load_state()
                except BaseException:
                    # If the durable state cannot be read, fail without making
                    # a second, potentially destructive write based on stale
                    # in-memory state.
                    raise exc
                if _durable_round_commit_matches(
                    durable_state,
                    round_number=number,
                ):
                    assert durable_state is not None
                    state.clear()
                    state.update(durable_state)
                    raise
                state["status"] = "failed"
                state["failure"] = f"{type(exc).__name__}: {exc}"
                self.store.write_state(state)
                self._write_run_meta(state)
                self.store.event(
                    "round_failed", round_number=number, error=state["failure"]
                )
                raise

        handoff_status = _validated_search_handoff(
            self.config,
            state,
            rounds_root=self.store.root / "rounds",
        )
        if handoff_status is not None:
            self._write_run_meta(state)
            if handoff_status == "incomplete-unresolved":
                raise UnresolvedAuditError(
                    "Stage 1 committed a representation-change handoff with "
                    "unresolved MILP candidate(s)"
                )
            return state

        renderer_handoff_status = _validated_renderer_expansion_handoff(
            state,
            self.store.root / "rounds",
        )
        if renderer_handoff_status is not None:
            self._write_run_meta(state)
            if renderer_handoff_status == "incomplete-unresolved":
                raise UnresolvedAuditError(
                    "Stage 1 committed a non-executable renderer expansion "
                    "handoff with unresolved candidate(s)"
                )
            return state

        canonical_rows = self._read_canonical_evaluations(
            recover_final_partial=False
        )
        trusted_exact, trusted_wins = self._trusted_exact_audit_view(
            canonical_rows
        )
        self._record_trusted_audit_view(
            state, trusted_exact, trusted_wins
        )
        unresolved_count = len(state.get("unresolved_candidates", {}))
        if unresolved_count and not trusted_wins:
            state["status"] = "incomplete-unresolved"
            self.store.write_state(state)
            self._write_run_meta(state)
            self.store.event(
                "search_incomplete_unresolved",
                rounds=state["current_round"],
                unresolved=unresolved_count,
            )
            raise UnresolvedAuditError(
                "Stage 1 exhausted max_rounds with "
                f"{unresolved_count} unresolved MILP candidate(s)"
            )

        state["status"] = "search-complete"
        self.store.write_state(state)
        self._write_run_meta(state)
        self.store.event(
            "search_completed",
            rounds=state["current_round"],
            trusted_exact=len(trusted_exact),
            trusted_wins=len(trusted_wins),
            unresolved_handed_off=unresolved_count,
        )
        return state
