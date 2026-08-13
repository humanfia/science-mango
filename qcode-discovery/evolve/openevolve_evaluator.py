"""OpenEvolve evaluator adapter for BB code discovery.

This module bridges OpenEvolve's ``evaluate(program_path)`` interface with
the project's multi-stage evaluation cascade.  OpenEvolve calls
``evaluate(program_path)`` (or ``evaluate_stage1`` / ``evaluate_stage2``
when cascade evaluation is enabled) with a temporary ``.py`` file containing
the evolved ``generate_candidates`` function.  This adapter dynamically
loads that function, runs it across target lattices, and returns a score
dict compatible with OpenEvolve's MAP-Elites population database.

Two-stage cascade
-----------------
**Stage 1** -- Quick k-only screening (~2 s)
    Evaluates the evolved program on 2 small lattices (``(6,6)`` and
    ``(12,6)``). Broad programs with valid codes on both probes receive the
    normal fitness score. A low-priority deterministic exploration lane also
    advances a small sample of large-lattice specialists, so these probes are
    not an absolute exclusion rule.
    Score: ``0.1 base + best_encoding_rate + log1p(num_high_k) / 10``.

**Stage 2** -- Bounded preflight and proof-safe distance fitness
    Calls the generator on every contracted target and Pareto lattice before
    any blocking distance work.  Replayable symplectic and low-weight-oracle
    witnesses reject candidates before a bounded deep pass uses BP-OSD/OSD-CS
    on the survivors.  A complete two-sector low-weight ``UNSAT`` result may
    contribute a bounded, source-bound distance-lower-bound signal. BP-family
    distances remain upper bounds: their magnitude never contributes ``d**2``
    fitness. Only exact non-negative distance rows may enter the discovered-
    code/Pareto persistence path.
    Diagnostic upper-bound metrics are written to a shared JSONL file for W&B
    background sync (since ``wandb.run`` is ``None`` in subprocess workers).

MAP-Elites feature dimensions
------------------------------
* ``pattern_type`` -- dominant structural class across the canonical
  evaluated pool.
* ``support_split_type`` -- dominant admissible ``(|A|, |B|)`` split, using
  the fixed challenge-contract order.
* ``search_structural_entropy`` -- normalized Shannon entropy of the
  structural-pattern distribution across that same pool.
* ``algebraic_relation_type`` -- dominant algebraic support relation, using
  the fixed ``RELATION_TYPES`` order.
* ``orbit_span_bin`` -- dominant affine-rank bin of the combined support.
* ``difference_spectrum_bin`` -- dominant primitive-difference spectrum bin.

These pool-level features encourage behavioral diversity without allowing a
single fixed safety-net code to determine the archive cell for an otherwise
different generator. ``term_count`` remains available as a backward-compatible
diagnostic metric, but is no longer an active ansatz-campaign archive axis.

Constants
---------
STAGE1_LATTICES : list[tuple[int, int]]
    ``[(6, 6), (12, 6)]`` -- quick screening lattices.
STAGE2_LATTICES : list[tuple[int, int]]
    Pareto-first union of the n=72/90/108 reference lattices and every
    formal target lattice declared by the search contract.
"""

from __future__ import annotations

import ctypes
import fcntl
import hashlib
import importlib.util
import json
import logging
import math
import os
import signal
import stat
import subprocess
import sys
import tempfile
import threading
import time
from functools import lru_cache
from pathlib import Path


def _install_private_worker_parent_guard(
    expected_parent_pid: int,
    lifecycle_fd: int,
) -> None:
    """Kill a private evaluator process group when its owner disappears."""

    if expected_parent_pid < 2 or lifecycle_fd < 0:
        raise RuntimeError("invalid Stage 2 parent guard")
    guardian_pid = os.fork()
    if guardian_pid == 0:
        signal.signal(signal.SIGTERM, signal.SIG_IGN)
        try:
            while os.read(lifecycle_fd, 4096):
                pass
        except OSError:
            pass
        finally:
            try:
                os.killpg(os.getpgrp(), signal.SIGKILL)
            finally:
                os._exit(128 + signal.SIGKILL)
    os.close(lifecycle_fd)

    # Linux parent-death signalling closes the small race between exec and the
    # guardian reaching its blocking read.  The guardian remains responsible
    # for killing every descendant in this private session.
    libc = ctypes.CDLL(None, use_errno=True)
    if libc.prctl(1, signal.SIGKILL, 0, 0, 0) != 0:
        error_number = ctypes.get_errno()
        os.killpg(os.getpgrp(), signal.SIGKILL)
        raise OSError(error_number, "prctl(PR_SET_PDEATHSIG) failed")
    if os.getppid() != expected_parent_pid:
        os.killpg(os.getpgrp(), signal.SIGKILL)


# Arm the lifecycle contract before importing scipy/qldpc-backed evaluation
# modules.  This path runs only in a private evaluator subprocess.
if (
    __name__ == "__main__"
    and len(sys.argv) == 6
    and sys.argv[1] in {
        "--stage1-worker",
        "--stage2-worker",
        "--preflight-worker",
    }
):
    _install_private_worker_parent_guard(
        int(sys.argv[4]),
        int(sys.argv[5]),
    )


# Ensure the project root is on sys.path so we can import evaluation.*
_PROJECT_ROOT = str(Path(__file__).resolve().parent.parent)
if _PROJECT_ROOT not in sys.path:
    sys.path.insert(0, _PROJECT_ROOT)

from evolve import dependency_contract as _dependency_contract
from evaluation.algebraic_mechanisms import (
    RELATION_TYPES,
    classify_algebraic_mechanism,
)
from evaluation.bb_code import build_bb_code, validate_terms
from evaluation.distance_milp import get_code_matrices
from evaluation.evaluator import (
    compute_challenge_rejection_cutoff,
    evaluate_batch,
    evaluate_batch_milp,
    evaluate_batch_milp_parallel,
    evaluate_milp_parallel,
)
from evaluation.final_gate import minimum_winning_distance
from evaluation.geometry import geometry_identity, normalize_geometry
from evaluation.low_weight_oracle import (
    LOW_WEIGHT_MITM_ENGINE,
    LOW_WEIGHT_MITM_MAX_THRESHOLD,
    verify_css_low_weight_oracle,
)
from evaluation.results import save_code, update_pareto_front
from evaluation.search_contract import (
    ACTIVE_GEOMETRY_CONTRACT,
    ACTIVE_STAGE1_FITNESS_LATTICES as CONTRACT_STAGE1_FITNESS_LATTICES,
    ACTIVE_STAGE2_DEEP_LATTICES as CONTRACT_STAGE2_DEEP_LATTICES,
    ACTIVE_STAGE2_FITNESS_LATTICES as CONTRACT_STAGE2_FITNESS_LATTICES,
    EVOLUTION_LATTICES,
    FINAL_GATE_PARETO_LATTICES as CONTRACT_PARETO_LATTICES,
    PUBLISHED_VOLUME_ANSATZ_V3_GEOMETRY_CONTRACT,
    PUBLISHED_VOLUME_ANSATZ_V3_REPRESENTATION_ID,
    TWISTED_MIN_CANDIDATES_PER_TWIST,
    allowed_twists,
    is_twisted_geometry_contract,
)
from evaluation.structural_dedup import (
    check_css_static_eligibility,
    deduplicate_css_results,
)
from evaluation.structural_features import (
    PATTERN_CLASSIFIER_VERSION,
    classify_pattern as _classify_pattern,
    count_terms as _count_terms,
)

logger = logging.getLogger(__name__)


class CandidateLogWriteError(RuntimeError):
    """A discovered candidate could not be durably persisted."""


class Stage1CandidateCommitMismatch(CandidateLogWriteError):
    """A journal prefix no longer exists in its bound candidate log."""


class Stage1PreflightLockTimeout(CandidateLogWriteError):
    """Another owner made no durable progress while holding the source lock."""


class Stage2DeepLockTimeout(CandidateLogWriteError):
    """Another owner made no durable progress while holding the deep lock."""


WINNER_PREFLIGHT_CONTRACT_VERSION = 2
WINNER_PREFLIGHT_CONTRACT_ID_ENV = "QCODE_WINNER_PREFLIGHT_CONTRACT_ID"
WINNER_PREFLIGHT_REUSE_ENV = "QCODE_WINNER_PREFLIGHT_REUSE"
CANDIDATE_LOG_PATH_ENV = "QCODE_CANDIDATE_LOG_PATH"
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
WINNER_PREFLIGHT_MARKER_FIELDS = (
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
_STAGE1_PREFLIGHT_COMPLETIONS: dict[
    tuple[str, str, int],
    dict[str, float],
] = {}
_STAGE1_PREFLIGHT_COMPLETIONS_LOCK = threading.Lock()
_MILP_CANDIDATE_LOG_PATH_BINDING: Path | None = None
_MILP_CANDIDATE_LOG_PATH_BINDING_LOCK = threading.Lock()
WINNER_CAPABLE_EXPLORATION_LANE = "winner_capable_quick_exploration"
QUICK_EXPLORATION_PERSISTENCE_REASON = "quick_distance_budget"
FULL_POOL_PREFLIGHT_PERSISTENCE_REASON = "full_pool_preflight"
DISTANCE_PENDING_PERSISTENCE_REASON = "selected_distance_pending"
UNRESOLVED_TOP_PERSISTENCE_REASON = "selected_distance_unresolved"
DISTANCE_ERROR_PERSISTENCE_REASON = "selected_distance_error"
CHALLENGE_SUPPORT_FILTER_VERSION = 1
CHALLENGE_SUPPORT_MIN_PER_SIDE = 2
CHALLENGE_SUPPORT_MAX_PER_SIDE = 6
CHALLENGE_SUPPORT_MAX_TOTAL = 6
CHALLENGE_SUPPORT_SPLITS = (
    (2, 2),
    (2, 3),
    (3, 2),
    (2, 4),
    (4, 2),
    (3, 3),
)
SUPPORT_FILTER_VERSION_METRIC = "support_filter_version"
SUPPORT_WEIGHT_ELIGIBLE_METRIC = "support_weight_eligible"
SUPPORT_WEIGHT_REJECTED_METRIC = "support_weight_rejected"
SUPPORT_WEIGHT_EVALUATED_METRIC = "support_weight_evaluated"
SUPPORT_WEIGHT_PARTITION_COMPLETE_METRIC = (
    "support_weight_partition_complete"
)
SUPPORT_WEIGHT_EVALUATION_COVERAGE_METRIC = (
    "support_weight_evaluation_coverage"
)
SUPPORT_WEIGHT_ELIGIBLE_FRACTION_METRIC = (
    "support_weight_eligible_fraction"
)
SUPPORT_WEIGHT_REJECTION_FRACTION_METRIC = (
    "support_weight_rejection_fraction"
)
SUPPORT_SPLITS_COVERED_METRIC = "support_splits_covered"
SUPPORT_SPLITS_TOTAL_METRIC = "support_splits_total"
SUPPORT_SPLIT_COVERAGE_METRIC = "support_split_coverage"
SUPPORT_SPLIT_LATTICE_COVERAGE_METRIC = "support_split_lattice_coverage"
GEOMETRY_TWISTS_REQUIRED_METRIC = "geometry_twists_required"
GEOMETRY_TWISTS_OBSERVED_METRIC = "geometry_twists_observed"
GEOMETRY_TWIST_COVERAGE_METRIC = "twist_coverage"
GEOMETRY_TWIST_COVERAGE_COMPLETE_METRIC = "geometry_twist_coverage_complete"
# Version 2 moves 4+-term mixed structures from cell 3 to the intended
# multi-term cell 4. Checkpoints containing version-1 descriptors must be
# freshly evaluated rather than silently compared across classifier versions.
PATTERN_CLASSIFIER_VERSION_METRIC = "pattern_classifier_version"
# Version 4 adds algebraic-relation, orbit-span, and difference-spectrum
# coordinates to the order-independent complete-pool descriptor. Archive
# coordinates from older checkpoints are therefore not comparable.
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
MAP_DESCRIPTOR_GEOMETRY_TWIST_CLASS_METRIC = "geometry_twist_class"
MAP_DESCRIPTOR_PATTERN_CARDINALITY = 6
STAGE1_SPECIALIST_EXPLORATION_DENOMINATOR = 16
MAX_CANDIDATES_PER_LATTICE = 5000
MAX_WINNER_CAPABLE_EXPLORATION_PER_LATTICE = 8
MAX_FINAL_GATE_PARETO_DISTANCE_PER_LATTICE = 4
MAX_DISTANCE_BACKEND_ERROR_MESSAGE_CHARS = 2048
CANDIDATE_LOG_CHUNK_MAX_RECORDS = 256
CANDIDATE_LOG_CHUNK_MAX_BYTES = 1 << 20
CANDIDATE_LOG_WAL_SCHEMA_VERSION = 1
CANDIDATE_LOG_WAL_HEADER_MAX_BYTES = 16 << 10
CANDIDATE_LOG_WAL_SUFFIX = ".candidate-wal"
CANDIDATE_LOG_WAL_TEMP_SUFFIX = ".tmp"
STAGE1_PREFLIGHT_JOURNAL_SCHEMA_VERSION = 1
STAGE1_PREFLIGHT_JOURNAL_DIRECTORY = ".stage1-preflight"
STAGE1_PREFLIGHT_MAX_EPOCH_ATTEMPTS = 2
STAGE1_PREFLIGHT_WORKER_ATTEMPTS = 2
STAGE1_PREFLIGHT_LOCK_WAIT_INTERVALS = 2
STAGE1_PREFLIGHT_ROW_PROGRAM_SHA256 = "winner_preflight_program_sha256"
STAGE1_PREFLIGHT_ROW_CONTRACT_ID = "winner_preflight_row_contract_id"
STAGE1_PREFLIGHT_ROW_EPOCH_ID = "winner_preflight_epoch_id"
STAGE1_PREFLIGHT_ROW_LATTICE = "winner_preflight_row_lattice"
STAGE1_PREFLIGHT_ROW_LATTICE_COMMIT = "winner_preflight_lattice_commit"
STAGE1_PREFLIGHT_ROW_LATTICE_SUMMARY = "winner_preflight_lattice_summary"
STAGE1_CANDIDATE_LOG_RECORDS_FIELD = "candidate_log_records"
STAGE2_DEEP_CONTRACT_VERSION = 3
STAGE2_DEEP_JOURNAL_SCHEMA_VERSION = 1
STAGE2_DEEP_RESULT_SCHEMA_VERSION = 1
STAGE2_DEEP_JOURNAL_DIRECTORY = ".stage2-deep"
STAGE2_DEEP_WORKER_ATTEMPTS = 2
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
# Full persistence is deliberately unbounded within the challenge-supported
# sparse universe. A fixed 5000-definition sample is useful for distance
# fitness, but is not a sound handoff to exact auditing: a supported winner
# outside that sample would otherwise be permanently invisible.
STAGE2_PREFLIGHT_CANDIDATE_LIMIT = None
STAGE2_DEEP_CANDIDATE_LIMIT = MAX_CANDIDATES_PER_LATTICE
STAGE2_DEEP_DISTANCE_PER_LATTICE = 3
STAGE2_DEEP_SCREEN_MULTIPLIER = 8
STAGE2_REFINE_TRIALS = 250
STAGE2_CHALLENGE_TARGET_FOM = 12.0
STAGE2_LOW_WEIGHT_ORACLE_MAX_WEIGHT = 4
STAGE2_LOW_WEIGHT_ORACLE_HARD_TIMEOUT_S = 30.0
STAGE2_SURVIVOR_CREDIT_PER_LATTICE = 1.0
STAGE2_RATE_TIE_BREAK_MAX_PER_LATTICE = 0.05
STAGE2_STRUCTURE_TIE_BREAK_MAX_PER_LATTICE = 0.05
STAGE2_HARD_TIMEOUT_MAX_S = 1050.0
STAGE2_OUTER_TIMEOUT_DEFAULT_S = 900.0
STAGE2_OUTER_TIMEOUT_MARGIN_S = 60.0
STAGE2_OUTER_TIMEOUT_ENV = "QCODE_EVALUATOR_OUTER_TIMEOUT_S"
WINNER_PREFLIGHT_HARD_TIMEOUT_MAX_S = STAGE2_HARD_TIMEOUT_MAX_S
WINNER_PREFLIGHT_OUTER_TIMEOUT_DEFAULT_S = STAGE2_OUTER_TIMEOUT_DEFAULT_S
WINNER_PREFLIGHT_OUTER_TIMEOUT_MARGIN_S = STAGE2_OUTER_TIMEOUT_MARGIN_S
STAGE2_NUMERIC_THREAD_ENV = (
    "OMP_NUM_THREADS",
    "OPENBLAS_NUM_THREADS",
    "MKL_NUM_THREADS",
    "NUMEXPR_NUM_THREADS",
    "VECLIB_MAXIMUM_THREADS",
    "BLIS_NUM_THREADS",
)


def _definition_key(result: dict) -> tuple:
    ell = int(result.get("ell", 0) or 0)
    m = int(result.get("m", 0) or 0)
    legacy = (
        ell,
        m,
        tuple(sorted(tuple(map(int, term)) for term in result.get("A_terms", []))),
        tuple(sorted(tuple(map(int, term)) for term in result.get("B_terms", []))),
    )
    canonical = normalize_geometry(ell, m, result.get("geometry"))
    if canonical is None:
        return legacy
    return (*legacy, _geometry_key(ell, m, canonical))


def _geometry_key(ell: int, m: int, geometry) -> tuple:
    """Return a stable tuple identity; explicit q=0 equals legacy geometry."""

    identity = geometry_identity(ell, m, geometry)
    return tuple(sorted(identity.items()))


def _candidate_components(candidate) -> tuple[object, object, object]:
    """Extract A/B/geometry from a legacy pair or mapping record."""

    if isinstance(candidate, dict):
        unknown = set(candidate) - {"A_terms", "B_terms", "geometry"}
        if unknown:
            raise TypeError(
                f"candidate mapping has unknown fields: {sorted(unknown)}"
            )
        if "A_terms" not in candidate or "B_terms" not in candidate:
            raise TypeError("candidate mapping requires A_terms and B_terms")
        return (
            candidate["A_terms"],
            candidate["B_terms"],
            candidate.get("geometry"),
        )
    if not isinstance(candidate, (list, tuple)) or len(candidate) != 2:
        raise TypeError(
            "candidate must be an A/B pair or a geometry-aware mapping"
        )
    return candidate[0], candidate[1], None


def _result_as_candidate(result: dict):
    """Reconstruct the evaluator candidate without dropping its geometry."""

    candidate = {
        "A_terms": result.get("A_terms", []),
        "B_terms": result.get("B_terms", []),
    }
    if result.get("geometry") is not None:
        candidate["geometry"] = result["geometry"]
        return candidate
    return (candidate["A_terms"], candidate["B_terms"])


def _candidate_twist(candidate, *, ell: int, m: int) -> int:
    """Return canonical q, treating every legacy/explicit q=0 form alike."""

    _a_terms, _b_terms, geometry = _candidate_components(candidate)
    canonical = normalize_geometry(ell, m, geometry)
    return 0 if canonical is None else int(canonical["twist"])


def _geometry_twist_class(ell: int, m: int, geometry) -> int:
    """Map q to rectangular, primitive-twist, or composite-twist MAP bins."""

    canonical = normalize_geometry(ell, m, geometry)
    if canonical is None:
        return 0
    twist = int(canonical["twist"])
    return 1 if math.gcd(twist, m) == 1 else 2


def _candidate_definition_key(
    candidate,
    *,
    ell: int,
    m: int,
) -> tuple:
    a_terms, b_terms, geometry = _candidate_components(candidate)
    legacy = (
        ell,
        m,
        tuple(sorted(map(tuple, a_terms))),
        tuple(sorted(map(tuple, b_terms))),
    )
    canonical = normalize_geometry(ell, m, geometry)
    if canonical is None:
        return legacy
    return (*legacy, _geometry_key(ell, m, canonical))


def _require_complete_quick_result_set(
    results: list[dict],
    candidates: list,
    *,
    ell: int,
    m: int,
) -> None:
    """Fail closed unless a quick adapter covers the frozen canonical pool."""

    expected_definitions = {
        _candidate_definition_key(candidate, ell=ell, m=m)
        for candidate in candidates
    }
    observed_definitions = {_definition_key(result) for result in results}
    if (
        len(results) != len(observed_definitions)
        or observed_definitions != expected_definitions
    ):
        raise CandidateLogWriteError(
            f"({ell},{m}): full preflight evaluator returned "
            f"{len(observed_definitions)} of "
            f"{len(expected_definitions)} canonical definitions"
        )


@lru_cache(maxsize=None)
def _winning_distance_window(n: int, k: int) -> tuple[int, int] | None:
    """Return the required win distance and the quantum-Singleton ceiling.

    A fixed ``k >= 8`` gate is not a mathematical consequence of the final
    acceptance rule.  For example, ``[[72, 4, 15]]`` has FOM 12.5 and also
    obeys the quantum Singleton bound.  The window below is therefore the
    cheap, fail-closed parameter test used before distance work: a candidate
    remains reachable iff at least one final-gate winning distance is no
    larger than ``floor((n-k)/2)+1``.
    """
    if (
        isinstance(n, bool)
        or isinstance(k, bool)
        or not isinstance(n, int)
        or not isinstance(k, int)
        or n < 1
        or k < 1
        or k > n
    ):
        return None
    singleton_upper = (n - k) // 2 + 1
    try:
        required = minimum_winning_distance(n, k)
    except ValueError:
        return None
    if required > singleton_upper:
        return None
    return required, singleton_upper


def _annotate_winner_capability(result: dict) -> bool:
    """Attach the machine-derived parameter window and return reachability."""
    try:
        n = int(result.get("n", 0) or 0)
        k = int(result.get("k", 0) or 0)
    except (TypeError, ValueError):
        return False
    window = _winning_distance_window(n, k)
    if window is None:
        result["winner_capable_parameters"] = False
        return False
    required, singleton_upper = window
    result.update({
        "winner_capable_parameters": True,
        "minimum_winning_distance": required,
        "singleton_distance_upper_bound": singleton_upper,
    })
    return True


def _has_positive_distance(result: dict) -> bool:
    value = result.get("d")
    if isinstance(value, bool):
        return False
    try:
        return int(value) > 0
    except (TypeError, ValueError):
        return False


def _candidate_definition_payload(
    candidate,
    *,
    ell: int,
    m: int,
) -> bytes:
    """Return the canonical defining payload for one generated candidate."""

    def typed_malformed(value):
        if isinstance(value, (list, tuple)):
            return {
                "type": type(value).__name__,
                "items": [typed_malformed(item) for item in value],
            }
        return {
            "type": f"{type(value).__module__}.{type(value).__qualname__}",
            "repr": repr(value),
        }

    try:
        normalized = _normalize_candidate_definition(
            candidate,
            ell=ell,
            m=m,
        )
        a_terms, b_terms, geometry = _candidate_components(normalized)
        defining = {
            "ell": int(ell),
            "m": int(m),
            "A_terms": [list(term) for term in sorted(a_terms)],
            "B_terms": [list(term) for term in sorted(b_terms)],
        }
        canonical_geometry = normalize_geometry(ell, m, geometry)
        if canonical_geometry is not None:
            defining["geometry"] = geometry_identity(
                ell, m, canonical_geometry
            )
        payload = json.dumps(
            defining,
            sort_keys=True,
            separators=(",", ":"),
            allow_nan=False,
        ).encode()
    except (TypeError, ValueError):
        payload = json.dumps(
            {
                "ell": int(ell),
                "m": int(m),
                "malformed_candidate": typed_malformed(candidate),
            },
            sort_keys=True,
            separators=(",", ":"),
        ).encode("utf-8", errors="replace")
    return payload


def _normalize_candidate_definition(
    candidate,
    *,
    ell: int | None = None,
    m: int | None = None,
):
    """Return one strict legacy pair or canonical geometry-aware mapping."""

    a_value, b_value, raw_geometry = _candidate_components(candidate)

    def strict_terms(value, label: str) -> list[tuple[int, int]]:
        if not isinstance(value, (list, tuple)):
            raise TypeError(f"{label} must be a list or tuple")
        normalized: list[tuple[int, int]] = []
        for index, term in enumerate(value):
            if not isinstance(term, (list, tuple)) or len(term) != 2:
                raise TypeError(f"{label}[{index}] must be an exponent pair")
            if any(type(coordinate) is not int for coordinate in term):
                raise TypeError(
                    f"{label}[{index}] coordinates must be strict integers"
                )
            normalized.append((term[0], term[1]))
        return normalized

    a_terms = strict_terms(a_value, "A_terms")
    b_terms = strict_terms(b_value, "B_terms")
    if isinstance(candidate, dict):
        if ell is None or m is None:
            raise TypeError("geometry-aware candidate normalization needs ell/m")
        canonical_geometry = normalize_geometry(ell, m, raw_geometry)
        normalized = {
            "A_terms": a_terms,
            "B_terms": b_terms,
        }
        # Preserve explicit q=0 for the immutable coverage audit while its
        # mathematical/cache identity remains the legacy rectangular one.
        if raw_geometry is not None:
            normalized["geometry"] = (
                canonical_geometry
                if canonical_geometry is not None
                else {
                    "schema_version": 1,
                    "family": "twisted_torus",
                    "twist": 0,
                }
            )
        return normalized
    return a_terms, b_terms


def _normalize_generated_candidates(
    candidates: list,
    *,
    ell: int,
    m: int,
) -> tuple[list[tuple[list[tuple[int, int]], list[tuple[int, int]]]], list[str]]:
    """Isolate malformed generator entries instead of losing a whole lattice."""

    normalized = []
    errors = []
    for index, candidate in enumerate(candidates):
        try:
            normalized.append(_normalize_candidate_definition(
                candidate,
                ell=ell,
                m=m,
            ))
        except (TypeError, ValueError) as exc:
            errors.append(
                f"({ell},{m}) candidate[{index}] malformed: "
                f"{type(exc).__name__}: {exc}"
            )
    return normalized, errors


def _challenge_support_split(candidate) -> tuple[int, int] | None:
    """Return the supported A/B term split, or ``None`` when out of scope.

    The final challenge search is deliberately restricted to sparse BB
    supports: each polynomial has between two and six monomials and their
    combined support weight is at most six.  This check is representation-only
    and therefore safe to run before constructing qLDPC objects.
    """

    a_terms, b_terms, _geometry = _candidate_components(candidate)
    split = (len(a_terms), len(b_terms))
    if (
        CHALLENGE_SUPPORT_MIN_PER_SIDE
        <= split[0]
        <= CHALLENGE_SUPPORT_MAX_PER_SIDE
        and CHALLENGE_SUPPORT_MIN_PER_SIDE
        <= split[1]
        <= CHALLENGE_SUPPORT_MAX_PER_SIDE
        and sum(split) <= CHALLENGE_SUPPORT_MAX_TOTAL
    ):
        return split
    return None


def _partition_challenge_support(
    candidates: list,
) -> tuple[list, list, dict[tuple[int, int], int], dict[tuple[int, int], int]]:
    """Partition a normalized pool before any expensive batch evaluation."""

    eligible = []
    rejected = []
    eligible_splits = {split: 0 for split in CHALLENGE_SUPPORT_SPLITS}
    rejected_splits: dict[tuple[int, int], int] = {}
    for candidate in candidates:
        split = _challenge_support_split(candidate)
        if split is None:
            rejected.append(candidate)
            a_terms, b_terms, _geometry = _candidate_components(candidate)
            raw_split = (len(a_terms), len(b_terms))
            rejected_splits[raw_split] = rejected_splits.get(raw_split, 0) + 1
            continue
        eligible.append(candidate)
        eligible_splits[split] += 1
    return eligible, rejected, eligible_splits, rejected_splits


def _candidate_sample_key(
    candidate,
    *,
    ell: int,
    m: int,
    sampling_salt: str,
) -> bytes:
    """Return a stable order-independent key for an oversized candidate pool."""
    payload = _candidate_definition_payload(candidate, ell=ell, m=m)
    return hashlib.sha256(sampling_salt.encode() + b"\0" + payload).digest()


def _deduplicate_candidate_definitions(
    candidates: list,
    *,
    ell: int,
    m: int,
) -> tuple[list, dict[bytes, int]]:
    """Keep the first canonical definition and count generator occurrences."""
    unique: list = []
    occurrences: dict[bytes, int] = {}
    for candidate in candidates:
        payload = _candidate_definition_payload(candidate, ell=ell, m=m)
        occurrences[payload] = occurrences.get(payload, 0) + 1
        if occurrences[payload] == 1:
            unique.append(candidate)
    return unique, occurrences


def _annotate_generator_occurrences(
    rows: list[dict],
    *,
    ell: int,
    m: int,
    occurrences: dict[bytes, int],
) -> None:
    """Bind each evaluated row to its raw generator multiplicity."""
    for row in rows:
        candidate = _result_as_candidate(row)
        payload = _candidate_definition_payload(candidate, ell=ell, m=m)
        row["generator_occurrence_count"] = occurrences.get(payload, 1)


def _bounded_candidate_sample(
    candidates: list,
    *,
    ell: int,
    m: int,
    limit: int = MAX_CANDIDATES_PER_LATTICE,
    sampling_salt: str = "",
) -> list:
    """Bound work without making the generator's fixed tail unreachable.

    The old prefix slice permanently excluded every item after position 5000.
    Stable hash sampling gives every definition an order-independent chance and
    changes its stratum when the evolved program (the caller-provided salt)
    changes.  The first and last definitions are also retained explicitly so a
    fixed generator tail is covered by regression tests and operational logs.
    """
    candidates, _occurrences = _deduplicate_candidate_definitions(
        candidates,
        ell=ell,
        m=m,
    )
    if len(candidates) <= limit:
        return candidates
    if limit < 2:
        raise ValueError("candidate sample limit must be at least two")
    endpoints = {0, len(candidates) - 1}
    remaining = sorted(
        (
            _candidate_sample_key(
                candidate,
                ell=ell,
                m=m,
                sampling_salt=sampling_salt,
            ),
            index,
        )
        for index, candidate in enumerate(candidates)
        if index not in endpoints
    )
    selected = endpoints | {
        index for _digest, index in remaining[: limit - len(endpoints)]
    }
    return [candidate for index, candidate in enumerate(candidates) if index in selected]


def _program_source_sha256(program_path: str) -> str:
    try:
        return hashlib.sha256(Path(program_path).read_bytes()).hexdigest()
    except OSError:
        return hashlib.sha256(str(program_path).encode()).hexdigest()


def _freeze_program_source_sha256(program_path: str) -> str:
    path = Path(program_path)
    if path.is_symlink() or not path.is_file():
        raise CandidateLogWriteError(
            f"evolved program is not one regular file: {path}"
        )
    before = path.stat()
    encoded = path.read_bytes()
    after = path.stat()
    if (
        (before.st_dev, before.st_ino, before.st_size, before.st_mtime_ns)
        != (after.st_dev, after.st_ino, after.st_size, after.st_mtime_ns)
    ):
        raise CandidateLogWriteError(
            "evolved program changed while its source was frozen"
        )
    return hashlib.sha256(encoded).hexdigest()


def _assert_program_source_unchanged(
    program_path: str,
    expected_sha256: str,
) -> None:
    if _freeze_program_source_sha256(program_path) != expected_sha256:
        raise CandidateLogWriteError(
            "evolved program changed during winner preflight"
        )


def _current_winner_preflight_contract_id() -> int:
    """Return the managed contract id, or a deterministic local fallback."""

    raw = os.environ.get(WINNER_PREFLIGHT_CONTRACT_ID_ENV)
    if raw is not None:
        try:
            contract_id = int(raw)
        except ValueError as exc:
            raise RuntimeError(
                f"{WINNER_PREFLIGHT_CONTRACT_ID_ENV} must be an integer"
            ) from exc
        if contract_id < 1 or contract_id >= 2**53:
            raise RuntimeError(
                f"{WINNER_PREFLIGHT_CONTRACT_ID_ENV} is outside the "
                "exact numeric metric range"
            )
        return contract_id

    # Direct invocations use the same canonical payload as the managed
    # launcher.  Deriving the dependency root from the imported contract
    # module also keeps fallback identity stable if this evaluator is copied
    # into a run directory (as in legacy --milp mode).
    dependency_root = Path(
        _dependency_contract.__file__
    ).resolve().parent.parent
    dependency_hashes: dict[str, str] = {}
    for name in sorted(_dependency_contract.LOCAL_EVALUATOR_DEPENDENCIES):
        relative_path = (
            _dependency_contract.LOCAL_EVALUATOR_DEPENDENCIES[name]
        )
        dependency_path = dependency_root / relative_path
        if dependency_path.is_symlink():
            raise RuntimeError(
                "winner preflight dependency may not be a symlink: "
                f"{dependency_path}"
            )
        try:
            dependency_source = dependency_path.resolve(
                strict=True
            ).read_bytes()
        except OSError as exc:
            raise RuntimeError(
                f"winner preflight dependency is missing: {dependency_path}"
            ) from exc
        dependency_hashes[name] = hashlib.sha256(
            dependency_source
        ).hexdigest()

    candidate_log = _freeze_candidate_log_path().resolve(strict=False)
    output_dir = candidate_log.parent
    payload = {
        "contract_version": WINNER_PREFLIGHT_CONTRACT_VERSION,
        "evaluator_sha256": hashlib.sha256(
            Path(__file__).resolve().read_bytes()
        ).hexdigest(),
        "dependency_sha256": dependency_hashes,
        "lattices": [list(lattice) for lattice in EVOLUTION_LATTICES],
        "candidate_log_path": str(candidate_log),
        "run_identity": {
            "output_dir": str(output_dir),
            "run_name": output_dir.name,
        },
    }
    if is_twisted_geometry_contract(ACTIVE_GEOMETRY_CONTRACT):
        # Keep the historical payload byte shape for rectangular campaigns,
        # while making the fresh q-stratified contract explicit even if a
        # future representation happens to reuse the same lattice list.
        payload["search_geometry_contract"] = ACTIVE_GEOMETRY_CONTRACT
    digest = hashlib.sha256(
        json.dumps(
            payload,
            sort_keys=True,
            separators=(",", ":"),
        ).encode("utf-8")
    ).hexdigest()
    return int(digest[:13], 16)


def _exact_nonnegative_preflight_metric(
    metrics: dict,
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
        raise CandidateLogWriteError(
            f"winner preflight marker is invalid: {name}"
        )
    return int(value)


def _validated_complete_preflight_markers(
    metrics: dict,
    *,
    expected_contract_id: int,
) -> dict[str, float]:
    if not isinstance(metrics, dict):
        raise CandidateLogWriteError(
            "winner preflight metrics are not an object"
        )
    values = {
        name: _exact_nonnegative_preflight_metric(metrics, name)
        for name in WINNER_PREFLIGHT_MARKER_FIELDS
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
        raise CandidateLogWriteError(
            "winner preflight markers do not prove complete persistence"
        )
    return {name: float(values[name]) for name in values}


def _stage1_preflight_key(program_path: str) -> tuple[str, str, int]:
    return (
        os.path.abspath(program_path),
        _freeze_program_source_sha256(program_path),
        _current_winner_preflight_contract_id(),
    )


def _register_stage1_preflight_completion(
    program_path: str,
    metrics: dict,
) -> None:
    key = _stage1_preflight_key(program_path)
    markers = _validated_complete_preflight_markers(
        metrics,
        expected_contract_id=key[2],
    )
    with _STAGE1_PREFLIGHT_COMPLETIONS_LOCK:
        _STAGE1_PREFLIGHT_COMPLETIONS[key] = markers


def _take_stage1_preflight_completion(
    program_path: str,
) -> dict | None:
    with _STAGE1_PREFLIGHT_COMPLETIONS_LOCK:
        if not _STAGE1_PREFLIGHT_COMPLETIONS:
            return None
    key = _stage1_preflight_key(program_path)
    with _STAGE1_PREFLIGHT_COMPLETIONS_LOCK:
        markers = _STAGE1_PREFLIGHT_COMPLETIONS.pop(key, None)
    if markers is None:
        return None
    return {
        "schema_version": 1,
        "program_sha256": key[1],
        "contract_id": key[2],
        "markers": markers,
    }


def _preflight_reuse_from_environment(
    program_path: str,
) -> dict[str, float] | None:
    raw = os.environ.get(WINNER_PREFLIGHT_REUSE_ENV)
    if raw is None:
        return None
    try:
        payload = json.loads(raw)
    except json.JSONDecodeError as exc:
        raise CandidateLogWriteError(
            "Stage 1 preflight reuse payload is unreadable"
        ) from exc
    expected_contract_id = _current_winner_preflight_contract_id()
    if (
        not isinstance(payload, dict)
        or set(payload)
        != {"schema_version", "program_sha256", "contract_id", "markers"}
        or payload.get("schema_version") != 1
        or payload.get("program_sha256")
        != _freeze_program_source_sha256(program_path)
        or payload.get("contract_id") != expected_contract_id
    ):
        raise CandidateLogWriteError(
            "Stage 1 preflight reuse binding is invalid"
        )
    return _validated_complete_preflight_markers(
        payload.get("markers"),
        expected_contract_id=expected_contract_id,
    )


_STAGE1_LATTICE_SUMMARY_COUNT_FIELDS = (
    "unique_candidates",
    "evaluated_candidate_definitions",
    "winner_capable_quick_exploration_eligible",
    "winner_capable_quick_exploration_persisted",
    "winner_capable_quick_exploration_omitted",
    STAGE1_CANDIDATE_LOG_RECORDS_FIELD,
    SUPPORT_WEIGHT_ELIGIBLE_METRIC,
    SUPPORT_WEIGHT_REJECTED_METRIC,
    SUPPORT_WEIGHT_EVALUATED_METRIC,
    *((
        GEOMETRY_TWISTS_REQUIRED_METRIC,
        GEOMETRY_TWISTS_OBSERVED_METRIC,
    ) if is_twisted_geometry_contract(ACTIVE_GEOMETRY_CONTRACT) else ()),
)


def _validated_stage1_lattice_summary(
    summary: object,
    *,
    expected_lattice: tuple[int, int],
) -> dict[str, object]:
    expected_fields = {
        "lattice",
        "pool_sha256",
        "lattices_completed",
        "lattice_failures",
        SUPPORT_FILTER_VERSION_METRIC,
        SUPPORT_WEIGHT_PARTITION_COMPLETE_METRIC,
        *({GEOMETRY_TWIST_COVERAGE_COMPLETE_METRIC}
          if is_twisted_geometry_contract(ACTIVE_GEOMETRY_CONTRACT)
          else set()),
        *_STAGE1_LATTICE_SUMMARY_COUNT_FIELDS,
    }
    if not isinstance(summary, dict) or set(summary) != expected_fields:
        raise CandidateLogWriteError(
            "Stage 1 lattice summary schema is invalid"
        )
    lattice = summary.get("lattice")
    if lattice != [expected_lattice[0], expected_lattice[1]]:
        raise CandidateLogWriteError(
            "Stage 1 lattice summary is bound to a different lattice"
        )
    pool_sha256 = summary.get("pool_sha256")
    if (
        not isinstance(pool_sha256, str)
        or len(pool_sha256) != 64
        or any(
            character not in "0123456789abcdef"
            for character in pool_sha256
        )
    ):
        raise CandidateLogWriteError(
            "Stage 1 lattice summary has an invalid pool digest"
        )
    values = {
        name: _exact_nonnegative_preflight_metric(summary, name)
        for name in expected_fields
        if name not in {"lattice", "pool_sha256"}
    }
    unique = values["unique_candidates"]
    support_eligible = values[SUPPORT_WEIGHT_ELIGIBLE_METRIC]
    support_rejected = values[SUPPORT_WEIGHT_REJECTED_METRIC]
    support_evaluated = values[SUPPORT_WEIGHT_EVALUATED_METRIC]
    winner_eligible = values[
        "winner_capable_quick_exploration_eligible"
    ]
    winner_persisted = values[
        "winner_capable_quick_exploration_persisted"
    ]
    candidate_log_records = values[
        STAGE1_CANDIDATE_LOG_RECORDS_FIELD
    ]
    if (
        values["lattices_completed"] != 1
        or values["lattice_failures"] != 0
        or values[SUPPORT_FILTER_VERSION_METRIC]
        != CHALLENGE_SUPPORT_FILTER_VERSION
        or values[SUPPORT_WEIGHT_PARTITION_COMPLETE_METRIC] != 1
        or (
            is_twisted_geometry_contract(ACTIVE_GEOMETRY_CONTRACT)
            and (
                values[GEOMETRY_TWIST_COVERAGE_COMPLETE_METRIC] != 1
                or values[GEOMETRY_TWISTS_OBSERVED_METRIC]
                != values[GEOMETRY_TWISTS_REQUIRED_METRIC]
            )
        )
        or unique != support_eligible + support_rejected
        or values["evaluated_candidate_definitions"] != support_evaluated
        or support_evaluated != support_eligible
        or winner_persisted != winner_eligible
        or candidate_log_records < winner_persisted
        or values["winner_capable_quick_exploration_omitted"] != 0
    ):
        raise CandidateLogWriteError(
            "Stage 1 lattice summary does not prove complete persistence"
        )
    return {
        "lattice": [expected_lattice[0], expected_lattice[1]],
        "pool_sha256": pool_sha256,
        **values,
    }


def _stage1_lattice_summary(
    metrics: dict,
    *,
    lattice: tuple[int, int],
    pool_sha256: str,
) -> dict[str, object]:
    _require_full_pool_persistence(
        metrics,
        expected_lattices=1,
        label=f"Stage 1 lattice {lattice}",
    )
    summary = {
        "lattice": [lattice[0], lattice[1]],
        "pool_sha256": pool_sha256,
        "lattices_completed": metrics.get("lattices_completed"),
        "lattice_failures": metrics.get("lattice_failures"),
        SUPPORT_FILTER_VERSION_METRIC: metrics.get(
            SUPPORT_FILTER_VERSION_METRIC
        ),
        SUPPORT_WEIGHT_PARTITION_COMPLETE_METRIC: metrics.get(
            SUPPORT_WEIGHT_PARTITION_COMPLETE_METRIC
        ),
        **({
            GEOMETRY_TWIST_COVERAGE_COMPLETE_METRIC: metrics.get(
                GEOMETRY_TWIST_COVERAGE_COMPLETE_METRIC
            ),
        } if is_twisted_geometry_contract(ACTIVE_GEOMETRY_CONTRACT) else {}),
        **{
            name: metrics.get(name)
            for name in _STAGE1_LATTICE_SUMMARY_COUNT_FIELDS
        },
    }
    return _validated_stage1_lattice_summary(
        summary,
        expected_lattice=lattice,
    )


def _generated_pool_sha256(
    candidates: object,
    *,
    lattice: tuple[int, int],
) -> str:
    if not isinstance(candidates, list):
        payload = {
            "lattice": [lattice[0], lattice[1]],
            "returned_type": type(candidates).__name__,
        }
    else:
        normalized, malformed_errors = _normalize_generated_candidates(
            candidates,
            ell=lattice[0],
            m=lattice[1],
        )
        payload = {
            "lattice": [lattice[0], lattice[1]],
            "raw_count": len(candidates),
            "normalized": [
                hashlib.sha256(
                    _candidate_definition_payload(
                        candidate,
                        ell=lattice[0],
                        m=lattice[1],
                    )
                ).hexdigest()
                for candidate in normalized
            ],
            "malformed_errors": malformed_errors,
        }
    encoded = json.dumps(
        payload,
        sort_keys=True,
        separators=(",", ":"),
        ensure_ascii=True,
        allow_nan=False,
    ).encode("ascii")
    return hashlib.sha256(encoded).hexdigest()


def _aggregate_stage1_lattice_summaries(
    summaries: list[dict[str, object]],
) -> dict:
    expected = list(EVOLUTION_LATTICES[: len(summaries)])
    validated = [
        _validated_stage1_lattice_summary(
            summary,
            expected_lattice=lattice,
        )
        for summary, lattice in zip(summaries, expected, strict=True)
    ]
    if len(validated) != len(EVOLUTION_LATTICES):
        raise CandidateLogWriteError(
            "winner preflight cannot complete before every lattice is durable"
        )
    totals = {
        name: sum(int(summary[name]) for summary in validated)
        for name in _STAGE1_LATTICE_SUMMARY_COUNT_FIELDS
    }
    return {
        **totals,
        SUPPORT_FILTER_VERSION_METRIC: CHALLENGE_SUPPORT_FILTER_VERSION,
        SUPPORT_WEIGHT_PARTITION_COMPLETE_METRIC: 1,
        **({
            GEOMETRY_TWIST_COVERAGE_COMPLETE_METRIC: 1,
            GEOMETRY_TWIST_COVERAGE_METRIC: 1.0,
            GEOMETRY_TWISTS_REQUIRED_METRIC: totals[
                GEOMETRY_TWISTS_REQUIRED_METRIC
            ],
            GEOMETRY_TWISTS_OBSERVED_METRIC: totals[
                GEOMETRY_TWISTS_OBSERVED_METRIC
            ],
        } if is_twisted_geometry_contract(ACTIVE_GEOMETRY_CONTRACT) else {}),
        "lattices_completed": len(validated),
        "lattice_failures": 0,
    }


def _stage1_preflight_journal_paths(
    candidate_log_path: Path,
    *,
    source_sha256: str,
    contract_id: int,
) -> tuple[Path, Path]:
    journal_root = (
        candidate_log_path.parent / STAGE1_PREFLIGHT_JOURNAL_DIRECTORY
    )
    journal_root.mkdir(parents=True, exist_ok=True)
    if journal_root.is_symlink() or not journal_root.is_dir():
        raise CandidateLogWriteError(
            f"Stage 1 journal root is unsafe: {journal_root}"
        )
    stem = f"{contract_id}-{source_sha256}"
    return journal_root / f"{stem}.json", journal_root / f"{stem}.lock"


def _stage1_preflight_progress_snapshot(
    journal_path: Path,
    *,
    source_sha256: str,
    contract_id: int,
    candidate_log_path: Path,
) -> tuple[str, int, int, int, str]:
    if not _path_entry_exists(journal_path):
        return ("", 0, 0, 0, "missing")
    journal = _load_stage1_preflight_journal(
        journal_path,
        source_sha256=source_sha256,
        contract_id=contract_id,
        candidate_log_path=candidate_log_path,
    )
    return (
        str(journal["epoch_id"]),
        int(journal["restart_count"]),
        int(journal["progress_sequence"]),
        len(journal["completed_lattices"]),
        str(journal["status"]),
    )


def _open_stage1_preflight_lock(
    lock_path: Path,
    *,
    journal_path: Path,
    source_sha256: str,
    contract_id: int,
    candidate_log_path: Path,
    inactivity_timeout: float,
) -> int:
    flags = os.O_RDWR | os.O_CREAT | os.O_CLOEXEC
    if hasattr(os, "O_NOFOLLOW"):
        flags |= os.O_NOFOLLOW
    descriptor = os.open(lock_path, flags, 0o600)
    metadata = os.fstat(descriptor)
    if not stat.S_ISREG(metadata.st_mode):
        os.close(descriptor)
        raise CandidateLogWriteError(
            f"Stage 1 journal lock is not regular: {lock_path}"
        )
    try:
        try:
            fcntl.flock(
                descriptor,
                fcntl.LOCK_EX | fcntl.LOCK_NB,
            )
            return descriptor
        except BlockingIOError:
            pass
        observed = _stage1_preflight_progress_snapshot(
            journal_path,
            source_sha256=source_sha256,
            contract_id=contract_id,
            candidate_log_path=candidate_log_path,
        )
        started = time.monotonic()
        deadline = started + inactivity_timeout
        absolute_deadline = (
            started
            + inactivity_timeout
            * STAGE1_PREFLIGHT_LOCK_WAIT_INTERVALS
        )
        while True:
            remaining = min(deadline, absolute_deadline) - time.monotonic()
            if remaining <= 0:
                raise Stage1PreflightLockTimeout(
                    "winner preflight source lock owner made no durable "
                    f"progress for {inactivity_timeout:.1f}s"
                )
            time.sleep(min(0.25, remaining))
            try:
                fcntl.flock(
                    descriptor,
                    fcntl.LOCK_EX | fcntl.LOCK_NB,
                )
                return descriptor
            except BlockingIOError:
                progress = _stage1_preflight_progress_snapshot(
                    journal_path,
                    source_sha256=source_sha256,
                    contract_id=contract_id,
                    candidate_log_path=candidate_log_path,
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
                        time.monotonic() + inactivity_timeout,
                        absolute_deadline,
                    )
    except BaseException:
        os.close(descriptor)
        raise


def _initial_stage1_preflight_journal(
    *,
    source_sha256: str,
    contract_id: int,
    candidate_log_path: Path,
    restart_count: int = 0,
) -> dict[str, object]:
    if type(restart_count) is not int or restart_count < 0:
        raise CandidateLogWriteError(
            "Stage 1 journal restart count is invalid"
        )
    return {
        "schema_version": STAGE1_PREFLIGHT_JOURNAL_SCHEMA_VERSION,
        "status": "in_progress",
        "program_sha256": source_sha256,
        "contract_id": contract_id,
        "candidate_log_path": str(candidate_log_path),
        "epoch_id": os.urandom(32).hex(),
        "restart_count": restart_count,
        "lattices": [list(lattice) for lattice in EVOLUTION_LATTICES],
        "completed_lattices": [],
        "progress_sequence": 0,
        "markers": None,
    }


def _validated_stage1_preflight_journal(
    payload: object,
    *,
    source_sha256: str,
    contract_id: int,
    candidate_log_path: Path,
) -> dict[str, object]:
    expected_fields = {
        "schema_version",
        "status",
        "program_sha256",
        "contract_id",
        "candidate_log_path",
        "epoch_id",
        "restart_count",
        "lattices",
        "completed_lattices",
        "progress_sequence",
        "markers",
    }
    if not isinstance(payload, dict) or set(payload) != expected_fields:
        raise CandidateLogWriteError("Stage 1 journal schema is invalid")
    expected_lattices = [list(lattice) for lattice in EVOLUTION_LATTICES]
    completed = payload.get("completed_lattices")
    epoch_id = payload.get("epoch_id")
    if (
        payload.get("schema_version")
        != STAGE1_PREFLIGHT_JOURNAL_SCHEMA_VERSION
        or payload.get("status") not in {"in_progress", "completed"}
        or payload.get("program_sha256") != source_sha256
        or payload.get("contract_id") != contract_id
        or payload.get("candidate_log_path") != str(candidate_log_path)
        or not isinstance(epoch_id, str)
        or len(epoch_id) != 64
        or any(
            character not in "0123456789abcdef"
            for character in epoch_id
        )
        or type(payload.get("restart_count")) is not int
        or payload["restart_count"] < 0
        or payload.get("lattices") != expected_lattices
        or not isinstance(completed, list)
        or len(completed) > len(expected_lattices)
        or type(payload.get("progress_sequence")) is not int
        or payload["progress_sequence"] < len(completed)
    ):
        raise CandidateLogWriteError("Stage 1 journal binding is invalid")
    normalized = [
        _validated_stage1_lattice_summary(
            summary,
            expected_lattice=EVOLUTION_LATTICES[index],
        )
        for index, summary in enumerate(completed)
    ]
    markers = payload.get("markers")
    if payload["status"] == "completed":
        aggregate = _aggregate_stage1_lattice_summaries(normalized)
        expected_markers = _winner_preflight_markers(
            aggregate,
            contract_id=contract_id,
        )
        validated_markers = _validated_complete_preflight_markers(
            markers,
            expected_contract_id=contract_id,
        )
        if validated_markers != expected_markers:
            raise CandidateLogWriteError(
                "Stage 1 completed journal markers do not match its lattice "
                "summaries"
            )
        markers = validated_markers
    elif markers is not None:
        raise CandidateLogWriteError(
            "Stage 1 in-progress journal contains completion markers"
        )
    return {
        **payload,
        "epoch_id": epoch_id,
        "completed_lattices": normalized,
        "progress_sequence": payload["progress_sequence"],
        "markers": markers,
    }


def _load_stage1_preflight_journal(
    journal_path: Path,
    *,
    source_sha256: str,
    contract_id: int,
    candidate_log_path: Path,
) -> dict[str, object]:
    if not _path_entry_exists(journal_path):
        return _initial_stage1_preflight_journal(
            source_sha256=source_sha256,
            contract_id=contract_id,
            candidate_log_path=candidate_log_path,
        )
    if journal_path.is_symlink() or not journal_path.is_file():
        raise CandidateLogWriteError(
            f"Stage 1 journal is not a regular file: {journal_path}"
        )
    try:
        payload = json.loads(journal_path.read_text())
    except (OSError, UnicodeDecodeError, json.JSONDecodeError) as exc:
        raise CandidateLogWriteError(
            f"Stage 1 journal is unreadable: {journal_path}"
        ) from exc
    return _validated_stage1_preflight_journal(
        payload,
        source_sha256=source_sha256,
        contract_id=contract_id,
        candidate_log_path=candidate_log_path,
    )


def _write_stage1_preflight_journal(
    journal_path: Path,
    payload: dict[str, object],
    *,
    source_sha256: str,
    contract_id: int,
    candidate_log_path: Path,
) -> dict[str, object]:
    normalized = _validated_stage1_preflight_journal(
        payload,
        source_sha256=source_sha256,
        contract_id=contract_id,
        candidate_log_path=candidate_log_path,
    )
    if journal_path.is_symlink():
        raise CandidateLogWriteError(
            f"refusing to replace symlinked Stage 1 journal: {journal_path}"
        )
    encoded = json.dumps(
        normalized,
        sort_keys=True,
        separators=(",", ":"),
        allow_nan=False,
    ).encode("utf-8")
    temporary = journal_path.with_name(
        f".{journal_path.name}.tmp-{os.getpid()}-"
        f"{threading.get_ident()}-{time.time_ns()}"
    )
    flags = os.O_WRONLY | os.O_CREAT | os.O_EXCL | os.O_CLOEXEC
    if hasattr(os, "O_NOFOLLOW"):
        flags |= os.O_NOFOLLOW
    descriptor = os.open(temporary, flags, 0o600)
    try:
        _write_all(descriptor, encoded)
        os.fsync(descriptor)
    finally:
        os.close(descriptor)
    os.replace(temporary, journal_path)
    directory_descriptor = os.open(
        journal_path.parent,
        os.O_RDONLY | os.O_CLOEXEC | getattr(os, "O_DIRECTORY", 0),
    )
    try:
        os.fsync(directory_descriptor)
    finally:
        os.close(directory_descriptor)
    return normalized


def _restart_stage1_preflight_journal(
    journal_path: Path,
    journal: dict[str, object],
    *,
    source_sha256: str,
    contract_id: int,
    candidate_log_path: Path,
) -> dict[str, object]:
    """Rotate the row epoch after the bound candidate tail was rolled back."""

    restarted = _initial_stage1_preflight_journal(
        source_sha256=source_sha256,
        contract_id=contract_id,
        candidate_log_path=candidate_log_path,
        restart_count=int(journal["restart_count"]) + 1,
    )
    return _write_stage1_preflight_journal(
        journal_path,
        restarted,
        source_sha256=source_sha256,
        contract_id=contract_id,
        candidate_log_path=candidate_log_path,
    )


def _recover_stage1_lattice_commits(
    candidate_log_path: Path,
    journal: dict[str, object],
) -> dict[str, object]:
    completed = list(journal["completed_lattices"])
    recovered: dict[tuple[int, int], dict[str, object]] = {}
    provenance_counts: dict[tuple[int, int], int] = {}
    commit_counts: dict[tuple[int, int], int] = {}
    candidate_log_path = _canonical_candidate_log_path(candidate_log_path)
    candidate_log_path.parent.mkdir(parents=True, exist_ok=True)
    flags = os.O_RDWR | os.O_APPEND | os.O_CREAT | os.O_CLOEXEC
    if hasattr(os, "O_NOFOLLOW"):
        flags |= os.O_NOFOLLOW
    try:
        descriptor = os.open(candidate_log_path, flags, 0o600)
    except OSError as exc:
        raise CandidateLogWriteError(
            f"Stage 1 candidate log cannot be opened: {candidate_log_path}"
        ) from exc
    try:
        fcntl.flock(descriptor, fcntl.LOCK_EX)
        _validate_locked_candidate_log(candidate_log_path, descriptor)
        _recover_candidate_log_wal_locked(
            candidate_log_path,
            descriptor,
        )
        os.fsync(descriptor)
        _fsync_candidate_log_directory(candidate_log_path)
        _validate_candidate_log_boundary(
            descriptor,
            os.fstat(descriptor).st_size,
        )
        # Downgrade without an unlocked window. Other recovery scans can now
        # proceed together, while every cooperating append remains blocked
        # until this inode-bound snapshot has been fully validated.
        fcntl.flock(descriptor, fcntl.LOCK_SH)
        before = os.fstat(descriptor)
        with os.fdopen(os.dup(descriptor), "rb") as source:
            source.seek(0)
            for line in source:
                try:
                    row = json.loads(line)
                except (UnicodeDecodeError, json.JSONDecodeError) as exc:
                    raise CandidateLogWriteError(
                        "candidate log is corrupt while recovering Stage 1"
                    ) from exc
                if (
                    not isinstance(row, dict)
                    or row.get(STAGE1_PREFLIGHT_ROW_PROGRAM_SHA256)
                    != journal["program_sha256"]
                    or row.get(STAGE1_PREFLIGHT_ROW_CONTRACT_ID)
                    != journal["contract_id"]
                    or row.get(STAGE1_PREFLIGHT_ROW_EPOCH_ID)
                    != journal["epoch_id"]
                ):
                    continue
                raw_lattice = row.get(STAGE1_PREFLIGHT_ROW_LATTICE)
                if (
                    not isinstance(raw_lattice, list)
                    or len(raw_lattice) != 2
                    or any(type(item) is not int for item in raw_lattice)
                ):
                    raise CandidateLogWriteError(
                        "candidate log has an invalid Stage 1 provenance lattice"
                    )
                lattice = (raw_lattice[0], raw_lattice[1])
                if lattice not in EVOLUTION_LATTICES:
                    raise CandidateLogWriteError(
                        "candidate log has out-of-contract Stage 1 provenance"
                    )
                provenance_counts[lattice] = (
                    provenance_counts.get(lattice, 0) + 1
                )
                if (
                    row.get(STAGE1_PREFLIGHT_ROW_LATTICE_COMMIT)
                    is not True
                ):
                    continue
                commit_counts[lattice] = commit_counts.get(lattice, 0) + 1
                summary = _validated_stage1_lattice_summary(
                    row.get(STAGE1_PREFLIGHT_ROW_LATTICE_SUMMARY),
                    expected_lattice=lattice,
                )
                prior = recovered.get(lattice)
                if prior is not None and prior != summary:
                    raise CandidateLogWriteError(
                        "candidate log has conflicting Stage 1 lattice commits"
                    )
                recovered[lattice] = summary
        after = os.fstat(descriptor)
        _validate_locked_candidate_log(candidate_log_path, descriptor)
        wal_file, temporary = _candidate_log_wal_paths(candidate_log_path)
        if (
            (before.st_dev, before.st_ino, before.st_size)
            != (after.st_dev, after.st_ino, after.st_size)
            or _path_entry_exists(wal_file)
            or _path_entry_exists(temporary)
        ):
            raise CandidateLogWriteError(
                "Stage 1 candidate commit snapshot was not captured from "
                "one stable WAL-clean file"
            )
    finally:
        try:
            fcntl.flock(descriptor, fcntl.LOCK_UN)
        finally:
            os.close(descriptor)

    for lattice, observed_records in provenance_counts.items():
        summary = recovered.get(lattice)
        if summary is None:
            raise Stage1CandidateCommitMismatch(
                "Stage 1 candidate provenance has no complete lattice "
                f"commit at {lattice}"
            )
        expected_records = int(
            summary[STAGE1_CANDIDATE_LOG_RECORDS_FIELD]
        )
        if (
            observed_records != expected_records
            or commit_counts.get(lattice, 0) != 1
        ):
            raise Stage1CandidateCommitMismatch(
                "Stage 1 candidate commit is incomplete or duplicated at "
                f"{lattice}: summary={expected_records}, "
                f"candidate_rows={observed_records}, "
                f"commit_rows={commit_counts.get(lattice, 0)}"
            )

    for index, summary in enumerate(completed):
        lattice = EVOLUTION_LATTICES[index]
        expected_records = int(
            summary[STAGE1_CANDIDATE_LOG_RECORDS_FIELD]
        )
        observed_records = provenance_counts.get(lattice, 0)
        commit = recovered.get(lattice)
        if (
            observed_records != expected_records
            or (expected_records > 0 and commit != summary)
            or (expected_records == 0 and commit is not None)
        ):
            raise Stage1CandidateCommitMismatch(
                "Stage 1 journal/candidate commit mismatch at lattice "
                f"{lattice}: journal={expected_records}, "
                f"candidate_rows={observed_records}, "
                f"commit={commit is not None}"
            )

    while len(completed) < len(EVOLUTION_LATTICES):
        lattice = EVOLUTION_LATTICES[len(completed)]
        summary = recovered.get(lattice)
        if summary is None:
            break
        completed.append(summary)
    committed_prefix = set(EVOLUTION_LATTICES[: len(completed)])
    unexpected = sorted(set(provenance_counts) - committed_prefix)
    if unexpected:
        raise Stage1CandidateCommitMismatch(
            "Stage 1 candidate commits are not a continuous lattice "
            f"prefix: {unexpected}"
        )
    return {
        **journal,
        "completed_lattices": completed,
        "progress_sequence": max(
            int(journal["progress_sequence"]),
            len(completed),
        ),
    }
def _stage1_lattice_spool_rows(spool_path: Path) -> list[dict]:
    try:
        encoded = spool_path.read_bytes()
    except FileNotFoundError:
        encoded = b""
    if encoded and not encoded.endswith(b"\n"):
        raise CandidateLogWriteError(
            "Stage 1 lattice spool ends with a partial JSON record"
        )
    rows = []
    for line in encoded.splitlines():
        try:
            row = json.loads(line)
        except json.JSONDecodeError as exc:
            raise CandidateLogWriteError(
                "Stage 1 lattice spool contains invalid JSON"
            ) from exc
        if not isinstance(row, dict):
            raise CandidateLogWriteError(
                "Stage 1 lattice spool row is not an object"
            )
        rows.append(row)
    return rows


def _stage1_lattice_commit_payload(
    spool_path: Path,
    *,
    source_sha256: str,
    contract_id: int,
    epoch_id: str,
    lattice: tuple[int, int],
    summary: dict[str, object],
) -> bytes:
    if (
        not isinstance(epoch_id, str)
        or len(epoch_id) != 64
        or any(
            character not in "0123456789abcdef"
            for character in epoch_id
        )
    ):
        raise CandidateLogWriteError(
            "Stage 1 lattice commit epoch is invalid"
        )
    rows = _stage1_lattice_spool_rows(spool_path)
    for row in rows:
        for field in (
            STAGE1_PREFLIGHT_ROW_PROGRAM_SHA256,
            STAGE1_PREFLIGHT_ROW_CONTRACT_ID,
            STAGE1_PREFLIGHT_ROW_EPOCH_ID,
            STAGE1_PREFLIGHT_ROW_LATTICE,
            STAGE1_PREFLIGHT_ROW_LATTICE_COMMIT,
            STAGE1_PREFLIGHT_ROW_LATTICE_SUMMARY,
        ):
            if field in row:
                raise CandidateLogWriteError(
                    "Stage 1 lattice spool forged managed provenance"
                )
        row[STAGE1_PREFLIGHT_ROW_PROGRAM_SHA256] = source_sha256
        row[STAGE1_PREFLIGHT_ROW_CONTRACT_ID] = contract_id
        row[STAGE1_PREFLIGHT_ROW_EPOCH_ID] = epoch_id
        row[STAGE1_PREFLIGHT_ROW_LATTICE] = [lattice[0], lattice[1]]
    expected_records = int(
        summary[STAGE1_CANDIDATE_LOG_RECORDS_FIELD]
    )
    if len(rows) != expected_records:
        raise CandidateLogWriteError(
            "Stage 1 lattice spool does not match its persistence summary: "
            f"lattice={lattice}, rows={len(rows)}, "
            f"persisted={expected_records}"
        )
    if rows:
        rows[-1][STAGE1_PREFLIGHT_ROW_LATTICE_COMMIT] = True
        rows[-1][STAGE1_PREFLIGHT_ROW_LATTICE_SUMMARY] = summary
    return b"".join(
        (
            json.dumps(
                row,
                ensure_ascii=False,
                sort_keys=True,
                separators=(",", ":"),
                allow_nan=False,
            )
            + "\n"
        ).encode("utf-8")
        for row in rows
    )


def _stage1_specialist_exploration_pass(program_path: str) -> bool:
    """Admit a small deterministic sample past an otherwise absolute gate."""
    digest = _program_source_sha256(program_path)
    return (
        int(digest[:16], 16) % STAGE1_SPECIALIST_EXPLORATION_DENOMINATOR == 0
    )


def _select_quick_exploration(
    rows: list[dict],
    *,
    ell: int,
    m: int,
    sampling_salt: str,
    limit: int = MAX_WINNER_CAPABLE_EXPLORATION_PER_LATTICE,
) -> list[dict]:
    """Select a bounded, deterministic and k-stratified quick-only lane.

    Hashing removes generator-order bias; the evolved-program digest supplies
    deterministic rotation as the program changes. One representative per
    dimension is preferred before filling the remaining quota globally.
    """
    if limit < 1:
        return []
    ranked = []
    seen: set[tuple] = set()
    for row in rows:
        definition = _definition_key(row)
        if definition in seen or not _annotate_winner_capability(row):
            continue
        seen.add(definition)
        digest = hashlib.sha256(
            sampling_salt.encode()
            + b"\0quick-exploration\0"
            + repr((ell, m, definition)).encode()
        ).digest()
        ranked.append((digest, row))
    ranked.sort(key=lambda item: item[0])

    selected: list[dict] = []
    selected_ids: set[int] = set()
    seen_k: set[int] = set()
    for _digest, row in ranked:
        k = int(row.get("k", 0) or 0)
        if k in seen_k:
            continue
        selected.append(row)
        selected_ids.add(id(row))
        seen_k.add(k)
        if len(selected) >= limit:
            return selected
    for _digest, row in ranked:
        if id(row) in selected_ids:
            continue
        selected.append(row)
        if len(selected) >= limit:
            break
    return selected


def _winner_capable_definitions(rows: list[dict]) -> list[dict]:
    """Return every unique positive-k definition with a feasible win window."""
    eligible: list[dict] = []
    seen: set[tuple] = set()
    for row in rows:
        if int(row.get("k", 0) or 0) <= 0:
            continue
        definition = _definition_key(row)
        if definition in seen or not _annotate_winner_capability(row):
            continue
        seen.add(definition)
        eligible.append(row)
    return eligible


def _zero_distance_persistence_row(
    row: dict,
    *,
    reason: str,
    backend_error: dict[str, str] | None = None,
) -> dict:
    """Return an explicitly non-proof row suitable for durable retry routing."""
    persisted = dict(row)
    for field in (
        "d_symplectic",
        "milp_details",
        "threshold_proof_witness",
        "threshold_proof_distance",
        "threshold_proof_source",
        "threshold_proof_lhs",
        "threshold_proof_rhs",
    ):
        persisted.pop(field, None)
    persisted.update({
        "d": 0,
        "d_is_exact": False,
        "distance_trusted": False,
        "distance_status": "unknown",
        "milp_attempted": False,
        "fom": 0.0,
        "score": 0.0,
        "stage": reason,
        "candidate_persistence_lane": WINNER_CAPABLE_EXPLORATION_LANE,
        "candidate_persistence_reason": reason,
    })
    if backend_error is None:
        persisted.pop("distance_backend_error", None)
    else:
        persisted["distance_backend_error"] = dict(backend_error)
        persisted["distance_status"] = "unknown_backend_error"
    if not _annotate_winner_capability(persisted):
        raise CandidateLogWriteError(
            "selected distance candidate lost its winner-capable parameters"
        )
    return persisted


def _distance_backend_error_record(exc: Exception) -> dict[str, str]:
    """Return bounded strict-JSON diagnostics for an untrusted backend error."""
    try:
        message = str(exc)
    except Exception as stringify_error:
        message = (
            "<exception message unavailable: "
            f"{type(stringify_error).__name__}>"
        )
    if len(message) > MAX_DISTANCE_BACKEND_ERROR_MESSAGE_CHARS:
        message = (
            message[: MAX_DISTANCE_BACKEND_ERROR_MESSAGE_CHARS - 3] + "..."
        )
    return {
        "type": type(exc).__name__[:256],
        "message": message,
    }


def _filter_static_eligible(results: list[dict]) -> tuple[list[dict], list[dict]]:
    """Remove disconnected/invalid positive-k codes before they affect fitness."""
    accepted = []
    rejected = []
    for result in results:
        if int(result.get("k", 0) or 0) <= 0:
            accepted.append(result)
            continue
        audit = check_css_static_eligibility(
            result["ell"], result["m"],
            result["A_terms"], result["B_terms"],
            geometry=result.get("geometry"),
            reported_n=result.get("n"),
            reported_k=result.get("k"),
        )
        result["static_eligibility"] = audit
        if audit["eligible"]:
            accepted.append(result)
        else:
            result["structural_rejection"] = "static_ineligible"
            rejected.append(result)
    return accepted, rejected

# Lattice subsets for staged evaluation.  Legacy keeps its historical scale;
# the checkpoint-incompatible twisted representation uses one quick probe per
# formal target length so an elongated-only support family can cross the
# cascade threshold instead of being rejected on two small rectangular probes.
STAGE1_LATTICES = list(CONTRACT_STAGE1_FITNESS_LATTICES)
# These are the defining lattices for the n=72, 90 and 108 final-gate Pareto
# references.  They run first in the full evaluator so every accepted win class
# has a durable OpenEvolve -> Humanize route even if a later large lattice uses
# the remainder of the evaluator wall budget.
FINAL_GATE_PARETO_LATTICES = list(CONTRACT_PARETO_LATTICES)
# Preserve the historical fitness basis when the persistence-only final-gate
# lattices are added. This keeps resumed OpenEvolve checkpoint scores and
# MAP-Elites cells comparable across the source upgrade.
STAGE2_FITNESS_LATTICES = list(CONTRACT_STAGE2_FITNESS_LATTICES)
# Stage 2 calls the generator on the complete shared contract. Fitness below
# remains restricted to STAGE2_FITNESS_LATTICES so resumed MAP-Elites scores
# stay comparable; the additional lattices are durable discovery probes.
STAGE2_LATTICES = list(EVOLUTION_LATTICES)
# Deep BP-OSD work stays on the historical fitness/Pareto basis.  A bounded
# quick preflight covers every contracted target before any blocking distance
# call, so the external soft timeout cannot make a tail lattice unreachable.
STAGE2_DEEP_LATTICES = list(CONTRACT_STAGE2_DEEP_LATTICES)
# Historical MILP fitness basis. Keep it separate from the added persistence
# probes for the same checkpoint-compatibility reason as
# ``STAGE2_FITNESS_LATTICES`` above.
if is_twisted_geometry_contract(ACTIVE_GEOMETRY_CONTRACT):
    STAGE2_MILP_FITNESS_LATTICES = list(STAGE2_FITNESS_LATTICES)
else:
    STAGE2_MILP_FITNESS_LATTICES = [
        (12, 6), (6, 12),
        (12, 12), (24, 6),
        (15, 12), (30, 6),
    ]
# Stage 2 for MILP: drop (16,9) and (18,8) which produce 0 valid x/y-swap codes.
STAGE2_LATTICES_MILP = [
    *FINAL_GATE_PARETO_LATTICES,
    *STAGE2_MILP_FITNESS_LATTICES,
]


def _pool_map_descriptor(
    rows: list[dict],
    *,
    lattices: set[tuple[int, int]] | None = None,
) -> dict[str, float]:
    """Describe one generator by its canonical evaluated pool.

    The old descriptor selected the highest-k/FOM row.  A fixed safety-net
    definition could therefore place many otherwise different generators in
    the same MAP cell.  This descriptor instead uses every unique,
    challenge-supported row on the requested fitness lattice basis:

    * ``term_count`` is the mean maximum A/B support size;
    * ``pattern_type`` is the dominant structural class, with deterministic
      lowest-class tie breaking;
    * ``support_split_type`` is the dominant challenge support split's fixed
      zero-based index in ``CHALLENGE_SUPPORT_SPLITS``, with the same
      deterministic tie breaking;
    * ``search_structural_entropy`` is Shannon entropy of the six-class
      pattern distribution, normalized by ``log(6)`` into ``[0, 1]``;
    * ``algebraic_relation_type`` is the dominant mechanism's fixed zero-based
      index in ``RELATION_TYPES``;
    * ``orbit_span_bin`` and ``difference_spectrum_bin`` are the dominant
      integer bins emitted by ``classify_algebraic_mechanism``.

    When evaluated rows expose ``k``, only rows with positive encoding
    dimension may determine the descriptor.  This prevents a generator from
    moving itself between MAP cells by padding its pool with disconnected or
    zero-logical-qubit definitions.  The all-rows fallback exists only for
    structural callers that do not provide an evaluated ``k`` field.
    """

    unique_rows: list[dict] = []
    seen: set[tuple] = set()
    for row in rows:
        if not isinstance(row, dict):
            continue
        try:
            lattice = (int(row.get("ell", 0)), int(row.get("m", 0)))
            if lattices is not None and lattice not in lattices:
                continue
            candidate = _result_as_candidate(row)
            support_split = _challenge_support_split(candidate)
            if support_split is None:
                continue
            definition = _definition_key(row)
            a_terms, b_terms, geometry = _candidate_components(candidate)
            pattern = _classify_pattern(a_terms, b_terms)
            term_count = _count_terms(a_terms, b_terms)
            support_split_type = CHALLENGE_SUPPORT_SPLITS.index(
                support_split
            )
            mechanism = classify_algebraic_mechanism(
                a_terms,
                b_terms,
                ell=lattice[0],
                m=lattice[1],
                geometry=geometry,
            )
            relation_type = RELATION_TYPES.index(
                mechanism["relation_type"]
            )
            orbit_span_bin = int(mechanism["orbit_span_bin"])
            difference_spectrum_bin = int(
                mechanism["difference_spectrum_bin"]
            )
            geometry_twist_class = _geometry_twist_class(
                lattice[0],
                lattice[1],
                row.get("geometry"),
            )
        except (TypeError, ValueError):
            continue
        if definition in seen:
            continue
        seen.add(definition)
        unique_rows.append({
            "pattern_type": pattern,
            "term_count": term_count,
            "positive_k": (
                isinstance(row.get("k"), (int, float))
                and not isinstance(row.get("k"), bool)
                and math.isfinite(float(row["k"]))
                and float(row["k"]) > 0.0
            ),
            "has_evaluated_k": (
                "k" in row
                and isinstance(row.get("k"), (int, float))
                and not isinstance(row.get("k"), bool)
                and math.isfinite(float(row["k"]))
            ),
            MAP_DESCRIPTOR_SUPPORT_SPLIT_METRIC: support_split_type,
            MAP_DESCRIPTOR_ALGEBRAIC_RELATION_METRIC: relation_type,
            MAP_DESCRIPTOR_ORBIT_SPAN_METRIC: orbit_span_bin,
            MAP_DESCRIPTOR_DIFFERENCE_SPECTRUM_METRIC: (
                difference_spectrum_bin
            ),
            MAP_DESCRIPTOR_GEOMETRY_TWIST_CLASS_METRIC: (
                geometry_twist_class
            ),
        })

    positive_rows = [row for row in unique_rows if row["positive_k"]]
    if positive_rows:
        unique_rows = positive_rows
    elif any(row["has_evaluated_k"] for row in unique_rows):
        unique_rows = []

    if not unique_rows:
        descriptor = {
            "term_count": 0.0,
            "pattern_type": 0.0,
            MAP_DESCRIPTOR_SUPPORT_SPLIT_METRIC: 0.0,
            MAP_DESCRIPTOR_STRUCTURAL_ENTROPY_METRIC: 0.0,
            MAP_DESCRIPTOR_ALGEBRAIC_RELATION_METRIC: 0.0,
            MAP_DESCRIPTOR_ORBIT_SPAN_METRIC: 0.0,
            MAP_DESCRIPTOR_DIFFERENCE_SPECTRUM_METRIC: 0.0,
            MAP_DESCRIPTOR_VERSION_METRIC: float(MAP_DESCRIPTOR_VERSION),
            MAP_DESCRIPTOR_POOL_SIZE_METRIC: 0.0,
            MAP_DESCRIPTOR_DOMINANT_SHARE_METRIC: 0.0,
        }
        if is_twisted_geometry_contract(ACTIVE_GEOMETRY_CONTRACT):
            descriptor[MAP_DESCRIPTOR_GEOMETRY_TWIST_CLASS_METRIC] = 0.0
        return descriptor

    pattern_counts: dict[float, int] = {}
    for row in unique_rows:
        pattern = row["pattern_type"]
        pattern_counts[pattern] = pattern_counts.get(pattern, 0) + 1
    dominant_pattern, dominant_count = min(
        pattern_counts.items(),
        key=lambda item: (-item[1], item[0]),
    )
    support_split_counts: dict[int, int] = {}
    for row in unique_rows:
        support_split_type = row[MAP_DESCRIPTOR_SUPPORT_SPLIT_METRIC]
        support_split_counts[support_split_type] = (
            support_split_counts.get(support_split_type, 0) + 1
        )
    dominant_support_split, _dominant_support_count = min(
        support_split_counts.items(),
        key=lambda item: (-item[1], item[0]),
    )
    dominant_algebraic_relation = min(
        (
            (value, sum(
                row[MAP_DESCRIPTOR_ALGEBRAIC_RELATION_METRIC] == value
                for row in unique_rows
            ))
            for value in range(len(RELATION_TYPES))
        ),
        key=lambda item: (-item[1], item[0]),
    )[0]

    def dominant_bin(metric: str) -> int:
        counts: dict[int, int] = {}
        for descriptor_row in unique_rows:
            value = int(descriptor_row[metric])
            counts[value] = counts.get(value, 0) + 1
        return min(counts.items(), key=lambda item: (-item[1], item[0]))[0]

    pool_size = len(unique_rows)
    structural_entropy = -sum(
        (count / pool_size) * math.log(count / pool_size)
        for count in pattern_counts.values()
    ) / math.log(MAP_DESCRIPTOR_PATTERN_CARDINALITY)
    structural_entropy = min(1.0, max(0.0, structural_entropy))
    descriptor = {
        "term_count": (
            sum(row["term_count"] for row in unique_rows) / pool_size
        ),
        "pattern_type": dominant_pattern,
        MAP_DESCRIPTOR_SUPPORT_SPLIT_METRIC: float(
            dominant_support_split
        ),
        MAP_DESCRIPTOR_STRUCTURAL_ENTROPY_METRIC: structural_entropy,
        MAP_DESCRIPTOR_ALGEBRAIC_RELATION_METRIC: float(
            dominant_algebraic_relation
        ),
        MAP_DESCRIPTOR_ORBIT_SPAN_METRIC: float(
            dominant_bin(MAP_DESCRIPTOR_ORBIT_SPAN_METRIC)
        ),
        MAP_DESCRIPTOR_DIFFERENCE_SPECTRUM_METRIC: float(
            dominant_bin(MAP_DESCRIPTOR_DIFFERENCE_SPECTRUM_METRIC)
        ),
        MAP_DESCRIPTOR_VERSION_METRIC: float(MAP_DESCRIPTOR_VERSION),
        MAP_DESCRIPTOR_POOL_SIZE_METRIC: float(pool_size),
        MAP_DESCRIPTOR_DOMINANT_SHARE_METRIC: (
            dominant_count / pool_size
        ),
    }
    if is_twisted_geometry_contract(ACTIVE_GEOMETRY_CONTRACT):
        descriptor[MAP_DESCRIPTOR_GEOMETRY_TWIST_CLASS_METRIC] = float(
            dominant_bin(MAP_DESCRIPTOR_GEOMETRY_TWIST_CLASS_METRIC)
        )
    return descriptor


def _structural_feedback(result: dict) -> str:
    """Generate structural feedback string for a code with d >= 4.

    Reports mixed vs pure term counts, shift direction vectors,
    and axis coupling -- simple properties that help the LLM reason
    about WHY a code worked.
    """
    A = result.get("A_terms", [])
    B = result.get("B_terms", [])

    def _classify_terms(terms, name):
        pure_x = sum(1 for x, y in terms if x > 0 and y == 0)
        pure_y = sum(1 for x, y in terms if x == 0 and y > 0)
        const = sum(1 for x, y in terms if x == 0 and y == 0)
        mixed = sum(1 for x, y in terms if x > 0 and y > 0)
        return f"{name}: {pure_x} pure-x, {pure_y} pure-y, {const} const, {mixed} mixed"

    lines = [
        _classify_terms(A, "A"),
        _classify_terms(B, "B"),
        f"A shifts: {A}",
        f"B shifts: {B}",
        f"Terms: |A|={len(A)}, |B|={len(B)}",
    ]

    a_has_mixed = any(x > 0 and y > 0 for x, y in A)
    b_has_mixed = any(x > 0 and y > 0 for x, y in B)
    if a_has_mixed and b_has_mixed:
        lines.append("Axis coupling: both A and B have mixed terms")
    elif a_has_mixed:
        lines.append("Axis coupling: only A has mixed terms")
    elif b_has_mixed:
        lines.append("Axis coupling: only B has mixed terms")
    else:
        lines.append("Axis coupling: none (pure-term code)")

    return "\n  ".join(lines)


def _append_candidate_jsonl(
    log_file: Path,
    payload: bytes | bytearray,
) -> dict[str, object] | None:
    """Append one batch through a recoverable write-ahead intent.

    The intent contains the complete bounded payload and its exact starting
    offset.  It is atomically installed and synced before the JSONL changes.
    A writer killed during (or immediately after) the append therefore leaves
    enough information for the next lock holder to finish the same batch
    without interleaving or duplicating bytes.
    """
    if not payload:
        return None
    log_file = _canonical_candidate_log_path(log_file)
    flags = os.O_RDWR | os.O_APPEND | os.O_CREAT | os.O_CLOEXEC
    if hasattr(os, "O_NOFOLLOW"):
        flags |= os.O_NOFOLLOW
    descriptor = os.open(log_file, flags, 0o600)
    try:
        fcntl.flock(descriptor, fcntl.LOCK_EX)
        _validate_locked_candidate_log(log_file, descriptor)
        _recover_candidate_log_wal_locked(log_file, descriptor)
        original_size = os.fstat(descriptor).st_size
        _validate_candidate_log_boundary(descriptor, original_size)
        _install_candidate_log_wal(
            log_file,
            start_offset=original_size,
            payload=payload,
        )
        try:
            _write_candidate_log_payload(descriptor, payload)
            os.fsync(descriptor)
        except BaseException:
            # Recoverable exceptions keep the historical all-or-nothing API:
            # truncate the partial suffix, sync it, then durably clear the WAL.
            # SIGKILL bypasses this block and leaves the WAL for the next
            # writer, which is the crash window this protocol closes.
            try:
                os.ftruncate(descriptor, original_size)
                os.fsync(descriptor)
                _clear_candidate_log_wal(log_file)
            except (OSError, CandidateLogWriteError):
                logger.exception(
                    "Failed to roll back candidate JSONL WAL transaction: %s",
                    log_file,
                )
            raise
        _clear_candidate_log_wal(log_file)
        _validate_locked_candidate_log(log_file, descriptor)
        committed = os.fstat(descriptor)
        if committed.st_size != original_size + len(payload):
            raise CandidateLogWriteError(
                "candidate JSONL changed before append identity was sealed"
            )
        return {
            "path": str(log_file),
            "device": committed.st_dev,
            "inode": committed.st_ino,
            "start_offset": original_size,
            "end_offset": committed.st_size,
            "sha256": hashlib.sha256(payload).hexdigest(),
            "bytes": len(payload),
            "wal_clean": True,
        }
    finally:
        try:
            fcntl.flock(descriptor, fcntl.LOCK_UN)
        finally:
            os.close(descriptor)


def _candidate_log_wal_paths(log_file: Path) -> tuple[Path, Path]:
    wal_file = log_file.with_name(log_file.name + CANDIDATE_LOG_WAL_SUFFIX)
    return wal_file, wal_file.with_name(
        wal_file.name + CANDIDATE_LOG_WAL_TEMP_SUFFIX
    )


def _canonical_candidate_log_path(path: str | Path) -> Path:
    """Canonicalize parent directories without following the final entry."""
    candidate = Path(path).expanduser()
    if not candidate.is_absolute():
        candidate = candidate.absolute()
    return candidate.parent.resolve(strict=False) / candidate.name


def _path_entry_exists(path: Path) -> bool:
    """Return whether a directory entry exists without following symlinks."""
    try:
        path.lstat()
    except FileNotFoundError:
        return False
    return True


def _fsync_candidate_log_directory(log_file: Path) -> None:
    flags = os.O_RDONLY | os.O_CLOEXEC
    if hasattr(os, "O_DIRECTORY"):
        flags |= os.O_DIRECTORY
    descriptor = os.open(log_file.parent, flags)
    try:
        os.fsync(descriptor)
    finally:
        os.close(descriptor)


def _write_all(descriptor: int, payload: bytes | bytearray) -> None:
    written = 0
    view = memoryview(payload)
    while written < len(view):
        count = os.write(descriptor, view[written:])
        if count <= 0:
            raise OSError("candidate log write made no progress")
        written += count


def _write_candidate_log_payload(
    descriptor: int,
    payload: bytes | bytearray,
) -> None:
    """Append payload bytes; kept separate for crash-injection tests."""
    _write_all(descriptor, payload)


def _candidate_log_wal_bytes(
    log_file: Path,
    *,
    start_offset: int,
    payload: bytes | bytearray,
) -> bytes:
    payload_bytes = bytes(payload)
    header = {
        "log_path": str(log_file),
        "payload_length": len(payload_bytes),
        "payload_sha256": hashlib.sha256(payload_bytes).hexdigest(),
        "schema_version": CANDIDATE_LOG_WAL_SCHEMA_VERSION,
        "start_offset": start_offset,
    }
    encoded_header = json.dumps(
        header,
        sort_keys=True,
        separators=(",", ":"),
        ensure_ascii=True,
        allow_nan=False,
    ).encode("ascii")
    if len(encoded_header) > CANDIDATE_LOG_WAL_HEADER_MAX_BYTES:
        raise CandidateLogWriteError(
            "candidate JSONL WAL header exceeds its safety bound"
        )
    return encoded_header + b"\n" + payload_bytes


def _install_candidate_log_wal(
    log_file: Path,
    *,
    start_offset: int,
    payload: bytes | bytearray,
) -> None:
    """Atomically and durably publish one complete append intent."""
    wal_file, temporary = _candidate_log_wal_paths(log_file)
    if _path_entry_exists(wal_file) or _path_entry_exists(temporary):
        raise CandidateLogWriteError(
            "candidate JSONL WAL path is unexpectedly occupied"
        )
    flags = os.O_WRONLY | os.O_CREAT | os.O_EXCL | os.O_CLOEXEC
    if hasattr(os, "O_NOFOLLOW"):
        flags |= os.O_NOFOLLOW
    descriptor = os.open(temporary, flags, 0o600)
    try:
        _write_all(
            descriptor,
            _candidate_log_wal_bytes(
                log_file,
                start_offset=start_offset,
                payload=payload,
            ),
        )
        os.fsync(descriptor)
    except BaseException:
        os.close(descriptor)
        try:
            temporary.unlink()
            _fsync_candidate_log_directory(log_file)
        except OSError:
            logger.exception(
                "Failed to clear incomplete candidate JSONL WAL temp: %s",
                temporary,
            )
        raise
    else:
        os.close(descriptor)
    # The fixed temporary name is protected by the candidate-log flock.  Any
    # pre-existing WAL/temp was rejected above, so replace cannot overwrite a
    # cooperating writer's intent.
    os.replace(temporary, wal_file)
    _fsync_candidate_log_directory(log_file)


def _strict_candidate_log_wal_header(encoded: bytes) -> dict:
    if len(encoded) > CANDIDATE_LOG_WAL_HEADER_MAX_BYTES:
        raise CandidateLogWriteError(
            "candidate JSONL WAL header exceeds its safety bound"
        )

    def strict_object(pairs):
        result = {}
        for key, value in pairs:
            if key in result:
                raise ValueError(f"duplicate key: {key}")
            result[key] = value
        return result

    try:
        header = json.loads(
            encoded.decode("ascii"),
            object_pairs_hook=strict_object,
        )
    except (UnicodeDecodeError, json.JSONDecodeError, ValueError) as exc:
        raise CandidateLogWriteError(
            "candidate JSONL WAL header is invalid"
        ) from exc
    expected_fields = {
        "log_path",
        "payload_length",
        "payload_sha256",
        "schema_version",
        "start_offset",
    }
    if not isinstance(header, dict) or set(header) != expected_fields:
        raise CandidateLogWriteError(
            "candidate JSONL WAL schema fields are invalid"
        )
    if (
        type(header["schema_version"]) is not int
        or header["schema_version"] != CANDIDATE_LOG_WAL_SCHEMA_VERSION
        or type(header["start_offset"]) is not int
        or header["start_offset"] < 0
        or type(header["payload_length"]) is not int
        or header["payload_length"] < 1
        or not isinstance(header["log_path"], str)
        or not isinstance(header["payload_sha256"], str)
        or len(header["payload_sha256"]) != 64
        or any(
            character not in "0123456789abcdef"
            for character in header["payload_sha256"]
        )
    ):
        raise CandidateLogWriteError(
            "candidate JSONL WAL typed fields are invalid"
        )
    return header


def _read_candidate_log_wal(
    log_file: Path,
) -> tuple[dict, bytes] | None:
    wal_file, temporary = _candidate_log_wal_paths(log_file)
    if _path_entry_exists(temporary):
        raise CandidateLogWriteError(
            f"candidate JSONL WAL has a residual temp file: {temporary}"
        )
    if not _path_entry_exists(wal_file):
        return None
    flags = os.O_RDONLY | os.O_CLOEXEC
    if hasattr(os, "O_NOFOLLOW"):
        flags |= os.O_NOFOLLOW
    try:
        descriptor = os.open(wal_file, flags)
    except OSError as exc:
        raise CandidateLogWriteError(
            f"candidate JSONL WAL cannot be opened safely: {wal_file}"
        ) from exc
    try:
        metadata = os.fstat(descriptor)
        if not stat.S_ISREG(metadata.st_mode):
            raise CandidateLogWriteError(
                "candidate JSONL WAL is not a regular file"
            )
        chunks = []
        remaining = metadata.st_size
        while remaining:
            chunk = os.read(descriptor, min(remaining, 1 << 20))
            if not chunk:
                raise CandidateLogWriteError(
                    "candidate JSONL WAL ended before its stated size"
                )
            chunks.append(chunk)
            remaining -= len(chunk)
    finally:
        os.close(descriptor)
    encoded = b"".join(chunks)
    header_end = encoded.find(b"\n")
    if header_end < 0:
        raise CandidateLogWriteError(
            "candidate JSONL WAL is missing its header delimiter"
        )
    header = _strict_candidate_log_wal_header(encoded[:header_end])
    payload = encoded[header_end + 1 :]
    if header["log_path"] != str(log_file):
        raise CandidateLogWriteError(
            "candidate JSONL WAL is bound to a different log path"
        )
    if len(payload) != header["payload_length"]:
        raise CandidateLogWriteError(
            "candidate JSONL WAL payload length does not match its header"
        )
    if hashlib.sha256(payload).hexdigest() != header["payload_sha256"]:
        raise CandidateLogWriteError(
            "candidate JSONL WAL payload hash does not match its header"
        )
    if not payload.endswith(b"\n"):
        raise CandidateLogWriteError(
            "candidate JSONL WAL payload is not a complete JSONL batch"
        )
    return header, payload


def _validate_locked_candidate_log(
    log_file: Path,
    descriptor: int,
) -> None:
    opened = os.fstat(descriptor)
    if not stat.S_ISREG(opened.st_mode):
        raise CandidateLogWriteError(
            "candidate JSONL destination is not a regular file"
        )
    try:
        named = os.stat(log_file, follow_symlinks=False)
    except OSError as exc:
        raise CandidateLogWriteError(
            "candidate JSONL destination disappeared after open"
        ) from exc
    if (opened.st_dev, opened.st_ino) != (named.st_dev, named.st_ino):
        raise CandidateLogWriteError(
            "candidate JSONL destination changed after open"
        )


def _validate_candidate_log_boundary(
    descriptor: int,
    size: int,
) -> None:
    if size and os.pread(descriptor, 1, size - 1) != b"\n":
        raise CandidateLogWriteError(
            "candidate JSONL ends in an untracked partial record"
        )


def _clear_candidate_log_wal(log_file: Path) -> None:
    wal_file, temporary = _candidate_log_wal_paths(log_file)
    if _path_entry_exists(temporary):
        raise CandidateLogWriteError(
            f"candidate JSONL WAL has a residual temp file: {temporary}"
        )
    try:
        wal_file.unlink()
    except FileNotFoundError as exc:
        raise CandidateLogWriteError(
            "candidate JSONL WAL disappeared before durable commit"
        ) from exc
    _fsync_candidate_log_directory(log_file)


def _recover_candidate_log_wal_locked(
    log_file: Path,
    descriptor: int,
) -> bool:
    transaction = _read_candidate_log_wal(log_file)
    if transaction is None:
        return False
    header, payload = transaction
    start_offset = header["start_offset"]
    current_size = os.fstat(descriptor).st_size
    end_offset = start_offset + len(payload)
    if current_size < start_offset or current_size > end_offset:
        raise CandidateLogWriteError(
            "candidate JSONL size is incompatible with its WAL offsets"
        )
    appended = current_size - start_offset
    existing = os.pread(descriptor, appended, start_offset)
    if len(existing) != appended or existing != payload[:appended]:
        raise CandidateLogWriteError(
            "candidate JSONL suffix does not match its WAL payload"
        )
    if appended < len(payload):
        _write_candidate_log_payload(descriptor, payload[appended:])
    os.fsync(descriptor)
    _validate_candidate_log_boundary(descriptor, end_offset)
    _clear_candidate_log_wal(log_file)
    return True


def recover_candidate_log_wal(
    candidate_log_path: str | Path,
) -> bool:
    """Recover one orphan append intent under the production inode lock.

    Returns ``True`` when a WAL was replayed or acknowledged as already fully
    appended, and ``False`` when no intent existed.  Corrupt or ambiguously
    bound sidecars fail closed and are deliberately left for inspection.
    """
    raw_path = os.fspath(candidate_log_path)
    if "\x00" in raw_path or not Path(raw_path).is_absolute():
        raise CandidateLogWriteError(
            "candidate WAL recovery requires an absolute log path"
        )
    log_file = _canonical_candidate_log_path(raw_path)
    log_file.parent.mkdir(parents=True, exist_ok=True)
    flags = os.O_RDWR | os.O_APPEND | os.O_CREAT | os.O_CLOEXEC
    if hasattr(os, "O_NOFOLLOW"):
        flags |= os.O_NOFOLLOW
    descriptor = os.open(log_file, flags, 0o600)
    try:
        fcntl.flock(descriptor, fcntl.LOCK_EX)
        _validate_locked_candidate_log(log_file, descriptor)
        recovered = _recover_candidate_log_wal_locked(log_file, descriptor)
        os.fsync(descriptor)
        _fsync_candidate_log_directory(log_file)
        return recovered
    finally:
        try:
            fcntl.flock(descriptor, fcntl.LOCK_UN)
        finally:
            os.close(descriptor)


def candidate_log_range_identity(
    candidate_log_path: str | Path,
    *,
    start_offset: int,
    end_offset: int | None = None,
) -> dict[str, object]:
    """Return a WAL-clean, inode-bound identity for one candidate byte range.

    An orphan WAL is recovered first under the same lock used by writers.
    Hashing is limited to the requested range; historical bytes before
    ``start_offset`` are never rescanned on the normal append/witness path.
    """
    if (
        isinstance(start_offset, bool)
        or not isinstance(start_offset, int)
        or start_offset < 0
        or end_offset is not None
        and (
            isinstance(end_offset, bool)
            or not isinstance(end_offset, int)
            or end_offset < start_offset
        )
    ):
        raise CandidateLogWriteError(
            "candidate range offsets must be ordered non-negative integers"
        )
    raw_path = os.fspath(candidate_log_path)
    if "\x00" in raw_path or not Path(raw_path).is_absolute():
        raise CandidateLogWriteError(
            "candidate range identity requires an absolute log path"
        )
    log_file = _canonical_candidate_log_path(raw_path)
    log_file.parent.mkdir(parents=True, exist_ok=True)
    flags = os.O_RDWR | os.O_APPEND | os.O_CREAT | os.O_CLOEXEC
    if hasattr(os, "O_NOFOLLOW"):
        flags |= os.O_NOFOLLOW
    descriptor = os.open(log_file, flags, 0o600)
    try:
        fcntl.flock(descriptor, fcntl.LOCK_EX)
        _validate_locked_candidate_log(log_file, descriptor)
        _recover_candidate_log_wal_locked(log_file, descriptor)
        os.fsync(descriptor)
        _fsync_candidate_log_directory(log_file)
        metadata = os.fstat(descriptor)
        observed_end = metadata.st_size if end_offset is None else end_offset
        if start_offset > metadata.st_size or observed_end > metadata.st_size:
            raise CandidateLogWriteError(
                "candidate identity range exceeds the durable log size"
            )
        if (
            start_offset
            and os.pread(descriptor, 1, start_offset - 1) != b"\n"
        ) or (
            observed_end
            and os.pread(descriptor, 1, observed_end - 1) != b"\n"
        ):
            raise CandidateLogWriteError(
                "candidate identity offsets are not complete JSONL boundaries"
            )
        digest = hashlib.sha256()
        position = start_offset
        while position < observed_end:
            chunk = os.pread(
                descriptor,
                min(1 << 20, observed_end - position),
                position,
            )
            if not chunk:
                raise CandidateLogWriteError(
                    "candidate log changed while hashing its byte range"
                )
            digest.update(chunk)
            position += len(chunk)
        after = os.fstat(descriptor)
        _validate_locked_candidate_log(log_file, descriptor)
        wal_file, temporary = _candidate_log_wal_paths(log_file)
        if (
            (metadata.st_dev, metadata.st_ino, metadata.st_size)
            != (after.st_dev, after.st_ino, after.st_size)
            or _path_entry_exists(wal_file)
            or _path_entry_exists(temporary)
        ):
            raise CandidateLogWriteError(
                "candidate log identity was not captured from a stable "
                "WAL-clean file"
            )
        return {
            "path": str(log_file),
            "device": metadata.st_dev,
            "inode": metadata.st_ino,
            "start_offset": start_offset,
            "end_offset": observed_end,
            "sha256": digest.hexdigest(),
            "bytes": observed_end - start_offset,
            "wal_clean": True,
        }
    finally:
        try:
            fcntl.flock(descriptor, fcntl.LOCK_UN)
        finally:
            os.close(descriptor)


def _freeze_candidate_log_run_name() -> str:
    """Capture the trusted launcher binding before importing evolved code."""

    run_name = os.environ.get("QCODE_RUN_NAME")
    if run_name in (None, ""):
        return ""
    if (
        run_name != Path(run_name).name
        or run_name in {".", ".."}
        or "\x00" in run_name
    ):
        raise CandidateLogWriteError(
            "QCODE_RUN_NAME is not a safe single path component"
        )
    return run_name


def _freeze_candidate_log_path(
    candidate_log_path: str | Path | None = None,
    *,
    run_name: str | None = None,
) -> Path:
    """Return one absolute candidate-log binding captured before untrusted code.

    Managed and ``--milp`` launchers supply an absolute path.  The historical
    run-name routing remains as a compatibility fallback for direct evaluator
    use and tests, but an inherited absolute binding always wins over it.
    """

    raw_path: str | None
    if candidate_log_path is not None:
        raw_path = os.fspath(candidate_log_path)
    else:
        raw_path = os.environ.get(CANDIDATE_LOG_PATH_ENV)
    if raw_path not in (None, ""):
        if "\x00" in raw_path:
            raise CandidateLogWriteError(
                f"{CANDIDATE_LOG_PATH_ENV} contains a NUL byte"
            )
        path = Path(raw_path)
        if not path.is_absolute():
            raise CandidateLogWriteError(
                f"{CANDIDATE_LOG_PATH_ENV} must be an absolute path"
            )
        return _canonical_candidate_log_path(path)

    if run_name is None:
        run_name = _freeze_candidate_log_run_name()
    if run_name:
        return (
            Path(_PROJECT_ROOT)
            / "results"
            / "evolution"
            / run_name
            / "all_codes.jsonl"
        ).absolute()
    return (
        Path(_PROJECT_ROOT)
        / "results"
        / "evolution"
        / "all_codes.jsonl"
    ).absolute()


def _freeze_milp_candidate_log_path() -> Path:
    """Pin the legacy MILP worker's path for its entire process lifetime."""

    global _MILP_CANDIDATE_LOG_PATH_BINDING
    with _MILP_CANDIDATE_LOG_PATH_BINDING_LOCK:
        if _MILP_CANDIDATE_LOG_PATH_BINDING is None:
            _MILP_CANDIDATE_LOG_PATH_BINDING = (
                _freeze_candidate_log_path()
            )
        return _MILP_CANDIDATE_LOG_PATH_BINDING


def _candidate_jsonl_record(result: dict) -> dict | None:
    """Build one candidate-log record, or return ``None`` when ineligible."""
    d = result.get("d", 0)
    exploration_lane = (
        result.get("candidate_persistence_lane")
        == WINNER_CAPABLE_EXPLORATION_LANE
        and result.get("winner_capable_parameters") is True
    )
    if d <= 0 and not exploration_lane:
        return None

    mechanism = classify_algebraic_mechanism(result)

    record = {
        "ell": result.get("ell"),
        "m": result.get("m"),
        "A_terms": result.get("A_terms"),
        "B_terms": result.get("B_terms"),
        "n": result.get("n"),
        "k": result.get("k"),
        "d": d,
        "fom": result.get("fom", 0.0),
        "stage": result.get("stage", ""),
        "pattern_type": _classify_pattern(
            result.get("A_terms", []), result.get("B_terms", [])
        ),
        "relation_type": mechanism["relation_type"],
        MAP_DESCRIPTOR_ALGEBRAIC_RELATION_METRIC: RELATION_TYPES.index(
            mechanism["relation_type"]
        ),
        MAP_DESCRIPTOR_ORBIT_SPAN_METRIC: mechanism["orbit_span_bin"],
        MAP_DESCRIPTOR_DIFFERENCE_SPECTRUM_METRIC: mechanism[
            "difference_spectrum_bin"
        ],
        SUPPORT_FILTER_VERSION_METRIC: CHALLENGE_SUPPORT_FILTER_VERSION,
        PATTERN_CLASSIFIER_VERSION_METRIC: PATTERN_CLASSIFIER_VERSION,
        "term_count": _count_terms(
            result.get("A_terms", []), result.get("B_terms", [])
        ),
        "generator_occurrence_count": result.get(
            "generator_occurrence_count", 1
        ),
        "timestamp": time.time(),
    }
    canonical_geometry = normalize_geometry(
        int(result.get("ell", 0) or 0),
        int(result.get("m", 0) or 0),
        result.get("geometry"),
    )
    if canonical_geometry is not None:
        record["geometry"] = canonical_geometry
    if ACTIVE_GEOMETRY_CONTRACT == (
        PUBLISHED_VOLUME_ANSATZ_V3_GEOMETRY_CONTRACT
    ):
        record["search_representation_id"] = (
            PUBLISHED_VOLUME_ANSATZ_V3_REPRESENTATION_ID
        )
    # Preserve distance semantics across the OpenEvolve -> Humanize handoff.
    # In particular, Humanize must be able to distinguish an unresolved
    # BP/OSD upper bound from exact/certified evidence without inferring that
    # distinction from the numerical d/FOM magnitude.
    for field in (
        "d_is_exact",
        "distance_trusted",
        "distance_status",
        "distance_upper_bound",
        "distance_upper_bound_source",
        "fom_upper_bound",
        "exact_distance",
        "exact_fom",
        "distance_lower_bound",
        "distance_lower_bound_proven",
        "distance_lower_bound_status",
        "fom_lower_bound",
        "low_weight_oracle_threshold",
        "low_weight_oracle",
        "threshold_proof_witness",
        "threshold_proof_distance",
        "threshold_proof_source",
        "threshold_proof_lhs",
        "threshold_proof_rhs",
        "fitness_distance_credit",
        "fitness_survivor_credit",
        "search_status",
        "distance_retry_required",
        "threshold_rejection_proven",
        "threshold_proof_source",
        "threshold_proof_distance",
        "fom_rejection_cutoff",
        "challenge_rejection_cutoff",
        "fom_target_excluded_by_upper_bound",
        "final_gate_excluded_by_upper_bound",
        "search_final_gate_excluded_by_upper_bound",
    ):
        if field in result:
            record[field] = result[field]
    if exploration_lane:
        record.update({
            "candidate_persistence_lane": WINNER_CAPABLE_EXPLORATION_LANE,
            "candidate_persistence_reason": result.get(
                "candidate_persistence_reason",
                QUICK_EXPLORATION_PERSISTENCE_REASON,
            ),
            "winner_capable_parameters": True,
            "minimum_winning_distance": result["minimum_winning_distance"],
            "singleton_distance_upper_bound": result[
                "singleton_distance_upper_bound"
            ],
            "d_is_exact": result.get("d_is_exact", False) is True,
            "distance_trusted": (
                result.get("distance_trusted", False) is True
            ),
            "distance_status": result.get("distance_status", "unknown"),
            "milp_attempted": result.get("milp_attempted", False) is True,
        })
        if isinstance(result.get("distance_backend_error"), dict):
            record["distance_backend_error"] = dict(
                result["distance_backend_error"]
            )
    return record


def _log_codes_jsonl(
    results: list[dict],
    run_name: str | None = None,
    *,
    candidate_log_path: str | Path | None = None,
) -> int:
    """Durably append candidates in bounded, individually synced chunks.

    At most one target-sized payload is materialized at a time; the full
    result pool is never duplicated into a records list plus a second encoded
    batch. A single record larger than the byte target occupies its own chunk
    rather than being discarded. Each chunk is locked, appended and fsynced
    before the cumulative count is advanced. A later chunk failure is
    surfaced, so no caller can emit a complete-preflight marker; already
    durable prefix chunks are safe for the Humanize offset/dedup protocol.
    """
    log_file = _freeze_candidate_log_path(
        candidate_log_path,
        run_name=run_name,
    )
    payload = bytearray()
    chunk_records = 0
    persisted = 0

    def flush_chunk() -> None:
        nonlocal payload, chunk_records, persisted
        if chunk_records == 0:
            return
        _append_candidate_jsonl(log_file, payload)
        persisted += chunk_records
        payload = bytearray()
        chunk_records = 0

    try:
        log_file.parent.mkdir(parents=True, exist_ok=True)
        for result in results:
            record = _candidate_jsonl_record(result)
            if record is None:
                continue
            encoded = (
                json.dumps(record, ensure_ascii=False, default=str) + "\n"
            ).encode("utf-8")
            if (
                chunk_records > 0
                and (
                    chunk_records >= CANDIDATE_LOG_CHUNK_MAX_RECORDS
                    or len(payload) + len(encoded)
                    > CANDIDATE_LOG_CHUNK_MAX_BYTES
                )
            ):
                flush_chunk()
            payload.extend(encoded)
            chunk_records += 1
        flush_chunk()
    except OSError as exc:
        raise CandidateLogWriteError(
            "failed to persist discovered candidate batch in "
            f"{log_file.parent} after {persisted} complete records"
        ) from exc
    return persisted


def _log_code_jsonl(
    result: dict,
    run_name: str | None = None,
    *,
    candidate_log_path: str | Path | None = None,
) -> None:
    """Append a code result to the run-specific all_codes.jsonl file.

    Logs all codes with ``d > 0`` plus statically eligible quick-only
    candidates in the explicit winner-capable exploration lane.  The latter
    closes the old top-k handoff gap without making arbitrary FOM claims.

    Routing is resolved from (in priority order):
    1. Explicit or inherited absolute candidate-log binding
    2. Explicit ``run_name`` argument
    3. ``QCODE_RUN_NAME`` compatibility fallback
    4. ``results/evolution/all_codes.jsonl``
    """
    _log_codes_jsonl(
        [result],
        run_name=run_name,
        candidate_log_path=candidate_log_path,
    )


def _error_result(error: str) -> dict:
    """Return an error result that includes all feature dimensions.

    MAP-Elites requires the feature dimensions to be present in every
    result, including errors.
    """
    result = {
        "combined_score": 0.0,
        "error": error,
        "lattices_with_high_k": 0.0,
        "num_high_k": 0.0,
    }
    result.update(_pool_map_descriptor([]))
    return result


def _load_generate_candidates(program_path: str):
    """Load generate_candidates from an evolved program file."""
    if not Path(program_path).exists():
        raise FileNotFoundError(f"Evolved program not found: {program_path}")
    if ACTIVE_GEOMETRY_CONTRACT == (
        PUBLISHED_VOLUME_ANSATZ_V3_GEOMETRY_CONTRACT
    ):
        from evaluation.ansatz_v3_program_guard import (
            validate_ansatz_v3_program,
        )

        validate_ansatz_v3_program(Path(program_path))
    spec = importlib.util.spec_from_file_location("evolved_program", program_path)
    module = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(module)

    if not hasattr(module, "generate_candidates"):
        raise AttributeError("Evolved program missing generate_candidates function")

    return module.generate_candidates


def _run_evaluation(
    generate_fn,
    lattices: list[tuple[int, int]],
    quick: bool = False,
    quick_trials: int = 100,
    refine_trials: int = 500,
    max_distance_per_lattice: int = 10,
    use_milp: bool = False,
    milp_timeout_per_logical: int = 30,
    milp_total_timeout: int = 120,
    milp_early_stop: int = 4,
    run_name: str | None = None,
    sampling_salt: str = "",
    candidate_limit: int | None = MAX_CANDIDATES_PER_LATTICE,
    persist_quick_exploration: bool = False,
    persist_all_quick_exploration: bool = False,
    candidate_log_path: str | Path | None = None,
) -> dict:
    """Run evaluation across lattices and compute aggregate metrics.

    When quick=False, each lattice invokes the generator exactly once:
    1. Partition the complete frozen canonical pool by the challenge support
       contract, then quick-screen and durably persist every winner-capable
       definition on its eligible side.
    2. Bound that same pool for fitness and estimate distance for its top
       `max_distance_per_lattice` candidates, using either BP-OSD (default) or
       MILP (when use_milp=True).
    """
    # This must happen before the first generator call.  Evolved code is
    # untrusted with respect to process environment and may mutate either
    # legacy QCODE_RUN_NAME or the absolute binding while being evaluated.
    candidate_log_path = _freeze_candidate_log_path(
        candidate_log_path,
        run_name=run_name,
    )
    if candidate_limit is None:
        if not (quick and persist_all_quick_exploration):
            raise ValueError(
                "an unbounded candidate universe is restricted to full "
                "quick-preflight persistence"
            )
    elif (
        isinstance(candidate_limit, bool)
        or not isinstance(candidate_limit, int)
        or candidate_limit < 2
    ):
        raise ValueError(
            "candidate_limit must be None or an integer of at least two"
        )
    if persist_all_quick_exploration and not persist_quick_exploration:
        raise ValueError(
            "persist_all_quick_exploration requires "
            "persist_quick_exploration"
        )

    all_results = []
    total_candidates = 0
    unique_candidates = 0
    evaluated_candidate_definitions = 0
    duplicate_candidate_occurrences = 0
    quick_exploration_eligible = 0
    quick_exploration_persisted = 0
    quick_exploration_omitted = 0
    distance_pending_persisted = 0
    unresolved_top_persisted = 0
    distance_error_top_persisted = 0
    distance_backend_error_count = 0
    malformed_candidate_definitions = 0
    errors = []
    tier0_rejected_count = 0
    structural_rejected_count = 0
    lattices_completed = 0
    lattice_failures = 0
    support_weight_eligible = 0
    support_weight_rejected = 0
    support_weight_evaluated = 0
    support_split_counts = {
        split: 0 for split in CHALLENGE_SUPPORT_SPLITS
    }
    support_rejection_split_counts: dict[tuple[int, int], int] = {}
    support_lattice_splits: set[tuple[int, int, int, int]] = set()
    geometry_twists_required = 0
    geometry_twists_observed = 0

    for ell, m in lattices:
        try:
            prelogged_quick_keys: set[tuple] = set()
            candidates = generate_fn(ell, m)
            if not isinstance(candidates, list):
                errors.append(f"({ell},{m}): generate_candidates returned {type(candidates)}, not list")
                lattice_failures += 1
                continue

            raw_candidate_count = len(candidates)
            total_candidates += raw_candidate_count
            candidates, malformed_errors = _normalize_generated_candidates(
                candidates,
                ell=ell,
                m=m,
            )
            malformed_candidate_definitions += len(malformed_errors)
            errors.extend(malformed_errors)
            candidates, candidate_occurrences = (
                _deduplicate_candidate_definitions(
                    candidates,
                    ell=ell,
                    m=m,
                )
            )
            unique_candidates += len(candidates)
            duplicate_candidate_occurrences += (
                raw_candidate_count - len(candidates)
            )
            (
                candidates,
                support_rejected,
                lattice_support_splits,
                lattice_rejection_splits,
            ) = _partition_challenge_support(candidates)
            if (
                is_twisted_geometry_contract(ACTIVE_GEOMETRY_CONTRACT)
            ):
                required_twists = set(allowed_twists(
                    ell,
                    m,
                    contract=ACTIVE_GEOMETRY_CONTRACT,
                ))
                observed_twist_counts: dict[int, int] = {}
                for candidate in candidates:
                    twist = _candidate_twist(candidate, ell=ell, m=m)
                    observed_twist_counts[twist] = (
                        observed_twist_counts.get(twist, 0) + 1
                    )
                observed_twists = set(observed_twist_counts)
                geometry_twists_required += len(required_twists)
                geometry_twists_observed += len(
                    required_twists.intersection(observed_twists)
                )
                missing_twists = required_twists - observed_twists
                underfilled_twists = {
                    twist: observed_twist_counts.get(twist, 0)
                    for twist in required_twists
                    if observed_twist_counts.get(twist, 0)
                    < TWISTED_MIN_CANDIDATES_PER_TWIST
                }
                if missing_twists or underfilled_twists:
                    errors.append(
                        f"({ell},{m}): challenge-supported twist quota is "
                        f"incomplete; missing={sorted(missing_twists)}, "
                        f"underfilled={dict(sorted(underfilled_twists.items()))}, "
                        f"required_per_twist="
                        f"{TWISTED_MIN_CANDIDATES_PER_TWIST}"
                    )
                    lattice_failures += 1
                    continue
            support_weight_eligible += len(candidates)
            support_weight_rejected += len(support_rejected)
            for split, count in lattice_support_splits.items():
                support_split_counts[split] += count
                if count:
                    support_lattice_splits.add((ell, m, *split))
            for split, count in lattice_rejection_splits.items():
                support_rejection_split_counts[split] = (
                    support_rejection_split_counts.get(split, 0) + count
                )

            distance_selection_limit = max_distance_per_lattice
            if (ell, m) in FINAL_GATE_PARETO_LATTICES:
                distance_selection_limit = min(
                    distance_selection_limit,
                    MAX_FINAL_GATE_PARETO_DISTANCE_PER_LATTICE,
                )

            if quick:
                if persist_all_quick_exploration:
                    # Complete persistence is a write-ahead contract, not the
                    # fitness sample. Evaluate and persist the frozen complete
                    # challenge-supported pool first; only then derive bounded
                    # fitness rows from those same objects without another
                    # generator/evaluator call.
                    evaluated_candidate_definitions += len(candidates)
                    complete_quick_results = evaluate_batch(
                        ell, m, candidates,
                        quick=True,
                        quick_trials=quick_trials,
                        fom_threshold_refine=6.0,
                        fom_threshold_exact=8.0,
                    )
                    _require_complete_quick_result_set(
                        complete_quick_results,
                        candidates,
                        ell=ell,
                        m=m,
                    )
                    support_weight_evaluated += len(candidates)
                    _annotate_generator_occurrences(
                        complete_quick_results,
                        ell=ell,
                        m=m,
                        occurrences=candidate_occurrences,
                    )
                    complete_quick_results, static_rejected = (
                        _filter_static_eligible(complete_quick_results)
                    )
                    tier0_rejected_count += len(static_rejected)
                    eligible_quick = _winner_capable_definitions(
                        complete_quick_results
                    )
                    quick_exploration_eligible += len(eligible_quick)
                    for result in eligible_quick:
                        result["candidate_persistence_lane"] = (
                            WINNER_CAPABLE_EXPLORATION_LANE
                        )
                        result["candidate_persistence_reason"] = (
                            FULL_POOL_PREFLIGHT_PERSISTENCE_REASON
                        )
                    persisted_count = _log_codes_jsonl(
                        eligible_quick,
                        candidate_log_path=candidate_log_path,
                    )
                    if persisted_count != len(eligible_quick):
                        raise CandidateLogWriteError(
                            f"({ell},{m}): full preflight persistence "
                            f"logged {persisted_count} of "
                            f"{len(eligible_quick)} eligible definitions"
                        )
                    prelogged_quick_keys = {
                        _definition_key(result) for result in eligible_quick
                    }
                    quick_exploration_persisted += len(eligible_quick)

                    sampled_candidates = candidates
                    if (
                        candidate_limit is not None
                        and len(sampled_candidates) > candidate_limit
                    ):
                        errors.append(
                            f"({ell},{m}): {len(sampled_candidates)} unique "
                            f"candidates, sampled to {candidate_limit}"
                        )
                        sampled_candidates = _bounded_candidate_sample(
                            sampled_candidates,
                            ell=ell,
                            m=m,
                            limit=candidate_limit,
                            sampling_salt=sampling_salt,
                        )
                    sampled_keys = {
                        _candidate_definition_key(
                            candidate,
                            ell=ell,
                            m=m,
                        )
                        for candidate in sampled_candidates
                    }
                    results = [
                        result
                        for result in complete_quick_results
                        if _definition_key(result) in sampled_keys
                    ]
                else:
                    # Ordinary quick fitness retains the historical bounded
                    # behavior. Managed Stage 1 enables complete persistence.
                    if (
                        candidate_limit is not None
                        and len(candidates) > candidate_limit
                    ):
                        errors.append(
                            f"({ell},{m}): {len(candidates)} unique candidates, "
                            f"sampled to {candidate_limit}"
                        )
                        candidates = _bounded_candidate_sample(
                            candidates,
                            ell=ell,
                            m=m,
                            limit=candidate_limit,
                            sampling_salt=sampling_salt,
                        )
                    evaluated_candidate_definitions += len(candidates)
                    results = evaluate_batch(
                        ell, m, candidates,
                        quick=True,
                        quick_trials=quick_trials,
                        fom_threshold_refine=6.0,
                        fom_threshold_exact=8.0,
                    )
                    expected_quick_keys = {
                        _candidate_definition_key(
                            candidate,
                            ell=ell,
                            m=m,
                        )
                        for candidate in candidates
                    }
                    support_weight_evaluated += len(
                        expected_quick_keys.intersection(
                            _definition_key(result) for result in results
                        )
                    )
                    _annotate_generator_occurrences(
                        results,
                        ell=ell,
                        m=m,
                        occurrences=candidate_occurrences,
                    )
                    results, static_rejected = _filter_static_eligible(results)
                    tier0_rejected_count += len(static_rejected)
                    if persist_quick_exploration:
                        eligible_quick = _winner_capable_definitions(results)
                        quick_exploration_eligible += len(eligible_quick)
                        persisted_quick = _select_quick_exploration(
                            eligible_quick,
                            ell=ell,
                            m=m,
                            sampling_salt=sampling_salt,
                        )
                        for result in persisted_quick:
                            result["candidate_persistence_lane"] = (
                                WINNER_CAPABLE_EXPLORATION_LANE
                            )
                            result["candidate_persistence_reason"] = (
                                QUICK_EXPLORATION_PERSISTENCE_REASON
                            )
                            _log_code_jsonl(
                                result,
                                candidate_log_path=candidate_log_path,
                            )
                        prelogged_quick_keys = {
                            _definition_key(result)
                            for result in persisted_quick
                        }
                        quick_exploration_persisted += len(persisted_quick)
                        quick_exploration_omitted += (
                            len(eligible_quick) - len(persisted_quick)
                        )
            else:
                # The generator has already been invoked exactly once for this
                # lattice. Before any bounded sampling, screen its complete
                # challenge-supported canonical pool and durably hand off every
                # statically eligible, winner-capable definition. This is
                # required even when Stage 2 reused a prior Stage 1 completion:
                # a random/stateful generator can produce a different pool on
                # this deep invocation.
                evaluated_candidate_definitions += len(candidates)
                if use_milp:
                    complete_quick_results = evaluate_batch_milp(
                        ell, m, candidates, quick=True,
                    )
                else:
                    complete_quick_results = evaluate_batch(
                        ell, m, candidates, quick=True,
                    )
                _require_complete_quick_result_set(
                    complete_quick_results,
                    candidates,
                    ell=ell,
                    m=m,
                )
                support_weight_evaluated += len(candidates)
                _annotate_generator_occurrences(
                    complete_quick_results,
                    ell=ell,
                    m=m,
                    occurrences=candidate_occurrences,
                )
                complete_quick_results, static_rejected = (
                    _filter_static_eligible(complete_quick_results)
                )
                tier0_rejected_count += len(static_rejected)
                eligible_quick = _winner_capable_definitions(
                    complete_quick_results
                )
                for result in eligible_quick:
                    result["candidate_persistence_lane"] = (
                        WINNER_CAPABLE_EXPLORATION_LANE
                    )
                    result["candidate_persistence_reason"] = (
                        FULL_POOL_PREFLIGHT_PERSISTENCE_REASON
                    )
                persisted_count = _log_codes_jsonl(
                    eligible_quick,
                    candidate_log_path=candidate_log_path,
                )
                if persisted_count != len(eligible_quick):
                    raise CandidateLogWriteError(
                        f"({ell},{m}): deep full-pool persistence logged "
                        f"{persisted_count} of {len(eligible_quick)} eligible "
                        "definitions"
                    )
                prelogged_quick_keys = {
                    _definition_key(result) for result in eligible_quick
                }
                quick_exploration_eligible += len(eligible_quick)
                quick_exploration_persisted += len(eligible_quick)

                # Only after the full write-ahead handoff may fitness/deep work
                # be bounded. The sample is taken from the same frozen canonical
                # objects; generate_fn is never called again for this lattice.
                sampled_candidates = candidates
                if (
                    candidate_limit is not None
                    and len(sampled_candidates) > candidate_limit
                ):
                    errors.append(
                        f"({ell},{m}): {len(sampled_candidates)} unique "
                        f"candidates, sampled to {candidate_limit}"
                    )
                    sampled_candidates = _bounded_candidate_sample(
                        sampled_candidates,
                        ell=ell,
                        m=m,
                        limit=candidate_limit,
                        sampling_salt=sampling_salt,
                    )
                sampled_keys = {
                    _candidate_definition_key(
                        candidate,
                        ell=ell,
                        m=m,
                    )
                    for candidate in sampled_candidates
                }
                quick_results = [
                    result
                    for result in complete_quick_results
                    if _definition_key(result) in sampled_keys
                ]

                # Select diverse candidates for distance estimation.
                # Diversify on BOTH k value AND polynomial A -- prevents
                # wasting MILP budget on near-duplicate codes (e.g. 5 codes
                # with same A at (15,12) all giving k=16).
                # When symplectic weight is available (MILP path), rank by
                # approximate FOM = k * d_symp^2 / n instead of k alone.
                promising = [
                    r for r in quick_results
                    if _annotate_winner_capability(r)
                ]
                n_code = 2 * ell * m
                def _rank_key(r):
                    d_s = r.get("d_symplectic", 0)
                    if d_s > 0 and use_milp:
                        return r["k"] * d_s * d_s / n_code
                    return r["k"]
                promising.sort(key=_rank_key, reverse=True)

                # Cheap challenge-target rejections must not consume the
                # expensive survivor budget.  Keep a larger deterministic,
                # stratified shortlist and evaluate it in refill waves below.
                # At most ``distance_selection_limit`` screen survivors ever
                # proceed through BP/OSD; terminal negatives are cheap.
                shortlist_limit = distance_selection_limit
                if not use_milp:
                    shortlist_limit = min(
                        len(promising),
                        distance_selection_limit
                        * STAGE2_DEEP_SCREEN_MULTIPLIER,
                    )

                # Pass 1: one per distinct k value
                seen_k: set[int] = set()
                top: list[dict] = []
                for r in promising:
                    if (
                        r["k"] not in seen_k
                        and len(top) < shortlist_limit
                    ):
                        seen_k.add(r["k"])
                        top.append(r)
                # Pass 2: one per distinct A polynomial (among same-k codes)
                seen_a: set[tuple] = {
                    tuple(sorted(map(tuple, r["A_terms"]))) for r in top
                }
                for r in promising:
                    if len(top) >= shortlist_limit:
                        break
                    a_key = tuple(sorted(map(tuple, r["A_terms"])))
                    if a_key not in seen_a and r not in top:
                        seen_a.add(a_key)
                        top.append(r)
                # Pass 3: fill remaining slots
                for r in promising:
                    if len(top) >= shortlist_limit:
                        break
                    if r not in top:
                        top.append(r)

                top, novelty_rejected = deduplicate_css_results(top)
                structural_rejected_count += len(novelty_rejected)
                rejected_keys = {
                    _definition_key(result) for result in novelty_rejected
                }
                quick_results = [
                    result for result in quick_results
                    if _definition_key(result) not in rejected_keys
                ]

                backend_error: dict[str, str] | None = None
                attempted: list[dict] = []
                results: list[dict] = []
                if use_milp:
                    attempted = list(top)
                    pending_top = [
                        _zero_distance_persistence_row(
                            result,
                            reason=DISTANCE_PENDING_PERSISTENCE_REASON,
                        )
                        for result in attempted
                    ]
                    for result in pending_top:
                        _log_code_jsonl(
                            result,
                            candidate_log_path=candidate_log_path,
                        )
                    distance_pending_persisted += len(pending_top)
                    top_candidates = [
                        _result_as_candidate(r) for r in attempted
                    ]
                    try:
                        # MILP: scale timeout with n.  The adaptive per-logical
                        # timeout in distance_milp.py uses max(8s, total/2k),
                        # so the total budget directly determines coverage.
                        # k=24 at n=288 with 240s: 8s/logical × 30 logicals
                        # (63% of 48).  Most codes solve instantly (d=2-4),
                        # so only 1-2 codes per lattice use the full budget.
                        n_code = 2 * ell * m
                        if n_code <= 200:
                            lat_timeout = min(milp_total_timeout, 120)
                            lat_per_log = min(milp_timeout_per_logical, 20)
                        elif n_code <= 300:
                            lat_timeout = min(milp_total_timeout, 240)
                            lat_per_log = min(milp_timeout_per_logical, 45)
                        else:
                            lat_timeout = milp_total_timeout
                            lat_per_log = milp_timeout_per_logical
                        results = evaluate_batch_milp(
                            ell, m, top_candidates,
                            milp_timeout_per_logical=lat_per_log,
                            milp_total_timeout=lat_timeout,
                            milp_early_stop=milp_early_stop,
                        )
                    except CandidateLogWriteError:
                        raise
                    except Exception as exc:
                        backend_error = _distance_backend_error_record(exc)
                        errors.append(
                            f"({ell},{m}): distance backend "
                            f"{backend_error['type']}: "
                            f"{backend_error['message']}"
                        )
                        distance_backend_error_count += 1
                        results = [
                            _zero_distance_persistence_row(
                                result,
                                reason=DISTANCE_ERROR_PERSISTENCE_REASON,
                                backend_error=backend_error,
                            )
                            for result in attempted
                        ]
                        distance_error_top_persisted += len(results)
                else:
                    # BP-family distances are upper bounds.  The challenge
                    # screen runs first inside evaluate_candidate; rejected
                    # rows do not consume one of the three BP/OSD survivor
                    # slots, so refill from the larger stratified shortlist.
                    survivor_count = 0
                    cursor = 0
                    while (
                        survivor_count < distance_selection_limit
                        and cursor < len(top)
                    ):
                        remaining = (
                            distance_selection_limit - survivor_count
                        )
                        wave = top[cursor:cursor + remaining]
                        cursor += len(wave)
                        attempted.extend(wave)
                        pending_wave = [
                            _zero_distance_persistence_row(
                                result,
                                reason=(
                                    DISTANCE_PENDING_PERSISTENCE_REASON
                                ),
                            )
                            for result in wave
                        ]
                        for result in pending_wave:
                            _log_code_jsonl(
                                result,
                                candidate_log_path=candidate_log_path,
                            )
                        distance_pending_persisted += len(pending_wave)
                        wave_candidates = [
                            _result_as_candidate(r) for r in wave
                        ]
                        try:
                            wave_results = evaluate_batch(
                                ell,
                                m,
                                wave_candidates,
                                quick=False,
                                quick_trials=refine_trials,
                                refine_trials=refine_trials,
                                fom_threshold_refine=6.0,
                                fom_threshold_osd_cs=8.0,
                                fom_threshold_exact=8.0,
                                skip_exact=True,
                                challenge_target_fom=(
                                    STAGE2_CHALLENGE_TARGET_FOM
                                ),
                                low_weight_oracle_max_weight=(
                                    STAGE2_LOW_WEIGHT_ORACLE_MAX_WEIGHT
                                ),
                                low_weight_oracle_hard_timeout_s=(
                                    STAGE2_LOW_WEIGHT_ORACLE_HARD_TIMEOUT_S
                                ),
                            )
                            expected_wave_keys = {
                                _candidate_definition_key(
                                    candidate,
                                    ell=ell,
                                    m=m,
                                )
                                for candidate in wave_candidates
                            }
                            observed_wave_keys = {
                                _definition_key(result)
                                for result in wave_results
                            }
                            if (
                                len(wave_results) != len(observed_wave_keys)
                                or observed_wave_keys != expected_wave_keys
                            ):
                                unresolved_label = (
                                    " unresolved"
                                    if all(
                                        not _has_positive_distance(result)
                                        for result in wave_results
                                    )
                                    else ""
                                )
                                raise CandidateLogWriteError(
                                    f"({ell},{m}): distance batch returned "
                                    f"{len(observed_wave_keys)}"
                                    f"{unresolved_label} definitions for a "
                                    f"top-{len(wave)} selection"
                                )
                        except CandidateLogWriteError:
                            raise
                        except Exception as exc:
                            backend_error = _distance_backend_error_record(exc)
                            errors.append(
                                f"({ell},{m}): distance backend "
                                f"{backend_error['type']}: "
                                f"{backend_error['message']}"
                            )
                            distance_backend_error_count += 1
                            wave_results = [
                                _zero_distance_persistence_row(
                                    result,
                                    reason=(
                                        DISTANCE_ERROR_PERSISTENCE_REASON
                                    ),
                                    backend_error=backend_error,
                                )
                                for result in wave
                            ]
                            distance_error_top_persisted += len(wave_results)
                            results.extend(wave_results)
                            break
                        results.extend(wave_results)
                        survivor_count += sum(
                            _consumes_stage2_survivor_budget(result)
                            for result in wave_results
                        )

                # The complete winner-capable pool is already durable. Retain
                # every unattempted sampled row as quick-only search evidence.
                # Only attempted rows receive selected-pending records.
                top = attempted
                top_keys = {_definition_key(result) for result in top}
                quick_only = [
                    r for r in quick_results if r.get("k", 0) > 0
                    and _definition_key(r) not in top_keys
                ]

                _annotate_generator_occurrences(
                    results,
                    ell=ell,
                    m=m,
                    occurrences=candidate_occurrences,
                )
                # Distance estimation can itself return an unresolved ``d=0``
                # row. Treat those selected-but-unresolved definitions exactly
                # like other quick-only candidates, instead of silently losing
                # them merely because they consumed a top-k slot.
                unresolved_top = [
                    result
                    for result in results
                    if (
                        result.get("k", 0) > 0
                        and not result.get("distance_backend_error")
                        and not _has_positive_distance(result)
                    )
                ]
                # Every unresolved result from the already-bounded top-k
                # universe is persisted first.  It must never compete with the
                # separate quick-only exploration quota: it already consumed a
                # distance slot and is stronger search evidence than an
                # arbitrary unmeasured definition.
                winner_capable_unresolved = [
                    result for result in unresolved_top
                    if _annotate_winner_capability(result)
                ]
                persisted_unresolved = _select_quick_exploration(
                    winner_capable_unresolved,
                    ell=ell,
                    m=m,
                    sampling_salt=sampling_salt,
                    # The producer contract bounds this list by the selected
                    # top-k universe. Use its observed size here so even a
                    # future batch adapter that violates that contract cannot
                    # turn the safety check itself into candidate loss.
                    limit=len(winner_capable_unresolved),
                )
                expected_unresolved = len({
                    _definition_key(result)
                    for result in winner_capable_unresolved
                })
                if expected_unresolved > len(top):
                    raise CandidateLogWriteError(
                        f"({ell},{m}): distance batch returned "
                        f"{expected_unresolved} unresolved definitions for a "
                        f"top-{len(top)} attempted selection"
                    )
                if len(persisted_unresolved) != expected_unresolved:
                    raise CandidateLogWriteError(
                        f"({ell},{m}): unresolved persistence invariant "
                        f"selected {len(persisted_unresolved)} of "
                        f"{expected_unresolved} canonical definitions"
                    )
                for result in persisted_unresolved:
                    result["candidate_persistence_lane"] = (
                        WINNER_CAPABLE_EXPLORATION_LANE
                    )
                    result["candidate_persistence_reason"] = (
                        UNRESOLVED_TOP_PERSISTENCE_REASON
                    )
                unresolved_top_persisted += len(persisted_unresolved)

                results.extend(quick_only)

            all_results.extend(results)

            # Log ALL codes with d > 0 to JSONL for Phase D pattern extraction
            for r in results:
                if (
                    r.get("candidate_persistence_reason")
                    in {
                        QUICK_EXPLORATION_PERSISTENCE_REASON,
                        FULL_POOL_PREFLIGHT_PERSISTENCE_REASON,
                    }
                    and _definition_key(r) in prelogged_quick_keys
                ):
                    continue
                _log_code_jsonl(
                    r,
                    candidate_log_path=candidate_log_path,
                )
            lattices_completed += 1
        except CandidateLogWriteError:
            # Persistence is part of a successful evaluation contract.  Let the
            # worker fail visibly instead of returning fitness for an unlogged
            # candidate that Stage 1 can never audit.
            raise
        except Exception as e:
            if not quick:
                # A deep lattice is complete only after its invocation-specific
                # frozen pool has passed the full write-ahead handoff. Returning
                # partial Stage 2 fitness would make a failed pool look audited.
                raise CandidateLogWriteError(
                    f"({ell},{m}): deep frozen-pool evaluation failed: "
                    f"{type(e).__name__}: {e}"
                ) from e
            errors.append(f"({ell},{m}): {type(e).__name__}: {e}")
            lattice_failures += 1

    # Compute aggregate metrics using encoding rate (exact) and FOM (approximate)
    valid = [r for r in all_results if r.get("k", 0) > 0]
    foms = [r.get("fom", 0.0) for r in valid if r.get("fom", 0.0) > 0]
    encoding_rates = [r.get("encoding_rate", 0.0) for r in valid]

    best_fom = max(foms) if foms else 0.0
    mean_fom = sum(foms) / len(foms) if foms else 0.0
    num_above_6 = sum(1 for f in foms if f >= 6.0)
    num_above_12 = sum(1 for f in foms if f >= 12.0)
    best_encoding_rate = max(encoding_rates) if encoding_rates else 0.0

    # Count high-k codes (k >= 8) -- exact metric, not affected by BP-OSD
    high_k_codes = [r for r in valid if r.get("k", 0) >= 8]
    # Count lattices with at least one high-k code (breadth across lattices)
    lattices_with_high_k = len(set(
        (r["ell"], r["m"]) for r in high_k_codes
    ))

    # Find the best code for reporting
    best_code = None
    if all_results:
        best_result = max(all_results, key=lambda r: r.get("fom", 0.0))
        if best_result.get("fom", 0.0) > 0:
            best_code = best_result

    support_partition_complete = int(
        unique_candidates
        == support_weight_eligible + support_weight_rejected
    )
    support_evaluation_coverage = (
        support_weight_evaluated / support_weight_eligible
        if support_weight_eligible
        else 1.0
    )
    support_weight_eligible_fraction = (
        support_weight_eligible / unique_candidates
        if unique_candidates
        else 0.0
    )
    support_weight_rejection_fraction = (
        support_weight_rejected / unique_candidates
        if unique_candidates
        else 0.0
    )
    support_splits_covered = sum(
        count > 0 for count in support_split_counts.values()
    )
    support_split_coverage = (
        support_splits_covered / len(CHALLENGE_SUPPORT_SPLITS)
    )
    support_lattice_split_total = (
        len(lattices) * len(CHALLENGE_SUPPORT_SPLITS)
    )
    support_split_lattice_coverage = (
        len(support_lattice_splits) / support_lattice_split_total
        if support_lattice_split_total
        else 1.0
    )
    geometry_twist_coverage = (
        geometry_twists_observed / geometry_twists_required
        if geometry_twists_required
        else 1.0
    )
    geometry_twist_coverage_complete = int(
        geometry_twists_observed == geometry_twists_required
    )

    return {
        "best_fom": best_fom,
        "mean_fom": mean_fom,
        "num_valid": len(valid),
        "num_above_6": num_above_6,
        "num_above_12": num_above_12,
        "total_candidates": total_candidates,
        "unique_candidates": unique_candidates,
        "evaluated_candidate_definitions": evaluated_candidate_definitions,
        "duplicate_candidate_occurrences": duplicate_candidate_occurrences,
        "winner_capable_quick_exploration_eligible": (
            quick_exploration_eligible
        ),
        "winner_capable_quick_exploration_persisted": (
            quick_exploration_persisted
        ),
        "winner_capable_quick_exploration_omitted": (
            quick_exploration_omitted
        ),
        "winner_capable_distance_pending_persisted": (
            distance_pending_persisted
        ),
        "winner_capable_unresolved_top_persisted": unresolved_top_persisted,
        "winner_capable_distance_error_persisted": (
            distance_error_top_persisted
        ),
        "distance_backend_error_count": distance_backend_error_count,
        "malformed_candidate_definitions": malformed_candidate_definitions,
        "tier0_rejected": tier0_rejected_count,
        "structural_rejected": structural_rejected_count,
        SUPPORT_FILTER_VERSION_METRIC: CHALLENGE_SUPPORT_FILTER_VERSION,
        SUPPORT_WEIGHT_ELIGIBLE_METRIC: support_weight_eligible,
        SUPPORT_WEIGHT_REJECTED_METRIC: support_weight_rejected,
        SUPPORT_WEIGHT_EVALUATED_METRIC: support_weight_evaluated,
        SUPPORT_WEIGHT_PARTITION_COMPLETE_METRIC: (
            support_partition_complete
        ),
        SUPPORT_WEIGHT_EVALUATION_COVERAGE_METRIC: (
            support_evaluation_coverage
        ),
        SUPPORT_WEIGHT_ELIGIBLE_FRACTION_METRIC: (
            support_weight_eligible_fraction
        ),
        SUPPORT_WEIGHT_REJECTION_FRACTION_METRIC: (
            support_weight_rejection_fraction
        ),
        SUPPORT_SPLITS_COVERED_METRIC: support_splits_covered,
        SUPPORT_SPLITS_TOTAL_METRIC: len(CHALLENGE_SUPPORT_SPLITS),
        SUPPORT_SPLIT_COVERAGE_METRIC: support_split_coverage,
        SUPPORT_SPLIT_LATTICE_COVERAGE_METRIC: (
            support_split_lattice_coverage
        ),
        **({
            GEOMETRY_TWISTS_REQUIRED_METRIC: geometry_twists_required,
            GEOMETRY_TWISTS_OBSERVED_METRIC: geometry_twists_observed,
            GEOMETRY_TWIST_COVERAGE_METRIC: geometry_twist_coverage,
            GEOMETRY_TWIST_COVERAGE_COMPLETE_METRIC: (
                geometry_twist_coverage_complete
            ),
        } if is_twisted_geometry_contract(ACTIVE_GEOMETRY_CONTRACT) else {}),
        "support_split_counts": {
            f"{a_count}+{b_count}": support_split_counts[
                (a_count, b_count)
            ]
            for a_count, b_count in CHALLENGE_SUPPORT_SPLITS
        },
        "support_weight_rejection_splits": {
            f"{a_count}+{b_count}": count
            for (a_count, b_count), count in sorted(
                support_rejection_split_counts.items()
            )
        },
        PATTERN_CLASSIFIER_VERSION_METRIC: PATTERN_CLASSIFIER_VERSION,
        "lattices_requested": len(lattices),
        "lattices_completed": lattices_completed,
        "lattice_failures": lattice_failures,
        "best_encoding_rate": best_encoding_rate,
        "num_high_k": len(high_k_codes),
        "lattices_with_high_k": lattices_with_high_k,
        "best_code": best_code,
        "all_results": all_results,
        "errors": errors,
    }


def _winner_preflight_markers(
    metrics: dict,
    *,
    contract_id: int,
) -> dict[str, float]:
    """Validate a full quick preflight and return checkpoint-safe metrics."""

    _require_complete_support_evaluation(
        metrics,
        label="winner preflight",
    )
    eligible = int(
        metrics.get("winner_capable_quick_exploration_eligible", -1)
    )
    persisted = int(
        metrics.get("winner_capable_quick_exploration_persisted", -1)
    )
    omitted = int(
        metrics.get("winner_capable_quick_exploration_omitted", -1)
    )
    completed = int(metrics.get("lattices_completed", -1))
    failures = int(metrics.get("lattice_failures", -1))
    if (
        completed != len(EVOLUTION_LATTICES)
        or failures != 0
        or eligible < 0
        or persisted != eligible
        or omitted != 0
    ):
        raise CandidateLogWriteError(
            "winner preflight did not complete its full persistence "
            f"contract: lattices={completed}/{len(EVOLUTION_LATTICES)}, "
            f"failures={failures}, eligible={eligible}, "
            f"persisted={persisted}, omitted={omitted}"
        )
    return {
        WINNER_PREFLIGHT_CONTRACT_VERSION_METRIC: float(
            WINNER_PREFLIGHT_CONTRACT_VERSION
        ),
        WINNER_PREFLIGHT_CONTRACT_ID_METRIC: float(contract_id),
        WINNER_PREFLIGHT_COMPLETE_METRIC: 1.0,
        WINNER_PREFLIGHT_INCOMPLETE_METRIC: 0.0,
        WINNER_PREFLIGHT_LATTICES_METRIC: float(len(EVOLUTION_LATTICES)),
        WINNER_PREFLIGHT_EVALUATED_METRIC: float(
            metrics.get("evaluated_candidate_definitions", 0)
        ),
        WINNER_PREFLIGHT_ELIGIBLE_METRIC: float(eligible),
        WINNER_PREFLIGHT_PERSISTED_METRIC: float(persisted),
        WINNER_PREFLIGHT_OMITTED_METRIC: 0.0,
        WINNER_PREFLIGHT_HARD_TIMEOUT_METRIC: 0.0,
        WINNER_PREFLIGHT_SUBPROCESS_FAILED_METRIC: 0.0,
    }


def _require_complete_support_evaluation(
    metrics: dict,
    *,
    label: str,
) -> None:
    """Prove that the cheap support partition covered its eligible side.

    Full-pool persistence now means the complete *challenge-supported* pool:
    every normalized canonical definition is deterministically assigned to
    either the eligible or support-weight-rejected partition, and every
    eligible definition reaches the quick evaluator before winner-capable
    rows are selected for persistence.
    """

    version = _exact_nonnegative_preflight_metric(
        metrics, SUPPORT_FILTER_VERSION_METRIC
    )
    unique = _exact_nonnegative_preflight_metric(
        metrics, "unique_candidates"
    )
    eligible = _exact_nonnegative_preflight_metric(
        metrics, SUPPORT_WEIGHT_ELIGIBLE_METRIC
    )
    rejected = _exact_nonnegative_preflight_metric(
        metrics, SUPPORT_WEIGHT_REJECTED_METRIC
    )
    evaluated = _exact_nonnegative_preflight_metric(
        metrics, SUPPORT_WEIGHT_EVALUATED_METRIC
    )
    reported_evaluated = _exact_nonnegative_preflight_metric(
        metrics, "evaluated_candidate_definitions"
    )
    partition_complete = _exact_nonnegative_preflight_metric(
        metrics, SUPPORT_WEIGHT_PARTITION_COMPLETE_METRIC
    )
    twisted_contract = (
        is_twisted_geometry_contract(ACTIVE_GEOMETRY_CONTRACT)
    )
    twists_required = (
        _exact_nonnegative_preflight_metric(
            metrics, GEOMETRY_TWISTS_REQUIRED_METRIC
        )
        if twisted_contract else 0
    )
    twists_observed = (
        _exact_nonnegative_preflight_metric(
            metrics, GEOMETRY_TWISTS_OBSERVED_METRIC
        )
        if twisted_contract else 0
    )
    twist_coverage_complete = (
        _exact_nonnegative_preflight_metric(
            metrics, GEOMETRY_TWIST_COVERAGE_COMPLETE_METRIC
        )
        if twisted_contract else 1
    )
    if (
        version != CHALLENGE_SUPPORT_FILTER_VERSION
        or partition_complete != 1
        or unique != eligible + rejected
        or evaluated != eligible
        or reported_evaluated != evaluated
        or (
            twisted_contract
            and (
                twist_coverage_complete != 1
                or twists_observed != twists_required
            )
        )
    ):
        raise CandidateLogWriteError(
            f"{label} did not completely cover the challenge support "
            f"partition: version={version}, unique={unique}, "
            f"eligible={eligible}, rejected={rejected}, "
            f"evaluated={evaluated}, partition_complete="
            f"{partition_complete}, twists={twists_observed}/"
            f"{twists_required}"
        )


def _require_full_pool_persistence(
    metrics: dict,
    *,
    expected_lattices: int,
    label: str,
) -> None:
    """Reject partial quick passes before their results can affect fitness."""

    _require_complete_support_evaluation(metrics, label=label)
    completed = _exact_nonnegative_preflight_metric(
        metrics, "lattices_completed"
    )
    failures = _exact_nonnegative_preflight_metric(
        metrics, "lattice_failures"
    )
    eligible = _exact_nonnegative_preflight_metric(
        metrics, "winner_capable_quick_exploration_eligible"
    )
    persisted = _exact_nonnegative_preflight_metric(
        metrics, "winner_capable_quick_exploration_persisted"
    )
    omitted = _exact_nonnegative_preflight_metric(
        metrics, "winner_capable_quick_exploration_omitted"
    )
    if (
        completed != expected_lattices
        or failures != 0
        or persisted != eligible
        or omitted != 0
    ):
        raise CandidateLogWriteError(
            f"{label} did not complete full-pool persistence: "
            f"lattices={completed}/{expected_lattices}, "
            f"failures={failures}, eligible={eligible}, "
            f"persisted={persisted}, omitted={omitted}"
        )


def _support_observability_metrics(metrics: dict) -> dict[str, float]:
    """Return the numeric support-filter metrics safe for OpenEvolve."""

    names = (
        SUPPORT_FILTER_VERSION_METRIC,
        SUPPORT_WEIGHT_ELIGIBLE_METRIC,
        SUPPORT_WEIGHT_REJECTED_METRIC,
        SUPPORT_WEIGHT_EVALUATED_METRIC,
        SUPPORT_WEIGHT_PARTITION_COMPLETE_METRIC,
        SUPPORT_WEIGHT_EVALUATION_COVERAGE_METRIC,
        SUPPORT_WEIGHT_ELIGIBLE_FRACTION_METRIC,
        SUPPORT_WEIGHT_REJECTION_FRACTION_METRIC,
        SUPPORT_SPLITS_COVERED_METRIC,
        SUPPORT_SPLITS_TOTAL_METRIC,
        SUPPORT_SPLIT_COVERAGE_METRIC,
        SUPPORT_SPLIT_LATTICE_COVERAGE_METRIC,
        *((
            GEOMETRY_TWISTS_REQUIRED_METRIC,
            GEOMETRY_TWISTS_OBSERVED_METRIC,
            GEOMETRY_TWIST_COVERAGE_METRIC,
            GEOMETRY_TWIST_COVERAGE_COMPLETE_METRIC,
        ) if is_twisted_geometry_contract(ACTIVE_GEOMETRY_CONTRACT) else ()),
        PATTERN_CLASSIFIER_VERSION_METRIC,
    )
    return {name: float(metrics.get(name, 0)) for name in names}


def _run_full_winner_preflight(
    generate_fn,
    *,
    sampling_salt: str,
    contract_id: int,
    run_name: str = "",
    candidate_log_path: str | Path | None = None,
) -> dict[str, float]:
    """Persist the complete supported winner-capable universe without a cap."""

    metrics = _run_evaluation(
        generate_fn,
        list(EVOLUTION_LATTICES),
        quick=True,
        run_name=run_name,
        candidate_log_path=candidate_log_path,
        sampling_salt=sampling_salt,
        candidate_limit=None,
        persist_quick_exploration=True,
        persist_all_quick_exploration=True,
    )
    return _winner_preflight_markers(metrics, contract_id=contract_id)


def _preflight_program(program_path: str) -> dict[str, float]:
    """Run only the durable winner preflight used by checkpoint backfill."""

    # Capture the contract before importing evolved code.  A generated module
    # may legitimately mutate process environment for its own algorithm, but
    # it cannot change which managed contract this evaluation is proving.
    contract_id = _current_winner_preflight_contract_id()
    candidate_log_path = _freeze_candidate_log_path()
    source_sha256 = _freeze_program_source_sha256(program_path)
    load_generate_candidates = _load_generate_candidates
    run_full_winner_preflight = _run_full_winner_preflight
    generate_fn = load_generate_candidates(program_path)
    _assert_program_source_unchanged(program_path, source_sha256)
    markers = run_full_winner_preflight(
        generate_fn,
        sampling_salt=source_sha256,
        contract_id=contract_id,
        candidate_log_path=candidate_log_path,
    )
    _assert_program_source_unchanged(program_path, source_sha256)
    return markers


def _evaluate_stage1_impl(
    program_path: str,
    *,
    generate_fn=None,
    preflight_markers: dict[str, float] | None = None,
    candidate_log_path: Path | None = None,
    source_sha256: str | None = None,
) -> dict:
    """Stage 1: score two quick probes after the durable full preflight.

    Broad programs with valid codes on both probes receive the normal fitness
    score. A deterministic 1/N sample of programs that fail full probe
    coverage receives a low-priority score just above the cascade threshold.
    This keeps the cheap probes useful without permanently excluding a
    strategy specialized for larger lattices.

    Score components (all lattices covered):
    - 0.1 base: guarantees passing cascade threshold (0.01)
    - best_rate: peak encoding rate (up to ~0.17 for k=12 at n=72)
    - high_k_quality: log-scaled count of k≥8 codes (diminishing returns,
      prevents gaming by sparse generators that score high on ratios)
    Total range: ~0.11 (barely alive) to ~0.8 (excellent), giving
    MAP-Elites ~7x differentiation vs the prior 15% spread.
    """
    contract_id = _current_winner_preflight_contract_id()
    if candidate_log_path is None:
        candidate_log_path = _freeze_candidate_log_path()
    else:
        candidate_log_path = _freeze_candidate_log_path(candidate_log_path)
    if source_sha256 is None:
        source_sha256 = _freeze_program_source_sha256(program_path)
    else:
        _assert_program_source_unchanged(program_path, source_sha256)
    load_generate_candidates = _load_generate_candidates
    run_full_winner_preflight = _run_full_winner_preflight
    run_evaluation = _run_evaluation
    if generate_fn is None:
        try:
            generate_fn = load_generate_candidates(program_path)
        except Exception as e:
            return _error_result(str(e))

    _assert_program_source_unchanged(program_path, source_sha256)
    if preflight_markers is None:
        preflight_markers = run_full_winner_preflight(
            generate_fn,
            sampling_salt=source_sha256,
            contract_id=contract_id,
            candidate_log_path=candidate_log_path,
        )
    else:
        preflight_markers = _validated_complete_preflight_markers(
            preflight_markers,
            expected_contract_id=contract_id,
        )
    _assert_program_source_unchanged(program_path, source_sha256)
    # Preserve the historical two-probe Stage 1 fitness scale after the
    # persistence-only full contract has completed.  This second cheap call is
    # intentional: adding target lattices must not distort resumed MAP-Elites
    # cells or turn the preflight into a new fitness objective.
    metrics = run_evaluation(
        generate_fn,
        STAGE1_LATTICES,
        quick=True,
        candidate_log_path=candidate_log_path,
        sampling_salt=source_sha256,
        persist_quick_exploration=True,
        persist_all_quick_exploration=True,
    )
    _require_full_pool_persistence(
        metrics,
        expected_lattices=len(STAGE1_LATTICES),
        label="Stage 1 historical fitness pass",
    )
    _assert_program_source_unchanged(program_path, source_sha256)
    specialist_exploration = _stage1_specialist_exploration_pass(program_path)

    if metrics["total_candidates"] == 0:
        if specialist_exploration:
            result = {
                "combined_score": 0.02,
                "num_valid": 0.0,
                "total_candidates": 0.0,
                "lattices_with_high_k": 0.0,
                "num_high_k": 0.0,
                "specialist_exploration": 1.0,
            }
            result.update(_pool_map_descriptor([]))
            result.update(_support_observability_metrics(metrics))
            result.update(preflight_markers)
            return result
        result = {
            "combined_score": 0.0,
            "num_valid": 0.0,
            "total_candidates": 0.0,
            "lattices_with_high_k": 0.0,
            "num_high_k": 0.0,
        }
        result.update(_pool_map_descriptor([]))
        result.update(_support_observability_metrics(metrics))
        result.update(preflight_markers)
        return result

    valid = [r for r in metrics.get("all_results", []) if r.get("k", 0) > 0]

    # Measure broad small-lattice coverage for the normal fitness lane.
    lattices_with_valid = set(
        (r["ell"], r["m"]) for r in valid
    )
    lattice_coverage = len(lattices_with_valid) / len(STAGE1_LATTICES)

    if lattice_coverage < 1.0:
        # A generator specialized for a larger modulus need not be good on both
        # tiny probes. A deterministic 1/N sample lets such specialists escape
        # the absolute gate without promoting every partial-coverage program.
        if specialist_exploration:
            score = 0.02
        else:
            score = len(lattices_with_valid) * 0.001
    else:
        # All lattices covered. Score by quality.
        best_rate = max(r.get("encoding_rate", 0.0) for r in valid)
        # Log-scaled count: rewards breadth without letting sparse
        # generators game the score (2 codes → 0.11, 259 codes → 0.56)
        high_k_quality = math.log1p(metrics["num_high_k"]) / 10.0
        score = 0.1 + best_rate + high_k_quality

    map_descriptor = _pool_map_descriptor(
        metrics.get("all_results", []),
        lattices=set(STAGE1_LATTICES),
    )

    result = {
        "combined_score": score,
        "num_valid": float(metrics["num_valid"]),
        "total_candidates": float(metrics["total_candidates"]),
        "lattices_with_high_k": float(metrics["lattices_with_high_k"]),
        "num_high_k": float(metrics["num_high_k"]),
        "specialist_exploration": float(
            lattice_coverage < 1.0 and specialist_exploration
        ),
    }
    result.update(map_descriptor)
    result.update(_support_observability_metrics(metrics))
    result.update(preflight_markers)
    return result


def _run_resumable_winner_preflight(
    program_path: str,
    *,
    _candidate_restart_budget: int = (
        STAGE1_PREFLIGHT_MAX_EPOCH_ATTEMPTS - 1
    ),
) -> tuple[dict[str, float], object, Path, str]:
    """Run the complete preflight as durable, per-lattice transactions.

    The worker process stays alive while progress is being made, so stateful
    generators retain their historical call order.  If the worker is killed
    externally, a replacement deterministically replays committed generator
    calls and verifies their canonical pool digests before continuing.
    """

    contract_id = _current_winner_preflight_contract_id()
    candidate_log_path = _freeze_candidate_log_path()
    source_sha256 = _freeze_program_source_sha256(program_path)
    journal_path, _lock_path = _stage1_preflight_journal_paths(
        candidate_log_path,
        source_sha256=source_sha256,
        contract_id=contract_id,
    )
    journal = _load_stage1_preflight_journal(
        journal_path,
        source_sha256=source_sha256,
        contract_id=contract_id,
        candidate_log_path=candidate_log_path,
    )
    if not _path_entry_exists(journal_path):
        journal = _write_stage1_preflight_journal(
            journal_path,
            journal,
            source_sha256=source_sha256,
            contract_id=contract_id,
            candidate_log_path=candidate_log_path,
        )
    try:
        recovered = _recover_stage1_lattice_commits(
            candidate_log_path,
            journal,
        )
    except Stage1CandidateCommitMismatch:
        journal = _restart_stage1_preflight_journal(
            journal_path,
            journal,
            source_sha256=source_sha256,
            contract_id=contract_id,
            candidate_log_path=candidate_log_path,
        )
        recovered = journal
    if recovered != journal:
        journal = _write_stage1_preflight_journal(
            journal_path,
            recovered,
            source_sha256=source_sha256,
            contract_id=contract_id,
            candidate_log_path=candidate_log_path,
        )

    generate_fn = _load_generate_candidates(program_path)
    _assert_program_source_unchanged(program_path, source_sha256)
    completed = list(journal["completed_lattices"])

    for index, lattice in enumerate(EVOLUTION_LATTICES):
        generated = generate_fn(lattice[0], lattice[1])
        _assert_program_source_unchanged(program_path, source_sha256)
        pool_sha256 = _generated_pool_sha256(
            generated,
            lattice=lattice,
        )
        if index < len(completed):
            if completed[index]["pool_sha256"] != pool_sha256:
                raise CandidateLogWriteError(
                    "Stage 1 generator replay changed the committed pool at "
                    f"lattice {lattice}"
                )
            journal = _write_stage1_preflight_journal(
                journal_path,
                {
                    **journal,
                    "progress_sequence": int(
                        journal["progress_sequence"]
                    ) + 1,
                },
                source_sha256=source_sha256,
                contract_id=contract_id,
                candidate_log_path=candidate_log_path,
            )
            continue

        def frozen_generate(ell: int, m: int):
            if (ell, m) != lattice:
                raise CandidateLogWriteError(
                    "Stage 1 lattice evaluator requested a different lattice"
                )
            return generated

        with tempfile.TemporaryDirectory(
            prefix="qcode-stage1-lattice-"
        ) as spool_root:
            spool_path = Path(spool_root) / "candidates.jsonl"
            metrics = _run_evaluation(
                frozen_generate,
                [lattice],
                quick=True,
                candidate_log_path=spool_path,
                sampling_salt=source_sha256,
                candidate_limit=None,
                persist_quick_exploration=True,
                persist_all_quick_exploration=True,
            )
            metrics[STAGE1_CANDIDATE_LOG_RECORDS_FIELD] = len(
                _stage1_lattice_spool_rows(spool_path)
            )
            summary = _stage1_lattice_summary(
                metrics,
                lattice=lattice,
                pool_sha256=pool_sha256,
            )
            commit_payload = _stage1_lattice_commit_payload(
                spool_path,
                source_sha256=source_sha256,
                contract_id=contract_id,
                epoch_id=str(journal["epoch_id"]),
                lattice=lattice,
                summary=summary,
            )
            if commit_payload:
                _append_candidate_jsonl(
                    candidate_log_path,
                    commit_payload,
                )

        completed.append(summary)
        journal = _write_stage1_preflight_journal(
            journal_path,
            {
                **journal,
                "status": "in_progress",
                "completed_lattices": completed,
                "progress_sequence": int(
                    journal["progress_sequence"]
                ) + 1,
                "markers": None,
            },
            source_sha256=source_sha256,
            contract_id=contract_id,
            candidate_log_path=candidate_log_path,
        )

    try:
        verified = _recover_stage1_lattice_commits(
            candidate_log_path,
            journal,
        )
    except Stage1CandidateCommitMismatch:
        if _candidate_restart_budget <= 0:
            raise
        _restart_stage1_preflight_journal(
            journal_path,
            journal,
            source_sha256=source_sha256,
            contract_id=contract_id,
            candidate_log_path=candidate_log_path,
        )
        return _run_resumable_winner_preflight(
            program_path,
            _candidate_restart_budget=_candidate_restart_budget - 1,
        )
    if verified != journal:
        journal = _write_stage1_preflight_journal(
            journal_path,
            verified,
            source_sha256=source_sha256,
            contract_id=contract_id,
            candidate_log_path=candidate_log_path,
        )
        completed = list(journal["completed_lattices"])

    aggregate = _aggregate_stage1_lattice_summaries(completed)
    markers = _winner_preflight_markers(
        aggregate,
        contract_id=contract_id,
    )
    if journal["status"] != "completed":
        journal = _write_stage1_preflight_journal(
            journal_path,
            {
                **journal,
                "status": "completed",
                "completed_lattices": completed,
                "progress_sequence": int(
                    journal["progress_sequence"]
                ) + 1,
                "markers": markers,
            },
            source_sha256=source_sha256,
            contract_id=contract_id,
            candidate_log_path=candidate_log_path,
        )
    else:
        markers = dict(journal["markers"])

    _assert_program_source_unchanged(program_path, source_sha256)
    return markers, generate_fn, candidate_log_path, source_sha256


def _evaluate_stage1_resumable_impl(program_path: str) -> dict:
    (
        markers,
        generate_fn,
        candidate_log_path,
        source_sha256,
    ) = _run_resumable_winner_preflight(program_path)
    return _evaluate_stage1_impl(
        program_path,
        generate_fn=generate_fn,
        preflight_markers=markers,
        candidate_log_path=candidate_log_path,
        source_sha256=source_sha256,
    )


def _stage2_preflight_sha256(
    markers: dict[str, float] | None,
    *,
    contract_id: int,
) -> str:
    """Bind a deep-evaluation journal to its exact Stage 1 handoff."""

    if markers is None:
        payload: object = {"mode": "direct-stage2-preflight"}
    else:
        payload = _validated_complete_preflight_markers(
            markers,
            expected_contract_id=contract_id,
        )
    encoded = json.dumps(
        payload,
        sort_keys=True,
        separators=(",", ":"),
        allow_nan=False,
    ).encode("utf-8")
    return hashlib.sha256(encoded).hexdigest()


def _stage2_deep_journal_paths(
    candidate_log_path: Path,
    *,
    source_sha256: str,
    contract_id: int,
    preflight_sha256: str,
) -> tuple[Path, Path]:
    journal_root = (
        candidate_log_path.parent / STAGE2_DEEP_JOURNAL_DIRECTORY
    )
    journal_root.mkdir(parents=True, exist_ok=True)
    if journal_root.is_symlink() or not journal_root.is_dir():
        raise CandidateLogWriteError(
            f"Stage 2 journal root is unsafe: {journal_root}"
        )
    stem = (
        f"{contract_id}-{source_sha256}-"
        f"{preflight_sha256[:16]}"
    )
    return journal_root / f"{stem}.json", journal_root / f"{stem}.lock"


def _stage2_lattice_result_path(
    journal_path: Path,
    *,
    epoch_id: str,
    index: int,
) -> Path:
    return journal_path.parent / (
        f"{journal_path.stem}-{epoch_id}-{index:03d}.result.json"
    )


def _initial_stage2_deep_journal(
    *,
    source_sha256: str,
    contract_id: int,
    candidate_log_path: Path,
    preflight_sha256: str,
) -> dict[str, object]:
    return {
        "schema_version": STAGE2_DEEP_JOURNAL_SCHEMA_VERSION,
        "status": "in_progress",
        "program_sha256": source_sha256,
        "contract_id": contract_id,
        "candidate_log_path": str(candidate_log_path),
        "preflight_sha256": preflight_sha256,
        "epoch_id": os.urandom(32).hex(),
        "lattices": [list(lattice) for lattice in STAGE2_DEEP_LATTICES],
        "completed_lattices": [],
        "progress_sequence": 0,
    }


def _valid_sha256(value: object) -> bool:
    return (
        isinstance(value, str)
        and len(value) == 64
        and all(character in "0123456789abcdef" for character in value)
    )


def _validated_stage2_lattice_entry(
    entry: object,
    *,
    expected_lattice: tuple[int, int],
) -> dict[str, object]:
    expected_fields = {
        "lattice",
        "pool_sha256",
        "result_sha256",
        "result_bytes",
    }
    if not isinstance(entry, dict) or set(entry) != expected_fields:
        raise CandidateLogWriteError(
            "Stage 2 lattice journal entry schema is invalid"
        )
    if entry.get("lattice") != list(expected_lattice):
        raise CandidateLogWriteError(
            "Stage 2 lattice journal entry has the wrong lattice"
        )
    if (
        not _valid_sha256(entry.get("pool_sha256"))
        or not _valid_sha256(entry.get("result_sha256"))
        or type(entry.get("result_bytes")) is not int
        or entry["result_bytes"] <= 0
    ):
        raise CandidateLogWriteError(
            "Stage 2 lattice journal entry binding is invalid"
        )
    return {
        "lattice": list(expected_lattice),
        "pool_sha256": str(entry["pool_sha256"]),
        "result_sha256": str(entry["result_sha256"]),
        "result_bytes": int(entry["result_bytes"]),
    }


def _validated_stage2_deep_journal(
    payload: object,
    *,
    source_sha256: str,
    contract_id: int,
    candidate_log_path: Path,
    preflight_sha256: str,
) -> dict[str, object]:
    expected_fields = {
        "schema_version",
        "status",
        "program_sha256",
        "contract_id",
        "candidate_log_path",
        "preflight_sha256",
        "epoch_id",
        "lattices",
        "completed_lattices",
        "progress_sequence",
    }
    if not isinstance(payload, dict) or set(payload) != expected_fields:
        raise CandidateLogWriteError("Stage 2 journal schema is invalid")
    completed = payload.get("completed_lattices")
    epoch_id = payload.get("epoch_id")
    expected_lattices = [
        list(lattice) for lattice in STAGE2_DEEP_LATTICES
    ]
    if (
        payload.get("schema_version")
        != STAGE2_DEEP_JOURNAL_SCHEMA_VERSION
        or payload.get("status") not in {"in_progress", "completed"}
        or payload.get("program_sha256") != source_sha256
        or payload.get("contract_id") != contract_id
        or payload.get("candidate_log_path") != str(candidate_log_path)
        or payload.get("preflight_sha256") != preflight_sha256
        or not _valid_sha256(epoch_id)
        or payload.get("lattices") != expected_lattices
        or not isinstance(completed, list)
        or len(completed) > len(expected_lattices)
        or type(payload.get("progress_sequence")) is not int
        or payload["progress_sequence"] < len(completed)
        or (
            payload.get("status") == "completed"
            and len(completed) != len(expected_lattices)
        )
        or (
            payload.get("status") == "in_progress"
            and len(completed) == len(expected_lattices)
        )
    ):
        raise CandidateLogWriteError("Stage 2 journal binding is invalid")
    normalized = [
        _validated_stage2_lattice_entry(
            entry,
            expected_lattice=STAGE2_DEEP_LATTICES[index],
        )
        for index, entry in enumerate(completed)
    ]
    return {
        **payload,
        "epoch_id": str(epoch_id),
        "completed_lattices": normalized,
        "progress_sequence": int(payload["progress_sequence"]),
    }


def _load_stage2_deep_journal(
    journal_path: Path,
    *,
    source_sha256: str,
    contract_id: int,
    candidate_log_path: Path,
    preflight_sha256: str,
) -> dict[str, object]:
    if not _path_entry_exists(journal_path):
        return _initial_stage2_deep_journal(
            source_sha256=source_sha256,
            contract_id=contract_id,
            candidate_log_path=candidate_log_path,
            preflight_sha256=preflight_sha256,
        )
    if journal_path.is_symlink() or not journal_path.is_file():
        raise CandidateLogWriteError(
            f"Stage 2 journal is not a regular file: {journal_path}"
        )
    try:
        payload = json.loads(journal_path.read_text())
    except (OSError, UnicodeDecodeError, json.JSONDecodeError) as exc:
        raise CandidateLogWriteError(
            f"Stage 2 journal is unreadable: {journal_path}"
        ) from exc
    return _validated_stage2_deep_journal(
        payload,
        source_sha256=source_sha256,
        contract_id=contract_id,
        candidate_log_path=candidate_log_path,
        preflight_sha256=preflight_sha256,
    )


def _write_stage2_deep_journal(
    journal_path: Path,
    payload: dict[str, object],
    *,
    source_sha256: str,
    contract_id: int,
    candidate_log_path: Path,
    preflight_sha256: str,
) -> dict[str, object]:
    normalized = _validated_stage2_deep_journal(
        payload,
        source_sha256=source_sha256,
        contract_id=contract_id,
        candidate_log_path=candidate_log_path,
        preflight_sha256=preflight_sha256,
    )
    if journal_path.is_symlink():
        raise CandidateLogWriteError(
            f"refusing to replace symlinked Stage 2 journal: {journal_path}"
        )
    encoded = json.dumps(
        normalized,
        sort_keys=True,
        separators=(",", ":"),
        allow_nan=False,
    ).encode("utf-8")
    temporary = journal_path.with_name(
        f".{journal_path.name}.tmp-{os.getpid()}-"
        f"{threading.get_ident()}-{time.time_ns()}"
    )
    flags = os.O_WRONLY | os.O_CREAT | os.O_EXCL | os.O_CLOEXEC
    if hasattr(os, "O_NOFOLLOW"):
        flags |= os.O_NOFOLLOW
    descriptor = os.open(temporary, flags, 0o600)
    try:
        _write_all(descriptor, encoded)
        os.fsync(descriptor)
    finally:
        os.close(descriptor)
    os.replace(temporary, journal_path)
    directory_descriptor = os.open(
        journal_path.parent,
        os.O_RDONLY | os.O_CLOEXEC | getattr(os, "O_DIRECTORY", 0),
    )
    try:
        os.fsync(directory_descriptor)
    finally:
        os.close(directory_descriptor)
    return normalized


def _validated_stage2_lattice_metrics(
    metrics: object,
    *,
    lattice: tuple[int, int],
) -> dict:
    if not isinstance(metrics, dict):
        raise CandidateLogWriteError(
            "Stage 2 lattice result metrics are not an object"
        )
    try:
        normalized = json.loads(json.dumps(
            metrics,
            sort_keys=True,
            separators=(",", ":"),
            allow_nan=False,
        ))
    except (TypeError, ValueError) as exc:
        raise CandidateLogWriteError(
            "Stage 2 lattice result metrics are not strict JSON"
        ) from exc
    _require_full_pool_persistence(
        normalized,
        expected_lattices=1,
        label=f"Stage 2 deep lattice {lattice}",
    )
    if (
        _exact_nonnegative_preflight_metric(
            normalized, "lattices_requested"
        ) != 1
        or _exact_nonnegative_preflight_metric(
            normalized, "lattices_completed"
        ) != 1
        or _exact_nonnegative_preflight_metric(
            normalized, "lattice_failures"
        ) != 0
        or _exact_nonnegative_preflight_metric(
            normalized, PATTERN_CLASSIFIER_VERSION_METRIC
        ) != PATTERN_CLASSIFIER_VERSION
    ):
        raise CandidateLogWriteError(
            "Stage 2 lattice result is incomplete"
        )
    all_results = normalized.get("all_results")
    errors = normalized.get("errors")
    split_counts = normalized.get("support_split_counts")
    rejection_splits = normalized.get(
        "support_weight_rejection_splits"
    )
    if (
        not isinstance(all_results, list)
        or any(
            not isinstance(row, dict)
            or row.get("ell") != lattice[0]
            or row.get("m") != lattice[1]
            for row in all_results
        )
        or not isinstance(errors, list)
        or any(not isinstance(error, str) for error in errors)
        or not isinstance(split_counts, dict)
        or set(split_counts)
        != {
            f"{a_count}+{b_count}"
            for a_count, b_count in CHALLENGE_SUPPORT_SPLITS
        }
        or any(
            type(value) is not int or value < 0
            for value in split_counts.values()
        )
        or not isinstance(rejection_splits, dict)
        or any(
            not isinstance(key, str)
            or type(value) is not int
            or value < 0
            for key, value in rejection_splits.items()
        )
    ):
        raise CandidateLogWriteError(
            "Stage 2 lattice result payload is invalid"
        )
    return normalized


def _stage2_lattice_result_payload(
    metrics: dict,
    *,
    source_sha256: str,
    contract_id: int,
    preflight_sha256: str,
    epoch_id: str,
    index: int,
    lattice: tuple[int, int],
    pool_sha256: str,
) -> tuple[bytes, dict]:
    normalized = _validated_stage2_lattice_metrics(
        metrics,
        lattice=lattice,
    )
    payload = {
        "schema_version": STAGE2_DEEP_RESULT_SCHEMA_VERSION,
        "program_sha256": source_sha256,
        "contract_id": contract_id,
        "preflight_sha256": preflight_sha256,
        "epoch_id": epoch_id,
        "index": index,
        "lattice": list(lattice),
        "pool_sha256": pool_sha256,
        "metrics": normalized,
    }
    encoded = json.dumps(
        payload,
        sort_keys=True,
        separators=(",", ":"),
        allow_nan=False,
    ).encode("utf-8")
    return encoded, normalized


def _validate_stage2_result_directory(
    result_path: Path,
    *,
    create: bool,
) -> None:
    result_root = result_path.parent
    if create:
        result_root.mkdir(parents=True, exist_ok=True)
    if result_root.is_symlink() or not result_root.is_dir():
        raise CandidateLogWriteError(
            f"Stage 2 result root is unsafe: {result_root}"
        )


def _read_stage2_lattice_result(
    result_path: Path,
    *,
    source_sha256: str,
    contract_id: int,
    preflight_sha256: str,
    epoch_id: str,
    index: int,
    lattice: tuple[int, int],
    pool_sha256: str,
    expected_sha256: str | None = None,
    expected_bytes: int | None = None,
) -> tuple[dict, str, int]:
    _validate_stage2_result_directory(result_path, create=False)
    if result_path.is_symlink() or not result_path.is_file():
        raise CandidateLogWriteError(
            f"Stage 2 lattice result is unsafe: {result_path}"
        )
    try:
        encoded = result_path.read_bytes()
        payload = json.loads(encoded)
    except (OSError, UnicodeDecodeError, json.JSONDecodeError) as exc:
        raise CandidateLogWriteError(
            f"Stage 2 lattice result is unreadable: {result_path}"
        ) from exc
    digest = hashlib.sha256(encoded).hexdigest()
    if (
        expected_sha256 is not None
        and digest != expected_sha256
        or expected_bytes is not None
        and len(encoded) != expected_bytes
    ):
        raise CandidateLogWriteError(
            "Stage 2 lattice result no longer matches its journal"
        )
    if (
        not isinstance(payload, dict)
        or set(payload)
        != {
            "schema_version",
            "program_sha256",
            "contract_id",
            "preflight_sha256",
            "epoch_id",
            "index",
            "lattice",
            "pool_sha256",
            "metrics",
        }
        or payload.get("schema_version")
        != STAGE2_DEEP_RESULT_SCHEMA_VERSION
        or payload.get("program_sha256") != source_sha256
        or payload.get("contract_id") != contract_id
        or payload.get("preflight_sha256") != preflight_sha256
        or payload.get("epoch_id") != epoch_id
        or payload.get("index") != index
        or payload.get("lattice") != list(lattice)
        or payload.get("pool_sha256") != pool_sha256
    ):
        raise CandidateLogWriteError(
            "Stage 2 lattice result binding is invalid"
        )
    metrics = _validated_stage2_lattice_metrics(
        payload.get("metrics"),
        lattice=lattice,
    )
    return metrics, digest, len(encoded)


def _write_stage2_lattice_result(
    result_path: Path,
    metrics: dict,
    *,
    source_sha256: str,
    contract_id: int,
    preflight_sha256: str,
    epoch_id: str,
    index: int,
    lattice: tuple[int, int],
    pool_sha256: str,
) -> tuple[dict, str, int]:
    _validate_stage2_result_directory(result_path, create=True)
    if _path_entry_exists(result_path):
        return _read_stage2_lattice_result(
            result_path,
            source_sha256=source_sha256,
            contract_id=contract_id,
            preflight_sha256=preflight_sha256,
            epoch_id=epoch_id,
            index=index,
            lattice=lattice,
            pool_sha256=pool_sha256,
        )
    encoded, normalized = _stage2_lattice_result_payload(
        metrics,
        source_sha256=source_sha256,
        contract_id=contract_id,
        preflight_sha256=preflight_sha256,
        epoch_id=epoch_id,
        index=index,
        lattice=lattice,
        pool_sha256=pool_sha256,
    )
    temporary = result_path.with_name(
        f".{result_path.name}.tmp-{os.getpid()}-"
        f"{threading.get_ident()}-{time.time_ns()}"
    )
    flags = os.O_WRONLY | os.O_CREAT | os.O_EXCL | os.O_CLOEXEC
    if hasattr(os, "O_NOFOLLOW"):
        flags |= os.O_NOFOLLOW
    descriptor = os.open(temporary, flags, 0o600)
    try:
        _write_all(descriptor, encoded)
        os.fsync(descriptor)
    finally:
        os.close(descriptor)
    try:
        os.link(temporary, result_path, follow_symlinks=False)
    except FileExistsError:
        temporary.unlink()
        return _read_stage2_lattice_result(
            result_path,
            source_sha256=source_sha256,
            contract_id=contract_id,
            preflight_sha256=preflight_sha256,
            epoch_id=epoch_id,
            index=index,
            lattice=lattice,
            pool_sha256=pool_sha256,
        )
    except BaseException:
        try:
            temporary.unlink()
        except FileNotFoundError:
            pass
        raise
    temporary.unlink()
    directory_descriptor = os.open(
        result_path.parent,
        os.O_RDONLY | os.O_CLOEXEC | getattr(os, "O_DIRECTORY", 0),
    )
    try:
        os.fsync(directory_descriptor)
    finally:
        os.close(directory_descriptor)
    return normalized, hashlib.sha256(encoded).hexdigest(), len(encoded)


_STAGE2_SUM_COUNT_FIELDS = (
    "total_candidates",
    "unique_candidates",
    "evaluated_candidate_definitions",
    "duplicate_candidate_occurrences",
    "winner_capable_quick_exploration_eligible",
    "winner_capable_quick_exploration_persisted",
    "winner_capable_quick_exploration_omitted",
    "winner_capable_distance_pending_persisted",
    "winner_capable_unresolved_top_persisted",
    "winner_capable_distance_error_persisted",
    "distance_backend_error_count",
    "malformed_candidate_definitions",
    "tier0_rejected",
    "structural_rejected",
    SUPPORT_WEIGHT_ELIGIBLE_METRIC,
    SUPPORT_WEIGHT_REJECTED_METRIC,
    SUPPORT_WEIGHT_EVALUATED_METRIC,
)


def _aggregate_stage2_lattice_metrics(
    lattice_metrics: list[dict],
) -> dict:
    if len(lattice_metrics) != len(STAGE2_DEEP_LATTICES):
        raise CandidateLogWriteError(
            "Stage 2 cannot aggregate an incomplete lattice prefix"
        )
    normalized = [
        _validated_stage2_lattice_metrics(
            metrics,
            lattice=STAGE2_DEEP_LATTICES[index],
        )
        for index, metrics in enumerate(lattice_metrics)
    ]
    totals = {
        name: sum(
            _exact_nonnegative_preflight_metric(metrics, name)
            for metrics in normalized
        )
        for name in _STAGE2_SUM_COUNT_FIELDS
    }
    all_results = [
        row
        for metrics in normalized
        for row in metrics["all_results"]
    ]
    errors = [
        error
        for metrics in normalized
        for error in metrics["errors"]
    ]
    split_counts = {
        f"{a_count}+{b_count}": sum(
            metrics["support_split_counts"][
                f"{a_count}+{b_count}"
            ]
            for metrics in normalized
        )
        for a_count, b_count in CHALLENGE_SUPPORT_SPLITS
    }
    rejection_splits: dict[str, int] = {}
    for metrics in normalized:
        for split, count in metrics[
            "support_weight_rejection_splits"
        ].items():
            rejection_splits[split] = (
                rejection_splits.get(split, 0) + count
            )
    valid = [row for row in all_results if row.get("k", 0) > 0]
    foms = [
        row.get("fom", 0.0)
        for row in valid
        if row.get("fom", 0.0) > 0
    ]
    encoding_rates = [
        row.get("encoding_rate", 0.0) for row in valid
    ]
    high_k_codes = [
        row for row in valid if row.get("k", 0) >= 8
    ]
    best_code = None
    if all_results:
        best_result = max(
            all_results,
            key=lambda row: row.get("fom", 0.0),
        )
        if best_result.get("fom", 0.0) > 0:
            best_code = best_result
    unique = totals["unique_candidates"]
    support_eligible = totals[SUPPORT_WEIGHT_ELIGIBLE_METRIC]
    support_rejected = totals[SUPPORT_WEIGHT_REJECTED_METRIC]
    support_evaluated = totals[SUPPORT_WEIGHT_EVALUATED_METRIC]
    support_splits_covered = sum(
        count > 0 for count in split_counts.values()
    )
    support_lattice_splits = sum(
        count > 0
        for metrics in normalized
        for count in metrics["support_split_counts"].values()
    )
    return {
        "best_fom": max(foms) if foms else 0.0,
        "mean_fom": sum(foms) / len(foms) if foms else 0.0,
        "num_valid": len(valid),
        "num_above_6": sum(fom >= 6.0 for fom in foms),
        "num_above_12": sum(fom >= 12.0 for fom in foms),
        **totals,
        SUPPORT_FILTER_VERSION_METRIC: CHALLENGE_SUPPORT_FILTER_VERSION,
        SUPPORT_WEIGHT_PARTITION_COMPLETE_METRIC: int(
            unique == support_eligible + support_rejected
        ),
        SUPPORT_WEIGHT_EVALUATION_COVERAGE_METRIC: (
            support_evaluated / support_eligible
            if support_eligible
            else 1.0
        ),
        SUPPORT_WEIGHT_ELIGIBLE_FRACTION_METRIC: (
            support_eligible / unique if unique else 0.0
        ),
        SUPPORT_WEIGHT_REJECTION_FRACTION_METRIC: (
            support_rejected / unique if unique else 0.0
        ),
        SUPPORT_SPLITS_COVERED_METRIC: support_splits_covered,
        SUPPORT_SPLITS_TOTAL_METRIC: len(CHALLENGE_SUPPORT_SPLITS),
        SUPPORT_SPLIT_COVERAGE_METRIC: (
            support_splits_covered / len(CHALLENGE_SUPPORT_SPLITS)
        ),
        SUPPORT_SPLIT_LATTICE_COVERAGE_METRIC: (
            support_lattice_splits
            / (
                len(STAGE2_DEEP_LATTICES)
                * len(CHALLENGE_SUPPORT_SPLITS)
            )
        ),
        "support_split_counts": split_counts,
        "support_weight_rejection_splits": dict(
            sorted(rejection_splits.items())
        ),
        PATTERN_CLASSIFIER_VERSION_METRIC: PATTERN_CLASSIFIER_VERSION,
        "lattices_requested": len(STAGE2_DEEP_LATTICES),
        "lattices_completed": len(STAGE2_DEEP_LATTICES),
        "lattice_failures": 0,
        "best_encoding_rate": (
            max(encoding_rates) if encoding_rates else 0.0
        ),
        "num_high_k": len(high_k_codes),
        "lattices_with_high_k": len({
            (row["ell"], row["m"]) for row in high_k_codes
        }),
        "best_code": best_code,
        "all_results": all_results,
        "errors": errors,
    }


def _run_resumable_stage2_deep(
    program_path: str,
    *,
    generate_fn,
    candidate_log_path: Path,
    source_sha256: str,
    contract_id: int,
    preflight_sha256: str,
) -> dict:
    """Evaluate the deep lattice sequence as durable ordered transactions."""

    journal_path, _lock_path = _stage2_deep_journal_paths(
        candidate_log_path,
        source_sha256=source_sha256,
        contract_id=contract_id,
        preflight_sha256=preflight_sha256,
    )
    journal = _load_stage2_deep_journal(
        journal_path,
        source_sha256=source_sha256,
        contract_id=contract_id,
        candidate_log_path=candidate_log_path,
        preflight_sha256=preflight_sha256,
    )
    if not _path_entry_exists(journal_path):
        journal = _write_stage2_deep_journal(
            journal_path,
            journal,
            source_sha256=source_sha256,
            contract_id=contract_id,
            candidate_log_path=candidate_log_path,
            preflight_sha256=preflight_sha256,
        )

    completed = list(journal["completed_lattices"])
    lattice_metrics: list[dict] = []
    for index, lattice in enumerate(STAGE2_DEEP_LATTICES):
        generated = generate_fn(lattice[0], lattice[1])
        _assert_program_source_unchanged(program_path, source_sha256)
        pool_sha256 = _generated_pool_sha256(
            generated,
            lattice=lattice,
        )
        result_path = _stage2_lattice_result_path(
            journal_path,
            epoch_id=str(journal["epoch_id"]),
            index=index,
        )
        if index < len(completed):
            entry = completed[index]
            if entry["pool_sha256"] != pool_sha256:
                raise CandidateLogWriteError(
                    "Stage 2 generator replay changed the committed pool at "
                    f"lattice {lattice}"
                )
            metrics, _digest, _size = _read_stage2_lattice_result(
                result_path,
                source_sha256=source_sha256,
                contract_id=contract_id,
                preflight_sha256=preflight_sha256,
                epoch_id=str(journal["epoch_id"]),
                index=index,
                lattice=lattice,
                pool_sha256=pool_sha256,
                expected_sha256=str(entry["result_sha256"]),
                expected_bytes=int(entry["result_bytes"]),
            )
            lattice_metrics.append(metrics)
            journal = _write_stage2_deep_journal(
                journal_path,
                {
                    **journal,
                    "progress_sequence": int(
                        journal["progress_sequence"]
                    ) + 1,
                },
                source_sha256=source_sha256,
                contract_id=contract_id,
                candidate_log_path=candidate_log_path,
                preflight_sha256=preflight_sha256,
            )
            continue

        def frozen_generate(ell: int, m: int):
            if (ell, m) != lattice:
                raise CandidateLogWriteError(
                    "Stage 2 lattice evaluator requested a different lattice"
                )
            return generated

        if _path_entry_exists(result_path):
            metrics, result_sha256, result_bytes = (
                _read_stage2_lattice_result(
                    result_path,
                    source_sha256=source_sha256,
                    contract_id=contract_id,
                    preflight_sha256=preflight_sha256,
                    epoch_id=str(journal["epoch_id"]),
                    index=index,
                    lattice=lattice,
                    pool_sha256=pool_sha256,
                )
            )
        else:
            metrics = _run_evaluation(
                frozen_generate,
                [lattice],
                quick=False,
                refine_trials=STAGE2_REFINE_TRIALS,
                max_distance_per_lattice=(
                    STAGE2_DEEP_DISTANCE_PER_LATTICE
                ),
                sampling_salt=source_sha256,
                candidate_log_path=candidate_log_path,
                candidate_limit=STAGE2_DEEP_CANDIDATE_LIMIT,
            )
            metrics, result_sha256, result_bytes = (
                _write_stage2_lattice_result(
                    result_path,
                    metrics,
                    source_sha256=source_sha256,
                    contract_id=contract_id,
                    preflight_sha256=preflight_sha256,
                    epoch_id=str(journal["epoch_id"]),
                    index=index,
                    lattice=lattice,
                    pool_sha256=pool_sha256,
                )
            )
        entry = {
            "lattice": list(lattice),
            "pool_sha256": pool_sha256,
            "result_sha256": result_sha256,
            "result_bytes": result_bytes,
        }
        completed.append(entry)
        lattice_metrics.append(metrics)
        journal = _write_stage2_deep_journal(
            journal_path,
            {
                **journal,
                "status": (
                    "completed"
                    if len(completed) == len(STAGE2_DEEP_LATTICES)
                    else "in_progress"
                ),
                "completed_lattices": completed,
                "progress_sequence": int(
                    journal["progress_sequence"]
                ) + 1,
            },
            source_sha256=source_sha256,
            contract_id=contract_id,
            candidate_log_path=candidate_log_path,
            preflight_sha256=preflight_sha256,
        )

    return _aggregate_stage2_lattice_metrics(lattice_metrics)


def _is_stage2_terminal_negative(row: dict) -> bool:
    """Return whether replayable evidence already excludes the challenge."""

    return (
        row.get("search_status") == "terminal_negative"
        or row.get("threshold_rejection_proven") is True
        or row.get("final_gate_excluded_by_upper_bound") is True
        or row.get("search_final_gate_excluded_by_upper_bound") is True
    )


def _is_stage2_search_survivor(row: dict) -> bool:
    """Admit only explicit screen survivors; absent status fails closed."""

    if _is_stage2_terminal_negative(row):
        return False
    if _normalized_stage2_lower_bound_row(row) is not None:
        return True
    status = row.get("search_status")
    if status == "unresolved":
        if row.get("distance_status") == "upper_bound":
            return True
        # A solver timeout with no incumbent supplies no mathematical
        # distance bound.  Legacy MILP may still retain it for one fixed,
        # bounded exploration credit, but only through this explicit marker;
        # the row never receives distance/FOM credit.
        return (
            row.get("fitness_survivor_eligible") is True
            and row.get("distance_status") == "unknown_no_incumbent"
        )
    if status == "exact":
        return (
            row.get("d_is_exact") is True
            and row.get("distance_status") == "exact"
        )
    return False


def _legacy_milp_upper_bound_safe_rows(rows: list[dict]) -> list[dict]:
    """Adapt legacy MILP rows to the contract-v2 evidence vocabulary.

    The legacy evaluator predates ``search_status`` and historically treated a
    feasible MILP incumbent as an achieved distance.  This adapter fails
    closed: exact distance credit requires both exact flags, while incumbents
    remain upper bounds and no-incumbent timeouts receive at most bounded
    survivor credit.
    """

    adapted: list[dict] = []
    for original in rows:
        row = dict(original)
        stage = str(row.get("stage", ""))
        exact = (
            row.get("d_is_exact") is True
            and row.get("distance_status") == "exact"
        )
        if exact:
            normalized = _normalized_stage2_exact_row(row)
            if normalized is not None:
                row = normalized
                row["search_status"] = "exact"
            else:
                row["search_status"] = "invalid"
                row["fitness_distance_credit"] = 0.0
        elif row.get("distance_status") == "upper_bound":
            row.update({
                "search_status": "unresolved",
                "fom_upper_bound": row.get("fom", 0.0),
                "fitness_distance_credit": 0.0,
            })
        elif stage in {
            "milp_timeout_no_incumbent",
            "milp_promising_timeout",
        }:
            row.update({
                "search_status": "unresolved",
                "distance_status": "unknown_no_incumbent",
                "fitness_survivor_eligible": True,
                "fitness_distance_credit": 0.0,
            })
        else:
            # Quick-only, malformed, and unsupported legacy rows cannot
            # silently become search survivors.
            row["search_status"] = "invalid"
            row["fitness_distance_credit"] = 0.0
        adapted.append(row)
    return adapted


def _consumes_stage2_survivor_budget(row: dict) -> bool:
    """Bound BP work while tolerating old test doubles during the v2 rollout."""

    if _is_stage2_terminal_negative(row):
        return False
    if _is_stage2_search_survivor(row):
        return True
    # Contract-v2 evaluator rows always carry ``search_status``.  The fallback
    # is deliberately control-flow-only: it prevents an old/mock evaluator
    # from expanding a three-candidate BP budget into the whole shortlist, but
    # such a row still receives zero fitness below.
    if "search_status" in row:
        return False
    try:
        return int(row.get("k", 0) or 0) > 0
    except (TypeError, ValueError):
        return False


def _stage2_result_rate(row: dict) -> float:
    try:
        k = int(row.get("k", 0) or 0)
        n = int(row.get("n", 0) or 0)
    except (TypeError, ValueError):
        return 0.0
    if k <= 0 or n <= 0 or k > n:
        return 0.0
    return k / n


def _strict_stage2_integer(value: object) -> int | None:
    """Return an integral numeric value without accepting bools or strings."""

    if (
        isinstance(value, bool)
        or not isinstance(value, (int, float))
        or not math.isfinite(float(value))
        or not float(value).is_integer()
    ):
        return None
    return int(value)


def _normalized_stage2_exact_row(row: dict) -> dict | None:
    """Validate exact evidence and recompute every distance-derived value.

    Exact fitness and positive persistence must not trust evaluator-provided
    ``fom``, ``exact_fom``, or ``fitness_distance_credit`` fields.  Require a
    self-consistent BB block length and exact distance, then return a copy with
    all distance-derived values rebuilt from ``(n, k, d)``.
    """

    if (
        _is_stage2_terminal_negative(row)
        or row.get("d_is_exact") is not True
        or row.get("distance_status") != "exact"
    ):
        return None

    ell = _strict_stage2_integer(row.get("ell"))
    m = _strict_stage2_integer(row.get("m"))
    n = _strict_stage2_integer(row.get("n"))
    k = _strict_stage2_integer(row.get("k"))
    if (
        ell is None
        or m is None
        or n is None
        or k is None
        or ell <= 0
        or m <= 0
        or n != 2 * ell * m
        or not (1 <= k <= n)
    ):
        return None

    raw_exact_distance = row.get("exact_distance")
    raw_distance = row.get("d")
    if raw_exact_distance is None and raw_distance is None:
        return None
    exact_distance = _strict_stage2_integer(
        raw_exact_distance
        if raw_exact_distance is not None
        else raw_distance
    )
    reported_distance = _strict_stage2_integer(
        raw_distance if raw_distance is not None else raw_exact_distance
    )
    if (
        exact_distance is None
        or reported_distance is None
        or exact_distance != reported_distance
        or not (1 <= exact_distance <= n)
    ):
        return None

    exact_fom = k * exact_distance * exact_distance / n
    normalized = dict(row)
    normalized.update({
        "d": exact_distance,
        "exact_distance": exact_distance,
        "fom": exact_fom,
        "exact_fom": exact_fom,
        "fitness_distance_credit": exact_fom,
    })
    return normalized


@lru_cache(maxsize=4096)
def _replay_stage2_lower_bound_candidate(
    ell: int,
    m: int,
    a_terms: tuple[tuple[int, int], ...],
    b_terms: tuple[tuple[int, int], ...],
    geometry_json: str,
    oracle_json: str,
) -> tuple[bool, int | None, int | None]:
    """Rebuild one BB candidate and independently replay its oracle artifact."""

    try:
        normalized_a = [tuple(term) for term in a_terms]
        normalized_b = [tuple(term) for term in b_terms]
        raw_geometry = json.loads(geometry_json)
        geometry = normalize_geometry(ell, m, raw_geometry)
        validate_terms(ell, m, normalized_a, "A")
        validate_terms(ell, m, normalized_b, "B")
        code = build_bb_code(
            ell,
            m,
            normalized_a,
            normalized_b,
            geometry=geometry,
        )
        hx, hz, lx, lz = get_code_matrices(code)
        oracle = json.loads(oracle_json)
        failures = verify_css_low_weight_oracle(oracle, hx, hz, lx, lz)
    except Exception:
        return False, None, None
    return (
        not failures and oracle.get("outcome") == "UNSAT",
        int(code.num_qudits),
        int(code.dimension),
    )


def _normalized_stage2_lower_bound_row(row: dict) -> dict | None:
    """Validate the source-bound two-sector oracle lower-bound projection."""

    if (
        _is_stage2_terminal_negative(row)
        or row.get("d_is_exact") is True
        or row.get("search_status") != "certified_lower_bound"
        or row.get("distance_evidence_conflict") is not None
        or row.get("distance_lower_bound_proven") is not True
        or row.get("distance_lower_bound_status") != "search_oracle_proven"
    ):
        return None
    ell = _strict_stage2_integer(row.get("ell"))
    m = _strict_stage2_integer(row.get("m"))
    n = _strict_stage2_integer(row.get("n"))
    k = _strict_stage2_integer(row.get("k"))
    lower_bound = _strict_stage2_integer(row.get("distance_lower_bound"))
    threshold = _strict_stage2_integer(row.get("low_weight_oracle_threshold"))
    if (
        ell is None
        or m is None
        or n is None
        or k is None
        or lower_bound is None
        or threshold is None
        or ell <= 0
        or m <= 0
        or n != 2 * ell * m
        or not 1 <= k <= n
        or not 1 <= lower_bound <= n
        or threshold < 0
        or lower_bound != threshold + 1
    ):
        return None
    try:
        challenge_cutoff = compute_challenge_rejection_cutoff(
            n,
            k,
            STAGE2_CHALLENGE_TARGET_FOM,
        )
        expected_threshold = min(
            STAGE2_LOW_WEIGHT_ORACLE_MAX_WEIGHT,
            challenge_cutoff,
        )
    except ValueError:
        return None
    if (
        threshold != expected_threshold
        or threshold > LOW_WEIGHT_MITM_MAX_THRESHOLD
        or row.get("challenge_rejection_cutoff") != challenge_cutoff
    ):
        return None
    for field in (
        "d",
        "distance_upper_bound",
        "bp_distance_upper_bound",
        "osd_cs_distance_upper_bound",
        "d_symplectic",
        "d_x_symplectic",
        "d_z_symplectic",
    ):
        value = row.get(field)
        if value is not None:
            normalized_upper = _strict_stage2_integer(value)
            if (
                normalized_upper is None
                or normalized_upper < 1
                or normalized_upper < lower_bound
            ):
                return None
    try:
        a_terms_list, b_terms_list = _normalize_candidate_definition((
            row.get("A_terms"),
            row.get("B_terms"),
        ))
        a_terms = tuple(sorted(a_terms_list))
        b_terms = tuple(sorted(b_terms_list))
        canonical_geometry = normalize_geometry(
            ell, m, row.get("geometry")
        )
        geometry_json = json.dumps(
            canonical_geometry,
            sort_keys=True,
            separators=(",", ":"),
            ensure_ascii=False,
            allow_nan=False,
        )
    except (TypeError, ValueError):
        return None
    oracle = row.get("low_weight_oracle")
    if not isinstance(oracle, dict):
        return None
    unsigned = dict(oracle)
    evidence_sha256 = unsigned.pop("evidence_sha256", None)
    try:
        encoded = json.dumps(
            unsigned,
            sort_keys=True,
            separators=(",", ":"),
            ensure_ascii=False,
            allow_nan=False,
        ).encode("utf-8")
    except (TypeError, ValueError):
        return None
    try:
        oracle_json = json.dumps(
            oracle,
            sort_keys=True,
            separators=(",", ":"),
            ensure_ascii=False,
            allow_nan=False,
        )
    except (TypeError, ValueError):
        return None
    sectors = oracle.get("sectors")
    if (
        oracle.get("schema_version") != 1
        or oracle.get("kind") != "qcode-css-low-weight-oracle"
        or oracle.get("outcome") != "UNSAT"
        or oracle.get("decision_complete") is not True
        or oracle.get("max_weight") != threshold
        or oracle.get("distance_lower_bound") != lower_bound
        or oracle.get("witness") is not None
        or evidence_sha256 != hashlib.sha256(encoded).hexdigest()
        or not isinstance(sectors, dict)
        or set(sectors) != {"X", "Z"}
        or any(
            not isinstance(sectors[side], dict)
            or sectors[side].get("outcome") != "UNSAT"
            or sectors[side].get("decision_complete") is not True
            or sectors[side].get("max_weight") != threshold
            or not isinstance(sectors[side].get("binding"), dict)
            or sectors[side]["binding"].get("engine")
            != LOW_WEIGHT_MITM_ENGINE
            for side in ("X", "Z")
        )
    ):
        return None
    replayed, rebuilt_n, rebuilt_k = _replay_stage2_lower_bound_candidate(
        ell,
        m,
        a_terms,
        b_terms,
        geometry_json,
        oracle_json,
    )
    if not replayed or rebuilt_n != n or rebuilt_k != k:
        return None
    fom_lower_bound = k * lower_bound * lower_bound / n
    normalized = dict(row)
    normalized.update({
        "distance_lower_bound": lower_bound,
        "fom_lower_bound": fom_lower_bound,
        "fitness_distance_credit": fom_lower_bound,
        "search_status": "certified_lower_bound",
    })
    return normalized


def _score_stage2_upper_bound_safe(rows: list[dict]) -> dict[str, object]:
    """Score proof-safe survivors without trusting BP distance magnitude.

    BP-OSD and OSD-CS produce valid upper bounds.  A larger upper bound is not
    evidence that the true minimum distance is larger, so neither ``d`` nor
    ``fom`` is read here. A source-bound two-sector oracle UNSAT may contribute
    its recomputed lower-bound FOM. For the ansatz-v3 representation, BP-only
    rows are diagnostic/negative feedback only: survivor, rate, and structural
    promotion all require exact or replayed lower-bound evidence. Historical
    representations retain their checkpoint-compatible bounded exploration
    credit. Each fitness lattice remains capped.
    """

    survivors_by_lattice: dict[tuple[int, int], list[dict]] = {}
    terminal_negative_count = 0
    for row in rows:
        try:
            key = (int(row.get("ell")), int(row.get("m")))
        except (TypeError, ValueError):
            continue
        if key not in STAGE2_FITNESS_LATTICES:
            continue
        if _is_stage2_terminal_negative(row):
            terminal_negative_count += 1
            continue
        if _is_stage2_search_survivor(row):
            admitted = row
            if row.get("search_status") == "exact":
                admitted = _normalized_stage2_exact_row(row)
                if admitted is None:
                    continue
            else:
                lower_bound = _normalized_stage2_lower_bound_row(row)
                if lower_bound is not None:
                    admitted = lower_bound
            survivors_by_lattice.setdefault(key, []).append(admitted)

    distance_credit = 0.0
    lower_bound_credit = 0.0
    survivor_credit = 0.0
    rate_tie_break = 0.0
    structural_tie_break = 0.0
    per_lattice_credit: dict[tuple[int, int], float] = {}
    proof_only_promotion = ACTIVE_GEOMETRY_CONTRACT == (
        PUBLISHED_VOLUME_ANSATZ_V3_GEOMETRY_CONTRACT
    )
    for key, survivors in sorted(survivors_by_lattice.items()):
        exact_rows = [
            row for row in survivors if row.get("search_status") == "exact"
        ]
        lower_bound_rows = [
            row
            for row in survivors
            if _normalized_stage2_lower_bound_row(row) is not None
        ]
        if exact_rows:
            # Exact evidence may receive positive distance credit, but only
            # after rebuilding FOM from strictly consistent n, k, and exact d.
            # Cap it per lattice so one result cannot restore the old
            # unbounded optimizer's curse.
            exact_credits = [
                float(normalized["exact_fom"])
                for row in exact_rows
                if (
                    normalized := _normalized_stage2_exact_row(row)
                ) is not None
            ]
            base = min(
                STAGE2_CHALLENGE_TARGET_FOM,
                max(exact_credits, default=0.0),
            )
            distance_credit += base
        elif lower_bound_rows:
            # A complete X+Z threshold UNSAT is genuine positive evidence.
            # Keep the historical one-point survivor floor, but otherwise let
            # the recomputed FOM lower bound determine the signal.  The cap
            # prevents one easy high-rate lattice from dominating MAP-Elites.
            proven_credits = [
                float(normalized["fom_lower_bound"])
                for row in lower_bound_rows
                if (
                    normalized := _normalized_stage2_lower_bound_row(row)
                ) is not None
            ]
            base = min(
                STAGE2_CHALLENGE_TARGET_FOM,
                max(
                    STAGE2_SURVIVOR_CREDIT_PER_LATTICE,
                    max(proven_credits, default=0.0),
                ),
            )
            distance_credit += base
            lower_bound_credit += base
        elif not proof_only_promotion:
            # An unresolved BP/OSD upper bound earns exploration/survival
            # credit, never distance credit, for checkpoint-compatible legacy
            # representations only. Ansatz v3 forbids all positive promotion
            # from decoder upper bounds.
            base = STAGE2_SURVIVOR_CREDIT_PER_LATTICE
            survivor_credit += base
        else:
            base = 0.0
        promotion_rows = (
            [*exact_rows, *lower_bound_rows]
            if proof_only_promotion
            else survivors
        )
        rate_bonus = (
            STAGE2_RATE_TIE_BREAK_MAX_PER_LATTICE
            * max(
                (_stage2_result_rate(row) for row in promotion_rows),
                default=0.0,
            )
        )
        support_splits = {
            (len(row.get("A_terms", [])), len(row.get("B_terms", [])))
            for row in promotion_rows
            if (
                isinstance(row.get("A_terms"), (list, tuple))
                and isinstance(row.get("B_terms"), (list, tuple))
                and (
                    len(row.get("A_terms", [])),
                    len(row.get("B_terms", [])),
                )
                in CHALLENGE_SUPPORT_SPLITS
            )
        }
        structural_fraction = min(
            1.0,
            len(support_splits)
            / min(
                STAGE2_DEEP_DISTANCE_PER_LATTICE,
                len(CHALLENGE_SUPPORT_SPLITS),
            ),
        )
        structure_bonus = (
            STAGE2_STRUCTURE_TIE_BREAK_MAX_PER_LATTICE
            * structural_fraction
        )
        rate_tie_break += rate_bonus
        structural_tie_break += structure_bonus
        per_lattice_credit[key] = base + rate_bonus + structure_bonus

    combined_score = (
        distance_credit
        + survivor_credit
        + rate_tie_break
        + structural_tie_break
    )
    return {
        "combined_score": combined_score,
        "fitness_distance_credit": distance_credit,
        "fitness_lower_bound_credit": lower_bound_credit,
        "fitness_survivor_credit": survivor_credit,
        "fitness_rate_tie_break": rate_tie_break,
        "fitness_structural_tie_break": structural_tie_break,
        "survivor_count": sum(map(len, survivors_by_lattice.values())),
        "survivor_lattices": len(survivors_by_lattice),
        "terminal_negative_count": terminal_negative_count,
        "per_lattice_credit": per_lattice_credit,
    }


def _verified_distance_persistence_rows(rows: list[dict]) -> list[dict]:
    """Return positive distance-elite rows backed by exact evidence only."""

    verified: list[dict] = []
    for row in rows:
        normalized = _normalized_stage2_exact_row(row)
        if normalized is not None:
            verified.append(normalized)
    return verified


def _bp_fom_upper_bound(row: dict) -> float:
    """Return a diagnostic upper-bound FOM, never a fitness contribution."""

    if row.get("d_is_exact") is True:
        return 0.0
    value = row.get("fom_upper_bound", row.get("fom", 0.0))
    if (
        isinstance(value, bool)
        or not isinstance(value, (int, float))
        or not math.isfinite(float(value))
        or float(value) <= 0
    ):
        return 0.0
    return float(value)


def _evaluate_stage2_impl(program_path: str) -> dict:
    """Stage 2: bounded target preflight plus deep distance evaluation.

    Every contracted lattice is partitioned by the challenge support contract.
    Every supported, statically eligible winner-capable definition is durably
    retained before a blocking distance backend runs. Deep BP-OSD scoring then
    uses the historical Pareto/fitness lattice basis.
    """
    # Capture and validate the Stage 1 handoff before importing evolved code.
    # In direct/fallback evaluation this environment value is absent, so Stage
    # 2 still performs its own complete preflight.
    contract_id = _current_winner_preflight_contract_id()
    candidate_log_path = _freeze_candidate_log_path()
    source_sha256 = _freeze_program_source_sha256(program_path)
    load_generate_candidates = _load_generate_candidates
    run_evaluation = _run_evaluation
    preflight_reuse = _preflight_reuse_from_environment(program_path)
    preflight_sha256 = _stage2_preflight_sha256(
        preflight_reuse,
        contract_id=contract_id,
    )
    try:
        generate_fn = load_generate_candidates(program_path)
    except Exception as e:
        return _error_result(str(e))

    _assert_program_source_unchanged(program_path, source_sha256)
    sampling_salt = source_sha256
    if preflight_reuse is None:
        preflight = run_evaluation(
            generate_fn,
            STAGE2_LATTICES,
            quick=True,
            candidate_log_path=candidate_log_path,
            sampling_salt=sampling_salt,
            candidate_limit=STAGE2_PREFLIGHT_CANDIDATE_LIMIT,
            persist_quick_exploration=True,
            persist_all_quick_exploration=True,
        )
        preflight_support_feedback_observed = 1
    else:
        reused_evaluated = int(
            preflight_reuse[WINNER_PREFLIGHT_EVALUATED_METRIC]
        )
        preflight = {
            "errors": [],
            "total_candidates": reused_evaluated,
            "unique_candidates": reused_evaluated,
            "evaluated_candidate_definitions": reused_evaluated,
            "winner_capable_quick_exploration_eligible": int(
                preflight_reuse[WINNER_PREFLIGHT_ELIGIBLE_METRIC]
            ),
            "winner_capable_quick_exploration_persisted": int(
                preflight_reuse[WINNER_PREFLIGHT_PERSISTED_METRIC]
            ),
            "winner_capable_quick_exploration_omitted": 0,
            "lattices_completed": len(STAGE2_LATTICES),
            "lattice_failures": 0,
            SUPPORT_FILTER_VERSION_METRIC: (
                CHALLENGE_SUPPORT_FILTER_VERSION
            ),
            SUPPORT_WEIGHT_ELIGIBLE_METRIC: reused_evaluated,
            SUPPORT_WEIGHT_REJECTED_METRIC: 0,
            SUPPORT_WEIGHT_EVALUATED_METRIC: reused_evaluated,
            SUPPORT_WEIGHT_PARTITION_COMPLETE_METRIC: 1,
            SUPPORT_WEIGHT_EVALUATION_COVERAGE_METRIC: 1.0,
            SUPPORT_WEIGHT_ELIGIBLE_FRACTION_METRIC: 1.0,
            SUPPORT_WEIGHT_REJECTION_FRACTION_METRIC: 0.0,
            SUPPORT_SPLITS_COVERED_METRIC: 0,
            SUPPORT_SPLITS_TOTAL_METRIC: len(CHALLENGE_SUPPORT_SPLITS),
            SUPPORT_SPLIT_COVERAGE_METRIC: 0.0,
            SUPPORT_SPLIT_LATTICE_COVERAGE_METRIC: 0.0,
            "support_split_counts": {},
            "support_weight_rejection_splits": {},
            PATTERN_CLASSIFIER_VERSION_METRIC: PATTERN_CLASSIFIER_VERSION,
        }
        if (
            is_twisted_geometry_contract(ACTIVE_GEOMETRY_CONTRACT)
        ):
            # The compact Stage-1 handoff does not repeat diagnostic q counts,
            # but its source-bound completion marker was issued only after
            # `_require_complete_support_evaluation` proved every immutable
            # stratum.  Reconstruct the deterministic contract total here so
            # the Stage-2 reuse path enforces the same v3 invariant without
            # changing the legacy handoff schema.
            twist_total = sum(
                len(allowed_twists(
                    ell,
                    m,
                    contract=ACTIVE_GEOMETRY_CONTRACT,
                ))
                for ell, m in STAGE2_LATTICES
            )
            preflight.update({
                GEOMETRY_TWISTS_REQUIRED_METRIC: twist_total,
                GEOMETRY_TWISTS_OBSERVED_METRIC: twist_total,
                GEOMETRY_TWIST_COVERAGE_METRIC: 1.0,
                GEOMETRY_TWIST_COVERAGE_COMPLETE_METRIC: 1,
            })
        # The Stage 1 marker proves complete support filtering because its
        # contract id binds this evaluator source, but compact checkpoint
        # markers do not retain the per-split diagnostic counts.
        preflight_support_feedback_observed = 0
    _require_full_pool_persistence(
        preflight,
        expected_lattices=len(STAGE2_LATTICES),
        label="Stage 2 full preflight",
    )
    _assert_program_source_unchanged(program_path, source_sha256)
    metrics = dict(_run_resumable_stage2_deep(
        program_path,
        generate_fn=generate_fn,
        candidate_log_path=candidate_log_path,
        source_sha256=source_sha256,
        contract_id=contract_id,
        preflight_sha256=preflight_sha256,
    ))
    _assert_program_source_unchanged(program_path, source_sha256)
    preflight_errors = list(preflight.get("errors", []))
    metrics["errors"] = list(dict.fromkeys([
        *preflight_errors,
        *metrics.get("errors", []),
    ]))
    metrics["malformed_candidate_definitions"] = (
        preflight.get("malformed_candidate_definitions", 0)
        + metrics.get("malformed_candidate_definitions", 0)
    )
    metrics["winner_capable_quick_exploration_persisted"] = (
        preflight.get(
            "winner_capable_quick_exploration_persisted", 0
        )
        + metrics.get(
            "winner_capable_quick_exploration_persisted", 0
        )
    )
    metrics["target_preflight_winner_capable_eligible"] = preflight.get(
        "winner_capable_quick_exploration_eligible", 0
    )
    metrics["target_preflight_winner_capable_persisted"] = preflight.get(
        "winner_capable_quick_exploration_persisted", 0
    )
    metrics["target_preflight_winner_capable_omitted"] = preflight.get(
        "winner_capable_quick_exploration_omitted", 0
    )
    if (
        metrics["target_preflight_winner_capable_omitted"] != 0
        or metrics["target_preflight_winner_capable_persisted"]
        != metrics["target_preflight_winner_capable_eligible"]
    ):
        raise CandidateLogWriteError(
            "Stage 2 preflight persistence invariant failed: "
            f"eligible={metrics['target_preflight_winner_capable_eligible']}, "
            "persisted="
            f"{metrics['target_preflight_winner_capable_persisted']}, "
            f"omitted={metrics['target_preflight_winner_capable_omitted']}"
        )
    metrics["target_preflight_lattices"] = len(STAGE2_LATTICES)
    metrics["target_preflight_candidates_generated"] = preflight.get(
        "total_candidates", 0
    )
    metrics["target_preflight_candidates_evaluated"] = preflight.get(
        "evaluated_candidate_definitions", 0
    )
    metrics["target_preflight_support_feedback_observed"] = (
        preflight_support_feedback_observed
    )
    metrics["target_preflight_support_weight_eligible"] = preflight.get(
        SUPPORT_WEIGHT_ELIGIBLE_METRIC, 0
    )
    metrics["target_preflight_support_weight_rejected"] = preflight.get(
        SUPPORT_WEIGHT_REJECTED_METRIC, 0
    )
    metrics["target_preflight_support_splits_covered"] = preflight.get(
        SUPPORT_SPLITS_COVERED_METRIC, 0
    )
    metrics["target_preflight_support_split_coverage"] = preflight.get(
        SUPPORT_SPLIT_COVERAGE_METRIC, 0.0
    )

    # --- Upper-bound-safe combined score ---
    # BP-OSD and OSD-CS only find feasible logical operators, hence upper
    # bounds on d.  Their magnitude is diagnostic and never contributes d²
    # fitness.  Explicit challenge-screen survivors receive one bounded credit
    # per historical fitness lattice plus small rate/structure tie-breaks.
    score = _score_stage2_upper_bound_safe(metrics["all_results"])
    combined = float(score["combined_score"])
    survivor_codes = [
        row
        for row in metrics["all_results"]
        if _is_stage2_search_survivor(row)
        and (row.get("ell"), row.get("m")) in STAGE2_FITNESS_LATTICES
    ]
    bp_upper_bounds = [
        _bp_fom_upper_bound(row) for row in metrics["all_results"]
    ]
    bp_upper_bounds = [value for value in bp_upper_bounds if value > 0]
    best_bp_fom_upper_bound = (
        max(bp_upper_bounds) if bp_upper_bounds else 0.0
    )
    mean_bp_fom_upper_bound = (
        sum(bp_upper_bounds) / len(bp_upper_bounds)
        if bp_upper_bounds
        else 0.0
    )

    # Build artifacts for LLM feedback.  Survivors are ordered only by exact
    # rate and structure.  Their unresolved upper-bound magnitudes stay in
    # telemetry and are deliberately hidden from the mutation model.
    artifacts = {}
    oracle_rejections = [
        row
        for row in metrics["all_results"]
        if row.get("threshold_proof_source") == "low_weight_oracle"
        and _is_stage2_terminal_negative(row)
        and isinstance(row.get("low_weight_oracle"), dict)
    ]
    oracle_lower_bounds = [
        normalized
        for row in metrics["all_results"]
        if (normalized := _normalized_stage2_lower_bound_row(row)) is not None
    ]
    if oracle_rejections:
        failure_lines = []
        for row in sorted(
            oracle_rejections,
            key=lambda item: (
                int(item.get("threshold_proof_distance", 0) or 0),
                _definition_key(item),
            ),
        )[:5]:
            witness = row["low_weight_oracle"].get("witness", {})
            support = witness.get("support", [])
            block_size = int(row["ell"]) * int(row["m"])
            block_support = [
                (
                    "left" if int(index) < block_size else "right",
                    int(index)
                    if int(index) < block_size
                    else int(index) - block_size,
                )
                for index in support
            ]
            failure_lines.append(
                f"  {witness.get('side', '?')}-logical w="
                f"{witness.get('weight', '?')} support={support} "
                f"block_support={block_support} at "
                f"({row['ell']},{row['m']}), A={row['A_terms']}, "
                f"B={row['B_terms']}"
            )
        artifacts["low_weight_oracle_failures"] = "\n".join([
            "Replayed low-weight logical witnesses. Mutations should disrupt "
            "these concrete supports/mechanisms; they are negative evidence, "
            "not achieved distance:",
            *failure_lines,
        ])
    if oracle_lower_bounds:
        lower_lines = []
        for row in sorted(
            oracle_lower_bounds,
            key=lambda item: (
                float(item["fom_lower_bound"]),
                _definition_key(item),
            ),
            reverse=True,
        )[:5]:
            lower_lines.append(
                f"  [[{row['n']},{row['k']},d>="
                f"{row['distance_lower_bound']}]] proven search lower FOM="
                f"{row['fom_lower_bound']:.3f} at ({row['ell']},{row['m']}), "
                f"A={row['A_terms']}, B={row['B_terms']}"
            )
        artifacts["low_weight_oracle_lower_bounds"] = "\n".join([
            "Complete two-sector low-weight exclusions (positive search "
            "evidence; final certification is still required):",
            *lower_lines,
        ])
    if survivor_codes:
        bc = max(
            survivor_codes,
            key=lambda row: (
                _stage2_result_rate(row),
                _definition_key(row),
            ),
        )
        artifacts["best_screen_survivor"] = (
            f"[[{bc['n']},{bc['k']},d=unresolved]] "
            f"rate={_stage2_result_rate(bc):.3f} "
            f"at ({bc['ell']},{bc['m']}); upper-bound magnitude withheld\n"
            f"  A={bc['A_terms']}\n"
            f"  B={bc['B_terms']}"
        )

    if metrics["errors"]:
        artifacts["errors"] = "\n".join(metrics["errors"][:5])

    split_counts = metrics.get("support_split_counts", {})
    split_feedback = ", ".join(
        f"{split}={split_counts.get(split, 0)}"
        for split in (
            f"{a_count}+{b_count}"
            for a_count, b_count in CHALLENGE_SUPPORT_SPLITS
        )
    )
    rejection_splits = metrics.get(
        "support_weight_rejection_splits", {}
    )
    rejection_feedback = ", ".join(
        f"{split}={count}"
        for split, count in sorted(rejection_splits.items())
    ) or "none"
    artifacts["support_filter"] = (
        f"Challenge support filter v{CHALLENGE_SUPPORT_FILTER_VERSION}: "
        f"{metrics.get(SUPPORT_WEIGHT_ELIGIBLE_METRIC, 0)} eligible, "
        f"{metrics.get(SUPPORT_WEIGHT_REJECTED_METRIC, 0)} rejected before "
        "batch evaluation; eligible fraction "
        f"{metrics.get(SUPPORT_WEIGHT_ELIGIBLE_FRACTION_METRIC, 0):.3f}, "
        "eligible evaluation coverage "
        f"{metrics.get(SUPPORT_WEIGHT_EVALUATION_COVERAGE_METRIC, 0):.3f}.\n"
        f"Supported split coverage: "
        f"{metrics.get(SUPPORT_SPLITS_COVERED_METRIC, 0)}/"
        f"{metrics.get(SUPPORT_SPLITS_TOTAL_METRIC, 0)} "
        f"({metrics.get(SUPPORT_SPLIT_COVERAGE_METRIC, 0):.3f}); "
        f"lattice-split coverage "
        f"{metrics.get(SUPPORT_SPLIT_LATTICE_COVERAGE_METRIC, 0):.3f}.\n"
        f"Eligible split counts: {split_feedback}.\n"
        f"Rejected support splits: {rejection_feedback}."
    )

    # Report screen survivors by exact rate, without exposing unresolved
    # upper-bound distance/FOM magnitudes to the mutation model.
    top5 = sorted(
        survivor_codes,
        key=lambda row: (
            _stage2_result_rate(row),
            _definition_key(row),
        ),
        reverse=True,
    )[:5]
    if top5:
        top5_lines = []
        for r in top5:
            top5_lines.append(
                f"  [[{r['n']},{r['k']},d=unresolved]] "
                f"rate={_stage2_result_rate(r):.3f} "
                f"({r['ell']},{r['m']}); upper-bound magnitude withheld"
            )
        artifacts["top_screen_survivors"] = "\n".join(top5_lines)

    # Structural feedback remains useful, but is deliberately decoupled from
    # the magnitude of the BP upper bound.
    if survivor_codes:
        struct_lines = []
        for r in sorted(
            survivor_codes,
            key=lambda row: (
                _stage2_result_rate(row),
                _definition_key(row),
            ),
            reverse=True,
        )[:3]:
            struct_lines.append(
                f"  [[{r['n']},{r['k']},d=unresolved]]:\n"
                f"    {_structural_feedback(r)}"
            )
        artifacts["structural_analysis"] = (
            "Structural analysis of challenge-screen survivors; unresolved "
            "upper-bound magnitudes are withheld:\n" + "\n".join(struct_lines)
        )

    # Per-lattice breakdown for the LLM
    lattice_lines = []
    per_lattice_credit = score["per_lattice_credit"]
    assert isinstance(per_lattice_credit, dict)
    for key in sorted(per_lattice_credit):
        lattice_lines.append(
            f"  ({key[0]},{key[1]}): bounded credit="
            f"{per_lattice_credit[key]:.3f}"
        )
    if metrics.get("target_preflight_support_feedback_observed", 0):
        target_support_feedback = (
            f"{metrics.get('target_preflight_support_weight_rejected', 0)} "
            "support-weight rejected, "
            f"{metrics.get('target_preflight_support_splits_covered', 0)}/"
            f"{len(CHALLENGE_SUPPORT_SPLITS)} splits covered.\n"
        )
    else:
        target_support_feedback = (
            "complete by bound Stage 1 marker; per-split diagnostics "
            "unavailable after compact checkpoint reuse.\n"
        )

    artifacts["summary"] = (
        "Target preflight: "
        f"{metrics.get('target_preflight_candidates_evaluated', 0)} "
        "challenge-supported definitions evaluated from "
        f"{metrics.get('target_preflight_candidates_generated', 0)} "
        f"raw generated candidates across "
        f"{metrics.get('target_preflight_lattices', 0)} lattices.\n"
        "Target preflight support filter: "
        f"{metrics.get('target_preflight_support_weight_eligible', 0)} "
        f"eligible, {target_support_feedback}"
        "Target preflight winner-capable persistence: "
        f"{metrics.get('target_preflight_winner_capable_eligible', 0)} "
        "eligible, "
        f"{metrics.get('target_preflight_winner_capable_persisted', 0)} "
        "persisted, "
        f"{metrics.get('target_preflight_winner_capable_omitted', 0)} "
        "omitted.\n"
        f"Deep evaluation: {metrics['total_candidates']} generated "
        f"candidates across {len(STAGE2_DEEP_LATTICES)} lattices.\n"
        f"Canonical definitions: {metrics['unique_candidates']} generated, "
        f"{metrics['evaluated_candidate_definitions']} evaluated, "
        f"{metrics['duplicate_candidate_occurrences']} duplicate occurrences "
        "collapsed.\n"
        "Deep challenge support: "
        f"{metrics.get(SUPPORT_WEIGHT_ELIGIBLE_METRIC, 0)} eligible, "
        f"{metrics.get(SUPPORT_WEIGHT_REJECTED_METRIC, 0)} rejected before "
        "batch evaluation, eligible fraction "
        f"{metrics.get(SUPPORT_WEIGHT_ELIGIBLE_FRACTION_METRIC, 0):.3f}, "
        f"{metrics.get(SUPPORT_SPLITS_COVERED_METRIC, 0)}/"
        f"{metrics.get(SUPPORT_SPLITS_TOTAL_METRIC, 0)} splits covered, "
        "eligible evaluation coverage "
        f"{metrics.get(SUPPORT_WEIGHT_EVALUATION_COVERAGE_METRIC, 0):.3f}.\n"
        "Zero-distance persistence: "
        f"{metrics.get('winner_capable_distance_pending_persisted', 0)} "
        "selected pending, "
        f"{metrics['winner_capable_unresolved_top_persisted']} unresolved "
        "top-k, "
        f"{metrics.get('winner_capable_distance_error_persisted', 0)} "
        "distance errors, "
        f"{metrics['winner_capable_quick_exploration_persisted']} quick-only.\n"
        "Distance backend failures: "
        f"{metrics.get('distance_backend_error_count', 0)}.\n"
        f"Valid codes (k>0): {metrics['num_valid']}\n"
        f"High-k codes (k>=8): {metrics['num_high_k']}\n"
        f"Lattices with high-k: {metrics['lattices_with_high_k']}/"
        f"{len(STAGE2_DEEP_LATTICES)}\n"
        "BP/OSD upper-bound diagnostics retained in telemetry only.\n"
        "Low-weight oracle: "
        f"{len(oracle_rejections)} replayed witness rejections, "
        f"{len(oracle_lower_bounds)} complete two-sector lower bounds.\n"
        f"Challenge-screen terminal negatives: "
        f"{score['terminal_negative_count']}; survivors: "
        f"{score['survivor_count']} across {score['survivor_lattices']} "
        "fitness lattices.\n"
        f"Combined score: {combined:.3f} = "
        f"{score['fitness_survivor_credit']:.3f} bounded survivor + "
        f"{score['fitness_distance_credit']:.3f} exact/lower-bound distance "
        f"({score['fitness_lower_bound_credit']:.3f} from oracle lower bounds) + "
        f"{score['fitness_rate_tie_break']:.3f} rate tie-break + "
        f"{score['fitness_structural_tie_break']:.3f} structure tie-break; "
        "BP upper-bound magnitude contributes zero.\n"
        f"Per-lattice breakdown:\n" + "\n".join(lattice_lines)
    )

    # BP-only rows never enter the positive discovered-code/Pareto stores.
    verified_to_save = [
        row
        for row in _verified_distance_persistence_rows(
            metrics["all_results"]
        )
        if float(row.get("exact_fom", row.get("fom", 0.0)) or 0.0) > 6.0
    ]
    if verified_to_save:
        best_verified = max(
            verified_to_save,
            key=lambda row: float(
                row.get("exact_fom", row.get("fom", 0.0)) or 0.0
            ),
        )
        try:
            save_code(best_verified)
            update_pareto_front(verified_to_save)
        except Exception:
            # Search fitness must not fail because optional compatibility
            # persistence is unavailable.
            pass

    # Write metrics to shared JSONL file for W&B sync from main process.
    # (wandb.run is None in subprocess workers, so direct wandb.log doesn't work.)
    metrics.update({
        "best_bp_fom_upper_bound": best_bp_fom_upper_bound,
        "mean_bp_fom_upper_bound": mean_bp_fom_upper_bound,
        "fitness_distance_credit": score["fitness_distance_credit"],
        "fitness_lower_bound_credit": score["fitness_lower_bound_credit"],
        "fitness_survivor_credit": score["fitness_survivor_credit"],
        "fitness_rate_tie_break": score["fitness_rate_tie_break"],
        "fitness_structural_tie_break": (
            score["fitness_structural_tie_break"]
        ),
        "screen_survivor_count": score["survivor_count"],
        "screen_survivor_lattices": score["survivor_lattices"],
        "screen_terminal_negative_count": (
            score["terminal_negative_count"]
        ),
        "low_weight_oracle_rejection_count": len(oracle_rejections),
        "low_weight_oracle_lower_bound_count": len(oracle_lower_bounds),
    })
    _write_metrics_jsonl(metrics)

    map_descriptor = _pool_map_descriptor(
        metrics.get("all_results", []),
        lattices=set(STAGE2_FITNESS_LATTICES),
    )

    result = {
        "combined_score": combined,
        STAGE2_CONTRACT_VERSION_METRIC: float(
            STAGE2_DEEP_CONTRACT_VERSION
        ),
        STAGE2_CONTRACT_ID_METRIC: float(contract_id),
        STAGE2_COMPLETE_METRIC: 1.0,
        STAGE2_INCOMPLETE_METRIC: 0.0,
        STAGE2_LATTICES_METRIC: float(len(STAGE2_DEEP_LATTICES)),
        STAGE2_HARD_TIMEOUT_METRIC: 0.0,
        STAGE2_SUBPROCESS_FAILED_METRIC: 0.0,
        "best_bp_fom_upper_bound": best_bp_fom_upper_bound,
        "mean_bp_fom_upper_bound": mean_bp_fom_upper_bound,
        "fitness_distance_credit": float(
            score["fitness_distance_credit"]
        ),
        "fitness_lower_bound_credit": float(
            score["fitness_lower_bound_credit"]
        ),
        "fitness_survivor_credit": float(
            score["fitness_survivor_credit"]
        ),
        "fitness_rate_tie_break": float(
            score["fitness_rate_tie_break"]
        ),
        "fitness_structural_tie_break": float(
            score["fitness_structural_tie_break"]
        ),
        "screen_survivor_count": float(score["survivor_count"]),
        "screen_survivor_lattices": float(score["survivor_lattices"]),
        "screen_terminal_negative_count": float(
            score["terminal_negative_count"]
        ),
        "low_weight_oracle_rejection_count": float(len(oracle_rejections)),
        "low_weight_oracle_lower_bound_count": float(len(oracle_lower_bounds)),
        "num_valid": float(metrics["num_valid"]),
        "num_high_k": float(metrics["num_high_k"]),
        "lattices_with_high_k": float(metrics["lattices_with_high_k"]),
        "best_encoding_rate": metrics["best_encoding_rate"],
        "num_bp_upper_bounds_above_6": float(metrics["num_above_6"]),
        "num_bp_upper_bounds_above_12": float(metrics["num_above_12"]),
        "total_candidates": float(metrics["total_candidates"]),
        "unique_candidates": float(metrics["unique_candidates"]),
        "evaluated_candidate_definitions": float(
            metrics["evaluated_candidate_definitions"]
        ),
        "duplicate_candidate_occurrences": float(
            metrics["duplicate_candidate_occurrences"]
        ),
        "winner_capable_quick_exploration_persisted": float(
            metrics["winner_capable_quick_exploration_persisted"]
        ),
        "winner_capable_distance_pending_persisted": float(
            metrics.get("winner_capable_distance_pending_persisted", 0)
        ),
        "winner_capable_unresolved_top_persisted": float(
            metrics["winner_capable_unresolved_top_persisted"]
        ),
        "winner_capable_distance_error_persisted": float(
            metrics.get("winner_capable_distance_error_persisted", 0)
        ),
        "distance_backend_error_count": float(
            metrics.get("distance_backend_error_count", 0)
        ),
        "target_preflight_lattices": float(
            metrics.get("target_preflight_lattices", 0)
        ),
        "target_preflight_candidates_evaluated": float(
            metrics.get("target_preflight_candidates_evaluated", 0)
        ),
        "target_preflight_winner_capable_eligible": float(
            metrics.get("target_preflight_winner_capable_eligible", 0)
        ),
        "target_preflight_winner_capable_persisted": float(
            metrics.get("target_preflight_winner_capable_persisted", 0)
        ),
        "target_preflight_winner_capable_omitted": float(
            metrics.get("target_preflight_winner_capable_omitted", 0)
        ),
        "target_preflight_support_feedback_observed": float(
            metrics.get("target_preflight_support_feedback_observed", 0)
        ),
        "target_preflight_support_weight_eligible": float(
            metrics.get("target_preflight_support_weight_eligible", 0)
        ),
        "target_preflight_support_weight_rejected": float(
            metrics.get("target_preflight_support_weight_rejected", 0)
        ),
        "target_preflight_support_splits_covered": float(
            metrics.get("target_preflight_support_splits_covered", 0)
        ),
        "target_preflight_support_split_coverage": float(
            metrics.get("target_preflight_support_split_coverage", 0)
        ),
    }
    result.update(map_descriptor)
    result.update(_support_observability_metrics(metrics))

    try:
        from openevolve.evaluation_result import EvaluationResult
        return EvaluationResult(metrics=result, artifacts=artifacts)
    except ImportError:
        return result


def _winner_preflight_hard_timeout_s() -> float:
    raw = os.environ.get(
        STAGE2_OUTER_TIMEOUT_ENV,
        str(WINNER_PREFLIGHT_OUTER_TIMEOUT_DEFAULT_S),
    )
    try:
        outer_timeout = float(raw)
    except (TypeError, ValueError) as exc:
        raise RuntimeError(
            f"{STAGE2_OUTER_TIMEOUT_ENV} must be numeric"
        ) from exc
    if (
        not math.isfinite(outer_timeout)
        or outer_timeout <= WINNER_PREFLIGHT_OUTER_TIMEOUT_MARGIN_S
    ):
        raise RuntimeError(
            f"{STAGE2_OUTER_TIMEOUT_ENV} leaves no hard-timeout margin"
        )
    return min(
        WINNER_PREFLIGHT_HARD_TIMEOUT_MAX_S,
        outer_timeout - WINNER_PREFLIGHT_OUTER_TIMEOUT_MARGIN_S,
    )


def _winner_preflight_attempt_hard_timeout_s(
    inactivity_timeout: float,
) -> float:
    """Absolute non-resettable wall for one owned Stage 1 child."""

    return (
        inactivity_timeout
        * (
            len(EVOLUTION_LATTICES)
            * STAGE1_PREFLIGHT_MAX_EPOCH_ATTEMPTS
            + 1
        )
    )


def _winner_preflight_failure_result(
    message: str,
    *,
    timed_out: bool,
) -> dict[str, float]:
    metrics = _error_result(message)
    metrics.update({
        WINNER_PREFLIGHT_CONTRACT_VERSION_METRIC: float(
            WINNER_PREFLIGHT_CONTRACT_VERSION
        ),
        WINNER_PREFLIGHT_CONTRACT_ID_METRIC: float(
            _current_winner_preflight_contract_id()
        ),
        WINNER_PREFLIGHT_COMPLETE_METRIC: 0.0,
        WINNER_PREFLIGHT_INCOMPLETE_METRIC: 1.0,
        WINNER_PREFLIGHT_LATTICES_METRIC: 0.0,
        WINNER_PREFLIGHT_EVALUATED_METRIC: 0.0,
        WINNER_PREFLIGHT_ELIGIBLE_METRIC: 0.0,
        WINNER_PREFLIGHT_PERSISTED_METRIC: 0.0,
        WINNER_PREFLIGHT_OMITTED_METRIC: 0.0,
        WINNER_PREFLIGHT_HARD_TIMEOUT_METRIC: float(timed_out),
        WINNER_PREFLIGHT_SUBPROCESS_FAILED_METRIC: 1.0,
    })
    return metrics


def _run_stage1_worker_attempt(
    program_path: str,
    *,
    source_sha256: str,
    contract_id: int,
    candidate_log_path: Path,
    journal_path: Path,
    inactivity_timeout: float,
) -> tuple[dict | None, str | None, bool]:
    """Run one owned child attempt and retain its exact source for retry."""

    observed = _load_stage1_preflight_journal(
        journal_path,
        source_sha256=source_sha256,
        contract_id=contract_id,
        candidate_log_path=candidate_log_path,
    )
    observed_completed = len(observed["completed_lattices"])
    observed_status = observed["status"]
    observed_progress = int(observed["progress_sequence"])
    observed_epoch = str(observed["epoch_id"])
    observed_restarts = int(observed["restart_count"])
    evaluator_path = Path(__file__).resolve()
    with tempfile.TemporaryDirectory(prefix="qcode-stage1-") as temp_dir:
        temp_root = Path(temp_dir)
        result_path = temp_root / "result.json"
        stdout_path = temp_root / "stdout.log"
        stderr_path = temp_root / "stderr.log"
        command = [
            sys.executable,
            str(evaluator_path),
            "--stage1-worker",
            os.path.abspath(program_path),
            str(result_path),
            str(os.getpid()),
        ]
        lifecycle_read_fd, lifecycle_write_fd = os.pipe()
        command.append(str(lifecycle_read_fd))
        child_environment = os.environ.copy()
        child_environment[CANDIDATE_LOG_PATH_ENV] = str(candidate_log_path)
        child_environment[WINNER_PREFLIGHT_CONTRACT_ID_ENV] = str(
            contract_id
        )
        child_environment.pop(WINNER_PREFLIGHT_REUSE_ENV, None)
        for variable in STAGE2_NUMERIC_THREAD_ENV:
            child_environment[variable] = "1"
        try:
            with stdout_path.open("wb") as stdout_file, stderr_path.open(
                "wb"
            ) as stderr_file:
                try:
                    process = subprocess.Popen(
                        command,
                        stdin=subprocess.DEVNULL,
                        stdout=stdout_file,
                        stderr=stderr_file,
                        close_fds=True,
                        env=child_environment,
                        pass_fds=(lifecycle_read_fd,),
                        start_new_session=True,
                    )
                finally:
                    os.close(lifecycle_read_fd)
                started = time.monotonic()
                deadline = started + inactivity_timeout
                absolute_deadline = (
                    started
                    + _winner_preflight_attempt_hard_timeout_s(
                        inactivity_timeout
                    )
                )
                try:
                    while True:
                        now = time.monotonic()
                        remaining = min(
                            deadline,
                            absolute_deadline,
                        ) - now
                        if remaining <= 0:
                            _terminate_stage2_process_group(process)
                            if now >= absolute_deadline:
                                reason = (
                                    "absolute wall timeout after "
                                    f"{_winner_preflight_attempt_hard_timeout_s(
                                        inactivity_timeout
                                    ):.1f}s"
                                )
                            else:
                                reason = (
                                    "wall timeout without durable lattice "
                                    "progress for "
                                    f"{inactivity_timeout:.1f}s"
                                )
                            return (
                                None,
                                "winner preflight exceeded its killable "
                                f"{reason} "
                                f"({observed_completed}/"
                                f"{len(EVOLUTION_LATTICES)} checkpointed)",
                                True,
                            )
                        try:
                            return_code = process.wait(
                                timeout=min(0.25, remaining)
                            )
                            break
                        except subprocess.TimeoutExpired:
                            journal = _load_stage1_preflight_journal(
                                journal_path,
                                source_sha256=source_sha256,
                                contract_id=contract_id,
                                candidate_log_path=candidate_log_path,
                            )
                            completed = len(
                                journal["completed_lattices"]
                            )
                            status = journal["status"]
                            progress = int(journal["progress_sequence"])
                            epoch = str(journal["epoch_id"])
                            restarts = int(journal["restart_count"])
                            if (
                                epoch != observed_epoch
                                or restarts != observed_restarts
                                or completed > observed_completed
                                or status != observed_status
                                or progress > observed_progress
                            ):
                                observed_completed = completed
                                observed_status = status
                                observed_progress = progress
                                observed_epoch = epoch
                                observed_restarts = restarts
                                deadline = min(
                                    time.monotonic() + inactivity_timeout,
                                    absolute_deadline,
                                )
                except BaseException:
                    if process.poll() is None:
                        _terminate_stage2_process_group(process)
                    raise
        finally:
            os.close(lifecycle_write_fd)

        if return_code != 0:
            stderr_tail = _read_stage2_stderr_tail(stderr_path)
            suffix = f": {stderr_tail}" if stderr_tail else ""
            return (
                None,
                "winner preflight subprocess exited with status "
                f"{return_code}{suffix}",
                False,
            )
        try:
            payload = json.loads(result_path.read_text())
        except (OSError, UnicodeDecodeError, json.JSONDecodeError) as exc:
            return (
                None,
                "winner preflight result is unreadable: "
                f"{type(exc).__name__}",
                False,
            )
        if (
            not isinstance(payload, dict)
            or set(payload) != {"schema_version", "status", "metrics"}
            or payload.get("schema_version") != 1
            or payload.get("status") != "completed"
            or not isinstance(payload.get("metrics"), dict)
        ):
            return (
                None,
                "winner preflight result schema is invalid",
                False,
            )
        return payload, None, False


def evaluate_stage1(program_path: str) -> dict:
    """Run Stage 1 with per-lattice progress walls and an exact-child retry.

    The previous wrapper applied one deadline to the whole 21-lattice
    preflight. A healthy worker was killed merely because cumulative work
    exceeded 1050 seconds. The deadline now resets after every durable
    lattice commit. If one attempt does time out, the same frozen mutation is
    restarted immediately and resumes its journal before OpenEvolve can drop
    the child.
    """

    source_sha256 = _freeze_program_source_sha256(program_path)
    contract_id = _current_winner_preflight_contract_id()
    candidate_log_path = _freeze_candidate_log_path()
    journal_path, lock_path = _stage1_preflight_journal_paths(
        candidate_log_path,
        source_sha256=source_sha256,
        contract_id=contract_id,
    )
    inactivity_timeout = _winner_preflight_hard_timeout_s()
    try:
        lock_descriptor = _open_stage1_preflight_lock(
            lock_path,
            journal_path=journal_path,
            source_sha256=source_sha256,
            contract_id=contract_id,
            candidate_log_path=candidate_log_path,
            inactivity_timeout=inactivity_timeout,
        )
    except Stage1PreflightLockTimeout as exc:
        return _winner_preflight_failure_result(
            str(exc),
            timed_out=True,
        )
    try:
        initial_journal = _load_stage1_preflight_journal(
            journal_path,
            source_sha256=source_sha256,
            contract_id=contract_id,
            candidate_log_path=candidate_log_path,
        )
        if not _path_entry_exists(journal_path):
            _write_stage1_preflight_journal(
                journal_path,
                initial_journal,
                source_sha256=source_sha256,
                contract_id=contract_id,
                candidate_log_path=candidate_log_path,
            )
        failure_message = "winner preflight did not start"
        failure_timed_out = False
        for attempt in range(1, STAGE1_PREFLIGHT_WORKER_ATTEMPTS + 1):
            try:
                payload, failure, timed_out = _run_stage1_worker_attempt(
                    program_path,
                    source_sha256=source_sha256,
                    contract_id=contract_id,
                    candidate_log_path=candidate_log_path,
                    journal_path=journal_path,
                    inactivity_timeout=inactivity_timeout,
                )
            except OSError as exc:
                payload = None
                failure = (
                    "winner preflight child could not be started or read: "
                    f"{type(exc).__name__}"
                )
                timed_out = False
            if payload is not None:
                try:
                    _assert_program_source_unchanged(
                        program_path,
                        source_sha256,
                    )
                    _register_stage1_preflight_completion(
                        program_path,
                        payload["metrics"],
                    )
                except CandidateLogWriteError as exc:
                    return _winner_preflight_failure_result(
                        f"winner preflight completion is invalid: {exc}",
                        timed_out=False,
                    )
                return payload["metrics"]
            failure_message = str(failure)
            failure_timed_out = timed_out
            failure_message += (
                f" (attempt {attempt}/"
                f"{STAGE1_PREFLIGHT_WORKER_ATTEMPTS})"
            )
        return _winner_preflight_failure_result(
            failure_message,
            timed_out=failure_timed_out,
        )
    finally:
        try:
            fcntl.flock(lock_descriptor, fcntl.LOCK_UN)
        finally:
            os.close(lock_descriptor)


def _stage2_failure_result(
    message: str,
    *,
    timed_out: bool,
    contract_id: int | None = None,
    completed_lattices: int = 0,
    stderr_tail: str = "",
):
    if contract_id is None:
        contract_id = _current_winner_preflight_contract_id()
    if (
        type(completed_lattices) is not int
        or not 0 <= completed_lattices <= len(STAGE2_DEEP_LATTICES)
    ):
        raise CandidateLogWriteError(
            "Stage 2 failure has an invalid durable lattice count"
        )
    # Deliberately omit combined_score and every MAP descriptor. OpenEvolve's
    # cascade merge lets Stage 2 overwrite Stage 1 values with same-name
    # metrics; the old all-zero error envelope therefore created a false
    # 0-0-0 archive cell. The managed launcher recognizes these exact markers
    # and quarantines the child before database.add.
    metrics = {
        STAGE2_CONTRACT_VERSION_METRIC: float(
            STAGE2_DEEP_CONTRACT_VERSION
        ),
        STAGE2_CONTRACT_ID_METRIC: float(contract_id),
        STAGE2_COMPLETE_METRIC: 0.0,
        STAGE2_INCOMPLETE_METRIC: 1.0,
        STAGE2_LATTICES_METRIC: float(completed_lattices),
        STAGE2_HARD_TIMEOUT_METRIC: float(timed_out),
        STAGE2_SUBPROCESS_FAILED_METRIC: 1.0,
    }
    artifacts = {
        "failure_stage": "stage2",
        "stage2_subprocess_error": message,
    }
    if stderr_tail:
        artifacts["stage2_stderr"] = stderr_tail
    try:
        from openevolve.evaluation_result import EvaluationResult
        return EvaluationResult(metrics=metrics, artifacts=artifacts)
    except ImportError:
        return metrics


def _validated_stage2_completion_markers(
    metrics: object,
    *,
    expected_contract_id: int,
) -> dict[str, float]:
    if not isinstance(metrics, dict):
        raise CandidateLogWriteError(
            "Stage 2 completion metrics are not an object"
        )
    values = {
        name: _exact_nonnegative_preflight_metric(metrics, name)
        for name in STAGE2_MARKER_FIELDS
    }
    if (
        values[STAGE2_CONTRACT_VERSION_METRIC]
        != STAGE2_DEEP_CONTRACT_VERSION
        or values[STAGE2_CONTRACT_ID_METRIC] != expected_contract_id
        or values[STAGE2_COMPLETE_METRIC] != 1
        or values[STAGE2_INCOMPLETE_METRIC] != 0
        or values[STAGE2_LATTICES_METRIC]
        != len(STAGE2_DEEP_LATTICES)
        or values[STAGE2_HARD_TIMEOUT_METRIC] != 0
        or values[STAGE2_SUBPROCESS_FAILED_METRIC] != 0
    ):
        raise CandidateLogWriteError(
            "Stage 2 completion markers are inconsistent"
        )
    return {name: float(values[name]) for name in STAGE2_MARKER_FIELDS}


def _terminate_stage2_process_group(process: subprocess.Popen) -> None:
    """Terminate a private Stage 2 process group without leaving descendants."""

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
    # The lifecycle guardian deliberately ignores SIGTERM, keeping this PGID
    # owned until the whole group is killed.  Always escalate even when the
    # leader exited promptly: another descendant may ignore TERM.
    try:
        os.killpg(process.pid, signal.SIGKILL)
    except ProcessLookupError:
        pass
    if not leader_reaped:
        process.wait()


def _read_stage2_stderr_tail(path: Path, limit: int = 8192) -> str:
    try:
        return path.read_bytes()[-limit:].decode("utf-8", errors="replace")
    except OSError:
        return ""


def _stage2_hard_timeout_s() -> float:
    raw = os.environ.get(
        STAGE2_OUTER_TIMEOUT_ENV,
        str(STAGE2_OUTER_TIMEOUT_DEFAULT_S),
    )
    try:
        outer_timeout = float(raw)
    except (TypeError, ValueError) as exc:
        raise RuntimeError(
            f"{STAGE2_OUTER_TIMEOUT_ENV} must be numeric"
        ) from exc
    if (
        not math.isfinite(outer_timeout)
        or outer_timeout <= STAGE2_OUTER_TIMEOUT_MARGIN_S
    ):
        raise RuntimeError(
            f"{STAGE2_OUTER_TIMEOUT_ENV} leaves no hard-timeout margin"
        )
    return min(
        STAGE2_HARD_TIMEOUT_MAX_S,
        outer_timeout - STAGE2_OUTER_TIMEOUT_MARGIN_S,
    )


def _stage2_attempt_hard_timeout_s(
    inactivity_timeout: float,
) -> float:
    """Absolute non-resettable wall for one owned Stage 2 child."""

    return inactivity_timeout * (len(STAGE2_DEEP_LATTICES) + 1)


def _stage2_deep_progress_snapshot(
    journal_path: Path,
    *,
    source_sha256: str,
    contract_id: int,
    candidate_log_path: Path,
    preflight_sha256: str,
) -> tuple[str, int, int, str]:
    if not _path_entry_exists(journal_path):
        return ("", 0, 0, "missing")
    journal = _load_stage2_deep_journal(
        journal_path,
        source_sha256=source_sha256,
        contract_id=contract_id,
        candidate_log_path=candidate_log_path,
        preflight_sha256=preflight_sha256,
    )
    return (
        str(journal["epoch_id"]),
        int(journal["progress_sequence"]),
        len(journal["completed_lattices"]),
        str(journal["status"]),
    )


def _open_stage2_deep_lock(
    lock_path: Path,
    *,
    journal_path: Path,
    source_sha256: str,
    contract_id: int,
    candidate_log_path: Path,
    preflight_sha256: str,
    inactivity_timeout: float,
) -> int:
    flags = os.O_RDWR | os.O_CREAT | os.O_CLOEXEC
    if hasattr(os, "O_NOFOLLOW"):
        flags |= os.O_NOFOLLOW
    descriptor = os.open(lock_path, flags, 0o600)
    if not stat.S_ISREG(os.fstat(descriptor).st_mode):
        os.close(descriptor)
        raise CandidateLogWriteError(
            f"Stage 2 journal lock is not regular: {lock_path}"
        )
    try:
        try:
            fcntl.flock(
                descriptor,
                fcntl.LOCK_EX | fcntl.LOCK_NB,
            )
            return descriptor
        except BlockingIOError:
            pass
        observed = _stage2_deep_progress_snapshot(
            journal_path,
            source_sha256=source_sha256,
            contract_id=contract_id,
            candidate_log_path=candidate_log_path,
            preflight_sha256=preflight_sha256,
        )
        started = time.monotonic()
        deadline = started + inactivity_timeout
        absolute_deadline = (
            started
            + _stage2_attempt_hard_timeout_s(inactivity_timeout)
            * STAGE2_DEEP_WORKER_ATTEMPTS
        )
        while True:
            remaining = min(deadline, absolute_deadline) - time.monotonic()
            if remaining <= 0:
                raise Stage2DeepLockTimeout(
                    "Stage 2 source lock owner made no durable progress for "
                    f"{inactivity_timeout:.1f}s"
                )
            time.sleep(min(0.25, remaining))
            try:
                fcntl.flock(
                    descriptor,
                    fcntl.LOCK_EX | fcntl.LOCK_NB,
                )
                return descriptor
            except BlockingIOError:
                progress = _stage2_deep_progress_snapshot(
                    journal_path,
                    source_sha256=source_sha256,
                    contract_id=contract_id,
                    candidate_log_path=candidate_log_path,
                    preflight_sha256=preflight_sha256,
                )
                if (
                    progress[0] != observed[0]
                    or progress[1] > observed[1]
                    or progress[2] > observed[2]
                    or progress[3] != observed[3]
                ):
                    observed = progress
                    deadline = min(
                        time.monotonic() + inactivity_timeout,
                        absolute_deadline,
                    )
    except BaseException:
        os.close(descriptor)
        raise


def _run_stage2_worker_attempt(
    program_path: str,
    *,
    preflight_reuse: dict | None,
    source_sha256: str,
    contract_id: int,
    candidate_log_path: Path,
    preflight_sha256: str,
    journal_path: Path,
    inactivity_timeout: float,
) -> tuple[dict | None, str | None, bool]:
    """Run one Stage 2 child while durable lattice progress renews its wall."""

    observed = _load_stage2_deep_journal(
        journal_path,
        source_sha256=source_sha256,
        contract_id=contract_id,
        candidate_log_path=candidate_log_path,
        preflight_sha256=preflight_sha256,
    )
    observed_epoch = str(observed["epoch_id"])
    observed_progress = int(observed["progress_sequence"])
    observed_completed = len(observed["completed_lattices"])
    observed_status = str(observed["status"])
    evaluator_path = Path(__file__).resolve()
    with tempfile.TemporaryDirectory(prefix="qcode-stage2-") as temp_dir:
        temp_root = Path(temp_dir)
        result_path = temp_root / "result.json"
        stdout_path = temp_root / "stdout.log"
        stderr_path = temp_root / "stderr.log"
        command = [
            sys.executable,
            str(evaluator_path),
            "--stage2-worker",
            os.path.abspath(program_path),
            str(result_path),
            str(os.getpid()),
        ]
        lifecycle_read_fd, lifecycle_write_fd = os.pipe()
        command.append(str(lifecycle_read_fd))
        child_environment = os.environ.copy()
        child_environment[CANDIDATE_LOG_PATH_ENV] = str(
            candidate_log_path
        )
        child_environment[WINNER_PREFLIGHT_CONTRACT_ID_ENV] = str(
            contract_id
        )
        if preflight_reuse is not None:
            child_environment[WINNER_PREFLIGHT_REUSE_ENV] = json.dumps(
                preflight_reuse,
                sort_keys=True,
                separators=(",", ":"),
            )
        else:
            child_environment.pop(WINNER_PREFLIGHT_REUSE_ENV, None)
        for variable in STAGE2_NUMERIC_THREAD_ENV:
            child_environment[variable] = "1"
        try:
            with stdout_path.open("wb") as stdout_file, stderr_path.open(
                "wb"
            ) as stderr_file:
                try:
                    process = subprocess.Popen(
                        command,
                        stdin=subprocess.DEVNULL,
                        stdout=stdout_file,
                        stderr=stderr_file,
                        close_fds=True,
                        env=child_environment,
                        pass_fds=(lifecycle_read_fd,),
                        start_new_session=True,
                    )
                finally:
                    os.close(lifecycle_read_fd)
                started = time.monotonic()
                deadline = started + inactivity_timeout
                absolute_deadline = (
                    started
                    + _stage2_attempt_hard_timeout_s(
                        inactivity_timeout
                    )
                )
                try:
                    while True:
                        now = time.monotonic()
                        remaining = min(
                            deadline,
                            absolute_deadline,
                        ) - now
                        if remaining <= 0:
                            _terminate_stage2_process_group(process)
                            if now >= absolute_deadline:
                                reason = (
                                    "absolute wall timeout after "
                                    f"{_stage2_attempt_hard_timeout_s(
                                        inactivity_timeout
                                    ):.1f}s"
                                )
                            else:
                                reason = (
                                    "wall timeout without durable lattice "
                                    "progress for "
                                    f"{inactivity_timeout:.1f}s"
                                )
                            return (
                                None,
                                "Stage 2 exceeded its killable "
                                f"{reason} ({observed_completed}/"
                                f"{len(STAGE2_DEEP_LATTICES)} "
                                "checkpointed)",
                                True,
                            )
                        try:
                            return_code = process.wait(
                                timeout=min(0.25, remaining)
                            )
                            break
                        except subprocess.TimeoutExpired:
                            journal = _load_stage2_deep_journal(
                                journal_path,
                                source_sha256=source_sha256,
                                contract_id=contract_id,
                                candidate_log_path=candidate_log_path,
                                preflight_sha256=preflight_sha256,
                            )
                            epoch = str(journal["epoch_id"])
                            progress = int(
                                journal["progress_sequence"]
                            )
                            completed = len(
                                journal["completed_lattices"]
                            )
                            status = str(journal["status"])
                            if (
                                epoch != observed_epoch
                                or progress > observed_progress
                                or completed > observed_completed
                                or status != observed_status
                            ):
                                observed_epoch = epoch
                                observed_progress = progress
                                observed_completed = completed
                                observed_status = status
                                deadline = min(
                                    time.monotonic()
                                    + inactivity_timeout,
                                    absolute_deadline,
                                )
                except BaseException:
                    if process.poll() is None:
                        _terminate_stage2_process_group(process)
                    raise
        finally:
            os.close(lifecycle_write_fd)

        stderr_tail = _read_stage2_stderr_tail(stderr_path)
        if return_code != 0:
            suffix = f": {stderr_tail}" if stderr_tail else ""
            return (
                None,
                "Stage 2 subprocess exited with status "
                f"{return_code}{suffix}",
                False,
            )
        try:
            payload = json.loads(result_path.read_text())
        except (OSError, UnicodeDecodeError, json.JSONDecodeError) as exc:
            return (
                None,
                f"Stage 2 result is unreadable: {type(exc).__name__}",
                False,
            )
        if (
            not isinstance(payload, dict)
            or set(payload) != {
                "schema_version",
                "status",
                "metrics",
                "artifacts",
            }
            or payload.get("schema_version") != 1
            or payload.get("status") != "completed"
            or not isinstance(payload.get("metrics"), dict)
            or not isinstance(payload.get("artifacts"), dict)
        ):
            return None, "Stage 2 result schema is invalid", False
        try:
            _validated_stage2_completion_markers(
                payload["metrics"],
                expected_contract_id=contract_id,
            )
        except CandidateLogWriteError as exc:
            return (
                None,
                f"Stage 2 result is incomplete: {exc}",
                False,
            )
        return payload, None, False


def _evaluate_stage2_managed(program_path: str) -> dict:
    """Run Stage 2 with per-lattice progress walls and exact-child retry.

    OpenEvolve 0.2.26 applies ``asyncio.wait_for`` to an executor thread.
    Cancelling that await does not stop the thread, so a timed-out evaluator
    can otherwise keep consuming CPU after its iteration was finalized. A
    private subprocess group makes the boundary real. The inactivity deadline
    now renews only when a durable lattice sidecar advances; a replacement
    child resumes the same frozen mutation once before the launcher receives
    a versioned incomplete envelope.
    """

    source_sha256 = _freeze_program_source_sha256(program_path)
    contract_id = _current_winner_preflight_contract_id()
    candidate_log_path = _freeze_candidate_log_path()
    preflight_reuse = _take_stage1_preflight_completion(program_path)
    preflight_markers = (
        preflight_reuse.get("markers")
        if isinstance(preflight_reuse, dict)
        else None
    )
    preflight_sha256 = _stage2_preflight_sha256(
        preflight_markers,
        contract_id=contract_id,
    )
    journal_path, lock_path = _stage2_deep_journal_paths(
        candidate_log_path,
        source_sha256=source_sha256,
        contract_id=contract_id,
        preflight_sha256=preflight_sha256,
    )
    inactivity_timeout = _stage2_hard_timeout_s()
    try:
        lock_descriptor = _open_stage2_deep_lock(
            lock_path,
            journal_path=journal_path,
            source_sha256=source_sha256,
            contract_id=contract_id,
            candidate_log_path=candidate_log_path,
            preflight_sha256=preflight_sha256,
            inactivity_timeout=inactivity_timeout,
        )
    except Stage2DeepLockTimeout as exc:
        return _stage2_failure_result(
            str(exc),
            timed_out=True,
            contract_id=contract_id,
        )
    try:
        journal = _load_stage2_deep_journal(
            journal_path,
            source_sha256=source_sha256,
            contract_id=contract_id,
            candidate_log_path=candidate_log_path,
            preflight_sha256=preflight_sha256,
        )
        if not _path_entry_exists(journal_path):
            journal = _write_stage2_deep_journal(
                journal_path,
                journal,
                source_sha256=source_sha256,
                contract_id=contract_id,
                candidate_log_path=candidate_log_path,
                preflight_sha256=preflight_sha256,
            )
        failure_message = "Stage 2 did not start"
        failure_timed_out = False
        for attempt in range(1, STAGE2_DEEP_WORKER_ATTEMPTS + 1):
            try:
                payload, failure, timed_out = _run_stage2_worker_attempt(
                    program_path,
                    preflight_reuse=preflight_reuse,
                    source_sha256=source_sha256,
                    contract_id=contract_id,
                    candidate_log_path=candidate_log_path,
                    preflight_sha256=preflight_sha256,
                    journal_path=journal_path,
                    inactivity_timeout=inactivity_timeout,
                )
            except (OSError, CandidateLogWriteError) as exc:
                payload = None
                failure = (
                    "Stage 2 child could not be started, resumed, or read: "
                    f"{type(exc).__name__}: {exc}"
                )
                timed_out = False
            if payload is not None:
                _assert_program_source_unchanged(
                    program_path,
                    source_sha256,
                )
                try:
                    from openevolve.evaluation_result import EvaluationResult
                    return EvaluationResult(
                        metrics=payload["metrics"],
                        artifacts=payload["artifacts"],
                    )
                except ImportError:
                    return payload["metrics"]
            failure_message = (
                f"{failure} (attempt {attempt}/"
                f"{STAGE2_DEEP_WORKER_ATTEMPTS})"
            )
            failure_timed_out = bool(timed_out)
        journal = _load_stage2_deep_journal(
            journal_path,
            source_sha256=source_sha256,
            contract_id=contract_id,
            candidate_log_path=candidate_log_path,
            preflight_sha256=preflight_sha256,
        )
        return _stage2_failure_result(
            failure_message,
            timed_out=failure_timed_out,
            contract_id=contract_id,
            completed_lattices=len(journal["completed_lattices"]),
        )
    finally:
        try:
            fcntl.flock(lock_descriptor, fcntl.LOCK_UN)
        finally:
            os.close(lock_descriptor)


def evaluate_stage2(program_path: str) -> dict:
    """Return only a versioned incomplete envelope for managed failures."""

    contract_id = _current_winner_preflight_contract_id()
    try:
        return _evaluate_stage2_managed(program_path)
    except Exception as exc:
        return _stage2_failure_result(
            "Stage 2 wrapper failed before a complete result: "
            f"{type(exc).__name__}: {exc}",
            timed_out=False,
            contract_id=contract_id,
        )


def _write_preflight_worker_result(
    result_path: str,
    metrics: dict,
) -> None:
    payload = {
        "schema_version": 1,
        "status": "completed",
        "metrics": metrics,
    }
    destination = Path(result_path)
    if destination.is_symlink() or destination.exists():
        raise FileExistsError(
            f"refusing to overwrite preflight result: {destination}"
        )
    temporary = destination.with_name(
        f".{destination.name}.tmp-{os.getpid()}"
    )
    encoded = json.dumps(
        payload,
        sort_keys=True,
        separators=(",", ":"),
        allow_nan=False,
    ).encode("utf-8")
    descriptor = os.open(
        temporary,
        os.O_WRONLY | os.O_CREAT | os.O_EXCL | os.O_CLOEXEC,
        0o600,
    )
    try:
        written = 0
        while written < len(encoded):
            count = os.write(descriptor, encoded[written:])
            if count <= 0:
                raise OSError("preflight result write made no progress")
            written += count
        os.fsync(descriptor)
    finally:
        os.close(descriptor)
    os.replace(temporary, destination)


def _stage1_worker_main(program_path: str, result_path: str) -> int:
    metrics = _evaluate_stage1_resumable_impl(program_path)
    if not isinstance(metrics, dict):
        raise TypeError("Stage 1 worker returned an invalid result")
    _write_preflight_worker_result(result_path, metrics)
    return 0


def _preflight_worker_main(program_path: str, result_path: str) -> int:
    metrics, _generate_fn, _candidate_log_path, _source_sha256 = (
        _run_resumable_winner_preflight(program_path)
    )
    if not isinstance(metrics, dict):
        raise TypeError("preflight worker returned an invalid result")
    _write_preflight_worker_result(result_path, metrics)
    return 0


def _stage2_worker_main(program_path: str, result_path: str) -> int:
    result = _evaluate_stage2_impl(program_path)
    metrics = getattr(result, "metrics", result)
    artifacts = getattr(result, "artifacts", {})
    if not isinstance(metrics, dict) or not isinstance(artifacts, dict):
        raise TypeError("Stage 2 worker returned an invalid result")
    payload = {
        "schema_version": 1,
        "status": "completed",
        "metrics": metrics,
        "artifacts": artifacts,
    }
    destination = Path(result_path)
    if destination.is_symlink() or destination.exists():
        raise FileExistsError(f"refusing to overwrite Stage 2 result: {destination}")
    temporary = destination.with_name(
        f".{destination.name}.tmp-{os.getpid()}"
    )
    encoded = json.dumps(
        payload,
        sort_keys=True,
        separators=(",", ":"),
        allow_nan=False,
    ).encode("utf-8")
    descriptor = os.open(
        temporary,
        os.O_WRONLY | os.O_CREAT | os.O_EXCL | os.O_CLOEXEC,
        0o600,
    )
    try:
        written = 0
        while written < len(encoded):
            count = os.write(descriptor, encoded[written:])
            if count <= 0:
                raise OSError("Stage 2 result write made no progress")
            written += count
        os.fsync(descriptor)
    finally:
        os.close(descriptor)
    os.replace(temporary, destination)
    return 0


def evaluate_stage2_milp(program_path: str) -> dict:
    """Stage 2 with parallel MILP distance verification.

    Two-phase approach:
    1. Quick k-only screening on all lattices (sequential, ~3s)
    2. Parallel MILP verification for top candidates across all lattices

    Key improvements over Campaign 4:
    - Parallel MILP evaluation using ProcessPoolExecutor (10 workers)
    - 300s per-logical timeout (proven sufficient for n≤288 exact)
    - 7200s total timeout per code (covers k=12-24 fully)
    - Incremental code persistence to JSONL after each solve
    - Scoring: only exact distance may contribute bounded FOM credit;
      incumbents/timeouts receive bounded survivor/proof-progress treatment
    - Symplectic weight pre-filter: codes with d_symp≤4 skip MILP entirely
    - Better LLM feedback with clear signal about what works vs doesn't
    """
    # The launcher may execute a patched copy from inside the output
    # directory. Freeze its absolute routing before importing evolved code;
    # deriving paths from this copy's ``__file__`` would otherwise create a
    # nested ``results/evolution/results`` tree.
    candidate_log_path = _freeze_milp_candidate_log_path()
    try:
        generate_fn = _load_generate_candidates(program_path)
    except Exception as e:
        return _error_result(str(e))

    # MILP budget parameters
    MILP_TIMEOUT_PER_LOGICAL = 300   # 300s proven sufficient (milp_optimality_audit.json)
    MILP_TOTAL_TIMEOUT = 7200        # 2h per code -- covers k≤24 fully
    MILP_EARLY_STOP = 4              # Exit immediately if d≤4
    MAX_DISTANCE_PER_LATTICE = 5     # Top-5 per lattice → ~30 MILP tasks
    MIN_RELEVANT_D = 6               # Only d≥6 codes contribute to score

    # Save path for incremental MILP persistence
    codes_jsonl = str(
        candidate_log_path.with_name("evolution_codes.jsonl")
    )

    # ── Phase 1: k-only screening (parallel) ───────────────────────
    # Collect all candidates across lattices, then evaluate in parallel
    # using ProcessPoolExecutor.  ~10x faster than sequential (~3 min
    # vs ~30 min for 120k candidates).
    all_quick_tasks = []  # (ell, m, A_terms, B_terms)
    total_candidates = 0
    errors = []

    for ell, m in STAGE2_LATTICES_MILP:
        try:
            candidates = generate_fn(ell, m)
            if not isinstance(candidates, list):
                errors.append(f"({ell},{m}): returned {type(candidates)}, not list")
                continue
            total_candidates += len(candidates)
            # Cap at 20000 per lattice.
            # Priority candidates (perturbations, simultaneous perturbations)
            # are generated first in the seed, so they survive the cap.
            # Strategy 4's exhaustive search fills remaining slots.
            if len(candidates) > 20000:
                errors.append(f"({ell},{m}): {len(candidates)} candidates, capped to 20000")
                candidates = candidates[:20000]

            normalized_candidates, malformed = _normalize_generated_candidates(
                candidates,
                ell=ell,
                m=m,
            )
            errors.extend(malformed)
            for candidate in normalized_candidates:
                A_terms, B_terms, geometry = _candidate_components(candidate)
                canonical_geometry = normalize_geometry(ell, m, geometry)
                task = (ell, m, A_terms, B_terms)
                if canonical_geometry is not None:
                    task = (*task, canonical_geometry)
                all_quick_tasks.append(task)
        except Exception as e:
            errors.append(f"({ell},{m}): {type(e).__name__}: {e}")

    all_quick_results = evaluate_batch_milp_parallel(
        all_quick_tasks, quick=True,
    )

    # ── Phase 2: Select top candidates for MILP ────────────────────
    # Use d_symplectic to filter and rank -- only codes with d_symp ≥ 5
    # are worth MILP verification (d_symp ≤ 4 already resolved by
    # evaluate_candidate_milp's pre-filter).  Among qualifying codes,
    # rank by approximate FOM = k * d_symp² / n.
    milp_tasks = []  # (ell, m, A_terms, B_terms)
    milp_skipped_low_d_symp = 0

    for ell, m in STAGE2_LATTICES_MILP:
        lattice_results = [
            r for r in all_quick_results
            if r.get("ell") == ell and r.get("m") == m
            and r.get("k", 0) >= 4
        ]

        # Filter: only consider codes with d_symplectic high enough to
        # potentially have d ≥ MIN_RELEVANT_D.  This is the key optimization
        # from the symplectic basis pre-filter.
        promising = []
        for r in lattice_results:
            d_s = r.get("d_symplectic", 0)
            if d_s > MILP_EARLY_STOP:
                promising.append(r)
            else:
                milp_skipped_low_d_symp += 1

        # A larger symplectic-basis weight is only a looser distance upper
        # bound, not evidence of larger true distance.  Use it to eliminate
        # low-distance rows above, but never to buy MILP budget.  Within one
        # lattice, exact k is a safe first-order priority; the later passes
        # retain k/A-polynomial diversity.
        def _rank_key(r):
            return (
                int(r.get("k", 0) or 0),
                _definition_key(r),
            )
        promising.sort(key=_rank_key, reverse=True)

        # Diversify: pick top candidates by k, A-polynomial diversity
        seen_k: set[int] = set()
        top: list[dict] = []
        for r in promising:
            if r["k"] not in seen_k and len(top) < MAX_DISTANCE_PER_LATTICE:
                seen_k.add(r["k"])
                top.append(r)
        seen_a: set[tuple] = {tuple(map(tuple, r["A_terms"])) for r in top}
        for r in promising:
            if len(top) >= MAX_DISTANCE_PER_LATTICE:
                break
            a_key = tuple(map(tuple, r["A_terms"]))
            if a_key not in seen_a and r not in top:
                seen_a.add(a_key)
                top.append(r)
        for r in promising:
            if len(top) >= MAX_DISTANCE_PER_LATTICE:
                break
            if r not in top:
                top.append(r)

        for r in top:
            canonical_geometry = normalize_geometry(
                ell, m, r.get("geometry")
            )
            task = (ell, m, r["A_terms"], r["B_terms"])
            if canonical_geometry is not None:
                task = (*task, canonical_geometry)
            milp_tasks.append(task)

    # ── Phase 3: Parallel MILP verification ────────────────────────
    # Run all MILP tasks in parallel using ProcessPoolExecutor.
    # Each result is saved to JSONL immediately after solving.
    milp_results = []
    if milp_tasks:
        milp_results = evaluate_milp_parallel(
            milp_tasks,
            milp_timeout_per_logical=MILP_TIMEOUT_PER_LOGICAL,
            milp_total_timeout=MILP_TOTAL_TIMEOUT,
            milp_early_stop=MILP_EARLY_STOP,
            save_path=codes_jsonl,
        )

    # Combine: MILP results + k-only results (for codes that didn't get MILP)
    all_results = list(milp_results)
    milp_keys = {_definition_key(r) for r in milp_results}
    for r in all_quick_results:
        key = _definition_key(r)
        if key not in milp_keys and r.get("k", 0) > 0:
            all_results.append(r)

    # ── Phase 4: Upper-bound-safe scoring ───────────────────────────
    # A MILP incumbent is a feasible logical operator and therefore only an
    # upper bound on distance.  Reuse the contract-v2 scorer so its magnitude
    # never contributes d²/FOM fitness.  Exact rows may receive capped distance
    # credit; partial/timeout rows receive at most one bounded survivor credit
    # per historical fitness lattice plus the same small tie-breaks.
    scoring_rows = _legacy_milp_upper_bound_safe_rows(all_results)
    score = _score_stage2_upper_bound_safe(scoring_rows)
    combined = float(score["combined_score"])

    # Aggregate exact metrics separately from diagnostic MILP upper bounds.
    valid = [r for r in all_results if r.get("k", 0) > 0]
    exact_rows = _verified_distance_persistence_rows(all_results)
    exact_foms = [
        float(r.get("fom", 0.0))
        for r in exact_rows
        if (
            isinstance(r.get("fom"), (int, float))
            and not isinstance(r.get("fom"), bool)
            and math.isfinite(float(r.get("fom")))
            and float(r.get("fom")) > 0
        )
    ]
    upper_bound_foms = [
        _bp_fom_upper_bound(r)
        for r in all_results
        if r.get("distance_status") == "upper_bound"
    ]
    upper_bound_foms = [value for value in upper_bound_foms if value > 0]
    best_fom = max(exact_foms) if exact_foms else 0.0
    mean_fom = (
        sum(exact_foms) / len(exact_foms) if exact_foms else 0.0
    )
    best_milp_fom_upper_bound = (
        max(upper_bound_foms) if upper_bound_foms else 0.0
    )
    mean_milp_fom_upper_bound = (
        sum(upper_bound_foms) / len(upper_bound_foms)
        if upper_bound_foms
        else 0.0
    )
    high_k_codes = [r for r in valid if r.get("k", 0) >= 8]
    lattices_with_high_k = len(set(
        (r["ell"], r["m"]) for r in high_k_codes
    ))
    num_above_6 = sum(1 for f in exact_foms if f >= 6.0)
    num_above_12 = sum(1 for f in exact_foms if f >= 12.0)
    num_milp_upper_bounds_above_6 = sum(
        value >= 6.0 for value in upper_bound_foms
    )
    num_milp_upper_bounds_above_12 = sum(
        value >= 12.0 for value in upper_bound_foms
    )

    # ── Phase 5: LLM feedback artifacts ────────────────────────────
    artifacts = {}

    def _stage_tag(r):
        """Human-readable label for MILP result quality."""
        stage = r.get("stage", "")
        if stage == "milp_exact":
            return "exact"
        elif stage == "milp_incumbent":
            return "d\u2264" + str(r["d"])
        elif stage == "milp_promising_timeout":
            return "d>" + str(r.get("milp_details", {}).get("early_stop", 4))
        elif stage in ("milp_low_d", "symplectic_low_d"):
            return "exact" if r.get("d", 0) <= 2 else f"d\u2264{r['d']}"
        return ""

    # Reference codes for perturbation gradient analysis
    _REFERENCE_CODES = [
        {"ell": 12, "m": 6, "A": [(3,0),(0,1),(0,2)], "B": [(0,3),(1,0),(2,0)],
         "d": 12, "k": 12, "name": "[[144,12,12]] gross"},
        {"ell": 12, "m": 12, "A": [(3,0),(0,2),(0,7)], "B": [(0,3),(1,0),(2,0)],
         "d": 18, "k": 12, "name": "[[288,12,18]] bravyi"},
        {"ell": 12, "m": 12, "A": [(6,0),(0,1),(0,2)], "B": [(0,3),(2,0),(4,0)],
         "d": 12, "k": 24, "name": "[[288,24,12]]"},
        {"ell": 12, "m": 12, "A": [(3,0),(0,1),(0,2)], "B": [(0,3),(1,0),(2,0)],
         "d": 12, "k": 16, "name": "[[288,16,12]] gross-scaled"},
        {"ell": 15, "m": 12, "A": [(3,0),(0,2),(0,4)], "B": [(0,6),(2,0),(4,0)],
         "d": 14, "k": 16, "name": "[[360,16,14]]"},
        {"ell": 30, "m": 6, "A": [(9,0),(0,1),(0,2)], "B": [(0,3),(25,0),(26,0)],
         "d": 24, "k": 12, "name": "[[360,12,24]] bravyi"},
    ]

    def _exponent_diff(terms1, terms2):
        """Count changed exponent positions between sorted term lists."""
        s1 = sorted(tuple(t) for t in terms1)
        s2 = sorted(tuple(t) for t in terms2)
        return sum(1 for a, b in zip(s1, s2) if a != b)

    def _describe_diff(terms1, terms2, poly_name):
        """Describe exponent changes between two polynomials."""
        s1 = sorted(tuple(t) for t in terms1)
        s2 = sorted(tuple(t) for t in terms2)
        changes = []
        for a, b in zip(s1, s2):
            if a != b:
                changes.append(f"{poly_name}: {a}->{b}")
        return changes

    # Only exact distances may be described as achieved codes.  Incumbents
    # remain useful diagnostic upper-bound witnesses, but cannot be selected as
    # the "best code" or presented as beating a published baseline.
    codes_with_d = list(exact_rows)
    unresolved_rows = [
        row
        for row in scoring_rows
        if _is_stage2_search_survivor(row)
        and row.get("search_status") == "unresolved"
    ]

    # Best code
    if codes_with_d:
        bc = max(codes_with_d, key=lambda r: r["fom"])
        tag = _stage_tag(bc)
        # Check if it beats any Bravyi baseline
        bravyi_foms = {144: 12.0, 288: 13.5, 360: 19.2}
        beat_bravyi = bc["fom"] > bravyi_foms.get(bc["n"], float("inf"))
        beat_tag = "  ← BEATS BRAVYI!" if beat_bravyi else ""
        artifacts["best_code"] = (
            f"[[{bc['n']},{bc['k']},{bc['d']}]] FOM={bc['fom']:.2f} "
            f"({tag}) at ({bc['ell']},{bc['m']}){beat_tag}\n"
            f"  A={bc['A_terms']}\n"
            f"  B={bc['B_terms']}"
        )

    if unresolved_rows:
        survivor = max(
            unresolved_rows,
            key=lambda row: (
                _stage2_result_rate(row),
                _definition_key(row),
            ),
        )
        artifacts["best_milp_survivor"] = (
            f"[[{survivor['n']},{survivor['k']},d=unresolved]] "
            f"rate={_stage2_result_rate(survivor):.3f} at "
            f"({survivor['ell']},{survivor['m']}); unresolved MILP result, "
            "upper-bound magnitude withheld, no achieved FOM or win claim\n"
            f"  A={survivor['A_terms']}\n"
            f"  B={survivor['B_terms']}"
        )

    if errors:
        artifacts["errors"] = "\n".join(errors[:5])

    # Top codes with d ≥ MIN_RELEVANT_D (the useful ones)
    relevant_codes = [r for r in codes_with_d if r.get("d", 0) >= MIN_RELEVANT_D]
    top5 = sorted(relevant_codes, key=lambda r: r.get("fom", 0), reverse=True)[:5]
    if top5:
        top5_lines = []
        for r in top5:
            tag = _stage_tag(r)
            tag_str = f" ({tag})" if tag else ""
            top5_lines.append(
                f"  [[{r['n']},{r['k']},{r['d']}]] FOM={r['fom']:.1f}"
                f"{tag_str} ({r['ell']},{r['m']})"
            )
        artifacts["top_codes"] = "Top codes with d>=" + str(MIN_RELEVANT_D) + ":\n" + "\n".join(top5_lines)

    # Low-d summary (to teach the LLM what's bad)
    low_d_count = sum(1 for r in codes_with_d if r.get("d", 0) < MIN_RELEVANT_D)
    if low_d_count > 0:
        max_k_low_d = max(
            (r.get("k", 0) for r in codes_with_d if r.get("d", 0) < MIN_RELEVANT_D),
            default=0,
        )
        artifacts["low_d_warning"] = (
            f"{low_d_count} codes with d<{MIN_RELEVANT_D} (max k={max_k_low_d}) -- "
            "these exact results cannot meet the intended distance objective. "
            f"Avoid univariate (A=f(y),B=g(x)) and self-dual (A=B)."
        )

    # Distance gradient analysis: compare MILP results to reference codes
    # to show the LLM how exponent changes affect d.
    gradient_lines = []
    for ref in _REFERENCE_CODES:
        ref_lattice = (ref["ell"], ref["m"])
        sorted(tuple(t) for t in ref["A"])
        sorted(tuple(t) for t in ref["B"])
        # Find MILP results at the same lattice that are close perturbations
        perturbations = []
        for r in codes_with_d:
            if (r["ell"], r["m"]) != ref_lattice:
                continue
            diff_a = _exponent_diff(r["A_terms"], ref["A"])
            diff_b = _exponent_diff(r["B_terms"], ref["B"])
            total_diff = diff_a + diff_b
            if 0 < total_diff <= 3:  # close perturbation, not identical
                changes = _describe_diff(ref["A"], r["A_terms"], "A")
                changes += _describe_diff(ref["B"], r["B_terms"], "B")
                d_delta = r["d"] - ref["d"]
                sign = "+" if d_delta > 0 else ""
                tag = _stage_tag(r)
                perturbations.append((
                    r["d"], d_delta, r.get("k", 0),
                    f"    d={r['d']} ({tag}) k={r['k']} [{', '.join(changes)}] "
                    f"d_change={sign}{d_delta}"
                ))
        if perturbations:
            # Sort: best d first
            perturbations.sort(key=lambda x: -x[0])
            gradient_lines.append(f"  Perturbations of {ref['name']} (d={ref['d']}, k={ref['k']}):")
            for _, _, _, line in perturbations[:5]:  # top 5
                gradient_lines.append(line)

    if gradient_lines:
        artifacts["distance_gradients"] = (
            "Distance gradients (how exponent changes affect d):\n"
            + "\n".join(gradient_lines)
        )

    # Per-lattice breakdown uses bounded credit, never incumbent FOM.
    lattice_lines = []
    per_lattice_credit = score["per_lattice_credit"]
    assert isinstance(per_lattice_credit, dict)
    for key in sorted(per_lattice_credit):
        lattice_lines.append(
            f"  ({key[0]},{key[1]}): bounded credit="
            f"{per_lattice_credit[key]:.3f}"
        )

    artifacts["summary"] = (
        f"Evaluated {total_candidates} candidates across "
        f"{len(STAGE2_LATTICES_MILP)} lattices.\n"
        f"MILP attempted: {len(milp_tasks)} codes ({milp_skipped_low_d_symp} "
        f"skipped by symplectic pre-filter d_symp<={MILP_EARLY_STOP}).\n"
        f"Valid codes (k>0): {len(valid)}\n"
        f"Exact codes with d>={MIN_RELEVANT_D}: {len(relevant_codes)}\n"
        f"Best exact FOM: {best_fom:.2f}\n"
        "MILP upper-bound diagnostics retained in telemetry only.\n"
        f"Unresolved MILP survivors: {len(unresolved_rows)}; "
        f"terminal negatives: {score['terminal_negative_count']}\n"
        f"Combined score: {combined:.3f} = "
        f"{score['fitness_survivor_credit']:.3f} bounded survivor + "
        f"{score['fitness_distance_credit']:.3f} exact distance + "
        f"{score['fitness_rate_tie_break']:.3f} rate tie-break + "
        f"{score['fitness_structural_tie_break']:.3f} structure tie-break; "
        "MILP upper-bound magnitude contributes zero.\n"
        f"Per-lattice breakdown:\n" + "\n".join(lattice_lines)
    )

    # ── Phase 6: Persistence ───────────────────────────────────────
    # Individual codes are already saved to JSONL by evaluate_milp_parallel.
    # Also save to discovered_codes.json and pareto_front.json for compat.
    to_save = [
        r
        for r in exact_rows
        if float(r.get("fom", 0.0) or 0.0) > 6.0
    ]
    if to_save:
        best_to_save = max(to_save, key=lambda r: r["fom"])
        try:
            save_code(best_to_save)
            update_pareto_front(to_save)
        except Exception:
            pass

    _write_metrics_jsonl({
        "best_fom": best_fom,
        "mean_fom": mean_fom,
        "best_milp_fom_upper_bound": best_milp_fom_upper_bound,
        "mean_milp_fom_upper_bound": mean_milp_fom_upper_bound,
        "fitness_distance_credit": score["fitness_distance_credit"],
        "fitness_survivor_credit": score["fitness_survivor_credit"],
        "fitness_rate_tie_break": score["fitness_rate_tie_break"],
        "fitness_structural_tie_break": (
            score["fitness_structural_tie_break"]
        ),
        "screen_survivor_count": score["survivor_count"],
        "screen_survivor_lattices": score["survivor_lattices"],
        "screen_terminal_negative_count": score["terminal_negative_count"],
        "num_valid": len(valid),
        "num_high_k": len(high_k_codes),
        "lattices_with_high_k": lattices_with_high_k,
        "best_encoding_rate": max((r.get("encoding_rate", 0) for r in valid), default=0),
        "num_above_6": num_above_6,
        "num_above_12": num_above_12,
        "num_milp_upper_bounds_above_6": (
            num_milp_upper_bounds_above_6
        ),
        "num_milp_upper_bounds_above_12": (
            num_milp_upper_bounds_above_12
        ),
        "total_candidates": total_candidates,
        "all_results": all_results,
    })

    map_descriptor = _pool_map_descriptor(
        all_results,
        lattices=set(STAGE2_MILP_FITNESS_LATTICES),
    )

    result = {
        "combined_score": combined,
        "best_fom": best_fom,
        "mean_fom": mean_fom,
        "best_milp_fom_upper_bound": best_milp_fom_upper_bound,
        "mean_milp_fom_upper_bound": mean_milp_fom_upper_bound,
        "fitness_distance_credit": float(score["fitness_distance_credit"]),
        "fitness_survivor_credit": float(score["fitness_survivor_credit"]),
        "fitness_rate_tie_break": float(score["fitness_rate_tie_break"]),
        "fitness_structural_tie_break": float(
            score["fitness_structural_tie_break"]
        ),
        "screen_survivor_count": float(score["survivor_count"]),
        "screen_survivor_lattices": float(score["survivor_lattices"]),
        "screen_terminal_negative_count": float(
            score["terminal_negative_count"]
        ),
        "num_valid": float(len(valid)),
        "num_high_k": float(len(high_k_codes)),
        "lattices_with_high_k": float(lattices_with_high_k),
        "best_encoding_rate": max((r.get("encoding_rate", 0) for r in valid), default=0),
        "num_above_6": float(num_above_6),
        "num_above_12": float(num_above_12),
        "num_milp_upper_bounds_above_6": float(
            num_milp_upper_bounds_above_6
        ),
        "num_milp_upper_bounds_above_12": float(
            num_milp_upper_bounds_above_12
        ),
        "total_candidates": float(total_candidates),
    }
    result.update(map_descriptor)

    try:
        from openevolve.evaluation_result import EvaluationResult
        return EvaluationResult(metrics=result, artifacts=artifacts)
    except ImportError:
        return result


def evaluate(program_path: str) -> dict:
    """Full evaluation (fallback when cascade is disabled)."""
    return evaluate_stage2(program_path)


def _write_metrics_jsonl(metrics: dict) -> None:
    """Append evaluation metrics to a shared JSONL file.

    This is called from subprocess workers where wandb.run is None.
    The main process reads this file and syncs to W&B.
    """
    import json
    import time

    metrics_dir = Path(_PROJECT_ROOT) / "results"
    metrics_dir.mkdir(parents=True, exist_ok=True)
    metrics_file = metrics_dir / "evolution_metrics.jsonl"

    bp_upper_bound_safe = "best_bp_fom_upper_bound" in metrics
    milp_upper_bound_safe = "best_milp_fom_upper_bound" in metrics
    upper_bound_safe = bp_upper_bound_safe or milp_upper_bound_safe
    # Build per-lattice diagnostics.  In contract v2 these are explicitly
    # upper bounds and never parent fitness.
    per_lattice: dict[tuple[int, int], float] = {}
    for r in metrics.get("all_results", []):
        if upper_bound_safe:
            fom = _bp_fom_upper_bound(r)
        else:
            d_raw = r.get("d", 0)
            k = r.get("k", 0)
            n = r.get("n", 0)
            fom = (
                k * d_raw * d_raw / n
                if k > 0 and n > 0 and d_raw > 0
                else 0.0
            )
        if fom > 0:
            key = (r["ell"], r["m"])
            per_lattice[key] = max(per_lattice.get(key, 0.0), fom)

    record = {
        "timestamp": time.time(),
        "num_valid": metrics.get("num_valid", 0),
        "num_high_k": metrics.get("num_high_k", 0),
        "lattices_with_high_k": metrics.get("lattices_with_high_k", 0),
        "best_encoding_rate": metrics.get("best_encoding_rate", 0),
        "total_candidates": metrics.get("total_candidates", 0),
        "target_preflight_winner_capable_eligible": metrics.get(
            "target_preflight_winner_capable_eligible", 0
        ),
        "target_preflight_winner_capable_persisted": metrics.get(
            "target_preflight_winner_capable_persisted", 0
        ),
        "target_preflight_winner_capable_omitted": metrics.get(
            "target_preflight_winner_capable_omitted", 0
        ),
        "winner_capable_distance_pending_persisted": metrics.get(
            "winner_capable_distance_pending_persisted", 0
        ),
        "winner_capable_distance_error_persisted": metrics.get(
            "winner_capable_distance_error_persisted", 0
        ),
        "distance_backend_error_count": metrics.get(
            "distance_backend_error_count", 0
        ),
        "distance_backend_errors": [
            error
            for error in metrics.get("errors", [])
            if "distance backend" in error
        ],
    }
    if upper_bound_safe:
        bound_prefix = "bp" if bp_upper_bound_safe else "milp"
        record.update({
            f"best_{bound_prefix}_fom_upper_bound": metrics.get(
                f"best_{bound_prefix}_fom_upper_bound", 0
            ),
            f"mean_{bound_prefix}_fom_upper_bound": metrics.get(
                f"mean_{bound_prefix}_fom_upper_bound", 0
            ),
            "fitness_distance_credit": metrics.get(
                "fitness_distance_credit", 0
            ),
            "fitness_survivor_credit": metrics.get(
                "fitness_survivor_credit", 0
            ),
            "fitness_rate_tie_break": metrics.get(
                "fitness_rate_tie_break", 0
            ),
            "fitness_structural_tie_break": metrics.get(
                "fitness_structural_tie_break", 0
            ),
            "screen_survivor_count": metrics.get(
                "screen_survivor_count", 0
            ),
            "screen_survivor_lattices": metrics.get(
                "screen_survivor_lattices", 0
            ),
            "screen_terminal_negative_count": metrics.get(
                "screen_terminal_negative_count", 0
            ),
            f"num_{bound_prefix}_upper_bounds_above_6": metrics.get(
                f"num_{bound_prefix}_upper_bounds_above_6",
                metrics.get("num_above_6", 0),
            ),
            f"num_{bound_prefix}_upper_bounds_above_12": metrics.get(
                f"num_{bound_prefix}_upper_bounds_above_12",
                metrics.get("num_above_12", 0),
            ),
            f"per_lattice_best_{bound_prefix}_fom_upper_bound": {
                f"{key[0]}x{key[1]}": value
                for key, value in per_lattice.items()
            },
        })
    else:
        record.update({
            "best_fom": metrics.get("best_fom", 0),
            "mean_fom": metrics.get("mean_fom", 0),
            "num_above_6": metrics.get("num_above_6", 0),
            "num_above_12": metrics.get("num_above_12", 0),
            "per_lattice_best_fom": {
                f"{key[0]}x{key[1]}": value
                for key, value in per_lattice.items()
            },
        })

    try:
        with open(metrics_file, "a") as f:
            f.write(json.dumps(record) + "\n")
    except OSError:
        pass  # Don't fail evaluation over metrics logging


if __name__ == "__main__":
    if len(sys.argv) != 6 or sys.argv[1] not in {
        "--stage1-worker",
        "--stage2-worker",
        "--preflight-worker",
    }:
        raise SystemExit(
            "usage: openevolve_evaluator.py "
            "(--stage1-worker|--stage2-worker|--preflight-worker) "
            "PROGRAM_PATH RESULT_PATH EXPECTED_PARENT_PID LIFECYCLE_FD"
        )
    worker = {
        "--stage1-worker": _stage1_worker_main,
        "--stage2-worker": _stage2_worker_main,
        "--preflight-worker": _preflight_worker_main,
    }[sys.argv[1]]
    raise SystemExit(worker(sys.argv[2], sys.argv[3]))
