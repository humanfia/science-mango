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

**Stage 2** -- Bounded preflight and distance-guided fitness
    Calls the generator on every contracted target and Pareto lattice before
    any blocking distance work.  A bounded deep pass uses 250-trial BP-OSD
    batches on the historical fitness/Pareto lattice basis.  The primary
    fitness metric is ``combined_score`` -- the sum of the best *credible*
    FOM per lattice, where credibility is determined by a trust filter on
    ``d / sqrt(n)``:

    * ``d / sqrt(n) <= 1.3`` -- full trust: use raw FOM.
    * ``d / sqrt(n) >= 2.0`` -- no trust: use encoding rate (``k/n``) only.
    * Between -- linear interpolation (smooth decay, no cliff).

    Credible codes are persisted to ``results/discovered_codes.json`` and
    the Pareto front.  Metrics are written to a shared JSONL file for
    W&B background sync (since ``wandb.run`` is ``None`` in subprocess
    workers).

MAP-Elites feature dimensions
------------------------------
* ``lattices_with_high_k`` -- number of distinct lattices with at least one
  code having ``k >= 8``.
* ``num_high_k`` -- total count of codes with ``k >= 8``.

These features encourage behavioral diversity in the population: programs
that find high-k codes at many lattices occupy different niches from
programs that find a single exceptional code.

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
# modules.  This path runs only in the private Stage 2 subprocess.
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

from evaluation.evaluator import (
    evaluate_batch,
    evaluate_batch_milp,
    evaluate_batch_milp_parallel,
    evaluate_milp_parallel,
    DISTANCE_TRUST_RATIO,
    DISTANCE_UNTRUST_RATIO,
)
from evaluation.final_gate import minimum_winning_distance
from evaluation.results import save_code, update_pareto_front
from evaluation.search_contract import (
    EVOLUTION_LATTICES,
    FINAL_GATE_PARETO_LATTICES as CONTRACT_PARETO_LATTICES,
)
from evaluation.structural_dedup import (
    check_css_static_eligibility,
    deduplicate_css_results,
)

logger = logging.getLogger(__name__)


class CandidateLogWriteError(RuntimeError):
    """A discovered candidate could not be durably persisted."""


WINNER_PREFLIGHT_CONTRACT_VERSION = 1
WINNER_PREFLIGHT_CONTRACT_ID_ENV = "QCODE_WINNER_PREFLIGHT_CONTRACT_ID"
WINNER_PREFLIGHT_REUSE_ENV = "QCODE_WINNER_PREFLIGHT_REUSE"
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
WINNER_CAPABLE_EXPLORATION_LANE = "winner_capable_quick_exploration"
QUICK_EXPLORATION_PERSISTENCE_REASON = "quick_distance_budget"
FULL_POOL_PREFLIGHT_PERSISTENCE_REASON = "full_pool_preflight"
DISTANCE_PENDING_PERSISTENCE_REASON = "selected_distance_pending"
UNRESOLVED_TOP_PERSISTENCE_REASON = "selected_distance_unresolved"
DISTANCE_ERROR_PERSISTENCE_REASON = "selected_distance_error"
STAGE1_SPECIALIST_EXPLORATION_DENOMINATOR = 16
MAX_CANDIDATES_PER_LATTICE = 5000
MAX_WINNER_CAPABLE_EXPLORATION_PER_LATTICE = 8
MAX_FINAL_GATE_PARETO_DISTANCE_PER_LATTICE = 4
MAX_DISTANCE_BACKEND_ERROR_MESSAGE_CHARS = 2048
# Full persistence is deliberately unbounded.  A fixed 5000-definition sample
# is useful for distance fitness, but is not a sound handoff to exact auditing:
# a winner outside that sample would otherwise be permanently invisible.
STAGE2_PREFLIGHT_CANDIDATE_LIMIT = None
STAGE2_DEEP_CANDIDATE_LIMIT = MAX_CANDIDATES_PER_LATTICE
STAGE2_DEEP_DISTANCE_PER_LATTICE = 3
STAGE2_REFINE_TRIALS = 250
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
    return (
        int(result.get("ell", 0) or 0),
        int(result.get("m", 0) or 0),
        tuple(sorted(tuple(map(int, term)) for term in result.get("A_terms", []))),
        tuple(sorted(tuple(map(int, term)) for term in result.get("B_terms", []))),
    )


def _candidate_definition_key(
    candidate,
    *,
    ell: int,
    m: int,
) -> tuple:
    a_terms, b_terms = candidate
    return (
        ell,
        m,
        tuple(sorted(map(tuple, a_terms))),
        tuple(sorted(map(tuple, b_terms))),
    )


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
        a_terms, b_terms = _normalize_candidate_definition(candidate)
        defining = {
            "ell": int(ell),
            "m": int(m),
            "A_terms": [list(term) for term in sorted(a_terms)],
            "B_terms": [list(term) for term in sorted(b_terms)],
        }
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
) -> tuple[list[tuple[int, int]], list[tuple[int, int]]]:
    """Return one strict A/B pair without validating its mathematics."""

    if not isinstance(candidate, (list, tuple)) or len(candidate) != 2:
        raise TypeError("candidate must contain exactly A_terms and B_terms")

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

    return (
        strict_terms(candidate[0], "A_terms"),
        strict_terms(candidate[1], "B_terms"),
    )


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
            normalized.append(_normalize_candidate_definition(candidate))
        except (TypeError, ValueError) as exc:
            errors.append(
                f"({ell},{m}) candidate[{index}] malformed: "
                f"{type(exc).__name__}: {exc}"
            )
    return normalized, errors


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
        candidate = (row.get("A_terms", []), row.get("B_terms", []))
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

    # Unmanaged evaluator smoke tests and direct invocations do not have the
    # launcher's source binding.  Still rotate the marker with this evaluator
    # source and the immutable lattice contract.  Managed runs always supply
    # the stronger evaluator+dependency binding through the environment.
    payload = {
        "contract_version": WINNER_PREFLIGHT_CONTRACT_VERSION,
        "evaluator_sha256": hashlib.sha256(
            Path(__file__).resolve().read_bytes()
        ).hexdigest(),
        "lattices": [list(lattice) for lattice in EVOLUTION_LATTICES],
    }
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

# Lattice subsets for staged evaluation
# Stage 1: small/fast lattices for quick screening
STAGE1_LATTICES = [(6, 6), (12, 6)]
# These are the defining lattices for the n=72, 90 and 108 final-gate Pareto
# references.  They run first in the full evaluator so every accepted win class
# has a durable OpenEvolve -> Humanize route even if a later large lattice uses
# the remainder of the evaluator wall budget.
FINAL_GATE_PARETO_LATTICES = list(CONTRACT_PARETO_LATTICES)
# Preserve the historical fitness basis when the persistence-only final-gate
# lattices are added. This keeps resumed OpenEvolve checkpoint scores and
# MAP-Elites cells comparable across the source upgrade.
STAGE2_FITNESS_LATTICES = [
    (12, 6), (6, 12),
    (12, 12), (24, 6),
    (15, 12), (30, 6),
    (16, 9), (18, 8),
]
# Stage 2 calls the generator on the complete shared contract. Fitness below
# remains restricted to STAGE2_FITNESS_LATTICES so resumed MAP-Elites scores
# stay comparable; the additional lattices are durable discovery probes.
STAGE2_LATTICES = list(EVOLUTION_LATTICES)
# Deep BP-OSD work stays on the historical fitness/Pareto basis.  A bounded
# quick preflight covers every contracted target before any blocking distance
# call, so the external soft timeout cannot make a tail lattice unreachable.
STAGE2_DEEP_LATTICES = [
    *FINAL_GATE_PARETO_LATTICES,
    *(
        lattice
        for lattice in STAGE2_FITNESS_LATTICES
        if lattice not in FINAL_GATE_PARETO_LATTICES
    ),
]
# Historical MILP fitness basis. Keep it separate from the added persistence
# probes for the same checkpoint-compatibility reason as
# ``STAGE2_FITNESS_LATTICES`` above.
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


def _classify_pattern(A_terms, B_terms) -> float:
    """Classify polynomial structure for MAP-Elites.

    0.0 = univariate (A=f(y), B=g(x) or vice versa, incl. constant-monomial)
    1.0 = x/y-swap (pure terms, no constant, each poly mixes x+y axes)
    2.0 = self-dual (A=B)
    3.0 = mixed monomials (has x^a*y^b with both a,b > 0)
    4.0 = multi-term pure (4+ terms, all pure)
    5.0 = hybrid/non-standard pure (has constant term, not univariate --
          e.g. 1+x+y type, or constant-mono A + x/y-swap B)
    """
    a_set = sorted(tuple(t) for t in A_terms)
    b_set = sorted(tuple(t) for t in B_terms)
    if a_set == b_set:
        return 2.0
    has_mixed = any(x > 0 and y > 0 for x, y in A_terms) or \
                any(x > 0 and y > 0 for x, y in B_terms)
    if has_mixed:
        return 3.0
    a_y_only = all(x == 0 for x, y in A_terms)
    a_x_only = all(y == 0 for x, y in A_terms)
    b_y_only = all(x == 0 for x, y in B_terms)
    b_x_only = all(y == 0 for x, y in B_terms)
    if (a_y_only and b_x_only) or (a_x_only and b_y_only):
        return 0.0
    # 4+ term pure polynomials get their own niche
    if len(A_terms) >= 4 or len(B_terms) >= 4:
        return 4.0
    # Hybrid / non-standard pure: has a constant term (0,0) but isn't
    # univariate.  Separates novel structures (1+x+y, hybrid cross-family)
    # from classic x/y-swap (which never has a constant term).
    a_has_const = any(x == 0 and y == 0 for x, y in A_terms)
    b_has_const = any(x == 0 and y == 0 for x, y in B_terms)
    if a_has_const or b_has_const:
        return 5.0
    return 1.0


def _count_terms(A_terms, B_terms) -> float:
    """Return max term count across A and B (for MAP-Elites feature)."""
    return float(max(len(A_terms), len(B_terms)))


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


def _append_candidate_jsonl(log_file: Path, payload: bytes) -> None:
    """Append a non-interleaved batch; roll back caught I/O failures."""
    # Evaluators run in separate worker processes.  O_APPEND prevents stale
    # offsets, while flock keeps a short/partial batch from interleaving with
    # another cooperating append. Flush the batch to stable storage before
    # reporting the evaluation as successful: a candidate that influenced
    # evolution must not disappear from the Stage 1 input log.
    flags = os.O_WRONLY | os.O_APPEND | os.O_CREAT | os.O_CLOEXEC
    if hasattr(os, "O_NOFOLLOW"):
        flags |= os.O_NOFOLLOW
    descriptor = os.open(log_file, flags, 0o600)
    try:
        fcntl.flock(descriptor, fcntl.LOCK_EX)
        original_size = os.fstat(descriptor).st_size
        try:
            written = 0
            while written < len(payload):
                count = os.write(descriptor, payload[written:])
                if count <= 0:
                    raise OSError("candidate JSONL append made no progress")
                written += count
            os.fsync(descriptor)
        except BaseException:
            # All writers in this module honor the same inode lock, so rollback
            # can safely remove a short record before surfacing the failure.
            try:
                os.ftruncate(descriptor, original_size)
                os.fsync(descriptor)
            except OSError:
                logger.exception(
                    "Failed to roll back partial candidate JSONL append: %s",
                    log_file,
                )
            raise
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
        "term_count": _count_terms(
            result.get("A_terms", []), result.get("B_terms", [])
        ),
        "generator_occurrence_count": result.get(
            "generator_occurrence_count", 1
        ),
        "timestamp": time.time(),
    }
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
) -> int:
    """Durably append a candidate batch under one lock and one ``fsync``.

    Serialisation finishes before the file is opened.  Once opened, the whole
    batch cannot interleave with cooperating writers; caught short writes and
    ``fsync`` failures are rolled back to the pre-batch offset.  SIGKILL can
    still leave a complete prefix, which the Humanize transaction's trusted
    offset truncation/archive protocol handles during recovery.  The returned
    count lets callers enforce full-persistence invariants.
    """
    records = [
        record
        for result in results
        if (record := _candidate_jsonl_record(result)) is not None
    ]
    if not records:
        return 0

    if run_name is None:
        run_name = _freeze_candidate_log_run_name()
    if run_name:
        log_dir = Path(_PROJECT_ROOT) / "results" / "evolution" / run_name
    else:
        log_dir = Path(_PROJECT_ROOT) / "results" / "evolution"
    payload = b"".join(
        (json.dumps(record, ensure_ascii=False, default=str) + "\n").encode(
            "utf-8"
        )
        for record in records
    )
    try:
        log_dir.mkdir(parents=True, exist_ok=True)
        _append_candidate_jsonl(log_dir / "all_codes.jsonl", payload)
    except OSError as exc:
        raise CandidateLogWriteError(
            f"failed to persist discovered candidate batch in {log_dir}"
        ) from exc
    return len(records)


def _log_code_jsonl(result: dict, run_name: str | None = None) -> None:
    """Append a code result to the run-specific all_codes.jsonl file.

    Logs all codes with ``d > 0`` plus statically eligible quick-only
    candidates in the explicit winner-capable exploration lane.  The latter
    closes the old top-k handoff gap without making arbitrary FOM claims.

    The run_name is resolved from (in priority order):
    1. Explicit ``run_name`` argument
    2. ``QCODE_RUN_NAME`` environment variable (set by run_evolution.py)
    3. Fallback to ``results/evolution/all_codes.jsonl``
    """
    _log_codes_jsonl([result], run_name=run_name)


def _error_result(error: str) -> dict:
    """Return an error result that includes all feature dimensions.

    MAP-Elites requires the feature dimensions to be present in every
    result, including errors.
    """
    return {
        "combined_score": 0.0,
        "error": error,
        "lattices_with_high_k": 0.0,
        "num_high_k": 0.0,
        "term_count": 0.0,
        "pattern_type": 0.0,
    }


def _load_generate_candidates(program_path: str):
    """Load generate_candidates from an evolved program file."""
    if not Path(program_path).exists():
        raise FileNotFoundError(f"Evolved program not found: {program_path}")
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
) -> dict:
    """Run evaluation across lattices and compute aggregate metrics.

    When quick=False, each lattice invokes the generator exactly once:
    1. Quick-screen and durably persist every winner-capable definition in the
       complete frozen canonical pool.
    2. Bound that same pool for fitness and estimate distance for its top
       `max_distance_per_lattice` candidates, using either BP-OSD (default) or
       MILP (when use_milp=True).
    """
    if run_name is None:
        # This must happen before the first generator call.  Evolved code is
        # untrusted with respect to process environment and may mutate
        # QCODE_RUN_NAME while it is being imported or evaluated.
        run_name = _freeze_candidate_log_run_name()
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

            distance_selection_limit = max_distance_per_lattice
            if (ell, m) in FINAL_GATE_PARETO_LATTICES:
                distance_selection_limit = min(
                    distance_selection_limit,
                    MAX_FINAL_GATE_PARETO_DISTANCE_PER_LATTICE,
                )

            if quick:
                if persist_all_quick_exploration:
                    # Complete persistence is a write-ahead contract, not the
                    # fitness sample. Evaluate and persist the frozen full pool
                    # first; only then derive bounded fitness rows from those
                    # same objects without another generator/evaluator call.
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
                        run_name=run_name,
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
                            _log_code_jsonl(result, run_name=run_name)
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
                # canonical pool and durably hand off every statically eligible,
                # winner-capable definition. This is required even when Stage 2
                # reused a prior Stage 1 completion: a random/stateful generator
                # can produce a different pool on this deep invocation.
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
                    run_name=run_name,
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

                # Pass 1: one per distinct k value
                seen_k: set[int] = set()
                top: list[dict] = []
                for r in promising:
                    if (
                        r["k"] not in seen_k
                        and len(top) < distance_selection_limit
                    ):
                        seen_k.add(r["k"])
                        top.append(r)
                # Pass 2: one per distinct A polynomial (among same-k codes)
                seen_a: set[tuple] = {
                    tuple(sorted(map(tuple, r["A_terms"]))) for r in top
                }
                for r in promising:
                    if len(top) >= distance_selection_limit:
                        break
                    a_key = tuple(sorted(map(tuple, r["A_terms"])))
                    if a_key not in seen_a and r not in top:
                        seen_a.add(a_key)
                        top.append(r)
                # Pass 3: fill remaining slots
                for r in promising:
                    if len(top) >= distance_selection_limit:
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
                top_candidates = [
                    (r["A_terms"], r["B_terms"]) for r in top
                ]
                top_keys = {_definition_key(result) for result in top}

                # The complete winner-capable pool is already durable. Retain
                # the bounded quick-only rows for fitness, and add a stronger
                # selected-pending record before entering a blocking backend.
                quick_only = [
                    r for r in quick_results if r.get("k", 0) > 0
                    and _definition_key(r) not in top_keys
                ]

                pending_top = [
                    _zero_distance_persistence_row(
                        result,
                        reason=DISTANCE_PENDING_PERSISTENCE_REASON,
                    )
                    for result in top
                ]
                for result in pending_top:
                    _log_code_jsonl(result, run_name=run_name)
                distance_pending_persisted += len(pending_top)

                backend_error: dict[str, str] | None = None
                try:
                    if use_milp:
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
                    else:
                        # BP-OSD: use refine_trials for tighter upper bounds.
                        # Skip exact distance (stage 5) -- requires SIGALRM which
                        # isn't available in OpenEvolve's worker threads.
                        results = evaluate_batch(
                            ell, m, top_candidates,
                            quick=False,
                            quick_trials=refine_trials,
                            refine_trials=refine_trials,
                            fom_threshold_refine=6.0,
                            fom_threshold_exact=float("inf"),
                        )
                except CandidateLogWriteError:
                    raise
                except Exception as exc:
                    backend_error = _distance_backend_error_record(exc)
                    errors.append(
                        f"({ell},{m}): distance backend "
                        f"{backend_error['type']}: {backend_error['message']}"
                    )
                    distance_backend_error_count += 1
                    results = [
                        _zero_distance_persistence_row(
                            result,
                            reason=DISTANCE_ERROR_PERSISTENCE_REASON,
                            backend_error=backend_error,
                        )
                        for result in top
                    ]
                    distance_error_top_persisted += len(results)

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
                        backend_error is None
                        and result.get("k", 0) > 0
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
                if expected_unresolved > distance_selection_limit:
                    raise CandidateLogWriteError(
                        f"({ell},{m}): distance batch returned "
                        f"{expected_unresolved} unresolved definitions for a "
                        f"top-{distance_selection_limit} selection"
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
                _log_code_jsonl(r, run_name=run_name)
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


def _require_full_pool_persistence(
    metrics: dict,
    *,
    expected_lattices: int,
    label: str,
) -> None:
    """Reject partial quick passes before their results can affect fitness."""

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


def _run_full_winner_preflight(
    generate_fn,
    *,
    sampling_salt: str,
    contract_id: int,
    run_name: str = "",
) -> dict[str, float]:
    """Persist the complete winner-capable quick universe without a cap."""

    metrics = _run_evaluation(
        generate_fn,
        list(EVOLUTION_LATTICES),
        quick=True,
        run_name=run_name,
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
    run_name = _freeze_candidate_log_run_name()
    source_sha256 = _freeze_program_source_sha256(program_path)
    load_generate_candidates = _load_generate_candidates
    run_full_winner_preflight = _run_full_winner_preflight
    generate_fn = load_generate_candidates(program_path)
    _assert_program_source_unchanged(program_path, source_sha256)
    markers = run_full_winner_preflight(
        generate_fn,
        sampling_salt=source_sha256,
        contract_id=contract_id,
        run_name=run_name,
    )
    _assert_program_source_unchanged(program_path, source_sha256)
    return markers


def _evaluate_stage1_impl(program_path: str) -> dict:
    """Stage 1: Quick screening on small lattices (k-only, ~2s).

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
    run_name = _freeze_candidate_log_run_name()
    source_sha256 = _freeze_program_source_sha256(program_path)
    load_generate_candidates = _load_generate_candidates
    run_full_winner_preflight = _run_full_winner_preflight
    run_evaluation = _run_evaluation
    try:
        generate_fn = load_generate_candidates(program_path)
    except Exception as e:
        return _error_result(str(e))

    _assert_program_source_unchanged(program_path, source_sha256)
    preflight_markers = run_full_winner_preflight(
        generate_fn,
        sampling_salt=source_sha256,
        contract_id=contract_id,
        run_name=run_name,
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
        run_name=run_name,
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
                "term_count": 0.0,
                "pattern_type": 0.0,
                "specialist_exploration": 1.0,
            }
            result.update(preflight_markers)
            return result
        result = {
            "combined_score": 0.0,
            "num_valid": 0.0,
            "total_candidates": 0.0,
            "lattices_with_high_k": 0.0,
            "num_high_k": 0.0,
            "term_count": 0.0,
            "pattern_type": 0.0,
        }
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

    # MAP-Elites features: compute from best valid code
    best_valid = max(valid, key=lambda r: r.get("k", 0)) if valid else None
    if best_valid:
        best_tc = _count_terms(best_valid["A_terms"], best_valid["B_terms"])
        best_pattern = _classify_pattern(best_valid["A_terms"], best_valid["B_terms"])
    else:
        best_tc = 0.0
        best_pattern = 0.0

    result = {
        "combined_score": score,
        "num_valid": float(metrics["num_valid"]),
        "total_candidates": float(metrics["total_candidates"]),
        "lattices_with_high_k": float(metrics["lattices_with_high_k"]),
        "num_high_k": float(metrics["num_high_k"]),
        "term_count": best_tc,
        "pattern_type": best_pattern,
        "specialist_exploration": float(
            lattice_coverage < 1.0 and specialist_exploration
        ),
    }
    result.update(preflight_markers)
    return result


def _evaluate_stage2_impl(program_path: str) -> dict:
    """Stage 2: bounded target preflight plus deep distance evaluation.

    Every contracted lattice is screened and every evaluated, statically
    eligible winner-capable definition is durably retained before a
    blocking distance backend runs.  Deep BP-OSD scoring then uses the
    historical Pareto/fitness lattice basis.
    """
    # Capture and validate the Stage 1 handoff before importing evolved code.
    # In direct/fallback evaluation this environment value is absent, so Stage
    # 2 still performs its own complete preflight.
    run_name = _freeze_candidate_log_run_name()
    source_sha256 = _freeze_program_source_sha256(program_path)
    load_generate_candidates = _load_generate_candidates
    run_evaluation = _run_evaluation
    preflight_reuse = _preflight_reuse_from_environment(program_path)
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
            run_name=run_name,
            sampling_salt=sampling_salt,
            candidate_limit=STAGE2_PREFLIGHT_CANDIDATE_LIMIT,
            persist_quick_exploration=True,
            persist_all_quick_exploration=True,
        )
    else:
        preflight = {
            "errors": [],
            "total_candidates": int(
                preflight_reuse[WINNER_PREFLIGHT_EVALUATED_METRIC]
            ),
            "evaluated_candidate_definitions": int(
                preflight_reuse[WINNER_PREFLIGHT_EVALUATED_METRIC]
            ),
            "winner_capable_quick_exploration_eligible": int(
                preflight_reuse[WINNER_PREFLIGHT_ELIGIBLE_METRIC]
            ),
            "winner_capable_quick_exploration_persisted": int(
                preflight_reuse[WINNER_PREFLIGHT_PERSISTED_METRIC]
            ),
            "winner_capable_quick_exploration_omitted": 0,
            "lattices_completed": len(STAGE2_LATTICES),
            "lattice_failures": 0,
        }
    _require_full_pool_persistence(
        preflight,
        expected_lattices=len(STAGE2_LATTICES),
        label="Stage 2 full preflight",
    )
    _assert_program_source_unchanged(program_path, source_sha256)
    metrics = dict(run_evaluation(
        generate_fn, STAGE2_DEEP_LATTICES,
        quick=False,
        refine_trials=STAGE2_REFINE_TRIALS,
        max_distance_per_lattice=(
            STAGE2_DEEP_DISTANCE_PER_LATTICE
        ),
        sampling_salt=sampling_salt,
        run_name=run_name,
        candidate_limit=STAGE2_DEEP_CANDIDATE_LIMIT,
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

    # --- Combined score ---
    # Sum of best *credible* FOM per lattice.
    #
    # BP-OSD with 1000 trials gives exact d for well-structured codes
    # (verified on [[72,12,6]], [[144,12,12]], [[288,12,18]]). But for
    # degenerate high-k codes it wildly overestimates d.
    #
    # We FILTER rather than cap: only trust BP-OSD estimates where
    # d ≤ TRUST_FULL * sqrt(n). Known best BB codes have d/sqrt(n) ≤ 1.26.
    # Degenerate high-k codes have d/sqrt(n) ≥ 2.5, leaving a wide gap.
    # Codes failing the filter get a small encoding-rate bonus (k/n)
    # instead, so they're not completely invisible but can't dominate.

    # Trust boundaries (imported from evaluation.evaluator -- single source of truth).
    TRUST_FULL = DISTANCE_TRUST_RATIO    # d/sqrt(n) ≤ 1.3: fully trust FOM
    TRUST_NONE = DISTANCE_UNTRUST_RATIO  # d/sqrt(n) ≥ 2.0: discard FOM, use k/n only
    # Between TRUST_FULL and TRUST_NONE: linear interpolation (soft decay, no cliff)
    best_fom = metrics["best_fom"]

    per_lattice_best: dict[tuple[int, int], float] = {}
    for r in metrics["all_results"]:
        d_raw = r.get("d", 0)
        k = r.get("k", 0)
        n = r.get("n", 0)
        if k <= 0 or n <= 0:
            continue
        key = (r["ell"], r["m"])
        if key not in STAGE2_FITNESS_LATTICES:
            # These small final-gate lattices feed the durable candidate log
            # but intentionally do not change the historical OpenEvolve
            # fitness scale of a resumed checkpoint.
            continue
        fallback = k / n  # encoding rate, always available
        if d_raw <= 0:
            credible_fom = fallback
        else:
            ratio = d_raw / math.sqrt(n)
            raw_fom = k * d_raw * d_raw / n
            if ratio <= TRUST_FULL:
                credible_fom = raw_fom
            elif ratio >= TRUST_NONE:
                credible_fom = fallback
            else:
                # Linear decay: 100% FOM at TRUST_FULL, 0% at TRUST_NONE
                alpha = (TRUST_NONE - ratio) / (TRUST_NONE - TRUST_FULL)
                credible_fom = alpha * raw_fom + (1 - alpha) * fallback
        per_lattice_best[key] = max(per_lattice_best.get(key, 0.0), credible_fom)

    combined = sum(per_lattice_best.values())

    # Build artifacts for LLM feedback.
    # Show the best code by CREDIBLE FOM (d-filtered), not raw BP-OSD FOM,
    # so the LLM learns from genuine patterns, not degenerate codes.
    artifacts = {}
    credible_codes = []
    for r in metrics["all_results"]:
        d_val = r.get("d", 0)
        n_val = r.get("n", 0)
        if d_val > 0 and n_val > 0 and d_val <= TRUST_FULL * math.sqrt(n_val):
            credible_codes.append(r)
    if credible_codes:
        bc = max(credible_codes, key=lambda r: r.get("fom", 0.0))
        artifacts["best_code"] = (
            f"[[{bc['n']},{bc['k']},{bc['d']}]] FOM={bc['fom']:.2f} "
            f"at ({bc['ell']},{bc['m']})\n"
            f"  A={bc['A_terms']}\n"
            f"  B={bc['B_terms']}"
        )
    elif metrics["best_code"]:
        bc = metrics["best_code"]
        artifacts["best_code"] = (
            f"[[{bc['n']},{bc['k']},{bc.get('d', '?')}]] "
            f"(d estimate unreliable) at ({bc['ell']},{bc['m']})\n"
            f"  A={bc['A_terms']}\n"
            f"  B={bc['B_terms']}"
        )

    if metrics["errors"]:
        artifacts["errors"] = "\n".join(metrics["errors"][:5])

    # Report top 5 codes by credible FOM (reusing list from above)
    top5 = sorted(credible_codes, key=lambda r: r.get("fom", 0), reverse=True)[:5]
    if top5:
        top5_lines = []
        for r in top5:
            top5_lines.append(
                f"  [[{r['n']},{r['k']},{r['d']}]] FOM={r['fom']:.1f} "
                f"rate={r.get('encoding_rate', 0):.3f} ({r['ell']},{r['m']})"
            )
        artifacts["top_codes"] = "\n".join(top5_lines)

    # Structural feedback for codes with d >= 4 (helps LLM reason about patterns)
    d4_codes = [r for r in credible_codes if r.get("d", 0) >= 4]
    if d4_codes:
        struct_lines = []
        for r in sorted(d4_codes, key=lambda r: r.get("fom", 0), reverse=True)[:3]:
            struct_lines.append(
                f"  [[{r['n']},{r['k']},{r['d']}]] FOM={r['fom']:.1f}:\n"
                f"    {_structural_feedback(r)}"
            )
        artifacts["structural_analysis"] = (
            "Structural analysis of top codes with d>=4:\n" + "\n".join(struct_lines)
        )

    # Per-lattice breakdown for the LLM
    lattice_lines = []
    for key in sorted(per_lattice_best.keys()):
        lattice_lines.append(
            f"  ({key[0]},{key[1]}): credible FOM={per_lattice_best[key]:.1f}"
        )

    artifacts["summary"] = (
        "Target preflight: "
        f"{metrics.get('target_preflight_candidates_evaluated', 0)} of "
        f"{metrics.get('target_preflight_candidates_generated', 0)} "
        f"generated candidates sampled across "
        f"{metrics.get('target_preflight_lattices', 0)} lattices.\n"
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
        f"Best raw FOM (BP-OSD, {STAGE2_REFINE_TRIALS} trials): "
        f"{best_fom:.2f}\n"
        f"Combined score: {combined:.1f} = sum of best credible FOM per lattice "
        f"(full trust d/sqrt(n) <= {TRUST_FULL}, soft decay to {TRUST_NONE})\n"
        f"Per-lattice breakdown:\n" + "\n".join(lattice_lines)
    )

    # Save only codes with trusted distances (d in fully-trusted zone)
    credible_to_save = [
        r for r in metrics["all_results"]
        if r.get("fom", 0) > 0
        and r.get("d", 0) > 0
        and r.get("n", 0) > 0
        and r["d"] <= TRUST_FULL * math.sqrt(r["n"])
    ]
    if credible_to_save:
        best_credible = max(credible_to_save, key=lambda r: r["fom"])
        if best_credible["fom"] > 6.0:
            try:
                save_code(best_credible)
                update_pareto_front(credible_to_save)
            except Exception:
                pass  # Don't fail evaluation over persistence

    # Write metrics to shared JSONL file for W&B sync from main process.
    # (wandb.run is None in subprocess workers, so direct wandb.log doesn't work.)
    _write_metrics_jsonl(metrics)

    # MAP-Elites features from best credible code
    fitness_credible_codes = [
        row for row in credible_codes
        if (row["ell"], row["m"]) in STAGE2_FITNESS_LATTICES
    ]
    best_credible_code = (
        max(fitness_credible_codes, key=lambda r: r.get("fom", 0))
        if fitness_credible_codes else None
    )
    if best_credible_code:
        s2_tc = _count_terms(best_credible_code["A_terms"], best_credible_code["B_terms"])
        s2_pattern = _classify_pattern(best_credible_code["A_terms"], best_credible_code["B_terms"])
    else:
        s2_tc = 0.0
        s2_pattern = 0.0

    result = {
        "combined_score": combined,
        "best_fom": best_fom,
        "mean_fom": metrics["mean_fom"],
        "num_valid": float(metrics["num_valid"]),
        "num_high_k": float(metrics["num_high_k"]),
        "lattices_with_high_k": float(metrics["lattices_with_high_k"]),
        "best_encoding_rate": metrics["best_encoding_rate"],
        "num_above_6": float(metrics["num_above_6"]),
        "num_above_12": float(metrics["num_above_12"]),
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
        "term_count": s2_tc,
        "pattern_type": s2_pattern,
    }

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


def evaluate_stage1(program_path: str) -> dict:
    """Run gate-before-persistence Stage 1 behind a killable wall timeout."""

    source_sha256 = _freeze_program_source_sha256(program_path)
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
                try:
                    return_code = process.wait(
                        timeout=_winner_preflight_hard_timeout_s()
                    )
                except subprocess.TimeoutExpired:
                    _terminate_stage2_process_group(process)
                    return _winner_preflight_failure_result(
                        "winner preflight exceeded its killable wall timeout",
                        timed_out=True,
                    )
                except BaseException:
                    _terminate_stage2_process_group(process)
                    raise
        finally:
            os.close(lifecycle_write_fd)

        if return_code != 0:
            return _winner_preflight_failure_result(
                f"winner preflight subprocess exited with status "
                f"{return_code}",
                timed_out=False,
            )
        try:
            payload = json.loads(result_path.read_text())
        except (OSError, UnicodeDecodeError, json.JSONDecodeError) as exc:
            return _winner_preflight_failure_result(
                "winner preflight result is unreadable: "
                f"{type(exc).__name__}",
                timed_out=False,
            )
        if (
            not isinstance(payload, dict)
            or set(payload)
            != {"schema_version", "status", "metrics"}
            or payload.get("schema_version") != 1
            or payload.get("status") != "completed"
            or not isinstance(payload.get("metrics"), dict)
        ):
            return _winner_preflight_failure_result(
                "winner preflight result schema is invalid",
                timed_out=False,
            )
        try:
            _assert_program_source_unchanged(program_path, source_sha256)
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


def _stage2_failure_result(
    message: str,
    *,
    timed_out: bool,
    stderr_tail: str = "",
):
    metrics = _error_result(message)
    metrics.update({
        "stage2_hard_timeout": float(timed_out),
        "stage2_subprocess_failed": 1.0,
    })
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


def evaluate_stage2(program_path: str) -> dict:
    """Run Stage 2 behind a killable wall-clock boundary.

    OpenEvolve 0.2.26 applies ``asyncio.wait_for`` to an executor thread.
    Cancelling that await does not stop the thread, so a timed-out evaluator
    can otherwise keep consuming CPU and appending candidates after its
    iteration was finalized.  A private subprocess group makes the deadline
    real and leaves headroom below the bound outer evaluator timeout.
    """

    evaluator_path = Path(__file__).resolve()
    preflight_reuse = _take_stage1_preflight_completion(program_path)
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
                try:
                    return_code = process.wait(
                        timeout=_stage2_hard_timeout_s()
                    )
                except subprocess.TimeoutExpired:
                    _terminate_stage2_process_group(process)
                    return _stage2_failure_result(
                        "Stage 2 exceeded its killable wall timeout",
                        timed_out=True,
                        stderr_tail=_read_stage2_stderr_tail(stderr_path),
                    )
                except BaseException:
                    _terminate_stage2_process_group(process)
                    raise
        finally:
            os.close(lifecycle_write_fd)

        stderr_tail = _read_stage2_stderr_tail(stderr_path)
        if return_code != 0:
            return _stage2_failure_result(
                f"Stage 2 subprocess exited with status {return_code}",
                timed_out=False,
                stderr_tail=stderr_tail,
            )
        try:
            payload = json.loads(result_path.read_text())
        except (OSError, UnicodeDecodeError, json.JSONDecodeError) as exc:
            return _stage2_failure_result(
                f"Stage 2 result is unreadable: {type(exc).__name__}",
                timed_out=False,
                stderr_tail=stderr_tail,
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
            return _stage2_failure_result(
                "Stage 2 result schema is invalid",
                timed_out=False,
                stderr_tail=stderr_tail,
            )
        try:
            from openevolve.evaluation_result import EvaluationResult
            return EvaluationResult(
                metrics=payload["metrics"],
                artifacts=payload["artifacts"],
            )
        except ImportError:
            return payload["metrics"]


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
    metrics = _evaluate_stage1_impl(program_path)
    if not isinstance(metrics, dict):
        raise TypeError("Stage 1 worker returned an invalid result")
    _write_preflight_worker_result(result_path, metrics)
    return 0


def _preflight_worker_main(program_path: str, result_path: str) -> int:
    metrics = _preflight_program(program_path)
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
    - Scoring: only codes with d≥6 contribute FOM (d≤4 are irrelevant)
    - Symplectic weight pre-filter: codes with d_symp≤4 skip MILP entirely
    - Better LLM feedback with clear signal about what works vs doesn't
    """
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
    codes_jsonl = str(Path(_PROJECT_ROOT) / "results" / "evolution_codes.jsonl")

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

            for A_terms, B_terms in candidates:
                all_quick_tasks.append((ell, m, A_terms, B_terms))
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
        n_code = 2 * ell * m
        promising = []
        for r in lattice_results:
            d_s = r.get("d_symplectic", 0)
            if d_s > MILP_EARLY_STOP:
                promising.append(r)
            else:
                milp_skipped_low_d_symp += 1

        # Rank by approximate FOM using symplectic weight
        def _rank_key(r):
            d_s = r.get("d_symplectic", 0)
            if d_s > 0:
                return r["k"] * d_s * d_s / n_code
            return r["k"]
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
            milp_tasks.append((ell, m, r["A_terms"], r["B_terms"]))

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
    milp_keys = {
        (r["ell"], r["m"], tuple(map(tuple, r["A_terms"])), tuple(map(tuple, r["B_terms"])))
        for r in milp_results
    }
    for r in all_quick_results:
        key = (r["ell"], r["m"], tuple(map(tuple, r["A_terms"])), tuple(map(tuple, r["B_terms"])))
        if key not in milp_keys and r.get("k", 0) > 0:
            all_results.append(r)

    # ── Phase 4: Scoring ───────────────────────────────────────────
    # Only codes with d ≥ MIN_RELEVANT_D contribute FOM to combined_score.
    # This sends a clear signal: d≤4 codes are worthless.
    per_lattice_best: dict[tuple[int, int], float] = {}
    for r in all_results:
        d = r.get("d", 0)
        fom = r.get("fom", 0.0)
        k = r.get("k", 0)
        if k <= 0:
            continue
        key = (r["ell"], r["m"])
        if key not in STAGE2_MILP_FITNESS_LATTICES:
            # Final-gate probes are persistence coverage, not a change to the
            # historical score of resumed --milp checkpoints.
            continue
        if d >= MIN_RELEVANT_D and fom > 0:
            per_lattice_best[key] = max(per_lattice_best.get(key, 0.0), fom)
        elif d > 0 and d < MIN_RELEVANT_D:
            # Low-d codes: tiny contribution (like encoding rate)
            per_lattice_best[key] = max(per_lattice_best.get(key, 0.0), 0.01)

    combined = sum(per_lattice_best.values())

    # Aggregate metrics
    valid = [r for r in all_results if r.get("k", 0) > 0]
    foms = [r.get("fom", 0.0) for r in valid if r.get("fom", 0.0) > 0]
    best_fom = max(foms) if foms else 0.0
    mean_fom = sum(foms) / len(foms) if foms else 0.0
    high_k_codes = [r for r in valid if r.get("k", 0) >= 8]
    lattices_with_high_k = len(set(
        (r["ell"], r["m"]) for r in high_k_codes
    ))
    num_above_6 = sum(1 for f in foms if f >= 6.0)
    num_above_12 = sum(1 for f in foms if f >= 12.0)

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

    # Codes with d reported (MILP-verified)
    codes_with_d = [
        r for r in all_results
        if r.get("d", 0) > 0 and r.get("fom", 0) > 0
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
            f"these DON'T count toward score. "
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

    # Per-lattice breakdown
    lattice_lines = []
    for key in sorted(per_lattice_best.keys()):
        lattice_lines.append(
            f"  ({key[0]},{key[1]}): best FOM={per_lattice_best[key]:.1f}"
        )

    artifacts["summary"] = (
        f"Evaluated {total_candidates} candidates across "
        f"{len(STAGE2_LATTICES_MILP)} lattices.\n"
        f"MILP verified: {len(milp_tasks)} codes ({milp_skipped_low_d_symp} "
        f"skipped by symplectic pre-filter d_symp<={MILP_EARLY_STOP}).\n"
        f"Valid codes (k>0): {len(valid)}\n"
        f"Codes with d>={MIN_RELEVANT_D}: {len(relevant_codes)} (these count toward score)\n"
        f"Best FOM: {best_fom:.2f}\n"
        f"Combined score: {combined:.1f} = sum of best FOM per lattice (d>={MIN_RELEVANT_D} only)\n"
        f"Per-lattice breakdown:\n" + "\n".join(lattice_lines)
    )

    # ── Phase 6: Persistence ───────────────────────────────────────
    # Individual codes are already saved to JSONL by evaluate_milp_parallel.
    # Also save to discovered_codes.json and pareto_front.json for compat.
    to_save = [
        r for r in all_results
        if r.get("fom", 0) > 6.0 and r.get("d", 0) > 0
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
        "num_valid": len(valid),
        "num_high_k": len(high_k_codes),
        "lattices_with_high_k": lattices_with_high_k,
        "best_encoding_rate": max((r.get("encoding_rate", 0) for r in valid), default=0),
        "num_above_6": num_above_6,
        "num_above_12": num_above_12,
        "total_candidates": total_candidates,
        "all_results": all_results,
    })

    # MAP-Elites features from best MILP-verified code
    milp_best = max(
        (
            r for r in all_results
            if (
                r.get("d", 0) > 0
                and (r["ell"], r["m"]) in STAGE2_MILP_FITNESS_LATTICES
            )
        ),
        key=lambda r: r.get("fom", 0), default=None,
    )
    if milp_best:
        milp_tc = _count_terms(milp_best["A_terms"], milp_best["B_terms"])
        milp_pattern = _classify_pattern(milp_best["A_terms"], milp_best["B_terms"])
    else:
        milp_tc = 0.0
        milp_pattern = 0.0

    result = {
        "combined_score": combined,
        "best_fom": best_fom,
        "mean_fom": mean_fom,
        "num_valid": float(len(valid)),
        "num_high_k": float(len(high_k_codes)),
        "lattices_with_high_k": float(lattices_with_high_k),
        "best_encoding_rate": max((r.get("encoding_rate", 0) for r in valid), default=0),
        "num_above_6": float(num_above_6),
        "num_above_12": float(num_above_12),
        "total_candidates": float(total_candidates),
        "term_count": milp_tc,
        "pattern_type": milp_pattern,
    }

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

    # Build per-lattice best FOM for detailed tracking
    per_lattice: dict[tuple[int, int], float] = {}
    for r in metrics.get("all_results", []):
        d_raw = r.get("d", 0)
        k = r.get("k", 0)
        n = r.get("n", 0)
        if k > 0 and n > 0 and d_raw > 0:
            fom = k * d_raw * d_raw / n
            key = (r["ell"], r["m"])
            per_lattice[key] = max(per_lattice.get(key, 0.0), fom)

    record = {
        "timestamp": time.time(),
        "best_fom": metrics.get("best_fom", 0),
        "mean_fom": metrics.get("mean_fom", 0),
        "num_valid": metrics.get("num_valid", 0),
        "num_high_k": metrics.get("num_high_k", 0),
        "lattices_with_high_k": metrics.get("lattices_with_high_k", 0),
        "best_encoding_rate": metrics.get("best_encoding_rate", 0),
        "num_above_6": metrics.get("num_above_6", 0),
        "num_above_12": metrics.get("num_above_12", 0),
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
        "per_lattice_best_fom": {
            f"{k[0]}x{k[1]}": v for k, v in per_lattice.items()
        },
    }

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
