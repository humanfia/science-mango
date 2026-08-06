"""Proof-safe OpenEvolve evaluator for coset two-block Stage 1.

There is deliberately no BP/OSD call in this module.  Decoder-returned logical
weights are distance upper bounds and cannot improve fitness.  Positive
distance credit is derived only from a complete two-sector low-weight UNSAT
decision (or a future independently replayed exact-distance field produced by
this evaluator).  A replayed SAT witness rejects the candidate whenever it is
below the dynamic FOM=12 exclusion threshold.
"""

from __future__ import annotations

import hashlib
import ctypes
import fcntl
import json
import math
import os
import signal
import stat
import subprocess
import sys
import threading
import time
from collections import Counter
from collections.abc import Mapping
from contextlib import contextmanager
from dataclasses import dataclass
from pathlib import Path
from typing import Any

PROJECT_ROOT = str(Path(__file__).resolve().parent.parent)
if PROJECT_ROOT not in sys.path:
    sys.path.insert(0, PROJECT_ROOT)

import numpy as np
from qldpc import codes
from qldpc.objects import Pauli

from evaluation.low_weight_oracle import (
    evaluate_css_low_weight_oracle,
    verify_css_low_weight_oracle,
)
from evaluation.evaluator import (
    compute_challenge_rejection_cutoff,
    compute_fom_rejection_cutoff,
)
from evaluation.final_gate import minimum_winning_distance
from evolve.coset_search_contract import (
    COSET_BATCH_ORBIT_PROFILE_METRIC,
    COSET_EVALUATOR_KIND,
    COSET_MAP_SCHEMA_METRIC,
    COSET_MAP_SCHEMA_VERSION,
    COSET_NONNORMAL_LANE_METRIC,
    COSET_NORMAL_LANE_METRIC,
    COSET_PROOF_BATCH_WALL_TIMEOUT_S,
    COSET_PROOF_CACHE_DIRECTORY,
    COSET_PROOF_LADDER_SCHEMA_VERSION,
    COSET_PROOF_LADDER_START_WEIGHT,
    COSET_PROOF_LADDER_VERSION_METRIC,
    COSET_PROOF_LADDER_WEIGHT_STEP,
    COSET_PROOF_MAX_CANDIDATES_PER_BATCH,
    COSET_PROOF_MAX_NEW_STEPS_PER_BATCH,
    COSET_PROOF_STEP_HARD_TIMEOUT_S,
    COSET_SUPPORT_ORBIT_BINS,
    MAX_GENERATED_CANDIDATES,
    TARGET_FOM,
    action_search_view,
    action_search_views,
    candidate_digest,
    coset_batch_map_descriptor,
    normalize_candidate,
    quota_by_normality,
    support_orbit_bin,
)
from evolve.coset_mutation_preflight import (
    CosetMutationRuntimeError,
    InvalidCosetMutation,
    preflight_coset_policy,
)


MAP_DESCRIPTOR_VERSION_METRIC = "map_descriptor_version"
MAP_DESCRIPTOR_VERSION = 4  # launcher envelope; coset semantics use own v1 marker
EVALUATOR_KIND_ID_METRIC = "qcode_evaluator_kind_id"
EVALUATOR_KIND_ID = 1.0
ACTION_CATALOG_ID_METRIC = "qcode_action_catalog_id"
CANDIDATE_LOG_PATH_ENV = "QCODE_CANDIDATE_LOG_PATH"
PREFLIGHT_CONTRACT_ID_ENV = "QCODE_WINNER_PREFLIGHT_CONTRACT_ID"
PREFLIGHT_CONTRACT_VERSION = 2
PREFLIGHT_UNIT_KIND_ID = 1.0  # action strata, not BB lattices
PREFLIGHT_UNIT_KIND_ID_METRIC = "winner_preflight_unit_kind_id"
PREFLIGHT_UNITS_METRIC = "winner_preflight_units"
PREFLIGHT_ACTION_STRATA_METRIC = "winner_preflight_action_strata"
MAX_ORACLE_CANDIDATES = COSET_PROOF_MAX_CANDIDATES_PER_BATCH
COSET_GENOME_FORMAT_ID_METRIC = "qcode_coset_genome_format_id"
COSET_TYPED_DSL_GENOME_FORMAT_ID = 1.0
_PROOF_CACHE_KIND = "qcode-coset-stage1-proof-cache"
_PROOF_CACHE_SCHEMA_VERSION = 2
_PROOF_CACHE_COMMIT_KIND = "qcode-coset-stage1-proof-cache-commit"
_PROOF_LEDGER_KIND = "qcode-coset-stage1-proof-ledger-v1"
_ORACLE_RUNG_WORKER_SCHEMA_VERSION = 1
_ORACLE_RUNG_WORKER_MAX_BYTES = 64 * 1024 * 1024
_ORACLE_RUNG_KILL_GRACE_S = 0.25
_ORACLE_INITIAL_TIMEOUT_S = 7.5
_ORACLE_UNKNOWN_RETRY_BACKOFF_S = 1.0
_ORACLE_FRONTIER_WIDTH = 2
_PROOF_CACHE_MAX_BYTES = 64 * 1024 * 1024
_PROOF_EVALUATION_LOCAL = threading.local()


def _source_sha256(path: str | Path) -> str:
    source = Path(path)
    if source.is_symlink() or not source.is_file():
        raise ValueError(f"evolved program must be a regular file: {source}")
    return hashlib.sha256(source.read_bytes()).hexdigest()


def _preflight_program(program_path: str):
    """Parse/render a mutation in a killable child, never in this worker."""

    path = Path(program_path).resolve(strict=True)
    result = preflight_coset_policy(path)
    return result, path


def _gf2_rank(matrix: np.ndarray) -> int:
    """Rank over F2 using packed Python rows, independent of qldpc caches."""

    array = np.ascontiguousarray(np.asarray(matrix, dtype=np.uint8) & 1)
    if array.ndim != 2:
        raise ValueError("parity check must be a matrix")
    rows = [
        int.from_bytes(np.packbits(row, bitorder="little").tobytes(), "little")
        for row in array
    ]
    rank = 0
    column_count = int(array.shape[1])
    for column in range(column_count - 1, -1, -1):
        pivot = next(
            (index for index in range(rank, len(rows)) if (rows[index] >> column) & 1),
            None,
        )
        if pivot is None:
            continue
        rows[rank], rows[pivot] = rows[pivot], rows[rank]
        pivot_row = rows[rank]
        for index in range(len(rows)):
            if index != rank and ((rows[index] >> column) & 1):
                rows[index] ^= pivot_row
        rank += 1
        if rank == len(rows):
            break
    return rank


def _matrix_pair_from_builder(candidate: Mapping[str, Any]):
    """Build through the immutable catalog and normalize its public result."""

    from evaluation import coset_two_block as builder

    build = getattr(builder, "build_coset_candidate", None)
    if not callable(build):
        build = getattr(builder, "build_coset_two_block", None)
    if not callable(build):
        raise RuntimeError(
            "coset builder does not expose build_coset_candidate()"
        )
    try:
        built = build(candidate)
    except TypeError:
        built = build(
            candidate["action_id"],
            candidate["left_support"],
            candidate["right_support"],
        )
    if isinstance(built, Mapping):
        code = built.get("code")
        hx = built.get("hx", built.get("matrix_x"))
        hz = built.get("hz", built.get("matrix_z"))
    else:
        code = built
        hx = getattr(built, "matrix_x", None)
        hz = getattr(built, "matrix_z", None)
    if code is not None and (hx is None or hz is None):
        hx = getattr(code, "matrix_x", None)
        hz = getattr(code, "matrix_z", None)
    if hx is None or hz is None:
        raise RuntimeError("coset builder did not return HX/HZ matrices")
    matrix_x = np.ascontiguousarray(np.asarray(hx, dtype=np.uint8) & 1)
    matrix_z = np.ascontiguousarray(np.asarray(hz, dtype=np.uint8) & 1)
    if matrix_x.ndim != 2 or matrix_z.ndim != 2:
        raise ValueError("coset HX/HZ must be matrices")
    if matrix_x.shape[1] != matrix_z.shape[1]:
        raise ValueError("coset HX/HZ have different block lengths")
    return matrix_x, matrix_z


def _action_catalog_sha256() -> str:
    """Return the immutable action-catalog identity used by later stages."""

    from evaluation import coset_two_block as builder

    value = getattr(builder, "ACTION_CATALOG_V2_SHA256", None)
    if callable(value):
        value = value()
    if value is None:
        provider = getattr(builder, "action_catalog_sha256", None)
        if callable(provider):
            value = provider()
    if value is None:
        catalog_path = Path(builder.__file__).with_name(
            "coset_two_block_actions.v2.json"
        )
        value = _source_sha256(catalog_path)
    if (
        not isinstance(value, str)
        or len(value) != 64
        or any(character not in "0123456789abcdef" for character in value)
    ):
        raise RuntimeError("coset action catalog SHA-256 is invalid")
    return value


def _action_catalog_contract_id() -> float:
    # Thirteen hex digits fit exactly in an IEEE-754 double and therefore
    # survive OpenEvolve's numeric metric/checkpoint round trip.
    return float(int(_action_catalog_sha256()[:13], 16))


def _stage2_construction(candidate: Mapping[str, Any]) -> dict[str, Any]:
    """Export the compact, source-bound construction consumed by Stage 2."""

    from evaluation.coset_action_catalog import V2_CATALOG_ID

    normalized = normalize_candidate(candidate)
    construction = {
        "kind": "coset-two-block-v2",
        "representation_id": normalized["representation_id"],
        "action_id": normalized["action_id"],
        "action_catalog_id": V2_CATALOG_ID,
        "action_catalog_sha256": _action_catalog_sha256(),
        "left_support": list(normalized["left_support"]),
        "right_support": list(normalized["right_support"]),
    }
    # When the immutable builder exposes its normalizer, replay it here.  The
    # explicit projection below ensures evolved code still cannot add fields.
    from evaluation import coset_two_block as builder

    validator = getattr(builder, "normalize_construction", None)
    if not callable(validator):
        validator = getattr(builder, "normalize_coset_construction", None)
    if callable(validator):
        replayed = validator(construction)
        if isinstance(replayed, Mapping) and isinstance(
            replayed.get("construction"), Mapping
        ):
            replayed = replayed["construction"]
        if not isinstance(replayed, Mapping):
            raise RuntimeError("coset construction normalizer returned no object")
        for name, expected in construction.items():
            if replayed.get(name) != expected:
                raise RuntimeError(
                    f"coset construction normalizer changed {name}"
                )
    return construction


def _tanner_component_count(hx: np.ndarray, hz: np.ndarray) -> int:
    """Count connected components of the combined CSS Tanner graph."""

    checks = np.vstack((hx, hz))
    check_count, qubit_count = checks.shape
    node_count = check_count + qubit_count
    parents = list(range(node_count))

    def find(node: int) -> int:
        while parents[node] != node:
            parents[node] = parents[parents[node]]
            node = parents[node]
        return node

    def union(left: int, right: int) -> None:
        root_left = find(left)
        root_right = find(right)
        if root_left != root_right:
            parents[root_right] = root_left

    for check_index, row in enumerate(checks):
        for qubit_index in np.flatnonzero(row):
            union(check_index, check_count + int(qubit_index))
    return len({find(node) for node in range(node_count)})


def _static_candidate(candidate: Mapping[str, Any]) -> dict[str, Any]:
    normalized = normalize_candidate(candidate)
    view = action_search_view(normalized["action_id"])
    hx, hz = _matrix_pair_from_builder(normalized)
    n = int(hx.shape[1])
    if n != 2 * view.block_size:
        raise ValueError("coset builder block size disagrees with catalog")
    css_commutation = not bool(np.any((hx @ hz.T) & 1))
    row_weights = np.concatenate((hx.sum(axis=1), hz.sum(axis=1)))
    column_degrees = np.vstack((hx, hz)).sum(axis=0)
    max_check_weight = int(row_weights.max(initial=0))
    max_qubit_degree = int(column_degrees.max(initial=0))
    tanner_components = _tanner_component_count(hx, hz)
    legal = bool(
        css_commutation
        and max_check_weight <= 6
        and max_qubit_degree <= 6
        and tanner_components == 1
    )
    rank_x = _gf2_rank(hx)
    rank_z = _gf2_rank(hz)
    k = n - rank_x - rank_z
    if k < 0:
        raise RuntimeError("coset CSS rank accounting produced negative k")
    return {
        "candidate": normalized,
        "construction": _stage2_construction(normalized),
        "candidate_sha256": candidate_digest(normalized),
        "action_id": view.action_id,
        "action_family_bin": view.action_family_bin,
        "subgroup_normal": view.subgroup_normal,
        "support_orbit_bin": support_orbit_bin(normalized),
        "hx": hx,
        "hz": hz,
        "n": n,
        "k": int(k),
        "rank_x": rank_x,
        "rank_z": rank_z,
        "css_commutation": css_commutation,
        "max_check_weight": max_check_weight,
        "max_qubit_degree": max_qubit_degree,
        "tanner_components": tanner_components,
        "static_legal": legal,
    }


def _dynamic_rejection_cutoff(n: int, k: int) -> int | None:
    """Return the official final-gate exclusion cutoff for ``(n, k)``.

    The scalar FOM cutoff alone is insufficient at the official challenge
    target: a code can also win by tying a published FOM at smaller block
    length (or by either fixed-coordinate Pareto rule).  Keep Stage 1 on the
    same machine-derived contract as the final gate so a witness at the first
    winning distance is never mislabeled as terminal negative.
    """
    if k <= 0:
        return None
    return compute_challenge_rejection_cutoff(int(n), int(k), TARGET_FOM)


def _cutoff_metadata(n: int, k: int) -> dict[str, int | None]:
    """Describe scalar and complete final-gate cutoffs without conflating them."""

    challenge_cutoff = _dynamic_rejection_cutoff(n, k)
    if challenge_cutoff is None:
        return {
            "fom_rejection_cutoff": None,
            "challenge_rejection_cutoff": None,
            "minimum_winning_distance": None,
        }
    scalar_cutoff = compute_fom_rejection_cutoff(n, k, TARGET_FOM)
    try:
        required = minimum_winning_distance(n, k)
    except ValueError:
        required = None
    return {
        "fom_rejection_cutoff": scalar_cutoff,
        "challenge_rejection_cutoff": challenge_cutoff,
        "minimum_winning_distance": required,
    }


def _proof_ladder(cutoff: int) -> tuple[int, ...]:
    """Return 4,6,8,... plus the exact (possibly odd/small) cutoff."""

    if isinstance(cutoff, bool) or not isinstance(cutoff, int) or cutoff < 1:
        return ()
    if cutoff <= COSET_PROOF_LADDER_START_WEIGHT:
        return (cutoff,)
    thresholds = list(range(
        COSET_PROOF_LADDER_START_WEIGHT,
        cutoff + 1,
        COSET_PROOF_LADDER_WEIGHT_STEP,
    ))
    if thresholds[-1] != cutoff:
        thresholds.append(cutoff)
    return tuple(thresholds)


@dataclass
class _OracleBatchBudget:
    """Non-resettable batch wall and count budget for new solver decisions."""

    remaining_new_steps: int
    deadline: float

    @classmethod
    def production(cls) -> "_OracleBatchBudget":
        return cls(
            remaining_new_steps=COSET_PROOF_MAX_NEW_STEPS_PER_BATCH,
            deadline=time.monotonic() + COSET_PROOF_BATCH_WALL_TIMEOUT_S,
        )

    @classmethod
    def single_step(cls) -> "_OracleBatchBudget":
        return cls(
            remaining_new_steps=1,
            deadline=time.monotonic() + COSET_PROOF_STEP_HARD_TIMEOUT_S,
        )

    def remaining_wall(self) -> float:
        return max(0.0, self.deadline - time.monotonic())

    def claim_timeout(self, *, requested_cap_s: float) -> float | None:
        remaining_wall = self.deadline - time.monotonic()
        if self.remaining_new_steps <= 0 or remaining_wall <= 0:
            return None
        self.remaining_new_steps -= 1
        return min(
            COSET_PROOF_STEP_HARD_TIMEOUT_S,
            float(requested_cap_s),
            remaining_wall,
        )


def _cache_canonical_sha256(value: Any) -> str:
    return hashlib.sha256(json.dumps(
        value,
        sort_keys=True,
        separators=(",", ":"),
        ensure_ascii=False,
        allow_nan=False,
    ).encode("utf-8")).hexdigest()


def _module_source_sha256(module: Any, *, label: str) -> str:
    source = getattr(module, "__file__", None)
    if not isinstance(source, str):
        raise RuntimeError(f"cannot fingerprint {label}")
    path = Path(source)
    if path.is_symlink() or not path.is_file():
        raise RuntimeError(f"cannot fingerprint {label}")
    return hashlib.sha256(path.read_bytes()).hexdigest()


def _binary_matrix_binding(name: str, value: np.ndarray) -> dict[str, Any]:
    matrix = np.ascontiguousarray(np.asarray(value, dtype=np.uint8) & 1)
    if matrix.ndim != 2:
        raise RuntimeError(f"{name} must be a binary matrix")
    packed = np.packbits(matrix.reshape(-1), bitorder="little").tobytes()
    payload = {
        "name": name,
        "shape": [int(item) for item in matrix.shape],
        "packed_sha256": hashlib.sha256(packed).hexdigest(),
    }
    payload["binding_sha256"] = _cache_canonical_sha256(payload)
    return payload


def _proof_problem_binding(
    *,
    candidate_sha256: str,
    threshold: int,
    hx: np.ndarray,
    hz: np.ndarray,
) -> dict[str, Any]:
    from evaluation import css_logical_detector, distance_sat, low_weight_oracle

    payload = {
        "candidate_sha256": candidate_sha256,
        "max_weight": threshold,
        "action_catalog_sha256": _action_catalog_sha256(),
        "hx": _binary_matrix_binding("hx", hx),
        "hz": _binary_matrix_binding("hz", hz),
        "source_sha256": {
            "coset_openevolve_evaluator": _module_source_sha256(
                sys.modules[__name__],
                label="coset_openevolve_evaluator.py",
            ),
            "low_weight_oracle": _module_source_sha256(
                low_weight_oracle,
                label="low_weight_oracle.py",
            ),
            "distance_sat": _module_source_sha256(
                distance_sat,
                label="distance_sat.py",
            ),
            "css_logical_detector": _module_source_sha256(
                css_logical_detector,
                label="css_logical_detector.py",
            ),
        },
    }
    payload["binding_sha256"] = _cache_canonical_sha256(payload)
    return payload


def _strict_self_hashed_mapping(
    value: Any,
    *,
    hash_field: str,
) -> bool:
    if not isinstance(value, Mapping):
        return False
    unsigned = dict(value)
    stored = unsigned.pop(hash_field, None)
    try:
        return (
            isinstance(stored, str)
            and len(stored) == 64
            and stored == _cache_canonical_sha256(unsigned)
        )
    except (TypeError, ValueError):
        return False


def _light_oracle_evidence_valid(
    evidence: Any,
    *,
    threshold: int,
) -> bool:
    """Validate sealed Stage-1 evidence without rerunning MITM or SAT.

    This path is restricted to a run-owned, candidate-log-committed ledger.
    Publication stages independently rebuild and reprove the candidate.
    """

    from evaluation import low_weight_oracle

    if not _strict_self_hashed_mapping(
        evidence,
        hash_field="evidence_sha256",
    ):
        return False
    assert isinstance(evidence, Mapping)
    outcome = evidence.get("outcome")
    sectors = evidence.get("sectors")
    if not (
        evidence.get("schema_version")
        == low_weight_oracle.LOW_WEIGHT_ORACLE_SCHEMA_VERSION
        and evidence.get("kind") == low_weight_oracle.LOW_WEIGHT_ORACLE_KIND
        and evidence.get("source_sha256")
        == _module_source_sha256(low_weight_oracle, label="low_weight_oracle.py")
        and evidence.get("max_weight") == threshold
        and outcome in {"SAT", "UNSAT", "UNKNOWN"}
        and isinstance(sectors, Mapping)
        and set(sectors) <= {"X", "Z"}
    ):
        return False
    sector_outcomes: dict[str, str] = {}
    for sector, raw in sectors.items():
        if not _strict_self_hashed_mapping(raw, hash_field="evidence_sha256"):
            return False
        assert isinstance(raw, Mapping)
        sector_outcome = raw.get("outcome")
        binding = raw.get("binding")
        if not (
            raw.get("schema_version")
            == low_weight_oracle.LOW_WEIGHT_ORACLE_SCHEMA_VERSION
            and raw.get("kind") == low_weight_oracle.LOW_WEIGHT_SECTOR_KIND
            and raw.get("max_weight") == threshold
            and sector_outcome in {"SAT", "UNSAT", "UNKNOWN"}
            and isinstance(binding, Mapping)
            and binding.get("source_sha256")
            == _module_source_sha256(
                low_weight_oracle,
                label="low_weight_oracle.py",
            )
            and binding.get("sector") == sector
            and binding.get("max_weight") == threshold
        ):
            return False
        binding_unsigned = dict(binding)
        binding_hash = binding_unsigned.pop("binding_sha256", None)
        if binding_hash != _cache_canonical_sha256(binding_unsigned):
            return False
        sector_outcomes[str(sector)] = str(sector_outcome)
    if outcome == "SAT":
        sat = [side for side, value in sector_outcomes.items() if value == "SAT"]
        return bool(
            sat
            and evidence.get("decision_complete") is True
            and evidence.get("retryable") is False
            and evidence.get("witness") == sectors[sat[0]].get("witness")
            and evidence.get("distance_lower_bound") is None
        )
    if outcome == "UNSAT":
        return bool(
            sector_outcomes == {"X": "UNSAT", "Z": "UNSAT"}
            and evidence.get("decision_complete") is True
            and evidence.get("retryable") is False
            and evidence.get("distance_lower_bound") == threshold + 1
            and evidence.get("witness") is None
        )
    return bool(
        evidence.get("decision_complete") is False
        and evidence.get("retryable") is True
        and evidence.get("distance_lower_bound") is None
        and evidence.get("witness") is None
        and not any(value == "SAT" for value in sector_outcomes.values())
    )


def _proof_cache_root() -> Path | None:
    """Derive the cache solely from the managed absolute candidate log."""

    raw_path = os.environ.get(CANDIDATE_LOG_PATH_ENV)
    if raw_path is None:
        return None
    if "\x00" in raw_path:
        raise RuntimeError("coset candidate log path must be absolute")
    candidate_log = Path(raw_path).expanduser()
    if not candidate_log.is_absolute():
        raise RuntimeError("coset candidate log path must be absolute")
    from evolve.openevolve_evaluator import _canonical_candidate_log_path

    candidate_log = _canonical_candidate_log_path(candidate_log)
    return candidate_log.parent / COSET_PROOF_CACHE_DIRECTORY


def _ensure_cache_directory(path: Path) -> None:
    try:
        metadata = path.lstat()
    except FileNotFoundError:
        try:
            path.mkdir(mode=0o700)
        except FileExistsError:
            pass
        metadata = path.lstat()
    if stat.S_ISLNK(metadata.st_mode) or not stat.S_ISDIR(metadata.st_mode):
        raise RuntimeError(f"coset proof cache directory is unsafe: {path}")


def _proof_cache_path(
    candidate_sha256: str,
    threshold: int,
    *,
    create_directories: bool,
) -> Path | None:
    if (
        not isinstance(candidate_sha256, str)
        or len(candidate_sha256) != 64
        or any(character not in "0123456789abcdef" for character in candidate_sha256)
    ):
        raise RuntimeError("coset proof cache candidate digest is invalid")
    if (
        isinstance(threshold, bool)
        or not isinstance(threshold, int)
        or threshold < 1
    ):
        raise RuntimeError("coset proof cache threshold is invalid")
    root = _proof_cache_root()
    if root is None:
        return None
    try:
        root.lstat()
    except FileNotFoundError:
        root_present = False
    else:
        root_present = True
    if create_directories:
        _ensure_cache_directory(root)
    elif not root_present:
        return root / candidate_sha256[:2] / (
            f"{candidate_sha256}-w{threshold}.json"
        )
    else:
        _ensure_cache_directory(root)
    shard = root / candidate_sha256[:2]
    try:
        shard.lstat()
    except FileNotFoundError:
        shard_present = False
    else:
        shard_present = True
    if create_directories:
        _ensure_cache_directory(shard)
    elif shard_present:
        _ensure_cache_directory(shard)
    return shard / f"{candidate_sha256}-w{threshold}.json"


def _proof_cache_version_path(base_path: Path, cache_sha256: str) -> Path:
    if (
        not isinstance(cache_sha256, str)
        or len(cache_sha256) != 64
        or any(character not in "0123456789abcdef" for character in cache_sha256)
    ):
        raise RuntimeError("coset proof cache generation digest is invalid")
    return base_path.with_name(
        f"{base_path.stem}-{cache_sha256}{base_path.suffix}"
    )


def _proof_cache_version_paths(base_path: Path) -> list[Path]:
    prefix = base_path.stem + "-"
    versions = []
    try:
        entries = list(base_path.parent.iterdir())
    except FileNotFoundError:
        return []
    for path in entries:
        name = path.name
        if not name.startswith(prefix) or not name.endswith(base_path.suffix):
            continue
        digest = name[len(prefix):-len(base_path.suffix)]
        if (
            len(digest) == 64
            and all(character in "0123456789abcdef" for character in digest)
        ):
            versions.append(path)
    return sorted(versions, key=lambda path: path.name)


def _read_regular_json(path: Path) -> dict[str, Any] | None:
    flags = os.O_RDONLY | os.O_CLOEXEC
    if hasattr(os, "O_NOFOLLOW"):
        flags |= os.O_NOFOLLOW
    try:
        descriptor = os.open(path, flags)
    except FileNotFoundError:
        return None
    except OSError as exc:
        raise RuntimeError(f"cannot safely open coset proof cache: {path}") from exc
    try:
        metadata = os.fstat(descriptor)
        if not stat.S_ISREG(metadata.st_mode):
            raise RuntimeError(f"coset proof cache is not a regular file: {path}")
        if metadata.st_size < 2 or metadata.st_size > _PROOF_CACHE_MAX_BYTES:
            return None
        chunks: list[bytes] = []
        remaining = metadata.st_size
        while remaining:
            chunk = os.read(descriptor, min(1024 * 1024, remaining))
            if not chunk:
                return None
            chunks.append(chunk)
            remaining -= len(chunk)
        if os.fstat(descriptor).st_size != metadata.st_size:
            return None
    finally:
        os.close(descriptor)
    try:
        value = json.loads(b"".join(chunks))
    except (UnicodeDecodeError, json.JSONDecodeError):
        return None
    return value if isinstance(value, dict) else None


def _validated_cache_envelope(
    raw: Any,
    *,
    candidate_sha256: str,
    threshold: int,
    hx: np.ndarray | None = None,
    hz: np.ndarray | None = None,
) -> dict[str, Any] | None:
    if not isinstance(raw, Mapping):
        return None
    expected_fields = {
        "schema_version",
        "proof_ladder_version",
        "kind",
        "candidate_sha256",
        "action_catalog_sha256",
        "max_weight",
        "problem_binding",
        "attempts",
        "latest_outcome",
        "evidence",
        "last_attempt",
        "retry_not_before_unix",
        "cache_sha256",
    }
    if set(raw) != expected_fields:
        return None
    unsigned = dict(raw)
    stored_hash = unsigned.pop("cache_sha256", None)
    try:
        hash_valid = stored_hash == _cache_canonical_sha256(unsigned)
    except (TypeError, ValueError):
        return None
    attempts = raw.get("attempts")
    evidence = raw.get("evidence")
    outcome = raw.get("latest_outcome")
    retry_not_before = raw.get("retry_not_before_unix")
    last_attempt = raw.get("last_attempt")
    problem_binding = raw.get("problem_binding")
    if not (
        hash_valid
        and raw.get("schema_version") == _PROOF_CACHE_SCHEMA_VERSION
        and raw.get("proof_ladder_version")
        == COSET_PROOF_LADDER_SCHEMA_VERSION
        and raw.get("kind") == _PROOF_CACHE_KIND
        and raw.get("candidate_sha256") == candidate_sha256
        and raw.get("action_catalog_sha256") == _action_catalog_sha256()
        and raw.get("max_weight") == threshold
        and _strict_self_hashed_mapping(
            problem_binding,
            hash_field="binding_sha256",
        )
        and isinstance(attempts, int)
        and not isinstance(attempts, bool)
        and attempts >= 1
        and outcome in {"SAT", "UNSAT", "UNKNOWN"}
        and isinstance(retry_not_before, (int, float))
        and not isinstance(retry_not_before, bool)
        and math.isfinite(float(retry_not_before))
        and float(retry_not_before) >= 0
        and isinstance(last_attempt, Mapping)
        and _strict_self_hashed_mapping(
            last_attempt,
            hash_field="attempt_sha256",
        )
        and last_attempt.get("outcome") == outcome
        and last_attempt.get("strategy_id")
        in {
            "sector-resume-timeout-7.5s-v1",
            "sector-resume-timeout-15s-v1",
            "sector-resume-timeout-30s-v1",
        }
        and isinstance(last_attempt.get("timeout_s"), (int, float))
        and not isinstance(last_attempt.get("timeout_s"), bool)
        and math.isfinite(float(last_attempt["timeout_s"]))
        and 0 < float(last_attempt["timeout_s"])
        <= COSET_PROOF_STEP_HARD_TIMEOUT_S
    ):
        return None
    if evidence is not None and not _light_oracle_evidence_valid(
        evidence,
        threshold=threshold,
    ):
        return None
    if outcome in {"SAT", "UNSAT"} and (
        not isinstance(evidence, Mapping)
        or evidence.get("outcome") != outcome
    ):
        return None
    if outcome == "UNKNOWN" and (
        evidence is not None
        and isinstance(evidence, Mapping)
        and evidence.get("outcome") != "UNKNOWN"
    ):
        return None
    if hx is not None and hz is not None:
        expected_problem = _proof_problem_binding(
            candidate_sha256=candidate_sha256,
            threshold=threshold,
            hx=hx,
            hz=hz,
        )
        if dict(problem_binding) != expected_problem:
            return None
    return dict(raw)


def _load_cached_evidence(
    candidate_sha256: str,
    threshold: int,
    *,
    hx: np.ndarray | None = None,
    hz: np.ndarray | None = None,
    require_committed: bool = True,
) -> dict[str, Any] | None:
    base_path = _proof_cache_path(
        candidate_sha256,
        threshold,
        create_directories=False,
    )
    if base_path is None:
        return None
    candidates: list[tuple[int, str, dict[str, Any]]] = []
    for path in _proof_cache_version_paths(base_path):
        envelope = _validated_cache_envelope(
            _read_regular_json(path),
            candidate_sha256=candidate_sha256,
            threshold=threshold,
            hx=hx,
            hz=hz,
        )
        if envelope is None:
            continue
        if path != _proof_cache_version_path(
            base_path,
            str(envelope["cache_sha256"]),
        ):
            continue
        if require_committed and not _cache_commit_valid(path, envelope):
            continue
        candidates.append((
            int(envelope["attempts"]),
            str(envelope["cache_sha256"]),
            envelope,
        ))
    if not candidates:
        return None
    return max(candidates, key=lambda item: (item[0], item[1]))[2]


def _cache_generations(
    base_path: Path,
    *,
    candidate_sha256: str,
    threshold: int,
    hx: np.ndarray,
    hz: np.ndarray,
) -> list[tuple[Path, dict[str, Any], bool]]:
    records = []
    for path in _proof_cache_version_paths(base_path):
        envelope = _validated_cache_envelope(
            _read_regular_json(path),
            candidate_sha256=candidate_sha256,
            threshold=threshold,
            hx=hx,
            hz=hz,
        )
        if envelope is None or path != _proof_cache_version_path(
            base_path,
            str(envelope["cache_sha256"]),
        ):
            continue
        records.append((path, envelope, _cache_commit_valid(path, envelope)))
    return records


def _atomic_write_cache(path: Path, payload: Mapping[str, Any]) -> None:
    if path.exists() or path.is_symlink():
        metadata = path.lstat()
        if stat.S_ISLNK(metadata.st_mode) or not stat.S_ISREG(metadata.st_mode):
            raise RuntimeError(f"refusing unsafe coset proof cache target: {path}")
    encoded = json.dumps(
        payload,
        sort_keys=True,
        separators=(",", ":"),
        ensure_ascii=False,
        allow_nan=False,
    ).encode("utf-8")
    temporary = path.with_name(
        f".{path.name}.tmp-{os.getpid()}-{threading.get_ident()}-{time.time_ns()}"
    )
    flags = os.O_WRONLY | os.O_CREAT | os.O_EXCL | os.O_CLOEXEC
    if hasattr(os, "O_NOFOLLOW"):
        flags |= os.O_NOFOLLOW
    descriptor = os.open(temporary, flags, 0o600)
    try:
        try:
            written = 0
            while written < len(encoded):
                count = os.write(descriptor, encoded[written:])
                if count <= 0:
                    raise OSError("coset proof cache write made no progress")
                written += count
            os.fsync(descriptor)
        finally:
            os.close(descriptor)
        os.replace(temporary, path)
        directory_flags = os.O_RDONLY | os.O_CLOEXEC
        if hasattr(os, "O_DIRECTORY"):
            directory_flags |= os.O_DIRECTORY
        directory = os.open(path.parent, directory_flags)
        try:
            os.fsync(directory)
        finally:
            os.close(directory)
    except BaseException:
        try:
            temporary.unlink()
        except FileNotFoundError:
            pass
        raise


def _write_immutable_cache(path: Path, payload: Mapping[str, Any]) -> None:
    existing = _read_regular_json(path)
    if existing is not None:
        if existing != dict(payload):
            raise RuntimeError("immutable coset proof generation changed")
        return
    if path.exists() or path.is_symlink():
        raise RuntimeError("immutable coset proof generation is unsafe")
    _atomic_write_cache(path, payload)
    if _read_regular_json(path) != dict(payload):
        raise RuntimeError("immutable coset proof generation did not replay")


@contextmanager
def _proof_evaluation_lease():
    """Make pending entries live only for one active evaluator transaction."""

    existing = getattr(_PROOF_EVALUATION_LOCAL, "token", None)
    if isinstance(existing, str):
        yield existing
        return
    root = _proof_cache_root()
    if root is None:
        yield None
        return
    _ensure_cache_directory(root)
    lease_directory = root / ".leases"
    _ensure_cache_directory(lease_directory)
    process = _process_identity()
    token = hashlib.sha256(json.dumps({
        "process": process,
        "thread": threading.get_ident(),
        "time_ns": time.time_ns(),
    }, sort_keys=True, separators=(",", ":")).encode("utf-8")).hexdigest()
    lease_path = lease_directory / f"{token}.json"
    marker = {
        "schema_version": 1,
        "kind": "qcode-coset-proof-evaluation-lease",
        "token": token,
        "process": process,
    }
    marker["lease_sha256"] = _cache_canonical_sha256(marker)
    _atomic_write_cache(lease_path, marker)
    _PROOF_EVALUATION_LOCAL.token = token
    try:
        yield token
    finally:
        _PROOF_EVALUATION_LOCAL.token = None
        try:
            lease_path.unlink()
        except FileNotFoundError:
            pass
        flags = os.O_RDONLY | os.O_CLOEXEC
        if hasattr(os, "O_DIRECTORY"):
            flags |= os.O_DIRECTORY
        descriptor = os.open(lease_directory, flags)
        try:
            os.fsync(descriptor)
        finally:
            os.close(descriptor)


def _seal_cache_envelope(
    *,
    candidate_sha256: str,
    threshold: int,
    attempts: int,
    hx: np.ndarray,
    hz: np.ndarray,
    evidence: Mapping[str, Any] | None,
    last_attempt: Mapping[str, Any],
) -> dict[str, Any]:
    unsigned_attempt = dict(last_attempt)
    unsigned_attempt.pop("attempt_sha256", None)
    outcome = unsigned_attempt.get("outcome")
    if outcome not in {"SAT", "UNSAT", "UNKNOWN"}:
        raise RuntimeError("coset proof attempt outcome is invalid")
    envelope = {
        "schema_version": _PROOF_CACHE_SCHEMA_VERSION,
        "proof_ladder_version": COSET_PROOF_LADDER_SCHEMA_VERSION,
        "kind": _PROOF_CACHE_KIND,
        "candidate_sha256": candidate_sha256,
        "action_catalog_sha256": _action_catalog_sha256(),
        "max_weight": threshold,
        "problem_binding": _proof_problem_binding(
            candidate_sha256=candidate_sha256,
            threshold=threshold,
            hx=hx,
            hz=hz,
        ),
        "attempts": attempts,
        "latest_outcome": outcome,
        "evidence": None if evidence is None else dict(evidence),
        "last_attempt": {
            **unsigned_attempt,
            "attempt_sha256": _cache_canonical_sha256(unsigned_attempt),
        },
        "retry_not_before_unix": (
            0.0
            if outcome in {"SAT", "UNSAT"}
            else time.time() + _ORACLE_UNKNOWN_RETRY_BACKOFF_S
        ),
    }
    envelope["cache_sha256"] = _cache_canonical_sha256(envelope)
    return envelope


def _cache_commit_path(cache_path: Path) -> Path:
    return cache_path.with_name(cache_path.name + ".commit.json")


def _proof_ledger_for_row(row: Mapping[str, Any]) -> dict[str, Any]:
    entries = []
    for raw in row.get("oracle_ladder_history", []):
        if not isinstance(raw, Mapping):
            continue
        cache_sha256 = raw.get("cache_sha256")
        evidence_sha256 = raw.get("evidence_sha256")
        attempt_sha256 = raw.get("attempt_sha256")
        threshold = raw.get("threshold")
        outcome = raw.get("outcome")
        if (
            isinstance(cache_sha256, str)
            and len(cache_sha256) == 64
            and (
                isinstance(evidence_sha256, str)
                and len(evidence_sha256) == 64
                or evidence_sha256 is None
                and isinstance(attempt_sha256, str)
                and len(attempt_sha256) == 64
            )
            and isinstance(threshold, int)
            and not isinstance(threshold, bool)
            and outcome in {"SAT", "UNSAT", "UNKNOWN"}
        ):
            entries.append({
                "threshold": threshold,
                "outcome": outcome,
                "evidence_sha256": evidence_sha256,
                "attempt_sha256": attempt_sha256,
                "cache_sha256": cache_sha256,
            })
    entries.sort(key=lambda item: item["threshold"])
    payload = {
        "kind": _PROOF_LEDGER_KIND,
        "schema_version": 1,
        "proof_ladder_version": COSET_PROOF_LADDER_SCHEMA_VERSION,
        "candidate_sha256": row["candidate_sha256"],
        "entries": entries,
    }
    payload["root_sha256"] = _cache_canonical_sha256(payload)
    return payload


def _candidate_range_payload(identity: Mapping[str, Any]) -> bytes | None:
    required = {
        "path",
        "device",
        "inode",
        "start_offset",
        "end_offset",
        "sha256",
        "bytes",
        "wal_clean",
    }
    if set(identity) != required or identity.get("wal_clean") is not True:
        return None
    path_value = identity.get("path")
    start = identity.get("start_offset")
    end = identity.get("end_offset")
    if (
        not isinstance(path_value, str)
        or not Path(path_value).is_absolute()
        or isinstance(start, bool)
        or not isinstance(start, int)
        or isinstance(end, bool)
        or not isinstance(end, int)
        or not 0 <= start <= end
    ):
        return None
    from evolve.openevolve_evaluator import candidate_log_range_identity

    try:
        observed = candidate_log_range_identity(
            Path(path_value),
            start_offset=start,
            end_offset=end,
        )
    except Exception:
        return None
    if observed != dict(identity):
        return None
    flags = os.O_RDONLY | os.O_CLOEXEC
    if hasattr(os, "O_NOFOLLOW"):
        flags |= os.O_NOFOLLOW
    try:
        descriptor = os.open(path_value, flags)
    except OSError:
        return None
    try:
        metadata = os.fstat(descriptor)
        if (
            not stat.S_ISREG(metadata.st_mode)
            or metadata.st_dev != identity["device"]
            or metadata.st_ino != identity["inode"]
            or metadata.st_size < end
        ):
            return None
        payload = bytearray()
        position = start
        while position < end:
            chunk = os.pread(
                descriptor,
                min(1 << 20, end - position),
                position,
            )
            if not chunk:
                return None
            payload.extend(chunk)
            position += len(chunk)
    finally:
        os.close(descriptor)
    if hashlib.sha256(payload).hexdigest() != identity["sha256"]:
        return None
    return bytes(payload)


def _cache_commit_valid(
    cache_path: Path,
    envelope: Mapping[str, Any],
) -> bool:
    marker = _read_regular_json(_cache_commit_path(cache_path))
    if not isinstance(marker, Mapping):
        return False
    expected = {
        "schema_version",
        "kind",
        "candidate_sha256",
        "max_weight",
        "cache_sha256",
        "ledger_root_sha256",
        "candidate_log_range",
        "commit_sha256",
    }
    if set(marker) != expected:
        return False
    unsigned = dict(marker)
    commit_sha256 = unsigned.pop("commit_sha256", None)
    if commit_sha256 != _cache_canonical_sha256(unsigned):
        return False
    candidate_log = _proof_cache_root()
    if candidate_log is None:
        return False
    raw_log = os.environ.get(CANDIDATE_LOG_PATH_ENV)
    if raw_log is None:
        return False
    from evolve.openevolve_evaluator import _canonical_candidate_log_path

    canonical_log = str(_canonical_candidate_log_path(raw_log))
    identity = marker.get("candidate_log_range")
    if not (
        marker.get("schema_version") == 1
        and marker.get("kind") == _PROOF_CACHE_COMMIT_KIND
        and marker.get("candidate_sha256")
        == envelope.get("candidate_sha256")
        and marker.get("max_weight") == envelope.get("max_weight")
        and marker.get("cache_sha256") == envelope.get("cache_sha256")
        and isinstance(marker.get("ledger_root_sha256"), str)
        and isinstance(identity, Mapping)
        and identity.get("path") == canonical_log
    ):
        return False
    payload = _candidate_range_payload(identity)
    if payload is None:
        return False
    try:
        rows = [
            json.loads(line)
            for line in payload.splitlines()
            if line.strip()
        ]
    except (UnicodeDecodeError, json.JSONDecodeError):
        return False
    for row in rows:
        if not isinstance(row, Mapping):
            continue
        ledger = row.get("proof_ledger")
        if not isinstance(ledger, Mapping):
            continue
        unsigned_ledger = dict(ledger)
        root = unsigned_ledger.pop("root_sha256", None)
        if (
            root != marker["ledger_root_sha256"]
            or root != _cache_canonical_sha256(unsigned_ledger)
            or ledger.get("kind") != _PROOF_LEDGER_KIND
            or ledger.get("candidate_sha256")
            != envelope.get("candidate_sha256")
        ):
            continue
        entries = ledger.get("entries")
        if isinstance(entries, list) and any(
            isinstance(entry, Mapping)
            and entry.get("max_weight", entry.get("threshold"))
            == envelope.get("max_weight")
            and entry.get("cache_sha256") == envelope.get("cache_sha256")
            for entry in entries
        ):
            return True
    return False


def _commit_cache_entries(
    rows: list[dict[str, Any]],
    candidate_log_range: Mapping[str, Any],
) -> None:
    for row in rows:
        ledger = _proof_ledger_for_row(row)
        for entry in ledger["entries"]:
            cache_base = _proof_cache_path(
                row["candidate_sha256"],
                int(entry["threshold"]),
                create_directories=False,
            )
            if cache_base is None:
                continue
            cache_path = _proof_cache_version_path(
                cache_base,
                str(entry["cache_sha256"]),
            )
            envelope = _validated_cache_envelope(
                _read_regular_json(cache_path),
                candidate_sha256=row["candidate_sha256"],
                threshold=int(entry["threshold"]),
                hx=row["hx"],
                hz=row["hz"],
            )
            if (
                envelope is None
                or envelope.get("cache_sha256") != entry["cache_sha256"]
            ):
                raise RuntimeError(
                    "proof cache changed before candidate-log commit"
                )
            # Never move an already durable entry's only commit marker to a
            # newer range. If that later round is abandoned/truncated, the
            # historical proof frontier must remain recoverable.
            if _cache_commit_valid(cache_path, envelope):
                continue
            marker = {
                "schema_version": 1,
                "kind": _PROOF_CACHE_COMMIT_KIND,
                "candidate_sha256": row["candidate_sha256"],
                "max_weight": int(entry["threshold"]),
                "cache_sha256": entry["cache_sha256"],
                "ledger_root_sha256": ledger["root_sha256"],
                "candidate_log_range": dict(candidate_log_range),
            }
            marker["commit_sha256"] = _cache_canonical_sha256(marker)
            _atomic_write_cache(_cache_commit_path(cache_path), marker)


def _cache_progress_hint(row: Mapping[str, Any]) -> int:
    """Untrusted scheduling hint; proof credit is always replayed later."""

    cutoff = _dynamic_rejection_cutoff(int(row["n"]), int(row["k"]))
    if cutoff is None:
        return 0
    progress = 0
    ladder = _proof_ladder(cutoff)
    for threshold in ladder:
        cached = _load_cached_evidence(row["candidate_sha256"], threshold)
        if cached is None:
            break
        outcome = cached["latest_outcome"]
        if outcome == "UNSAT":
            progress = threshold
            continue
        if outcome == "SAT":
            return -1
        break
    else:
        # A complete threshold proof is useful when hydrated, but it must not
        # occupy a continuation slot or consume a new-step budget forever.
        if ladder and progress == ladder[-1]:
            return -1
    return progress


def _oracle_probe_rows(
    rows: list[dict[str, Any]],
    limit: int = MAX_ORACLE_CANDIDATES,
    *,
    selection_salt: str = "",
) -> list[dict[str, Any]]:
    """Select proof probes with progress priority and salted action rotation."""

    eligible = [
        row for row in rows if row["static_legal"] and row["k"] > 0
    ]
    if not eligible or limit < 1:
        return []
    if not isinstance(selection_salt, str):
        raise TypeError("oracle selection salt must be a string")
    views = action_search_views()
    total = min(limit, len(eligible))
    fixed_quotas = quota_by_normality(views, total)
    class_budgets = {
        normal: sum(
            fixed_quotas[view.action_id]
            for view in views
            if view.subgroup_normal is normal
        )
        for normal in (False, True)
    }

    def priority(row: Mapping[str, Any]) -> tuple[Any, ...]:
        return (
            -(row["k"] / row["n"]),
            row["support_orbit_bin"],
            row["candidate_sha256"],
        )

    def rendezvous(label: str) -> int:
        return int.from_bytes(hashlib.sha256(
            (selection_salt + "\0" + label).encode("utf-8")
        ).digest(), "big")

    progress = {
        row["candidate_sha256"]: _cache_progress_hint(row)
        for row in eligible
    }

    def action_rows(action_id: str) -> list[dict[str, Any]]:
        ordered = sorted(
            (row for row in eligible if row["action_id"] == action_id),
            key=priority,
        )
        # Keep the historical high/low-rate alternation within each action,
        # then stably lift candidates with an unfinished cached ladder.
        diverse: list[dict[str, Any]] = []
        left, right = 0, len(ordered) - 1
        while left <= right:
            diverse.append(ordered[left])
            left += 1
            if left <= right:
                diverse.append(ordered[right])
                right -= 1
        diverse_index = {
            row["candidate_sha256"]: index
            for index, row in enumerate(diverse)
        }
        return sorted(
            diverse,
            key=lambda row: (
                -progress[row["candidate_sha256"]],
                diverse_index[row["candidate_sha256"]],
            ),
        )

    selected: list[dict[str, Any]] = []
    selected_digests: set[str] = set()
    for normal in (False, True):
        budget = class_budgets[normal]
        if budget <= 0:
            continue
        class_views = [
            view for view in views
            if view.subgroup_normal is normal
            and any(row["action_id"] == view.action_id for row in eligible)
        ]
        if not class_views:
            continue
        action_progress = {
            view.action_id: max(
                progress[row["candidate_sha256"]]
                for row in eligible
                if row["action_id"] == view.action_id
            )
            for view in class_views
        }
        # Reserve a rotating exploration slice so a large catalog cannot be
        # permanently reduced to the lexicographically first few actions.
        exploration_slots = (
            max(1, budget // 3) if len(class_views) > 1 else 0
        )
        continuation_slots = max(0, budget - exploration_slots)
        progressed = sorted(
            (
                view for view in class_views
                if action_progress[view.action_id] > 0
            ),
            key=lambda view: (
                -action_progress[view.action_id],
                -rendezvous("action:" + view.action_id),
                view.action_id,
            ),
        )
        chosen = progressed[:continuation_slots]
        chosen_ids = {view.action_id for view in chosen}
        rotating = sorted(
            (view for view in class_views if view.action_id not in chosen_ids),
            key=lambda view: (
                -rendezvous("action:" + view.action_id),
                view.action_id,
            ),
        )
        action_slots = min(budget, len(class_views))
        chosen.extend(rotating[:max(0, action_slots - len(chosen))])

        for view in chosen:
            candidate = action_rows(view.action_id)[0]
            selected.append(candidate)
            selected_digests.add(candidate["candidate_sha256"])

        remaining_class = budget - len(chosen)
        if remaining_class > 0:
            extras = sorted(
                (
                    row for row in eligible
                    if row["subgroup_normal"] is normal
                    and row["candidate_sha256"] not in selected_digests
                ),
                key=lambda row: (
                    -progress[row["candidate_sha256"]],
                    -rendezvous("candidate:" + row["candidate_sha256"]),
                    *priority(row),
                ),
            )
            for row in extras[:remaining_class]:
                selected.append(row)
                selected_digests.add(row["candidate_sha256"])

    if len(selected) < total:
        remainder = sorted(
            (
                row for row in eligible
                if row["candidate_sha256"] not in selected_digests
            ),
            key=lambda row: (
                -progress[row["candidate_sha256"]],
                -rendezvous("candidate:" + row["candidate_sha256"]),
                *priority(row),
            ),
        )
        selected.extend(remainder[:total - len(selected)])
    return selected


def _encoded_binary_matrix(value: np.ndarray) -> dict[str, Any]:
    matrix = np.ascontiguousarray(np.asarray(value, dtype=np.uint8) & 1)
    packed = np.packbits(matrix.reshape(-1), bitorder="little").tobytes()
    payload = {
        "shape": [int(item) for item in matrix.shape],
        "packed_hex": packed.hex(),
        "packed_sha256": hashlib.sha256(packed).hexdigest(),
    }
    return payload


def _decoded_binary_matrix(value: Any, *, label: str) -> np.ndarray:
    if not isinstance(value, Mapping) or set(value) != {
        "shape",
        "packed_hex",
        "packed_sha256",
    }:
        raise ValueError(f"{label} worker matrix envelope is invalid")
    shape = value.get("shape")
    if (
        not isinstance(shape, list)
        or len(shape) != 2
        or any(
            isinstance(item, bool)
            or not isinstance(item, int)
            or not 0 <= item <= 8192
            for item in shape
        )
        or shape[1] < 1
    ):
        raise ValueError(f"{label} worker matrix shape is invalid")
    try:
        packed = bytes.fromhex(str(value.get("packed_hex")))
    except ValueError as exc:
        raise ValueError(f"{label} worker matrix encoding is invalid") from exc
    expected_bytes = (shape[0] * shape[1] + 7) // 8
    if (
        len(packed) != expected_bytes
        or hashlib.sha256(packed).hexdigest() != value.get("packed_sha256")
    ):
        raise ValueError(f"{label} worker matrix digest is invalid")
    bits = np.unpackbits(
        np.frombuffer(packed, dtype=np.uint8),
        bitorder="little",
    )[: shape[0] * shape[1]]
    return bits.reshape(shape).astype(np.uint8)


def _oracle_rung_worker_payload(
    row: Mapping[str, Any],
    *,
    threshold: int,
    inner_timeout_s: float,
    terminal_sectors: Mapping[str, Mapping[str, Any]],
) -> bytes:
    payload = {
        "schema_version": _ORACLE_RUNG_WORKER_SCHEMA_VERSION,
        "candidate_sha256": row["candidate_sha256"],
        "expected_k": int(row["k"]),
        "max_weight": threshold,
        "inner_timeout_s": inner_timeout_s,
        "hx": _encoded_binary_matrix(row["hx"]),
        "hz": _encoded_binary_matrix(row["hz"]),
        "terminal_sectors": dict(terminal_sectors),
    }
    encoded = json.dumps(
        payload,
        sort_keys=True,
        separators=(",", ":"),
        allow_nan=False,
    ).encode("utf-8")
    if len(encoded) > _ORACLE_RUNG_WORKER_MAX_BYTES:
        raise RuntimeError("coset oracle rung request exceeds the safety cap")
    return encoded


def _oracle_rung_worker_main() -> int:
    try:
        encoded = sys.stdin.buffer.read(_ORACLE_RUNG_WORKER_MAX_BYTES + 1)
        if len(encoded) > _ORACLE_RUNG_WORKER_MAX_BYTES:
            raise ValueError("oracle rung request exceeds the safety cap")
        request = json.loads(encoded)
        if not isinstance(request, Mapping) or set(request) != {
            "schema_version",
            "candidate_sha256",
            "expected_k",
            "max_weight",
            "inner_timeout_s",
            "hx",
            "hz",
            "terminal_sectors",
        }:
            raise ValueError("oracle rung request schema is invalid")
        threshold = request["max_weight"]
        expected_k = request["expected_k"]
        timeout = request["inner_timeout_s"]
        if (
            request["schema_version"] != _ORACLE_RUNG_WORKER_SCHEMA_VERSION
            or not isinstance(request["candidate_sha256"], str)
            or len(request["candidate_sha256"]) != 64
            or isinstance(threshold, bool)
            or not isinstance(threshold, int)
            or threshold < 1
            or isinstance(expected_k, bool)
            or not isinstance(expected_k, int)
            or expected_k < 1
            or isinstance(timeout, bool)
            or not isinstance(timeout, (int, float))
            or not math.isfinite(float(timeout))
            or float(timeout) <= 0
            or not isinstance(request["terminal_sectors"], Mapping)
            or set(request["terminal_sectors"]) - {"X", "Z"}
        ):
            raise ValueError("oracle rung request values are invalid")
        hx = _decoded_binary_matrix(request["hx"], label="HX")
        hz = _decoded_binary_matrix(request["hz"], label="HZ")
        code = codes.CSSCode(
            hx,
            hz,
            field=2,
            promise_equal_distance_xz=False,
        )
        if int(code.dimension) != expected_k:
            raise RuntimeError(
                "independent CSSCode dimension disagrees with GF2 rank"
            )
        lx = np.asarray(code.get_logical_ops(Pauli.X), dtype=np.uint8)
        lz = np.asarray(code.get_logical_ops(Pauli.Z), dtype=np.uint8)
        evidence = evaluate_css_low_weight_oracle(
            hx,
            hz,
            lx,
            lz,
            max_weight=threshold,
            hard_timeout_s=float(timeout),
            terminal_sectors=request["terminal_sectors"],
        )
        failures = verify_css_low_weight_oracle(
            evidence,
            hx,
            hz,
            lx,
            lz,
            replay_mitm_unsat=False,
        )
        if failures:
            raise RuntimeError(
                "low-weight oracle did not replay: " + "; ".join(failures)
            )
        response = {
            "schema_version": _ORACLE_RUNG_WORKER_SCHEMA_VERSION,
            "status": "ok",
            "evidence": evidence,
        }
    except BaseException as exc:
        response = {
            "schema_version": _ORACLE_RUNG_WORKER_SCHEMA_VERSION,
            "status": "error",
            "error_type": type(exc).__name__,
            "error_sha256": hashlib.sha256(
                f"{type(exc).__name__}:{exc}".encode(
                    "utf-8",
                    errors="replace",
                )
            ).hexdigest(),
        }
    result = json.dumps(
        response,
        sort_keys=True,
        separators=(",", ":"),
        allow_nan=False,
    ).encode("utf-8")
    if len(result) > _ORACLE_RUNG_WORKER_MAX_BYTES:
        return 2
    sys.stdout.buffer.write(result)
    sys.stdout.buffer.flush()
    return 0 if response["status"] == "ok" else 1


def _terminate_oracle_process_group(process: subprocess.Popen[bytes]) -> None:
    pgid = process.pid
    process.poll()

    def group_exists() -> bool:
        try:
            os.killpg(pgid, 0)
        except ProcessLookupError:
            return False
        except PermissionError:
            return True
        return True

    try:
        os.killpg(pgid, signal.SIGTERM)
    except ProcessLookupError:
        pass
    deadline = time.monotonic() + _ORACLE_RUNG_KILL_GRACE_S
    while group_exists() and time.monotonic() < deadline:
        process.poll()
        time.sleep(0.01)
    if group_exists():
        try:
            os.killpg(pgid, signal.SIGKILL)
        except ProcessLookupError:
            pass
        deadline = time.monotonic() + _ORACLE_RUNG_KILL_GRACE_S
        while group_exists() and time.monotonic() < deadline:
            process.poll()
            time.sleep(0.01)
    try:
        process.wait(timeout=_ORACLE_RUNG_KILL_GRACE_S)
    except subprocess.TimeoutExpired as exc:
        raise RuntimeError("cannot reap coset oracle process-group leader") from exc
    if group_exists():
        raise RuntimeError("coset oracle process group survived SIGKILL")


def _run_oracle_rung_hard_wall(
    row: Mapping[str, Any],
    *,
    threshold: int,
    timeout_s: float,
    terminal_sectors: Mapping[str, Mapping[str, Any]],
) -> tuple[dict[str, Any] | None, dict[str, Any]]:
    """Run logical construction and both sectors inside one killable wall."""

    started = time.monotonic()
    inner_timeout = max(0.05, float(timeout_s) - 0.5)
    encoded = _oracle_rung_worker_payload(
        row,
        threshold=threshold,
        inner_timeout_s=inner_timeout,
        terminal_sectors=terminal_sectors,
    )
    worker_environment = os.environ.copy()
    for name in (
        "OMP_NUM_THREADS",
        "OMP_THREAD_LIMIT",
        "OPENBLAS_NUM_THREADS",
        "MKL_NUM_THREADS",
        "NUMEXPR_NUM_THREADS",
        "VECLIB_MAXIMUM_THREADS",
        "BLIS_NUM_THREADS",
    ):
        worker_environment[name] = "1"
    process = subprocess.Popen(
        [sys.executable, str(Path(__file__).resolve()), "--oracle-rung-worker"],
        stdin=subprocess.PIPE,
        stdout=subprocess.PIPE,
        stderr=subprocess.DEVNULL,
        start_new_session=True,
        env=worker_environment,
    )
    hard_wall_timeout = False
    worker_failed = False
    try:
        output, _ = process.communicate(input=encoded, timeout=float(timeout_s))
    except subprocess.TimeoutExpired:
        hard_wall_timeout = True
        _terminate_oracle_process_group(process)
        output = b""
    else:
        # A solver descendant must never outlive a normally exiting or failed
        # worker leader. The group cleanup is intentionally unconditional.
        _terminate_oracle_process_group(process)
    if len(output) > _ORACLE_RUNG_WORKER_MAX_BYTES:
        worker_failed = True
        output = b""
    evidence: dict[str, Any] | None = None
    if not hard_wall_timeout and process.returncode == 0:
        try:
            response = json.loads(output)
        except (UnicodeDecodeError, json.JSONDecodeError):
            worker_failed = True
        else:
            if (
                isinstance(response, Mapping)
                and response.get("schema_version")
                == _ORACLE_RUNG_WORKER_SCHEMA_VERSION
                and response.get("status") == "ok"
                and _light_oracle_evidence_valid(
                    response.get("evidence"),
                    threshold=threshold,
                )
            ):
                evidence = dict(response["evidence"])
            else:
                worker_failed = True
    elif not hard_wall_timeout:
        worker_failed = True
    return evidence, {
        "hard_wall_timeout": hard_wall_timeout,
        "worker_failed": worker_failed,
        "elapsed_s": time.monotonic() - started,
        "resumed_sectors": sorted(terminal_sectors),
    }


def _attempt_timeout_strategy(attempts_before: int) -> tuple[str, float]:
    if attempts_before <= 0:
        return "sector-resume-timeout-7.5s-v1", _ORACLE_INITIAL_TIMEOUT_S
    if attempts_before == 1:
        return "sector-resume-timeout-15s-v1", 2 * _ORACLE_INITIAL_TIMEOUT_S
    return "sector-resume-timeout-30s-v1", COSET_PROOF_STEP_HARD_TIMEOUT_S


def _process_identity(pid: int | None = None) -> dict[str, int]:
    selected_pid = os.getpid() if pid is None else int(pid)
    start_ticks = -1
    try:
        fields = Path(f"/proc/{selected_pid}/stat").read_text().split()
        start_ticks = int(fields[21])
    except (OSError, ValueError, IndexError):
        pass
    return {"pid": selected_pid, "linux_start_ticks": start_ticks}


def _pending_writer_alive(last_attempt: Any) -> bool:
    if not isinstance(last_attempt, Mapping):
        return False
    identity = last_attempt.get("writer_process")
    token = last_attempt.get("evaluation_token")
    if not isinstance(identity, Mapping) or set(identity) != {
        "pid",
        "linux_start_ticks",
    }:
        return False
    pid = identity.get("pid")
    start_ticks = identity.get("linux_start_ticks")
    if (
        isinstance(pid, bool)
        or not isinstance(pid, int)
        or pid < 1
        or isinstance(start_ticks, bool)
        or not isinstance(start_ticks, int)
        or not isinstance(token, str)
        or len(token) != 64
    ):
        return False
    observed = _process_identity(pid)
    if observed["linux_start_ticks"] < 0 or observed != dict(identity):
        return False
    root = _proof_cache_root()
    if root is None:
        return False
    marker = _read_regular_json(root / ".leases" / f"{token}.json")
    return bool(
        isinstance(marker, Mapping)
        and set(marker) == {
            "schema_version",
            "kind",
            "token",
            "process",
            "lease_sha256",
        }
        and marker.get("schema_version") == 1
        and marker.get("kind") == "qcode-coset-proof-evaluation-lease"
        and marker.get("token") == token
        and marker.get("process") == dict(identity)
        and _strict_self_hashed_mapping(
            marker,
            hash_field="lease_sha256",
        )
    )


def _terminal_sectors_from_cache(
    envelope: Mapping[str, Any] | None,
) -> dict[str, Mapping[str, Any]]:
    if not isinstance(envelope, Mapping):
        return {}
    evidence = envelope.get("evidence")
    sectors = evidence.get("sectors") if isinstance(evidence, Mapping) else None
    if not isinstance(sectors, Mapping):
        return {}
    return {
        str(sector): dict(raw)
        for sector, raw in sectors.items()
        if sector in {"X", "Z"}
        and isinstance(raw, Mapping)
        and raw.get("outcome") in {"SAT", "UNSAT"}
    }


def _deadline_lock(
    descriptor: int,
    *,
    deadline: float,
) -> bool:
    while True:
        try:
            fcntl.flock(descriptor, fcntl.LOCK_EX | fcntl.LOCK_NB)
            return True
        except BlockingIOError:
            remaining = deadline - time.monotonic()
            if remaining <= 0:
                return False
            time.sleep(min(0.05, remaining))


def _run_oracle_step(
    row: Mapping[str, Any],
    *,
    threshold: int,
    budget: _OracleBatchBudget,
) -> tuple[dict[str, Any] | None, dict[str, Any]]:
    """Load one committed terminal rung or atomically attempt a retry."""

    candidate_sha256 = str(row["candidate_sha256"])
    path = _proof_cache_path(
        candidate_sha256,
        threshold,
        create_directories=True,
    )
    if path is None:
        strategy_id, timeout_cap = _attempt_timeout_strategy(0)
        timeout = budget.claim_timeout(requested_cap_s=timeout_cap)
        if timeout is None:
            return None, {
                "attempts": 0,
                "budget_exhausted": True,
                "deferred": True,
                "cache_hit": False,
                "latest_outcome": None,
            }
        evidence, worker = _run_oracle_rung_hard_wall(
            row,
            threshold=threshold,
            timeout_s=timeout,
            terminal_sectors={},
        )
        outcome = (
            evidence.get("outcome")
            if isinstance(evidence, Mapping) else "UNKNOWN"
        )
        last_attempt = {
            "outcome": outcome,
            "strategy_id": strategy_id,
            "timeout_s": float(timeout),
            "hard_wall_timeout": bool(worker["hard_wall_timeout"]),
            "worker_failed": bool(worker["worker_failed"]),
            "elapsed_s": float(worker["elapsed_s"]),
            "resumed_sectors": [],
        }
        last_attempt["attempt_sha256"] = _cache_canonical_sha256(last_attempt)
        return evidence, {
            "attempts": 1,
            "budget_exhausted": False,
            "deferred": False,
            "cache_hit": False,
            "cache_sha256": None,
            "last_attempt": last_attempt,
        }
    lock_path = path.with_name(path.name + ".lock")
    try:
        metadata = lock_path.lstat()
    except FileNotFoundError:
        metadata = None
    if metadata is not None and (
        stat.S_ISLNK(metadata.st_mode) or not stat.S_ISREG(metadata.st_mode)
    ):
        raise RuntimeError("coset proof cache lock is unsafe")
    flags = os.O_RDWR | os.O_CREAT | os.O_CLOEXEC
    if hasattr(os, "O_NOFOLLOW"):
        flags |= os.O_NOFOLLOW
    try:
        lock_descriptor = os.open(lock_path, flags, 0o600)
    except OSError as exc:
        raise RuntimeError(
            f"cannot safely open coset proof cache lock: {lock_path}"
        ) from exc
    locked = False
    try:
        if not stat.S_ISREG(os.fstat(lock_descriptor).st_mode):
            raise RuntimeError("coset proof cache lock is not a regular file")
        locked = _deadline_lock(lock_descriptor, deadline=budget.deadline)
        if not locked:
            return None, {
                "attempts": 0,
                "budget_exhausted": True,
                "deferred": True,
                "cache_hit": False,
                "latest_outcome": None,
            }
        generations = _cache_generations(
            path,
            candidate_sha256=candidate_sha256,
            threshold=threshold,
            hx=row["hx"],
            hz=row["hz"],
        )
        committed_records = [
            (generation_path, envelope)
            for generation_path, envelope, is_committed in generations
            if is_committed
        ]
        selected_committed = (
            max(
                committed_records,
                key=lambda item: (
                    int(item[1]["attempts"]),
                    str(item[1]["cache_sha256"]),
                ),
            )
            if committed_records else None
        )
        cached = None if selected_committed is None else selected_committed[1]
        committed = cached is not None
        active_pending = next((
            envelope
            for _generation_path, envelope, is_committed in generations
            if not is_committed
            and _pending_writer_alive(envelope.get("last_attempt"))
        ), None)
        if (
            committed
            and cached is not None
            and cached["latest_outcome"] in {"SAT", "UNSAT"}
        ):
            return dict(cached["evidence"]), {
                "attempts": cached["attempts"],
                "budget_exhausted": False,
                "deferred": False,
                "cache_hit": True,
                "cache_sha256": cached["cache_sha256"],
                "last_attempt": dict(cached["last_attempt"]),
            }
        if (
            committed
            and cached is not None
            and time.time() < float(cached["retry_not_before_unix"])
        ) or active_pending is not None:
            return None, {
                "attempts": int(cached["attempts"]) if committed else 0,
                "budget_exhausted": False,
                "deferred": True,
                "cache_hit": False,
                "latest_outcome": (
                    active_pending["latest_outcome"]
                    if active_pending is not None
                    else cached["latest_outcome"]
                ),
            }
        attempts_before = int(cached["attempts"]) if committed and cached else 0
        strategy_id, timeout_cap = _attempt_timeout_strategy(attempts_before)
        timeout = budget.claim_timeout(requested_cap_s=timeout_cap)
        if timeout is None:
            return None, {
                "attempts": attempts_before,
                "budget_exhausted": True,
                "deferred": True,
                "cache_hit": False,
                "latest_outcome": (
                    None if cached is None else cached["latest_outcome"]
                ),
            }
        terminal_sectors = _terminal_sectors_from_cache(
            cached if committed else None
        )
        evidence, worker = _run_oracle_rung_hard_wall(
            row,
            threshold=threshold,
            timeout_s=timeout,
            terminal_sectors=terminal_sectors,
        )
        outcome = (
            evidence.get("outcome")
            if isinstance(evidence, Mapping)
            else "UNKNOWN"
        )
        last_attempt = {
            "outcome": outcome,
            "strategy_id": strategy_id,
            "timeout_s": float(timeout),
            "hard_wall_timeout": bool(worker["hard_wall_timeout"]),
            "worker_failed": bool(worker["worker_failed"]),
            "elapsed_s": float(worker["elapsed_s"]),
            "resumed_sectors": list(worker["resumed_sectors"]),
            "writer_process": _process_identity(),
            "evaluation_token": getattr(
                _PROOF_EVALUATION_LOCAL,
                "token",
                None,
            ),
        }
        attempts = attempts_before + 1
        envelope = _seal_cache_envelope(
            candidate_sha256=candidate_sha256,
            threshold=threshold,
            attempts=attempts,
            hx=row["hx"],
            hz=row["hz"],
            evidence=evidence,
            last_attempt=last_attempt,
        )
        generation_path = _proof_cache_version_path(
            path,
            str(envelope["cache_sha256"]),
        )
        _write_immutable_cache(generation_path, envelope)
        return evidence, {
            "attempts": attempts,
            "budget_exhausted": False,
            "deferred": False,
            "cache_hit": False,
            "cache_sha256": envelope["cache_sha256"],
            "last_attempt": dict(envelope["last_attempt"]),
        }
    finally:
        if locked:
            try:
                fcntl.flock(lock_descriptor, fcntl.LOCK_UN)
            except OSError:
                pass
        os.close(lock_descriptor)


def _apply_oracle_sat(
    row: dict[str, Any],
    evidence: Mapping[str, Any],
    *,
    cutoff: int,
) -> None:
    official_cutoff = _dynamic_rejection_cutoff(row["n"], row["k"])
    if cutoff != official_cutoff:
        raise RuntimeError("oracle rejection cutoff disagrees with final gate")
    witness = evidence.get("witness")
    witness_weight = (
        witness.get("weight") if isinstance(witness, Mapping) else None
    )
    if not isinstance(witness_weight, int):
        raise RuntimeError("replayed SAT evidence has no witness weight")
    rejected = witness_weight <= cutoff
    if not rejected:
        raise RuntimeError("ladder SAT witness exceeds its rejection cutoff")
    upper_fom = row["k"] * witness_weight * witness_weight / row["n"]
    row.update({
        "oracle_outcome": "SAT",
        "oracle_threshold": evidence["max_weight"],
        "low_weight_oracle": dict(evidence),
        "distance_lower_bound": None,
        "distance_lower_bound_evidence": None,
        "distance_lower_bound_evidence_sha256": None,
        "low_weight_witness": dict(witness),
        "threshold_rejected": True,
        "oracle_evidence_sha256": evidence.get("evidence_sha256"),
        "d": witness_weight,
        "d_is_exact": False,
        "distance_trusted": False,
        "distance_status": "upper_bound",
        "distance_upper_bound": witness_weight,
        "distance_upper_bound_source": "low_weight_oracle",
        "fom": upper_fom,
        "fom_upper_bound": upper_fom,
        "fitness_distance_credit": 0.0,
        "stage": "low_weight_oracle_rejected",
        "search_status": "terminal_negative",
        "distance_retry_required": False,
        "oracle_retryable": False,
        "oracle_ladder_complete": True,
        "oracle_ladder_next_threshold": None,
        "threshold_rejection_proven": True,
        "threshold_proof_source": "low_weight_oracle",
        "threshold_proof_distance": witness_weight,
        "threshold_proof_witness": dict(witness),
        **_cutoff_metadata(row["n"], row["k"]),
        "fom_target_excluded_by_upper_bound": True,
        "final_gate_excluded_by_upper_bound": True,
        "search_final_gate_excluded_by_upper_bound": True,
        "candidate_persistence_lane": "negative_search_feedback",
        "candidate_persistence_reason": "replayed_low_weight_logical_witness",
    })


def _apply_oracle_lower_bound(
    row: dict[str, Any],
    evidence: Mapping[str, Any],
    *,
    cutoff: int,
    complete: bool,
) -> None:
    official_cutoff = _dynamic_rejection_cutoff(row["n"], row["k"])
    if cutoff != official_cutoff:
        raise RuntimeError("oracle lower-bound cutoff disagrees with final gate")
    lower_bound = evidence.get("distance_lower_bound")
    threshold = evidence.get("max_weight")
    if (
        not isinstance(lower_bound, int)
        or not isinstance(threshold, int)
        or lower_bound != threshold + 1
    ):
        raise RuntimeError("UNSAT ladder evidence has no exact threshold bound")
    cutoff_metadata = _cutoff_metadata(row["n"], row["k"])
    scalar_cutoff = cutoff_metadata["fom_rejection_cutoff"]
    challenge_cutoff = cutoff_metadata["challenge_rejection_cutoff"]
    challenge_survivor = bool(
        complete
        and isinstance(challenge_cutoff, int)
        and lower_bound > challenge_cutoff
    )
    fom_survivor = bool(
        complete
        and isinstance(scalar_cutoff, int)
        and lower_bound > scalar_cutoff
    )
    row.update({
        "oracle_outcome": "UNSAT",
        "oracle_threshold": threshold,
        "low_weight_oracle": dict(evidence),
        "distance_lower_bound": lower_bound,
        "distance_lower_bound_evidence": dict(evidence),
        "distance_lower_bound_evidence_sha256": evidence.get(
            "evidence_sha256"
        ),
        "low_weight_witness": None,
        "threshold_rejected": False,
        "oracle_evidence_sha256": evidence.get("evidence_sha256"),
        "distance_lower_bound_proven": True,
        "distance_lower_bound_status": "search_oracle_proven",
        "fom_lower_bound": row["k"] * lower_bound * lower_bound / row["n"],
        "low_weight_oracle_threshold": threshold,
        "search_status": (
            "fom_threshold_survivor"
            if fom_survivor
            else "challenge_threshold_survivor"
            if challenge_survivor
            else "partial_lower_bound"
        ),
        "distance_retry_required": not complete,
        "oracle_retryable": not complete,
        "oracle_ladder_complete": complete,
        "oracle_ladder_next_threshold": None,
        **cutoff_metadata,
        "challenge_target_lower_bound_proven": challenge_survivor,
        "fom_target_lower_bound_proven": fom_survivor,
    })


def _run_oracle(
    row: dict[str, Any],
    *,
    budget: _OracleBatchBudget | None = None,
    max_new_steps: int | None = None,
) -> dict[str, int | bool]:
    """Hydrate committed rungs and climb continuously within a local quantum."""

    row.update({
        "oracle_outcome": "NOT_RUN",
        "oracle_threshold": None,
        "low_weight_oracle": None,
        "distance_lower_bound": None,
        "distance_lower_bound_evidence": None,
        "distance_lower_bound_evidence_sha256": None,
        "low_weight_witness": None,
        "threshold_rejected": False,
        "oracle_retryable": True,
        "oracle_ladder_schema_version": COSET_PROOF_LADDER_SCHEMA_VERSION,
        "oracle_ladder_history": [],
        "oracle_ladder_complete": False,
        "oracle_ladder_next_threshold": None,
        "oracle_batch_budget_exhausted": False,
        "oracle_last_attempt": None,
        "oracle_deferred": False,
        "challenge_target_lower_bound_proven": False,
        "fom_target_lower_bound_proven": False,
    })
    if not row["static_legal"] or row["k"] <= 0:
        row.update({
            "oracle_retryable": False,
            "distance_retry_required": False,
            "search_status": "invalid",
        })
        return {"new_steps": 0, "cache_hits": 0, "deferred": False}
    cutoff = _dynamic_rejection_cutoff(row["n"], row["k"])
    assert cutoff is not None
    ladder = _proof_ladder(cutoff)
    row.update({
        "oracle_ladder_cutoff": cutoff,
        "oracle_ladder_thresholds": list(ladder),
        **_cutoff_metadata(row["n"], row["k"]),
    })
    if not ladder:
        row.update({
            "distance_retry_required": True,
            "search_status": "unresolved",
        })
        return {"new_steps": 0, "cache_hits": 0, "deferred": False}
    if budget is None:
        budget = _OracleBatchBudget.production()
    if max_new_steps is None:
        max_new_steps = budget.remaining_new_steps
    if (
        isinstance(max_new_steps, bool)
        or not isinstance(max_new_steps, int)
        or max_new_steps < 0
    ):
        raise ValueError("max_new_steps must be a non-negative integer")

    history: list[dict[str, Any]] = []
    last_unsat: dict[str, Any] | None = None
    next_index = 0
    cache_hits = 0
    for index, threshold in enumerate(ladder):
        cached = _load_cached_evidence(
            row["candidate_sha256"],
            threshold,
            hx=row["hx"],
            hz=row["hz"],
        )
        if cached is None or cached["latest_outcome"] == "UNKNOWN":
            next_index = index
            break
        evidence = dict(cached["evidence"])
        cache_hits += 1
        history.append({
            "threshold": threshold,
            "outcome": evidence["outcome"],
            "attempts": cached["attempts"],
            "cache_hit": True,
            "evidence_sha256": evidence.get("evidence_sha256"),
            "attempt_sha256": cached["last_attempt"].get(
                "attempt_sha256"
            ),
            "cache_sha256": cached["cache_sha256"],
        })
        if evidence["outcome"] == "SAT":
            row["oracle_ladder_history"] = history
            _apply_oracle_sat(row, evidence, cutoff=cutoff)
            return {
                "new_steps": 0,
                "cache_hits": cache_hits,
                "deferred": False,
            }
        last_unsat = evidence
    else:
        next_index = len(ladder)

    if next_index >= len(ladder):
        if last_unsat is None:
            raise RuntimeError("completed proof ladder has no UNSAT evidence")
        row["oracle_ladder_history"] = history
        _apply_oracle_lower_bound(
            row,
            last_unsat,
            cutoff=cutoff,
            complete=True,
        )
        return {
            "new_steps": 0,
            "cache_hits": cache_hits,
            "deferred": False,
        }

    new_steps = 0
    while next_index < len(ladder) and new_steps < max_new_steps:
        threshold = ladder[next_index]
        evidence, attempt = _run_oracle_step(
            row,
            threshold=threshold,
            budget=budget,
        )
        if attempt.get("cache_hit"):
            if evidence is None:
                raise RuntimeError("terminal cache hit has no evidence")
            cache_hits += 1
        elif not attempt.get("deferred"):
            new_steps += 1
        if evidence is None:
            last_attempt = attempt.get("last_attempt")
            if (
                isinstance(last_attempt, Mapping)
                and isinstance(attempt.get("cache_sha256"), str)
            ):
                history.append({
                    "threshold": threshold,
                    "outcome": "UNKNOWN",
                    "attempts": attempt["attempts"],
                    "cache_hit": False,
                    "evidence_sha256": None,
                    "attempt_sha256": last_attempt.get("attempt_sha256"),
                    "cache_sha256": attempt["cache_sha256"],
                })
            row["oracle_ladder_history"] = history
            if last_unsat is not None:
                _apply_oracle_lower_bound(
                    row,
                    last_unsat,
                    cutoff=cutoff,
                    complete=False,
                )
            row.update({
                "oracle_outcome": (
                    "UNKNOWN"
                    if isinstance(last_attempt, Mapping)
                    else "NOT_RUN"
                ),
                "oracle_threshold": (
                    last_unsat.get("max_weight")
                    if last_unsat is not None else None
                ),
                "oracle_ladder_next_threshold": threshold,
                "oracle_batch_budget_exhausted": bool(
                    attempt.get("budget_exhausted")
                ),
                "oracle_retryable": True,
                "distance_retry_required": True,
                "search_status": (
                    "partial_lower_bound_retry"
                    if last_unsat is not None else "unresolved"
                ),
                "oracle_last_attempt": last_attempt,
                "oracle_last_attempt_outcome": (
                    None if last_attempt is None else last_attempt.get("outcome")
                ),
                "oracle_last_attempt_threshold": threshold,
                "oracle_deferred": bool(attempt.get("deferred")),
            })
            return {
                "new_steps": new_steps,
                "cache_hits": cache_hits,
                "deferred": bool(attempt.get("deferred")),
            }

        outcome = evidence["outcome"]
        last_attempt = attempt.get("last_attempt")
        history.append({
            "threshold": threshold,
            "outcome": outcome,
            "attempts": attempt["attempts"],
            "cache_hit": bool(attempt["cache_hit"]),
            "evidence_sha256": evidence.get("evidence_sha256"),
            "attempt_sha256": (
                None if last_attempt is None else last_attempt.get("attempt_sha256")
            ),
            "cache_sha256": attempt.get("cache_sha256"),
        })
        row["oracle_ladder_history"] = history
        row["oracle_last_attempt"] = last_attempt
        row["oracle_last_attempt_threshold"] = threshold
        if outcome == "SAT":
            _apply_oracle_sat(row, evidence, cutoff=cutoff)
            return {
                "new_steps": new_steps,
                "cache_hits": cache_hits,
                "deferred": False,
            }
        if outcome == "UNKNOWN":
            if last_unsat is not None:
                _apply_oracle_lower_bound(
                    row,
                    last_unsat,
                    cutoff=cutoff,
                    complete=False,
                )
                row["low_weight_oracle"] = dict(last_unsat)
                row["oracle_evidence_sha256"] = last_unsat.get(
                    "evidence_sha256"
                )
                row["oracle_threshold"] = last_unsat["max_weight"]
            else:
                row["low_weight_oracle"] = dict(evidence)
                row["oracle_evidence_sha256"] = evidence.get(
                    "evidence_sha256"
                )
                row["oracle_threshold"] = threshold
            row.update({
                "oracle_outcome": "UNKNOWN",
                "low_weight_witness": None,
                "threshold_rejected": False,
                "oracle_retryable": True,
                "distance_retry_required": True,
                "search_status": (
                    "partial_lower_bound_retry"
                    if last_unsat is not None else "unresolved"
                ),
                "oracle_ladder_next_threshold": threshold,
                "oracle_last_attempt": {
                    **dict(last_attempt or {}),
                    "evidence": dict(evidence),
                },
                "oracle_last_attempt_outcome": "UNKNOWN",
            })
            return {
                "new_steps": new_steps,
                "cache_hits": cache_hits,
                "deferred": False,
            }

        last_unsat = evidence
        next_index += 1
        complete = next_index == len(ladder)
        _apply_oracle_lower_bound(
            row,
            evidence,
            cutoff=cutoff,
            complete=complete,
        )
        if complete:
            return {
                "new_steps": new_steps,
                "cache_hits": cache_hits,
                "deferred": False,
            }
        row["oracle_ladder_next_threshold"] = ladder[next_index]

    row["oracle_ladder_history"] = history
    if last_unsat is not None:
        _apply_oracle_lower_bound(
            row,
            last_unsat,
            cutoff=cutoff,
            complete=False,
        )
    row.update({
        "oracle_ladder_next_threshold": ladder[next_index],
        "oracle_retryable": True,
        "distance_retry_required": True,
        "oracle_deferred": True,
        "search_status": (
            "partial_lower_bound_budget"
            if last_unsat is not None else "unresolved_budget"
        ),
    })
    return {
        "new_steps": new_steps,
        "cache_hits": cache_hits,
        "deferred": True,
    }


def _fitness(row: Mapping[str, Any]) -> float:
    """Score only exact/static facts and proof-safe distance evidence."""

    if (
        not row.get("static_legal")
        or row.get("k", 0) <= 0
        or row.get("threshold_rejected") is True
    ):
        return 0.0
    n = int(row["n"])
    k = int(row["k"])
    score = 0.10  # directly rebuilt static legality
    score += 0.25 * min(1.0, (k / n) / 0.25)  # exact rank-derived rate
    lower = row.get("distance_lower_bound")
    if isinstance(lower, int) and lower > 0:
        proven_fom = k * lower * lower / n
        score += 0.45 * min(1.0, proven_fom / TARGET_FOM)
    exact = row.get("exact_distance")
    if isinstance(exact, int) and exact > 0:
        exact_fom = k * exact * exact / n
        score += 0.20 * min(1.0, exact_fom / TARGET_FOM)
    return min(score, 1.0)


def _safe_json_row(row: Mapping[str, Any]) -> dict[str, Any]:
    record = {
        **dict(row["candidate"]),
        "construction": dict(row["construction"]),
        "candidate_sha256": row["candidate_sha256"],
        "n": row["n"],
        "k": row["k"],
        "rank_x": row["rank_x"],
        "rank_z": row["rank_z"],
        "css_commutation": row["css_commutation"],
        "max_check_weight": row["max_check_weight"],
        "max_qubit_degree": row["max_qubit_degree"],
        "tanner_components": row["tanner_components"],
        "static_legal": row["static_legal"],
        "subgroup_normal": row["subgroup_normal"],
        "support_orbit_bin": row["support_orbit_bin"],
        "low_weight_oracle_outcome": row.get("oracle_outcome", "NOT_RUN"),
        "low_weight_oracle_threshold": row.get("oracle_threshold"),
        "low_weight_oracle": row.get("low_weight_oracle"),
        "distance_lower_bound": row.get("distance_lower_bound"),
        "low_weight_witness": row.get("low_weight_witness"),
        "threshold_rejected": row.get("threshold_rejected", False),
        "fitness": row["fitness"],
        "distance_semantics": "proof-lower-bound-or-replayed-witness-only",
        "proof_ledger": _proof_ledger_for_row(row),
    }
    for field in (
        "d",
        "d_is_exact",
        "distance_trusted",
        "distance_status",
        "distance_upper_bound",
        "distance_upper_bound_source",
        "fom",
        "fom_upper_bound",
        "fitness_distance_credit",
        "distance_lower_bound_proven",
        "distance_lower_bound_status",
        "distance_lower_bound_evidence",
        "distance_lower_bound_evidence_sha256",
        "fom_lower_bound",
        "stage",
        "search_status",
        "distance_retry_required",
        "oracle_retryable",
        "oracle_evidence_sha256",
        "oracle_ladder_schema_version",
        "oracle_ladder_history",
        "oracle_ladder_cutoff",
        "oracle_ladder_thresholds",
        "oracle_ladder_complete",
        "oracle_ladder_next_threshold",
        "oracle_batch_budget_exhausted",
        "oracle_last_attempt_outcome",
        "oracle_last_attempt",
        "oracle_last_attempt_threshold",
        "oracle_deferred",
        "oracle_frontier_selected",
        "threshold_rejection_proven",
        "threshold_proof_source",
        "threshold_proof_distance",
        "threshold_proof_witness",
        "fom_rejection_cutoff",
        "challenge_rejection_cutoff",
        "minimum_winning_distance",
        "fom_target_excluded_by_upper_bound",
        "final_gate_excluded_by_upper_bound",
        "search_final_gate_excluded_by_upper_bound",
        "candidate_persistence_lane",
        "candidate_persistence_reason",
        "challenge_target_lower_bound_proven",
        "fom_target_lower_bound_proven",
    ):
        if field in row:
            record[field] = row[field]
    return record


def _append_candidate_rows(rows: list[dict[str, Any]]) -> int:
    raw_path = os.environ.get(CANDIDATE_LOG_PATH_ENV)
    if raw_path is None:
        return 0
    path = Path(raw_path).expanduser()
    if not path.is_absolute():
        raise RuntimeError("coset candidate log path must be absolute")
    path.parent.mkdir(parents=True, exist_ok=True)
    payload = bytearray()
    for row in rows:
        payload.extend(
            json.dumps(
                _safe_json_row(row),
                sort_keys=True,
                separators=(",", ":"),
                allow_nan=False,
            ).encode("utf-8")
        )
        payload.extend(b"\n")

    # Share the default evaluator's write-ahead log.  A process killed after a
    # partial os.write leaves a complete, fsynced intent that the next writer
    # finishes before appending, so no interior corrupt JSONL row can survive.
    from evolve.openevolve_evaluator import _append_candidate_jsonl

    committed_range = _append_candidate_jsonl(path, payload)
    if not isinstance(committed_range, Mapping):
        raise RuntimeError("candidate JSONL append did not return a range identity")
    _commit_cache_entries(rows, committed_range)
    return len(rows)


def _fixed_categorical_entropy(
    values: list[Any],
    *,
    category_count: int,
) -> float:
    """Entropy against an immutable category space, never the sample size."""

    if (
        isinstance(category_count, bool)
        or not isinstance(category_count, int)
        or category_count < 2
    ):
        raise ValueError("category_count must be an integer of at least two")
    if not values:
        return 0.0
    counts = Counter(values)
    if len(counts) > category_count:
        raise RuntimeError("observed more structural categories than the contract")
    value = -sum(
        (count / len(values)) * math.log(count / len(values))
        for count in counts.values()
    )
    return value / math.log(category_count)


def _structural_diversity(rows: list[Mapping[str, Any]]) -> float:
    """Score pre-oracle viable coverage without rewarding survivor collapse."""

    if not rows:
        return 0.0
    action_count = len(action_search_views())
    action_diversity = _fixed_categorical_entropy(
        [row["action_id"] for row in rows],
        category_count=action_count,
    )
    normality_diversity = _fixed_categorical_entropy(
        [row["subgroup_normal"] for row in rows],
        category_count=2,
    )
    orbit_diversity = _fixed_categorical_entropy(
        [row["support_orbit_bin"] for row in rows],
        category_count=COSET_SUPPORT_ORBIT_BINS,
    )
    # A tiny statically viable subset must not receive the same diversity
    # credit as a full production batch with the same proportions.
    coverage = min(1.0, len(rows) / MAX_GENERATED_CANDIDATES)
    return coverage * (
        action_diversity + normality_diversity + orbit_diversity
    ) / 3


def _validate_production_candidate_batch(
    candidates: list[Mapping[str, Any]],
) -> None:
    """Reassert the renderer's immutable 384-row lane contract."""

    if len(candidates) != MAX_GENERATED_CANDIDATES:
        raise RuntimeError(
            "trusted coset renderer did not emit the exact production batch"
        )
    views = action_search_views()
    expected = quota_by_normality(views, MAX_GENERATED_CANDIDATES)
    observed = Counter(
        candidate.get("action_id")
        if isinstance(candidate, Mapping)
        else None
        for candidate in candidates
    )
    if observed != Counter(expected):
        raise RuntimeError(
            "trusted coset renderer violated immutable action quotas"
        )


def _preflight_markers(
    *,
    evaluated: int,
    eligible: int,
    persisted: int,
    action_strata: int,
):
    contract_raw = os.environ.get(PREFLIGHT_CONTRACT_ID_ENV, "0")
    try:
        contract_id = int(contract_raw)
    except ValueError as exc:
        raise RuntimeError("invalid coset preflight contract ID") from exc
    if contract_id < 0:
        raise RuntimeError("invalid coset preflight contract ID")
    expected_strata = len(action_search_views())
    if action_strata != expected_strata:
        raise RuntimeError(
            "coset preflight did not evaluate every enabled action stratum"
        )
    return {
        "winner_preflight_contract_version": float(PREFLIGHT_CONTRACT_VERSION),
        "winner_preflight_contract_id": float(contract_id),
        "winner_preflight_complete": 1.0,
        "winner_preflight_incomplete": 0.0,
        PREFLIGHT_UNIT_KIND_ID_METRIC: PREFLIGHT_UNIT_KIND_ID,
        PREFLIGHT_UNITS_METRIC: float(action_strata),
        PREFLIGHT_ACTION_STRATA_METRIC: float(action_strata),
        "winner_preflight_candidate_definitions_evaluated": float(evaluated),
        "winner_preflight_winner_capable_eligible": float(eligible),
        "winner_preflight_winner_capable_persisted": float(persisted),
        "winner_preflight_winner_capable_omitted": 0.0,
        "winner_preflight_hard_timeout": 0.0,
        "winner_preflight_subprocess_failed": 0.0,
    }


def _preflight_contract_id() -> int:
    raw = os.environ.get(PREFLIGHT_CONTRACT_ID_ENV, "0")
    try:
        value = int(raw)
    except ValueError as exc:
        raise RuntimeError("invalid coset preflight contract ID") from exc
    if value < 0:
        raise RuntimeError("invalid coset preflight contract ID")
    return value


def _invalid_mutation_result(exc: InvalidCosetMutation):
    """Return the exact managed envelope that becomes one worker_error."""

    reason = getattr(exc, "reason_code", None)
    program_sha256 = getattr(exc, "program_sha256", None)
    program_bytes = getattr(exc, "program_bytes", None)
    detail_sha256 = getattr(exc, "detail_sha256", None)
    error_type = getattr(exc, "error_type", None)
    program_sha256_valid = (
        isinstance(program_sha256, str)
        and len(program_sha256) == 64
    ) or (
        program_sha256 is None
        and reason == "source_too_large"
    )
    if (
        not isinstance(reason, str)
        or not reason
        or not program_sha256_valid
        or isinstance(program_bytes, bool)
        or not isinstance(program_bytes, int)
        or program_bytes < 0
        or not isinstance(detail_sha256, str)
        or len(detail_sha256) != 64
        or not isinstance(error_type, str)
        or not error_type
    ):
        raise CosetMutationRuntimeError(
            "invalid mutation preflight returned malformed failure metadata"
        )
    safe_error = json.dumps(
        {
            "detail_sha256": detail_sha256,
            "error_type": error_type,
            "kind": "qcode-coset-invalid-mutation",
            "program_bytes": program_bytes,
            "program_sha256": program_sha256,
            "reason": reason,
        },
        sort_keys=True,
        separators=(",", ":"),
        allow_nan=False,
    )
    zero_fields = {
        "combined_score": 0.0,
        "lattices_with_high_k": 0.0,
        "map_descriptor_dominant_pattern_share": 0.0,
        "map_descriptor_pool_size": 0.0,
        "support_split_type": 0.0,
        "search_structural_entropy": 0.0,
        "algebraic_relation_type": 0.0,
        "orbit_span_bin": 0.0,
        "difference_spectrum_bin": 0.0,
        MAP_DESCRIPTOR_VERSION_METRIC: float(MAP_DESCRIPTOR_VERSION),
        "num_high_k": 0.0,
        "term_count": 0.0,
        "pattern_type": 0.0,
        COSET_PROOF_LADDER_VERSION_METRIC: float(
            COSET_PROOF_LADDER_SCHEMA_VERSION
        ),
    }
    metrics = {
        **zero_fields,
        "error": safe_error,
        "winner_preflight_contract_version": float(
            PREFLIGHT_CONTRACT_VERSION
        ),
        "winner_preflight_contract_id": float(_preflight_contract_id()),
        "winner_preflight_complete": 0.0,
        "winner_preflight_incomplete": 1.0,
        PREFLIGHT_UNIT_KIND_ID_METRIC: PREFLIGHT_UNIT_KIND_ID,
        PREFLIGHT_UNITS_METRIC: 0.0,
        PREFLIGHT_ACTION_STRATA_METRIC: 0.0,
        "winner_preflight_candidate_definitions_evaluated": 0.0,
        "winner_preflight_winner_capable_eligible": 0.0,
        "winner_preflight_winner_capable_persisted": 0.0,
        "winner_preflight_winner_capable_omitted": 0.0,
        "winner_preflight_hard_timeout": 0.0,
        "winner_preflight_subprocess_failed": 1.0,
    }
    artifacts = {
        "failure_stage": "mutation_preflight",
        "invalid_mutation": {
            "reason": reason,
            "program_sha256": program_sha256,
            "program_bytes": program_bytes,
            "detail_sha256": detail_sha256,
            "error_type": error_type,
        },
    }
    try:
        from openevolve.evaluation_result import EvaluationResult

        return EvaluationResult(metrics=metrics, artifacts=artifacts)
    except ImportError:
        return metrics


def _runtime_failure_result(exc: CosetMutationRuntimeError):
    """Emit a deliberately non-checkpointable envelope for trusted failures."""

    detail = hashlib.sha256(
        f"{type(exc).__name__}:{exc}".encode("utf-8", errors="replace")
    ).hexdigest()
    metrics = {
        "combined_score": 0.0,
        MAP_DESCRIPTOR_VERSION_METRIC: float(MAP_DESCRIPTOR_VERSION),
        EVALUATOR_KIND_ID_METRIC: EVALUATOR_KIND_ID,
        ACTION_CATALOG_ID_METRIC: _action_catalog_contract_id(),
        COSET_PROOF_LADDER_VERSION_METRIC: float(
            COSET_PROOF_LADDER_SCHEMA_VERSION
        ),
        "qcode_mutation_preflight_runtime_failure": 1.0,
    }
    artifacts = {
        "failure_stage": "mutation_preflight_runtime",
        "runtime_failure_sha256": detail,
    }
    try:
        from openevolve.evaluation_result import EvaluationResult

        return EvaluationResult(metrics=metrics, artifacts=artifacts)
    except ImportError:
        return metrics


def _run_proof_frontier_and_persist(
    rows: list[dict[str, Any]],
    oracle_order: list[dict[str, Any]],
) -> tuple[int, list[dict[str, int | bool]]]:
    """Execute one lease-bound proof frontier and durably commit its rows."""

    with _proof_evaluation_lease():
        for row in rows:
            row.update({
                "oracle_outcome": "NOT_RUN",
                "oracle_threshold": None,
                "low_weight_oracle": None,
                "distance_lower_bound": None,
                "low_weight_witness": None,
                "threshold_rejected": False,
                "oracle_retryable": True,
                "oracle_ladder_schema_version": (
                    COSET_PROOF_LADDER_SCHEMA_VERSION
                ),
                "oracle_ladder_history": [],
                "oracle_ladder_complete": False,
                "oracle_ladder_next_threshold": None,
                "oracle_batch_budget_exhausted": False,
                "distance_retry_required": True,
                "search_status": "unresolved",
            })
        oracle_budget = _OracleBatchBudget.production()
        hydration_budget = _OracleBatchBudget(
            remaining_new_steps=0,
            deadline=oracle_budget.deadline,
        )
        for row in oracle_order:
            _run_oracle(row, budget=hydration_budget, max_new_steps=0)

        frontier: list[dict[str, Any]] = []
        for normal in (False, True):
            candidate = next((
                row for row in oracle_order
                if row["subgroup_normal"] is normal
                and row.get("oracle_retryable") is True
                and row.get("threshold_rejected") is not True
                and row.get("oracle_ladder_complete") is not True
            ), None)
            if candidate is not None:
                frontier.append(candidate)
        frontier_digests = {row["candidate_sha256"] for row in frontier}
        for row in oracle_order:
            if len(frontier) >= _ORACLE_FRONTIER_WIDTH:
                break
            if (
                row["candidate_sha256"] not in frontier_digests
                and row.get("oracle_retryable") is True
                and row.get("threshold_rejected") is not True
                and row.get("oracle_ladder_complete") is not True
            ):
                frontier.append(row)
                frontier_digests.add(row["candidate_sha256"])
        remaining = [
            row for row in oracle_order
            if row["candidate_sha256"] not in frontier_digests
        ]
        frontier_quantum = math.ceil(
            COSET_PROOF_MAX_NEW_STEPS_PER_BATCH / _ORACLE_FRONTIER_WIDTH
        )
        oracle_run_stats: list[dict[str, int | bool]] = []
        for row in [*frontier, *remaining]:
            if (
                oracle_budget.remaining_new_steps <= 0
                or oracle_budget.remaining_wall() <= 0
            ):
                break
            if (
                row.get("oracle_retryable") is not True
                or row.get("threshold_rejected") is True
                or row.get("oracle_ladder_complete") is True
            ):
                continue
            row["oracle_frontier_selected"] = True
            oracle_run_stats.append(_run_oracle(
                row,
                budget=oracle_budget,
                max_new_steps=min(
                    frontier_quantum,
                    oracle_budget.remaining_new_steps,
                ),
            ))
        for row in oracle_order:
            row.setdefault("oracle_frontier_selected", False)
        for row in rows:
            row["fitness"] = _fitness(row)
        persistable = [
            row for row in rows if row["static_legal"] and row["k"] > 0
        ]
        persisted = _append_candidate_rows(persistable)
        return persisted, oracle_run_stats


def _evaluate(program_path: str):
    started = time.monotonic()
    try:
        preflight, source_path = _preflight_program(program_path)
    except InvalidCosetMutation as exc:
        return _invalid_mutation_result(exc)
    except CosetMutationRuntimeError as exc:
        return _runtime_failure_result(exc)
    program_sha256 = preflight.program_sha256
    raw = list(preflight.candidates)
    _validate_production_candidate_batch(raw)
    normalized = []
    seen = set()
    invalid = 0
    for candidate in raw:
        try:
            item = normalize_candidate(candidate)
            digest = candidate_digest(item)
        except (TypeError, ValueError):
            invalid += 1
            continue
        if digest in seen:
            continue
        seen.add(digest)
        normalized.append(item)
    if invalid or len(normalized) != len(raw):
        raise RuntimeError(
            "trusted coset renderer produced invalid or duplicate candidates"
        )
    expected_action_ids = {
        view.action_id for view in action_search_views()
    }
    observed_action_ids = {
        item["action_id"] for item in normalized
    }
    if observed_action_ids != expected_action_ids:
        raise ValueError(
            "generate_candidates() must cover every search-enabled action"
        )
    # Descriptor coordinates are sealed before any candidate build or oracle
    # work.  They therefore describe the typed policy's immutable renderer
    # output and cannot drift because of a timeout or solver outcome.
    map_descriptor = coset_batch_map_descriptor(
        normalized,
        policy_sha256=preflight.policy_sha256,
    )
    rows = []
    build_errors = 0
    for candidate in normalized:
        try:
            rows.append(_static_candidate(candidate))
        except Exception:
            build_errors += 1
    built_action_ids = {row["action_id"] for row in rows}
    if built_action_ids != expected_action_ids:
        missing = sorted(expected_action_ids - built_action_ids)
        raise RuntimeError(
            "coset evaluator failed to build every enabled action stratum: "
            f"missing={missing}"
        )
    oracle_order = _oracle_probe_rows(
        rows,
        selection_salt=preflight.policy_sha256,
    )
    persisted, oracle_run_stats = _run_proof_frontier_and_persist(
        rows,
        oracle_order,
    )

    eligible_rows = [
        row for row in rows
        if row["static_legal"] and row["k"] > 0 and not row["threshold_rejected"]
    ]
    # Preserve terminal SAT witnesses in the transaction-bound candidate
    # stream so Humanize can replay concrete failure geometry.  These rows are
    # a negative-only advisory lane and do not count as winner-capable
    # preflight persistence or positive fitness.
    persistable_rows = [
        row for row in rows if row["static_legal"] and row["k"] > 0
    ]
    if persisted != len(persistable_rows) and os.environ.get(CANDIDATE_LOG_PATH_ENV):
        raise RuntimeError("coset candidate persistence count is incomplete")
    winner_capable_persisted = (
        len(eligible_rows)
        if os.environ.get(CANDIDATE_LOG_PATH_ENV)
        and persisted == len(persistable_rows)
        else 0
    )

    # Structural diversity is measured before the negative-only oracle lane.
    # Otherwise rejecting most candidates can perversely increase the score.
    diversity = _structural_diversity(persistable_rows)
    best = max(eligible_rows, key=lambda row: row["fitness"], default=None)
    best_fitness = 0.0 if best is None else float(best["fitness"])
    combined_score = min(0.999, 0.8 * best_fitness + 0.199 * diversity)
    metrics = {
        "combined_score": combined_score,
        "exact_k_best": float(0 if best is None else best["k"]),
        "static_legal_candidates": float(sum(row["static_legal"] for row in rows)),
        "unique_candidate_definitions": float(len(normalized)),
        "invalid_candidate_definitions": float(invalid),
        "build_errors": float(build_errors),
        "low_weight_rejections": float(sum(row["threshold_rejected"] for row in rows)),
        "candidate_log_records_persisted": float(persisted),
        "proven_lower_bound_candidates": float(sum(
            isinstance(row.get("distance_lower_bound"), int) for row in rows
        )),
        "proof_ladder_new_steps": float(sum(
            int(statistic["new_steps"]) for statistic in oracle_run_stats
        )),
        "proof_ladder_cache_hits": float(sum(
            sum(
                bool(step.get("cache_hit", False))
                for step in row.get("oracle_ladder_history", [])
            )
            for row in oracle_order
        )),
        "proof_ladder_unknown": float(sum(
            row.get("oracle_outcome") == "UNKNOWN" for row in oracle_order
        )),
        "proof_ladder_complete": float(sum(
            row.get("oracle_ladder_complete") is True for row in oracle_order
        )),
        "proof_ladder_survivors": float(sum(
            row.get("challenge_target_lower_bound_proven") is True
            for row in oracle_order
        )),
        "proof_ladder_fom_survivors": float(sum(
            row.get("fom_target_lower_bound_proven") is True
            for row in oracle_order
        )),
        "proof_ladder_retryable": float(sum(
            row.get("oracle_retryable") is True for row in oracle_order
        )),
        "proof_ladder_deferred": float(sum(
            row.get("oracle_deferred") is True for row in oracle_order
        )),
        "proof_ladder_frontier_rows": float(sum(
            row.get("oracle_frontier_selected") is True for row in oracle_order
        )),
        "proof_ladder_hard_wall_timeouts": float(sum(
            isinstance(row.get("oracle_last_attempt"), Mapping)
            and row["oracle_last_attempt"].get("hard_wall_timeout") is True
            for row in oracle_order
        )),
        "proof_ladder_batch_budget_exhausted": float(any(
            row.get("oracle_batch_budget_exhausted") is True
            for row in oracle_order
        )),
        "action_coverage": float(len({row["action_id"] for row in rows})),
        "normality_coverage": float(len({row["subgroup_normal"] for row in rows})),
        "search_diversity": diversity,
        MAP_DESCRIPTOR_VERSION_METRIC: float(MAP_DESCRIPTOR_VERSION),
        COSET_MAP_SCHEMA_METRIC: float(COSET_MAP_SCHEMA_VERSION),
        EVALUATOR_KIND_ID_METRIC: EVALUATOR_KIND_ID,
        ACTION_CATALOG_ID_METRIC: _action_catalog_contract_id(),
        COSET_GENOME_FORMAT_ID_METRIC: COSET_TYPED_DSL_GENOME_FORMAT_ID,
        COSET_PROOF_LADDER_VERSION_METRIC: float(
            COSET_PROOF_LADDER_SCHEMA_VERSION
        ),
        COSET_NONNORMAL_LANE_METRIC: float(
            map_descriptor["coordinates"][COSET_NONNORMAL_LANE_METRIC]
        ),
        COSET_NORMAL_LANE_METRIC: float(
            map_descriptor["coordinates"][COSET_NORMAL_LANE_METRIC]
        ),
        COSET_BATCH_ORBIT_PROFILE_METRIC: float(
            map_descriptor["coordinates"][COSET_BATCH_ORBIT_PROFILE_METRIC]
        ),
        "evaluation_elapsed_s": time.monotonic() - started,
        **_preflight_markers(
            evaluated=len(normalized),
            eligible=len(eligible_rows),
            persisted=winner_capable_persisted,
            action_strata=len(built_action_ids),
        ),
    }
    oracle_failure_lines = []
    for row in sorted(
        (item for item in rows if item["threshold_rejected"]),
        key=lambda item: item["candidate_sha256"],
    )[:8]:
        witness = row.get("low_weight_witness")
        if not isinstance(witness, Mapping):
            continue
        oracle_failure_lines.append(
            "  action={action} side={side} weight={weight} support={support} "
            "left_support={left} right_support={right}".format(
                action=row["action_id"],
                side=witness.get("side"),
                weight=witness.get("weight"),
                support=witness.get("support"),
                left=row["candidate"]["left_support"],
                right=row["candidate"]["right_support"],
            )
        )
    artifacts = {
        "representation": "coset-two-block",
        "evaluator_kind": COSET_EVALUATOR_KIND,
        "program_path": str(source_path),
        "program_sha256": program_sha256,
        "policy_sha256": preflight.policy_sha256,
        "map_descriptor": map_descriptor,
        "mutation_preflight_elapsed_s": preflight.elapsed_s,
        "distance_semantics": {
            "bp_upper_bound_positive_credit": False,
            "positive_distance_sources": [
                "replayed two-sector UNSAT lower bound",
                "independently replayed exact distance",
            ],
        },
        "best_candidates": [
            _safe_json_row(row)
            for row in sorted(
                eligible_rows,
                key=lambda item: (-item["fitness"], item["candidate_sha256"]),
            )[:12]
        ],
    }
    if oracle_failure_lines:
        artifacts["low_weight_oracle_failures"] = "\n".join([
            "Replayed short logical operators are negative-only evidence. "
            "Mutate the implicated action/orbit/support mechanism:",
            *oracle_failure_lines,
        ])
    try:
        from openevolve.evaluation_result import EvaluationResult

        return EvaluationResult(metrics=metrics, artifacts=artifacts)
    except ImportError:
        return metrics


def evaluate_stage1(program_path: str):
    return _evaluate(program_path)


def evaluate_stage2(program_path: str):
    # Stage 1 intentionally owns the only search signal for this new family.
    # The campaign config keeps the cascade threshold above every possible
    # score, so reaching this function is a configuration error.
    raise RuntimeError("coset Stage-2 cascade is disabled; use the five-stage pool")


def evaluate(program_path: str):
    return evaluate_stage1(program_path)


def _write_preflight_worker_result(
    result_path: str,
    metrics: dict[str, Any],
    artifacts: dict[str, Any],
) -> None:
    payload = {
        "schema_version": 1,
        "status": "completed",
        "metrics": metrics,
        "artifacts": artifacts,
    }
    destination = Path(result_path)
    if destination.is_symlink() or destination.exists():
        raise FileExistsError(
            f"refusing to overwrite coset preflight result: {destination}"
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
                raise OSError("coset preflight result write made no progress")
            written += count
        os.fsync(descriptor)
    finally:
        os.close(descriptor)
    os.replace(temporary, destination)


def _preflight_worker_main(program_path: str, result_path: str) -> int:
    result = _evaluate(program_path)
    metrics = getattr(result, "metrics", result)
    artifacts = getattr(result, "artifacts", {})
    if not isinstance(metrics, dict) or not isinstance(artifacts, dict):
        raise TypeError("coset preflight worker returned an invalid result")
    _write_preflight_worker_result(result_path, metrics, artifacts)
    return 0


def _arm_parent_lifecycle(expected_parent_pid: str, lifecycle_fd: str) -> None:
    try:
        parent_pid = int(expected_parent_pid)
        descriptor = int(lifecycle_fd)
    except ValueError as exc:
        raise RuntimeError("coset preflight lifecycle arguments are invalid") from exc
    if parent_pid < 1 or descriptor < 0:
        raise RuntimeError("coset preflight lifecycle binding is invalid")
    if sys.platform.startswith("linux"):
        libc = ctypes.CDLL(None, use_errno=True)
        if libc.prctl(1, signal.SIGKILL, 0, 0, 0) != 0:
            error = ctypes.get_errno()
            raise OSError(error, "cannot arm coset preflight parent-death signal")
    if os.getppid() != parent_pid:
        raise RuntimeError("coset preflight parent changed before lifecycle arm")

    def monitor() -> None:
        try:
            while True:
                try:
                    payload = os.read(descriptor, 1)
                except InterruptedError:
                    continue
                if payload:
                    continue
                os.kill(os.getpid(), signal.SIGKILL)
        finally:
            try:
                os.close(descriptor)
            except OSError:
                pass

    threading.Thread(
        target=monitor,
        name="coset-preflight-lifecycle",
        daemon=True,
    ).start()


__all__ = [
    "evaluate",
    "evaluate_stage1",
    "evaluate_stage2",
]


if __name__ == "__main__":
    if len(sys.argv) == 2 and sys.argv[1] == "--oracle-rung-worker":
        raise SystemExit(_oracle_rung_worker_main())
    if len(sys.argv) != 6 or sys.argv[1] != "--preflight-worker":
        raise SystemExit(
            "usage: coset_openevolve_evaluator.py "
            "(--oracle-rung-worker | --preflight-worker PROGRAM_PATH "
            "RESULT_PATH EXPECTED_PARENT_PID LIFECYCLE_FD)"
        )
    _arm_parent_lifecycle(sys.argv[4], sys.argv[5])
    raise SystemExit(_preflight_worker_main(sys.argv[2], sys.argv[3]))
