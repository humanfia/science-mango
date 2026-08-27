#!/usr/bin/env python3
"""Final source-bound max-18 SAT lane for the paper Dic5 quotient code.

The paper's value 22 is an upper bound only.  This runner independently
rebuilds the matrices and queries one complete symmetry-normalized Z sector:
logical syndrome bit zero is fixed to one (partition_index=0), with no qubit
anchors.  The existing public production SAT API cannot inject extra clauses,
so the actual solver instance is the frozen plain CNF.  A separately verified
5000-clause coset-minimal enhancement is recorded only as a disabled optional
plan.

A SAT result rejects only after official matrix-level witness replay.  One
strict Z-sector UNSAT decision, combined with the even-parity, logical
symmetry, and X/Z-isometry certificates, establishes d >= 20.  UNKNOWN,
INFEASIBLE, malformed, or unverifiable results remain UNRESOLVED.
"""

from __future__ import annotations

import argparse
import hashlib
import importlib.metadata
import importlib.util
import json
import math
import os
import sys
import time
from dataclasses import dataclass
from itertools import combinations, product
from pathlib import Path
from typing import Any, Callable, Mapping, Sequence


THREAD_ENV = (
    "OMP_NUM_THREADS",
    "OMP_THREAD_LIMIT",
    "OPENBLAS_NUM_THREADS",
    "MKL_NUM_THREADS",
    "NUMEXPR_NUM_THREADS",
    "VECLIB_MAXIMUM_THREADS",
    "BLIS_NUM_THREADS",
    "NUMBA_NUM_THREADS",
    "GOTO_NUM_THREADS",
)
for _environment_name in THREAD_ENV:
    os.environ[_environment_name] = "1"

import numpy as np  # noqa: E402
from qldpc import codes  # noqa: E402


PROJECT = Path(__file__).resolve().parent.parent
sys.path.insert(0, str(PROJECT))

from evaluation.admissibility_policy import (  # noqa: E402
    require_css_w6_admissibility,
)
from evaluation.css_logical_detector import (  # noqa: E402
    verify_css_logical_detectors,
)
from evaluation.distance_milp import get_code_matrices  # noqa: E402
from evaluation.distance_sat import (  # noqa: E402
    SAT_EVIDENCE_KIND,
    SAT_EVIDENCE_SCHEMA_VERSION,
    SAT_FORMULATION,
    SAT_NATIVE_THREAD_ENV,
    build_css_threshold_cnf,
    solve_css_sector_sat,
    verify_css_threshold_sat_witness,
)
from evaluation.strict_fom1525_policy import (  # noqa: E402
    TARGET_MODE,
    build_target_binding,
    classify_target,
    validate_target_binding,
)
from evaluation.tanner_equivalence import canonical_hash  # noqa: E402
from evaluation.paper400_dic5_xz_isometry import (  # noqa: E402
    verify_paper400_dic5_xz_isometry,
)
from evaluation.paper400_dic5_logical_symmetry import (  # noqa: E402
    verify_paper400_dic5_logical_symmetry,
)


SCHEMA_VERSION = 1
GATE = "qcode-paper400-dic5-w6-lower-final-v5"
SECTOR_ORDER = ("Z",)
PARTITION_INDEX = 0
ANCHOR_INDICES: tuple[int, ...] = ()
TARGET_REQUIRED_DISTANCE = 20
TARGET_REJECTION_CUTOFF = 19
SOLVER_MAX_WEIGHT = 18
SOLVER = "cadical195"
CARDINALITY_ENCODING = "kmtotalizer"
DEFAULT_TIMEOUT_PER_SECTOR_S = 43200.0

EXPECTED_MATRIX_SHA256 = {
    "H_X": "80a86c5d5d68c52bca21cc67074dc0f6766e3cf1832959e9b78be35228cd97c2",
    "H_Z": "d2224a102f1b96e9215280f32fc550467f7ea92ecb3b9c8633fc5269b9e8a7f3",
}
EXPECTED_TANNER_CANONICAL_DIGEST = (
    "b6902be992cb72bb0039d479e78ab9c36b1e539f7960077ab90688ed116d9594"
)
EXPECTED_TARGET_BINDING_SHA256 = (
    "b1897f46e4237026c2f0cb7e375c16b5b825fe163ba114cf40449ef809ecf831"
)
EXPECTED_W6_REPORT_SHA256 = (
    "964db9f3a97130e2792eab4716bb8e043928ce306e4ddc1c2fe1fbcfcb88596e"
)
EXPECTED_LOGICAL_DETECTOR_SHA256 = (
    "dc1ec4a2dbc28ca8c12e869bb0e3a0dd829bb9aff93b1f999b75f16be50e0f95"
)
EXPECTED_XZ_ISOMETRY_REPORT_SHA256 = (
    "962efea74604ef1f4444d4fbcceecfd84018ffac06710f6e26529e7f550708a9"
)
EXPECTED_LOGICAL_SYMMETRY_REPORT_SHA256 = (
    "5d5af0e1a1974fa4161074c11427dfec9cc6bbf9a36c29fcbda2e9b94216825a"
)
EXPECTED_LOGICAL_MATRIX_SHA256 = {
    "L_X": "ae5dbf5b0e50f80ff9f09a845f0eb2cbac6f98979eeb44b71d05a27433bfcd49",
    "L_Z": "4f2e07b817ec93436d98ff3ceac96359d4221c4774a71c3c6fe19dd1fe7e3f2e",
}
EXPECTED_CNF = {
    "Z": {
        "cnf_sha256": "2f6aad2bb19fef0563ebec15372a74000a48ff252194208c412734e449c417ac",
        "num_variables": 4428,
        "num_clauses": 14922,
    },
}
EXPECTED_OPTIONAL_COSET_EXTRA_SHA256 = (
    "96643ea8615f8a98d4b8a57655cf5181049a4746988cb4f7643f344d9eba0404"
)
EXPECTED_OPTIONAL_COSET_ENHANCED_CNF_SHA256 = (
    "ba0203cd6c970af2dce9ff876053e19776d28873c5fbcbb7a3361944d989718c"
)

SOURCE_RECORD = {
    "schema_version": 1,
    "authority": "arXiv:2608.08996v1 supplementary construction",
    "url": "https://arxiv.org/html/2608.08996v1",
    "group": "Dic5 x Dic5",
    "relations": ["r^10=e", "s^2=r^5", "srs^-1=r^-1"],
    "quotient": "K=<r1^5 r2^5>",
    "A": ["s1 r2 s2", "r1^9 r2^2 s2", "r1^2 s1 r2^3 s2"],
    "B": ["r1^8", "r1^2 r2", "r2 s2"],
    "reported_code": "[[400,16,<=22]],w=6",
    "distance_semantics": "22 is a QDistEvol upper bound, never lower or exact authority",
}

SOURCE_PATHS = {
    "evaluation/admissibility_policy.py": PROJECT / "evaluation/admissibility_policy.py",
    "evaluation/css_logical_detector.py": PROJECT / "evaluation/css_logical_detector.py",
    "evaluation/distance_milp.py": PROJECT / "evaluation/distance_milp.py",
    "evaluation/distance_sat.py": PROJECT / "evaluation/distance_sat.py",
    "evaluation/paper400_dic5_xz_isometry.py": (
        PROJECT / "evaluation/paper400_dic5_xz_isometry.py"
    ),
    "evaluation/paper400_dic5_logical_symmetry/__init__.py": (
        PROJECT / "evaluation/paper400_dic5_logical_symmetry/__init__.py"
    ),
    "evaluation/paper400_dic5_logical_symmetry_final.py": (
        PROJECT / "evaluation/paper400_dic5_logical_symmetry_final.py"
    ),
    "evaluation/strict_fom1525_policy.py": PROJECT / "evaluation/strict_fom1525_policy.py",
    "evaluation/tanner_equivalence.py": PROJECT / "evaluation/tanner_equivalence.py",
    "scripts/run_paper400_dic5_w6_lower_final_v5.py": Path(__file__).resolve(),
}

GroupElement = tuple[int, int, int, int]
SolverCallback = Callable[..., Mapping[str, Any]]


class Paper400ValidationError(RuntimeError):
    """The frozen construction, source, result, or execution contract failed."""


@dataclass(frozen=True)
class SectorSpec:
    sector: str
    checks: np.ndarray
    logicals: np.ndarray
    cnf: dict[str, Any]


@dataclass(frozen=True)
class PreparedInstance:
    hx: np.ndarray
    hz: np.ndarray
    lx: np.ndarray
    lz: np.ndarray
    sectors: tuple[SectorSpec, ...]
    report: dict[str, Any]


def _canonical_bytes(value: Any) -> bytes:
    return json.dumps(
        value,
        sort_keys=True,
        separators=(",", ":"),
        ensure_ascii=False,
        allow_nan=False,
    ).encode()


def _canonical_sha256(value: Any) -> str:
    return hashlib.sha256(_canonical_bytes(value)).hexdigest()


def _seal(value: Mapping[str, Any], field: str) -> dict[str, Any]:
    result = dict(value)
    result.pop(field, None)
    result[field] = _canonical_sha256(result)
    return result


def _file_sha256(path: Path) -> str:
    if not path.is_file() or path.is_symlink():
        raise Paper400ValidationError(f"source is not a regular file: {path}")
    return hashlib.sha256(path.read_bytes()).hexdigest()


def source_bundle() -> dict[str, Any]:
    files = {name: _file_sha256(path) for name, path in SOURCE_PATHS.items()}
    runtime: dict[str, Any] = {
        "python": list(sys.version_info[:3]),
        "executable_realpath": str(Path(sys.executable).resolve()),
        "packages": {},
    }
    for distribution in ("numpy", "qldpc", "python-sat", "python-igraph"):
        try:
            version = importlib.metadata.version(distribution)
        except importlib.metadata.PackageNotFoundError:
            version = None
        runtime["packages"][distribution] = version
    for module_name in ("qldpc", "pysat", "pysolvers", "igraph"):
        spec = importlib.util.find_spec(module_name)
        origin = None if spec is None else spec.origin
        runtime[module_name] = {
            "origin": origin,
            "sha256": (
                _file_sha256(Path(origin))
                if origin is not None and Path(origin).is_file()
                else None
            ),
        }
    bundle = {
        "schema_version": 1,
        "files_sha256": files,
        "runtime": runtime,
        "source_record": SOURCE_RECORD,
        "source_record_sha256": _canonical_sha256(SOURCE_RECORD),
    }
    return _seal(bundle, "source_bundle_sha256")


def _dic_mul(left: tuple[int, int], right: tuple[int, int]) -> tuple[int, int]:
    a, b = left
    c, d = right
    return ((a + (-c if b else c) + (5 if b and d else 0)) % 10, b ^ d)


def _mul(left: GroupElement, right: GroupElement) -> GroupElement:
    return _dic_mul(left[:2], right[:2]) + _dic_mul(left[2:], right[2:])


IDENTITY: GroupElement = (0, 0, 0, 0)
DIAGONAL_CENTER: GroupElement = (5, 0, 5, 0)
R1: GroupElement = (1, 0, 0, 0)
S1: GroupElement = (0, 1, 0, 0)
R2: GroupElement = (0, 0, 1, 0)
S2: GroupElement = (0, 0, 0, 1)
RAW_GROUP = tuple(product(range(10), range(2), range(10), range(2)))


def _power(value: GroupElement, exponent: int) -> GroupElement:
    result = IDENTITY
    for _ in range(exponent):
        result = _mul(result, value)
    return result


def _inverse(value: GroupElement) -> GroupElement:
    for trial in RAW_GROUP:
        if _mul(value, trial) == IDENTITY and _mul(trial, value) == IDENTITY:
            return trial
    raise AssertionError("finite group element has no inverse")


def _canonical_coset(value: GroupElement) -> GroupElement:
    return min(value, _mul(value, DIAGONAL_CENTER))


QUOTIENT_REPS = tuple(sorted({_canonical_coset(value) for value in RAW_GROUP}))
QUOTIENT_INDEX = {value: index for index, value in enumerate(QUOTIENT_REPS)}


def _word(*values: GroupElement) -> GroupElement:
    result = IDENTITY
    for value in values:
        result = _mul(result, value)
    return _canonical_coset(result)


def _construction_terms() -> tuple[tuple[GroupElement, ...], tuple[GroupElement, ...]]:
    a_terms = (
        _word(S1, R2, S2),
        _word(_power(R1, 9), _power(R2, 2), S2),
        _word(_power(R1, 2), S1, _power(R2, 3), S2),
    )
    b_terms = (
        _word(_power(R1, 8)),
        _word(_power(R1, 2), R2),
        _word(R2, S2),
    )
    return a_terms, b_terms


def _action_matrix(terms: Sequence[GroupElement], side: str) -> np.ndarray:
    matrix = np.zeros((200, 200), dtype=np.uint8)
    for row, value in enumerate(QUOTIENT_REPS):
        for term in terms:
            image = _canonical_coset(
                _mul(term, value) if side == "left" else _mul(value, term)
            )
            matrix[row, QUOTIENT_INDEX[image]] ^= 1
    return matrix


def _matrix_sha256(matrix: np.ndarray) -> str:
    binary = np.ascontiguousarray(matrix, dtype=np.uint8) & 1
    digest = hashlib.sha256()
    digest.update(f"{binary.shape[0]}x{binary.shape[1]}:".encode())
    digest.update(np.packbits(binary, axis=None, bitorder="little").tobytes())
    return digest.hexdigest()


def _array_sha256(name: str, value: np.ndarray) -> str:
    array = np.ascontiguousarray(np.asarray(value, dtype=np.uint8) & 1)
    digest = hashlib.sha256()
    digest.update(name.encode())
    digest.update(b"\0")
    digest.update(json.dumps(list(array.shape), separators=(",", ":")).encode())
    digest.update(b"\0")
    digest.update(array.tobytes(order="C"))
    return digest.hexdigest()


def _rank_f2(value: np.ndarray) -> int:
    matrix = np.asarray(value, dtype=np.uint8).copy() & 1
    rank = 0
    for column in range(matrix.shape[1]):
        pivots = np.flatnonzero(matrix[rank:, column])
        if pivots.size == 0:
            continue
        pivot = rank + int(pivots[0])
        matrix[[rank, pivot]] = matrix[[pivot, rank]]
        rows = np.flatnonzero(matrix[:, column])
        rows = rows[rows != rank]
        matrix[rows] ^= matrix[rank]
        rank += 1
        if rank == matrix.shape[0]:
            break
    return rank


def _span_minimum_weight(basis: np.ndarray) -> int:
    rows = np.asarray(basis, dtype=np.uint8) & 1
    current = np.zeros(rows.shape[1], dtype=np.uint8)
    previous = 0
    best = rows.shape[1] + 1
    for index in range(1, 1 << rows.shape[0]):
        gray = index ^ (index >> 1)
        difference = gray ^ previous
        bit = (difference & -difference).bit_length() - 1
        current ^= rows[bit]
        best = min(best, int(current.sum()))
        previous = gray
    return best


def _tanner_digest(code: codes.CSSCode) -> str:
    digest = hashlib.sha256()
    for left, right in canonical_hash(code):
        digest.update(int(left).to_bytes(4, "little"))
        digest.update(int(right).to_bytes(4, "little"))
    return digest.hexdigest()


def _cnf_summary(checks: np.ndarray, logicals: np.ndarray, sector: str) -> dict[str, Any]:
    cnf = build_css_threshold_cnf(
        checks,
        logicals,
        max_weight=SOLVER_MAX_WEIGHT,
        sector=sector,
        cardinality_encoding=CARDINALITY_ENCODING,
        partition_index=PARTITION_INDEX,
        anchor_indices=ANCHOR_INDICES,
    )
    keys = (
        "cnf_sha256",
        "num_variables",
        "num_clauses",
        "n",
        "num_checks",
        "num_logicals",
        "max_weight",
        "cardinality_encoding",
        "partition_index",
        "anchor_indices",
        "anchor_unit_clauses_sha256",
    )
    summary = {key: cnf[key] for key in keys}
    expected = EXPECTED_CNF[sector]
    if any(summary[key] != value for key, value in expected.items()):
        raise Paper400ValidationError(f"{sector} CNF hash/count mismatch")
    if summary["partition_index"] != PARTITION_INDEX or summary["anchor_indices"] != []:
        raise Paper400ValidationError("plain mode-B partition/anchor binding mismatch")
    return summary


def _optional_coset_minimal_plan(
    stabilizers: np.ndarray,
    checks: np.ndarray,
    logicals: np.ndarray,
) -> dict[str, Any]:
    """Verify, but do not enable, the deterministic 5000-clause enhancement."""

    rows = np.asarray(stabilizers, dtype=np.uint8) & 1
    if rows.shape != (200, 400) or not np.all(rows.sum(axis=1) == 6):
        raise Paper400ValidationError("optional coset plan requires 200 weight-6 rows")
    if np.any((np.asarray(checks, dtype=np.uint8) @ rows.T) & 1):
        raise Paper400ValidationError("Z stabilizers do not preserve the check syndrome")
    if np.any((np.asarray(logicals, dtype=np.uint8) @ rows.T) & 1):
        raise Paper400ValidationError("Z stabilizers do not preserve the logical syndrome")
    plain = build_css_threshold_cnf(
        checks,
        logicals,
        max_weight=SOLVER_MAX_WEIGHT,
        sector="Z",
        cardinality_encoding=CARDINALITY_ENCODING,
        partition_index=PARTITION_INDEX,
        anchor_indices=ANCHOR_INDICES,
    )
    if plain["cnf_sha256"] != EXPECTED_CNF["Z"]["cnf_sha256"]:
        raise Paper400ValidationError("optional plan plain-CNF binding mismatch")
    extra_clauses: list[list[int]] = []
    for row in rows:
        support = [int(index) + 1 for index in np.flatnonzero(row)]
        first, *remaining = support
        extra_clauses.extend(
            [[-variable for variable in subset] for subset in combinations(support, 4)]
        )
        extra_clauses.extend(
            [[-first, -left, -right] for left, right in combinations(remaining, 2)]
        )
    extra_sha256 = _canonical_sha256(extra_clauses)
    enhanced_sha256 = _canonical_sha256({
        "num_variables": plain["num_variables"],
        "clauses": plain["clauses"] + extra_clauses,
        "native_atmost": plain["native_atmost"],
    })
    if (
        len(extra_clauses) != 5000
        or len({tuple(clause) for clause in extra_clauses}) != 5000
        or extra_sha256 != EXPECTED_OPTIONAL_COSET_EXTRA_SHA256
        or enhanced_sha256 != EXPECTED_OPTIONAL_COSET_ENHANCED_CNF_SHA256
    ):
        raise Paper400ValidationError("optional coset-minimal encoding mismatch")
    report = {
        "schema_version": 1,
        "verified": True,
        "production_enabled": False,
        "injected_into_solver": False,
        "actual_production_mode": "plain-public-solve-css-sector-sat-v1",
        "disabled_reason": (
            "the existing production SAT API rebuilds its CNF internally and "
            "has no prebuilt/extra-clause injection contract"
        ),
        "plain_cnf_sha256": plain["cnf_sha256"],
        "extra_clause_count": len(extra_clauses),
        "extra_clause_sha256": extra_sha256,
        "optional_enhanced_num_variables": plain["num_variables"],
        "optional_enhanced_num_clauses": len(plain["clauses"]) + len(extra_clauses),
        "optional_enhanced_cnf_sha256": enhanced_sha256,
        "soundness": (
            "a minimum-weight representative in each Hz rowspace coset has "
            "overlap at most three with every weight-6 generator; among equal-"
            "weight representatives, the lexicographic minimum has zero at "
            "the smallest flipped coordinate"
        ),
    }
    return _seal(report, "report_sha256")

def prepare_instance() -> PreparedInstance:
    if len(QUOTIENT_REPS) != 200:
        raise Paper400ValidationError("diagonal-center quotient does not have order 200")
    if _power(DIAGONAL_CENTER, 2) != IDENTITY or any(
        _mul(value, DIAGONAL_CENTER) != _mul(DIAGONAL_CENTER, value)
        for value in RAW_GROUP
    ):
        raise Paper400ValidationError("K is not the claimed central order-two subgroup")
    relations = {
        "r1^10=e": _power(R1, 10) == IDENTITY,
        "r2^10=e": _power(R2, 10) == IDENTITY,
        "s1^2=r1^5": _power(S1, 2) == _power(R1, 5),
        "s2^2=r2^5": _power(S2, 2) == _power(R2, 5),
        "s1r1s1^-1=r1^-1": _word(S1, R1, _inverse(S1)) == _canonical_coset(_inverse(R1)),
        "s2r2s2^-1=r2^-1": _word(S2, R2, _inverse(S2)) == _canonical_coset(_inverse(R2)),
    }
    if not all(relations.values()):
        raise Paper400ValidationError("Dic5 relation replay failed")
    a_terms, b_terms = _construction_terms()
    if a_terms != ((0, 1, 1, 1), (4, 0, 7, 1), (2, 1, 3, 1)):
        raise Paper400ValidationError("A formula normalization mismatch")
    if b_terms != ((3, 0, 5, 0), (2, 0, 1, 0), (0, 0, 1, 1)):
        raise Paper400ValidationError("B formula normalization mismatch")
    a_left = _action_matrix(a_terms, "left")
    b_right = _action_matrix(b_terms, "right")
    hx0 = np.ascontiguousarray(np.hstack((a_left, b_right)), dtype=np.uint8)
    hz0 = np.ascontiguousarray(np.hstack((b_right.T, a_left.T)), dtype=np.uint8)
    matrix_hashes = {"H_X": _matrix_sha256(hx0), "H_Z": _matrix_sha256(hz0)}
    if matrix_hashes != EXPECTED_MATRIX_SHA256:
        raise Paper400ValidationError("matrix hash mismatch")
    rank_x, rank_z = _rank_f2(hx0), _rank_f2(hz0)
    if (rank_x, rank_z, 400 - rank_x - rank_z) != (192, 192, 16):
        raise Paper400ValidationError("[[400,16]] parameter replay failed")
    if np.any((hx0 @ hz0.T) & 1):
        raise Paper400ValidationError("CSS commutation failed")
    code = codes.CSSCode(hx0, hz0)
    hx, hz, lx, lz = (
        np.ascontiguousarray(value, dtype=np.uint8) & 1
        for value in get_code_matrices(code)
    )
    if not np.array_equal(hx, hx0) or not np.array_equal(hz, hz0):
        raise Paper400ValidationError("qldpc matrix extraction changed the construction")
    logical_hashes = {"L_X": _matrix_sha256(lx), "L_Z": _matrix_sha256(lz)}
    if logical_hashes != EXPECTED_LOGICAL_MATRIX_SHA256:
        raise Paper400ValidationError("logical basis bytes changed")
    w6 = require_css_w6_admissibility(hx, hz)
    detector = verify_css_logical_detectors(hx, hz, lx, lz)
    if w6.get("report_sha256") != EXPECTED_W6_REPORT_SHA256 or w6.get("passed") is not True:
        raise Paper400ValidationError("W6 replay failed")
    if detector.get("report_sha256") != EXPECTED_LOGICAL_DETECTOR_SHA256 or detector.get("verified") is not True:
        raise Paper400ValidationError("logical detector replay failed")
    ones = np.ones((1, 400), dtype=np.uint8)
    augmented_x = _rank_f2(np.vstack((hx, ones)))
    augmented_z = _rank_f2(np.vstack((hz, ones)))
    parity = {
        "schema_version": 1,
        "method": "all-ones-in-both-check-rowspaces-v1",
        "rank_Hx": rank_x,
        "rank_Hz": rank_z,
        "rank_Hx_with_ones": augmented_x,
        "rank_Hz_with_ones": augmented_z,
        "all_X_normalizer_operators_even": augmented_z == rank_z,
        "all_Z_normalizer_operators_even": augmented_x == rank_x,
        "target_rejection_cutoff": TARGET_REJECTION_CUTOFF,
        "derived_solver_cutoff": SOLVER_MAX_WEIGHT,
    }
    parity = _seal(parity, "report_sha256")
    if not parity["all_X_normalizer_operators_even"] or not parity["all_Z_normalizer_operators_even"]:
        raise Paper400ValidationError("even-parity lift failed")
    target = validate_target_binding(build_target_binding(400, 16), 400, 16)
    if (
        target["binding_sha256"] != EXPECTED_TARGET_BINDING_SHA256
        or target["mode"] != TARGET_MODE
        or target["required_distance"] != TARGET_REQUIRED_DISTANCE
        or target["rejection_cutoff"] != TARGET_REJECTION_CUTOFF
        or classify_target(400, 16, 20)["passed"] is not True
        or classify_target(400, 16, 19)["passed"] is not False
    ):
        raise Paper400ValidationError("strict 61/4 target replay failed")
    tanner = _tanner_digest(code)
    if tanner != EXPECTED_TANNER_CANONICAL_DIGEST:
        raise Paper400ValidationError("colored-Tanner canonical digest mismatch")
    logical_symmetry = verify_paper400_dic5_logical_symmetry(hx, hz, lx, lz)
    if (
        logical_symmetry.get("verified") is not True
        or logical_symmetry.get("report_sha256")
        != EXPECTED_LOGICAL_SYMMETRY_REPORT_SHA256
        or logical_symmetry.get("physical_group_order") != 200
        or logical_symmetry.get("Z_logical_action", {}).get(
            "logical_action_group_order"
        ) != 100
        or logical_symmetry.get("Z_logical_action", {}).get(
            "normalizing_bit_complete"
        ) is not True
        or logical_symmetry.get("canonical_Z_partition")
        != {
            "partition_index": PARTITION_INDEX,
            "anchor_indices": [],
            "complete_up_to_symmetry": True,
        }
    ):
        raise Paper400ValidationError("logical-symmetry partition replay failed")
    isometry = verify_paper400_dic5_xz_isometry(hx, hz, lx=lx, lz=lz)
    if (
        isometry.get("verified") is not True
        or isometry.get("report_sha256") != EXPECTED_XZ_ISOMETRY_REPORT_SHA256
        or isometry.get("canonical_sector") != "Z"
        or isometry.get("covered_sectors") != ["X", "Z"]
        or isometry.get("logical_basis_replay", {}).get("verified") is not True
        or isometry.get("logical_basis_replay", {}).get("X_to_Z_rank") != 16
        or isometry.get("logical_basis_replay", {}).get("Z_to_X_rank") != 16
    ):
        raise Paper400ValidationError("X/Z isometry replay failed")
    sector_data = {
        "X": (hz, lz),
        "Z": (hx, lx),
    }
    sectors = tuple(
        SectorSpec(sector, *sector_data[sector], _cnf_summary(*sector_data[sector], sector))
        for sector in SECTOR_ORDER
    )
    optional_coset_minimal = _optional_coset_minimal_plan(hz, hx, lx)
    construction = {
        "schema_version": 1,
        "normal_form": "(a,b,c,d)=r1^a s1^b r2^c s2^d",
        "quotient_representative": "lexicographic min of {g,g(r1^5r2^5)}",
        "quotient_order": 200,
        "A_terms": [list(item) for item in a_terms],
        "B_terms": [list(item) for item in b_terms],
        "matrix_convention": "H_X=[A_left|B_right], H_Z=[B_right^T|A_left^T], action image in column",
    }
    construction = _seal(construction, "construction_sha256")
    report = {
        "schema_version": 1,
        "gate": GATE,
        "source_record_sha256": _canonical_sha256(SOURCE_RECORD),
        "construction": construction,
        "relations": relations,
        "matrix_sha256": matrix_hashes,
        "tanner_canonical_digest": tanner,
        "parameters": {"n": 400, "k": 16, "rank_Hx": rank_x, "rank_Hz": rank_z},
        "weights": {
            "Hx_rows": sorted(set(int(item) for item in hx.sum(axis=1))),
            "Hz_rows": sorted(set(int(item) for item in hz.sum(axis=1))),
            "Hx_column_degree": sorted(set(int(item) for item in hx.sum(axis=0))),
            "Hz_column_degree": sorted(set(int(item) for item in hz.sum(axis=0))),
            "combined_column_degree": sorted(set(int(item) for item in np.vstack((hx, hz)).sum(axis=0))),
        },
        "w6": w6,
        "logical_detector": detector,
        "logical_basis": {
            "matrix_sha256": logical_hashes,
            "span_minimum_weight_X": _span_minimum_weight(lx),
            "span_minimum_weight_Z": _span_minimum_weight(lz),
            "semantics": "basis-span witnesses are upper bounds only",
        },
        "parity": parity,
        "logical_symmetry": logical_symmetry,
        "xz_isometry": isometry,
        "optional_coset_minimal_plan": optional_coset_minimal,
        "target": target,
        "solver_derivation": {
            "target_rejection_cutoff": TARGET_REJECTION_CUTOFF,
            "parity_derived_max_weight": SOLVER_MAX_WEIGHT,
            "partition_index": PARTITION_INDEX,
            "anchors": list(ANCHOR_INDICES),
            "actual_solver_mode": "plain-public-solve-css-sector-sat-v1",
            "sectors": [spec.cnf for spec in sectors],
        },
        "paper_upper_bound_authoritative_for_lower_or_exact": False,
    }
    report = _seal(report, "preflight_sha256")
    return PreparedInstance(hx, hz, lx, lz, sectors, report)


def _expected_instance_binding(
    spec: SectorSpec,
    checkpoint_identity: Mapping[str, Any],
) -> dict[str, Any]:
    distance_sat_path = PROJECT / "evaluation/distance_sat.py"
    try:
        pysat_version = importlib.metadata.version("python-sat")
    except importlib.metadata.PackageNotFoundError:
        pysat_version = None
    binding = {
        "formulation": SAT_FORMULATION,
        "formulation_revision": "xor-chain-global-or-pysat-cardinality-v1",
        "source_sha256": _file_sha256(distance_sat_path),
        "sector": spec.sector,
        "n": int(spec.checks.shape[1]),
        "num_checks": int(spec.checks.shape[0]),
        "num_logicals": int(spec.logicals.shape[0]),
        "check_matrix_sha256": _array_sha256("checks", spec.checks),
        "target_logicals_sha256": _array_sha256("logicals", spec.logicals),
        "max_weight": SOLVER_MAX_WEIGHT,
        "cardinality_encoding": CARDINALITY_ENCODING,
        "partition_index": PARTITION_INDEX,
        "anchor_indices": list(ANCHOR_INDICES),
        "backend": {
            "distribution": "python-sat",
            "version": pysat_version,
            "solver": SOLVER,
        },
        "solver_execution": {
            "policy": "one-shot-spawn-v1",
            "incremental_conflict_budget": None,
        },
        "checkpoint_identity": json.loads(_canonical_bytes(checkpoint_identity)),
        "native_thread_environment": {name: "1" for name in SAT_NATIVE_THREAD_ENV},
    }
    return _seal(binding, "binding_sha256")


def _solver_cnf_record(spec: SectorSpec) -> dict[str, Any]:
    return {
        key: spec.cnf[key]
        for key in (
            "num_variables",
            "num_clauses",
            "cnf_sha256",
            "cardinality_encoding",
            "anchor_unit_clauses_sha256",
        )
    }


def classify_sector_evidence(
    evidence: Mapping[str, Any],
    spec: SectorSpec,
    checkpoint_identity: Mapping[str, Any],
    *,
    timeout: float,
) -> dict[str, Any]:
    raw = dict(evidence) if isinstance(evidence, Mapping) else {}
    failures: list[str] = []
    unsigned = dict(raw)
    stored_evidence_hash = unsigned.pop("evidence_sha256", None)
    try:
        evidence_hash_valid = stored_evidence_hash == _canonical_sha256(unsigned)
    except (TypeError, ValueError):
        evidence_hash_valid = False
    if not evidence_hash_valid:
        failures.append("evidence self-hash mismatch")
    expected_instance = _expected_instance_binding(spec, checkpoint_identity)
    common = {
        "schema_version": SAT_EVIDENCE_SCHEMA_VERSION,
        "evidence_kind": SAT_EVIDENCE_KIND,
        "formulation": SAT_FORMULATION,
        "instance": expected_instance,
        "sector": spec.sector,
        "max_weight": SOLVER_MAX_WEIGHT,
        "cardinality_encoding": CARDINALITY_ENCODING,
        "backend": expected_instance["backend"],
        "partition_index": PARTITION_INDEX,
        "anchor_indices": list(ANCHOR_INDICES),
        "zero_anchor_indices": [],
        "one_anchor_index": None,
        "anchor_cube_sha256": None,
        "hard_timeout_s": float(timeout),
        "resumed": False,
        "workers": 1,
        "random_seed": 0,
    }
    for key, expected in common.items():
        if raw.get(key) != expected:
            failures.append(f"{key} binding mismatch")
    outcome = raw.get("outcome")
    if raw.get("status_name") != str(outcome).upper():
        failures.append("status_name mismatch")
    cnf_valid = raw.get("cnf") == _solver_cnf_record(spec)
    if outcome in {"sat", "unsat"} and not cnf_valid:
        failures.append("terminal CNF binding mismatch")
    witness_failures: list[str] = []
    if outcome == "sat":
        witness_failures = verify_css_threshold_sat_witness(
            raw, spec.checks, spec.logicals
        )
    strict_sat = bool(
        outcome == "sat"
        and raw.get("decision_complete") is True
        and raw.get("threshold_infeasible") is False
        and raw.get("success") is True
        and raw.get("retryable") is False
        and raw.get("message") is None
        and not failures
        and not witness_failures
    )
    strict_unsat = bool(
        outcome == "unsat"
        and raw.get("decision_complete") is True
        and raw.get("threshold_infeasible") is True
        and raw.get("success") is False
        and raw.get("operator") is None
        and raw.get("objective") is None
        and raw.get("logical_syndrome") is None
        and raw.get("retryable") is False
        and raw.get("message") is None
        and not failures
    )
    record = {
        "schema_version": 1,
        "sector": spec.sector,
        "outcome": outcome,
        "strict_verified_sat_rejection": strict_sat,
        "strict_bound_unsat": strict_unsat,
        "official_witness_verifier_invoked": outcome == "sat",
        "official_witness_failures": witness_failures,
        "binding_failures": failures,
        "evidence": raw,
    }
    return _seal(record, "record_sha256")


def derive_campaign_status(
    records: Sequence[Mapping[str, Any]],
    *,
    parity_verified: bool,
    logical_symmetry_verified: bool,
    isometry_verified: bool,
) -> dict[str, Any]:
    if any(item.get("strict_verified_sat_rejection") is True for item in records):
        return {
            "status": "REJECTED",
            "distance_lower_bound": None,
            "reason": "officially replayed logical witness of weight <=18",
        }
    by_sector = {str(item.get("sector")): item for item in records}
    both_unsat = all(
        by_sector.get(sector, {}).get("strict_bound_unsat") is True
        for sector in SECTOR_ORDER
    )
    if (
        both_unsat
        and parity_verified
        and logical_symmetry_verified
        and isometry_verified
    ):
        return {
            "status": "LOWER_BOUND_20",
            "distance_lower_bound": 20,
            "reason": (
                "plain partition-0 Z UNSAT through 18 plus independently "
                "replayed logical-symmetry coverage, even parity, and X/Z "
                "distance isometry"
            ),
        }
    return {
        "status": "UNRESOLVED",
        "distance_lower_bound": None,
        "reason": "UNKNOWN, INFEASIBLE, incomplete sector coverage, or invalid evidence",
    }


def run_sector_sequence(
    specs: Sequence[SectorSpec],
    identities: Mapping[str, Mapping[str, Any]],
    *,
    timeout: float,
    solver_callback: SolverCallback,
    record_callback: Callable[[dict[str, Any]], None] | None = None,
) -> list[dict[str, Any]]:
    records: list[dict[str, Any]] = []
    for spec in specs:
        identity = identities[spec.sector]
        evidence = solver_callback(
            spec.checks,
            spec.logicals,
            max_weight=SOLVER_MAX_WEIGHT,
            timeout=float(timeout),
            workers=1,
            seed=0,
            sector=spec.sector,
            cardinality_encoding=CARDINALITY_ENCODING,
            solver=SOLVER,
            partition_index=PARTITION_INDEX,
            anchor_indices=ANCHOR_INDICES,
            checkpoint_path=identity["checkpoint_path"],
            progress_path=identity["progress_path"],
            resume=False,
            checkpoint_identity=identity,
            termination_grace_s=2.0,
        )
        record = classify_sector_evidence(
            evidence, spec, identity, timeout=float(timeout)
        )
        records.append(record)
        if record_callback is not None:
            record_callback(record)
        if record["strict_verified_sat_rejection"] is True:
            break
    return records


def _write_new_bytes(path: Path, payload: bytes) -> None:
    flags = os.O_WRONLY | os.O_CREAT | os.O_EXCL
    flags |= getattr(os, "O_NOFOLLOW", 0)
    descriptor = os.open(path, flags, 0o600)
    try:
        view = memoryview(payload)
        while view:
            written = os.write(descriptor, view)
            view = view[written:]
        os.fsync(descriptor)
    finally:
        os.close(descriptor)
    directory = os.open(path.parent, os.O_RDONLY)
    try:
        os.fsync(directory)
    finally:
        os.close(directory)


def _write_new_json(path: Path, value: Mapping[str, Any]) -> None:
    _write_new_bytes(path, _canonical_bytes(value) + b"\n")


def create_isolated_root(root: Path) -> Path:
    requested = Path(root)
    if not requested.is_absolute():
        raise Paper400ValidationError("result root must be absolute")
    parent = requested.parent.resolve(strict=True)
    if requested.parent != parent or not parent.is_dir() or parent.is_symlink():
        raise Paper400ValidationError("result parent must be a real directory")
    os.mkdir(requested, 0o700)
    for name in ("input", "state", "sectors"):
        os.mkdir(requested / name, 0o700)
    return requested


RESOURCE_CPU_INTERVALS = 3
RESOURCE_CPU_INTERVAL_S = 2.0
RESOURCE_MAX_BUSY_PERCENT = 60.0
RESOURCE_MIN_RAW_HEADROOM = 512 * 1024**2
RESOURCE_MIN_EFFECTIVE_HEADROOM = 16 * 1024**3
RESOURCE_MAX_EFFECTIVE_FRACTION = 0.75
RESOURCE_MAX_MEMORY_PSI_FULL_AVG10 = 1.0
RESOURCE_MAX_MEMORY_PSI_FULL_AVG60 = 1.0


def _read_cpu_snapshot(cpu: int) -> tuple[int, int]:
    for line in Path("/proc/stat").read_text(encoding="utf-8").splitlines():
        fields = line.split()
        if fields and fields[0] == f"cpu{cpu}":
            values = [int(item) for item in fields[1:]]
            idle = values[3] + (values[4] if len(values) > 4 else 0)
            return sum(values), idle
    raise Paper400ValidationError(f"CPU {cpu} is absent from /proc/stat")


def _read_integer_mapping(path: Path) -> dict[str, int]:
    result: dict[str, int] = {}
    for line in path.read_text(encoding="utf-8").splitlines():
        fields = line.split()
        if len(fields) != 2:
            raise Paper400ValidationError(f"invalid integer cgroup record: {path}")
        try:
            result[fields[0]] = int(fields[1])
        except ValueError as exc:
            raise Paper400ValidationError(
                f"invalid integer cgroup value: {path}"
            ) from exc
    return result


def _read_pressure(path: Path) -> dict[str, dict[str, float | int]]:
    result: dict[str, dict[str, float | int]] = {}
    for line in path.read_text(encoding="utf-8").splitlines():
        fields = line.split()
        if not fields:
            continue
        values: dict[str, float | int] = {}
        for field in fields[1:]:
            if "=" not in field:
                raise Paper400ValidationError(f"invalid PSI record: {path}")
            key, raw = field.split("=", 1)
            try:
                values[key] = int(raw) if key == "total" else float(raw)
            except ValueError as exc:
                raise Paper400ValidationError(
                    f"invalid PSI value: {path}"
                ) from exc
        result[fields[0]] = values
    return result


def _evaluate_resource_gate(
    *,
    cpu: int,
    busy_percent: Sequence[float],
    niceness: int,
    affinity: Sequence[int],
    memory_current: int,
    memory_max: int | None,
    memory_stat: Mapping[str, int],
    memory_events: Mapping[str, int],
    memory_pressure: Mapping[str, Mapping[str, float | int]],
    thread_environment: Mapping[str, str | None],
) -> dict[str, Any]:
    busy = [float(value) for value in busy_percent]
    affinity_list = [int(value) for value in affinity]
    file_bytes = int(memory_stat.get("file", 0))
    inactive_file_bytes = int(memory_stat.get("inactive_file", 0))
    reclaimable = max(0, min(file_bytes, inactive_file_bytes))
    effective_current = max(0, int(memory_current) - reclaimable)
    if memory_max is None:
        raw_headroom = None
        effective_headroom = None
        effective_fraction = 0.0
        raw_headroom_safe = True
        effective_headroom_safe = True
        effective_fraction_safe = True
    else:
        maximum = int(memory_max)
        raw_headroom = maximum - int(memory_current)
        effective_headroom = maximum - effective_current
        effective_fraction = effective_current / maximum if maximum > 0 else math.inf
        raw_headroom_safe = raw_headroom >= RESOURCE_MIN_RAW_HEADROOM
        effective_headroom_safe = (
            effective_headroom >= RESOURCE_MIN_EFFECTIVE_HEADROOM
        )
        effective_fraction_safe = (
            maximum > 0
            and effective_fraction <= RESOURCE_MAX_EFFECTIVE_FRACTION
        )
    full_pressure = memory_pressure.get("full", {})
    try:
        full_avg10 = float(full_pressure["avg10"])
        full_avg60 = float(full_pressure["avg60"])
    except (KeyError, TypeError, ValueError):
        full_avg10 = math.inf
        full_avg60 = math.inf
    pressure_safe = bool(
        math.isfinite(full_avg10)
        and math.isfinite(full_avg60)
        and full_avg10 < RESOURCE_MAX_MEMORY_PSI_FULL_AVG10
        and full_avg60 < RESOURCE_MAX_MEMORY_PSI_FULL_AVG60
    )
    oom_safe = all(
        int(memory_events.get(name, -1)) == 0
        for name in ("oom", "oom_kill", "oom_group_kill")
    )
    cpu_safe = bool(
        len(busy) == RESOURCE_CPU_INTERVALS
        and all(math.isfinite(value) and value < RESOURCE_MAX_BUSY_PERCENT for value in busy)
        and affinity_list == [int(cpu)]
        and int(niceness) == 19
    )
    thread_environment_safe = all(
        thread_environment.get(name) == "1" for name in THREAD_ENV
    )
    memory_safe = bool(
        raw_headroom_safe
        and effective_headroom_safe
        and effective_fraction_safe
        and oom_safe
        and pressure_safe
    )
    report = {
        "schema_version": 2,
        "method": "cache-aware-cgroup-v2",
        "cpu": int(cpu),
        "cpu_interval_count": RESOURCE_CPU_INTERVALS,
        "cpu_interval_s": RESOURCE_CPU_INTERVAL_S,
        "busy_percent": [round(value, 3) for value in busy],
        "cpu_safe": cpu_safe,
        "niceness": int(niceness),
        "affinity": affinity_list,
        "memory_current": int(memory_current),
        "memory_max": None if memory_max is None else int(memory_max),
        "memory_stat": {str(key): int(value) for key, value in memory_stat.items()},
        "memory_events": {str(key): int(value) for key, value in memory_events.items()},
        "memory_pressure": {
            str(kind): {
                str(key): value
                for key, value in values.items()
            }
            for kind, values in memory_pressure.items()
        },
        "file_bytes": file_bytes,
        "inactive_file_bytes": inactive_file_bytes,
        "reclaimable_file_bytes": reclaimable,
        "raw_headroom_bytes": raw_headroom,
        "effective_current_bytes": effective_current,
        "effective_headroom_bytes": effective_headroom,
        "effective_current_fraction": effective_fraction,
        "raw_headroom_safe": raw_headroom_safe,
        "effective_headroom_safe": effective_headroom_safe,
        "effective_fraction_safe": effective_fraction_safe,
        "oom_safe": oom_safe,
        "memory_psi_full_avg10": full_avg10,
        "memory_psi_full_avg60": full_avg60,
        "pressure_safe": pressure_safe,
        "memory_safe": memory_safe,
        "thread_environment": {
            name: thread_environment.get(name) for name in THREAD_ENV
        },
        "thread_environment_safe": thread_environment_safe,
        "passed": bool(cpu_safe and memory_safe and thread_environment_safe),
    }
    return _seal(report, "report_sha256")


def require_resource_gate() -> dict[str, Any]:
    affinity = sorted(os.sched_getaffinity(0))
    niceness = os.getpriority(os.PRIO_PROCESS, 0)
    if len(affinity) != 1 or niceness != 19:
        raise Paper400ValidationError("production must be pinned to one CPU at nice 19")
    cpu = affinity[0]
    snapshots = [_read_cpu_snapshot(cpu)]
    for _ in range(RESOURCE_CPU_INTERVALS):
        time.sleep(RESOURCE_CPU_INTERVAL_S)
        snapshots.append(_read_cpu_snapshot(cpu))
    busy: list[float] = []
    for before, after in zip(snapshots[:-1], snapshots[1:], strict=True):
        total = after[0] - before[0]
        idle = after[1] - before[1]
        busy.append(100.0 * (1.0 - idle / max(1, total)))
    cgroup = Path("/sys/fs/cgroup")
    current = int((cgroup / "memory.current").read_text(encoding="utf-8").strip())
    maximum_text = (cgroup / "memory.max").read_text(encoding="utf-8").strip()
    maximum = None if maximum_text == "max" else int(maximum_text)
    report = _evaluate_resource_gate(
        cpu=cpu,
        busy_percent=busy,
        niceness=niceness,
        affinity=affinity,
        memory_current=current,
        memory_max=maximum,
        memory_stat=_read_integer_mapping(cgroup / "memory.stat"),
        memory_events=_read_integer_mapping(cgroup / "memory.events"),
        memory_pressure=_read_pressure(cgroup / "memory.pressure"),
        thread_environment={name: os.environ.get(name) for name in THREAD_ENV},
    )
    if report["passed"] is not True:
        raise Paper400ValidationError(f"resource gate failed: {report}")
    return report

def run_campaign(
    root: Path,
    *,
    timeout: float = DEFAULT_TIMEOUT_PER_SECTOR_S,
    solver_callback: SolverCallback | None = None,
    enforce_resource_gate: bool = True,
) -> dict[str, Any]:
    if not math.isfinite(float(timeout)) or float(timeout) <= 0:
        raise Paper400ValidationError("timeout must be positive and finite")
    if solver_callback is None:
        solver_callback = solve_css_sector_sat
    resource = (
        require_resource_gate()
        if enforce_resource_gate
        else {"passed": False, "test_override": True}
    )
    prepared = prepare_instance()
    sources_before = source_bundle()
    output_root = create_isolated_root(Path(root))
    campaign_binding = _seal({
        "schema_version": 1,
        "gate": GATE,
        "root": str(output_root),
        "source_bundle_sha256": sources_before["source_bundle_sha256"],
        "preflight_sha256": prepared.report["preflight_sha256"],
        "logical_symmetry_report_sha256": (
            prepared.report["logical_symmetry"]["report_sha256"]
        ),
        "xz_isometry_report_sha256": prepared.report["xz_isometry"]["report_sha256"],
        "sector_order": list(SECTOR_ORDER),
        "target_binding_sha256": EXPECTED_TARGET_BINDING_SHA256,
        "target_rejection_cutoff": TARGET_REJECTION_CUTOFF,
        "parity_derived_solver_max_weight": SOLVER_MAX_WEIGHT,
        "partition_index": PARTITION_INDEX,
        "anchors": list(ANCHOR_INDICES),
        "actual_solver_mode": "plain-public-solve-css-sector-sat-v1",
        "solver": SOLVER,
        "cardinality_encoding": CARDINALITY_ENCODING,
        "timeout_per_sector_s": float(timeout),
        "workers": 1,
        "resume": False,
    }, "binding_sha256")
    identities: dict[str, dict[str, Any]] = {}
    for sector in SECTOR_ORDER:
        identities[sector] = _seal({
            "schema_version": 1,
            "campaign_binding_sha256": campaign_binding["binding_sha256"],
            "sector": sector,
            "cnf_sha256": next(
                spec.cnf["cnf_sha256"] for spec in prepared.sectors
                if spec.sector == sector
            ),
            "checkpoint_path": str(output_root / "state" / f"{sector}.json"),
            "progress_path": str(output_root / "state" / f"{sector}.progress.json"),
        }, "identity_sha256")
    manifest = _seal({
        "schema_version": 1,
        "gate": GATE,
        "status": "SEALED_NOT_RUN",
        "solver_invoked": False,
        "source_bundle": sources_before,
        "resource_gate": resource,
        "preflight": prepared.report,
        "campaign_binding": campaign_binding,
        "sector_identities": identities,
        "authority": {
            "paper_22_is_upper_only": True,
            "sat_requires_official_witness_replay": True,
            "unknown_is_unresolved": True,
            "infeasible_is_unresolved": True,
            "plain_partition0_Z_unsat_plus_symmetry_parity_and_isometry_required_for_lower_20": True,
            "optional_coset_minimal_plan_not_injected": True,
            "publication_certificate": False,
        },
    }, "manifest_sha256")
    _write_new_json(output_root / "input" / "manifest.json", manifest)
    written: list[dict[str, str]] = []

    def persist(record: dict[str, Any]) -> None:
        current_sources = source_bundle()
        if current_sources != sources_before:
            raise Paper400ValidationError("source closure changed during solver run")
        path = output_root / "sectors" / f"{record['sector']}.json"
        _write_new_json(path, record)
        written.append({"sector": record["sector"], "path": str(path), "file_sha256": _file_sha256(path)})

    records = run_sector_sequence(
        prepared.sectors,
        identities,
        timeout=float(timeout),
        solver_callback=solver_callback,
        record_callback=persist,
    )
    sources_after = source_bundle()
    if sources_after != sources_before:
        raise Paper400ValidationError("source closure changed before terminal commit")
    parity_verified = bool(
        prepared.report["parity"]["all_X_normalizer_operators_even"]
        and prepared.report["parity"]["all_Z_normalizer_operators_even"]
    )
    logical_symmetry_verified = bool(
        prepared.report["logical_symmetry"]["verified"]
        and prepared.report["logical_symmetry"]["report_sha256"]
        == EXPECTED_LOGICAL_SYMMETRY_REPORT_SHA256
        and prepared.report["logical_symmetry"]["canonical_Z_partition"][
            "complete_up_to_symmetry"
        ]
    )
    isometry_verified = bool(
        prepared.report["xz_isometry"]["verified"]
        and prepared.report["xz_isometry"]["report_sha256"]
        == EXPECTED_XZ_ISOMETRY_REPORT_SHA256
    )
    decision = derive_campaign_status(
        records,
        parity_verified=parity_verified,
        logical_symmetry_verified=logical_symmetry_verified,
        isometry_verified=isometry_verified,
    )
    terminal = _seal({
        "schema_version": 1,
        "gate": GATE,
        **decision,
        "root": str(output_root),
        "manifest_sha256": manifest["manifest_sha256"],
        "source_bundle_sha256": sources_before["source_bundle_sha256"],
        "campaign_binding_sha256": campaign_binding["binding_sha256"],
        "target": prepared.report["target"],
        "target_rejection_cutoff": TARGET_REJECTION_CUTOFF,
        "parity_derived_solver_max_weight": SOLVER_MAX_WEIGHT,
        "logical_symmetry_report_sha256": EXPECTED_LOGICAL_SYMMETRY_REPORT_SHA256,
        "xz_isometry_report_sha256": EXPECTED_XZ_ISOMETRY_REPORT_SHA256,
        "partition_index": PARTITION_INDEX,
        "anchors": list(ANCHOR_INDICES),
        "actual_solver_mode": "plain-public-solve-css-sector-sat-v1",
        "sector_order": list(SECTOR_ORDER),
        "sector_artifacts": written,
        "publication_certificate": False,
    }, "terminal_sha256")
    _write_new_json(output_root / "terminal.json", terminal)
    return terminal


def build_parser() -> argparse.ArgumentParser:
    parser = argparse.ArgumentParser(description=__doc__)
    subparsers = parser.add_subparsers(dest="action", required=True)
    subparsers.add_parser("preflight", help="rebuild and hash everything; no solver")
    run = subparsers.add_parser(
        "run", help="run the canonical partition-0 Z sector in a new isolated root"
    )
    run.add_argument("--root", required=True, type=Path)
    run.add_argument("--timeout-per-sector", type=float, default=DEFAULT_TIMEOUT_PER_SECTOR_S)
    return parser


def main(argv: list[str] | None = None) -> int:
    args = build_parser().parse_args(argv)
    if args.action == "preflight":
        result = {
            "preflight": prepare_instance().report,
            "source_bundle": source_bundle(),
            "solver_invoked": False,
        }
    else:
        result = run_campaign(args.root, timeout=args.timeout_per_sector)
    print(_canonical_bytes(result).decode())
    return 0


if __name__ == "__main__":
    raise SystemExit(main())


