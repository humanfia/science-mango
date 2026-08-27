"""Canonical-type-strict optimized Dic5 CNF derived only from final_v5.

The zero-solver construction uses Hx[:192], Lx[:1], Z/max18/partition0,
no anchors, and the proved 3000-clause coset-minimal reduction.  Production
uses one in-process CaDiCaL call to avoid a duplicate qldpc Python image.  An
external 43600 s watchdog is required policy around the fixed 43200 s solve;
it is not internally enforced.  A killed process cannot expose a partial
valid authoritative terminal; incomplete state remains unresolved.  SAT requires complete-CNF and full-Hx/full-Lx official replay.
Proofless UNSAT is current-source only and never publishable or uploadable.
"""

from __future__ import annotations

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

import numpy as np

from scripts import run_paper400_dic5_w6_lower_final_v5 as baseline


PROJECT = Path(__file__).resolve().parent.parent
SCHEMA_VERSION = 14
GATE = "qcode-paper400-dic5-optimized-coset-cnf-final-v13"
EVIDENCE_KIND = "qcode-paper400-dic5-optimized-prebuilt-sat-evidence-final-v13"
FORMULATION = "paper400-dic5-basis192-bit0-coset-minimal-cnf-final-v13"
SECTOR = "Z"
MAX_WEIGHT = 18
PARTITION_INDEX = 0
ANCHOR_INDICES: tuple[int, ...] = ()
SOLVER = "cadical195"
CARDINALITY_ENCODING = "kmtotalizer"
BASIS_ROWS = 192
OPERATOR_VARIABLES = 400
SOLVER_BUDGET_S = 43200.0
REQUIRED_OUTER_HARD_TIMEOUT_S = 43600.0
OUTER_WATCHDOG_POLICY = "required-external-not-internally-enforced-v1"

EXPECTED_BASELINE_PREFLIGHT_SHA256 = (
    "fc93435ce3c000e5293601e214dfd79e8df5bce0b6295b6cdb6fb433454a250b"
)
EXPECTED_BASELINE_CNF_SHA256 = (
    "2f6aad2bb19fef0563ebec15372a74000a48ff252194208c412734e449c417ac"
)
EXPECTED_BASIS_INDICES_SHA256 = (
    "8f824944b05312482763055d2d994a8aba1ca5173513fb48c04d6f0d3159c54e"
)
EXPECTED_BASIS_MATRIX_SHA256 = (
    "8d71ad17abcababd00a5650c0bf1dc752574f889ece989d3749ca44e5539410c"
)
EXPECTED_REDUCED_PLAIN_CNF_SHA256 = (
    "3261688b85fcaad8480f45249991b5d7d7a68e711e5bc9349796225e40348b94"
)
EXPECTED_REDUCED_EXTRA_SHA256 = (
    "9cbe33db6855c743936abc30c396a9cc15f800c561cf16b4ad71eae84a661cd1"
)
EXPECTED_OPTIMIZED_CNF_SHA256 = (
    "3ca7bbc31792b27363af4dd56ca79facf1501a1a97d66d64b5684b3597191537"
)
EXPECTED_OPTIMIZED_DIMACS_SHA256 = (
    "0e4c96f4f002f956d12ff9d3f50d6487d389afcea63d02177fc2a29c4755bd07"
)
EXPECTED_OPTIMIZED_NUM_VARIABLES = 2955
EXPECTED_OPTIMIZED_NUM_CLAUSES = 12022
EXPECTED_OPTIMIZED_DIMACS_BYTES = 203044

EVIDENCE_FIELDS = frozenset({
    "schema_version", "evidence_kind", "formulation", "instance", "cnf",
    "sector", "max_weight", "cardinality_encoding", "backend",
    "partition_index", "anchor_indices", "solver_budget_s",
    "required_outer_hard_timeout_s", "outer_watchdog_policy", "resumed",
    "timed_out", "workers", "random_seed", "solver_invocations",
    "execution_mode", "outcome", "status_name", "decision_complete",
    "threshold_infeasible", "success", "retryable", "message", "operator",
    "objective", "logical_syndrome", "full_model", "elapsed_s",
    "solver_time_s", "solver_stats", "durable_proof",
    "publication_certificate", "upload_authorized", "evidence_sha256",
})


class Dic5OptimizedCnfFinalV13Error(RuntimeError):
    """A construction, source, runtime, or evidence binding failed."""


@dataclass(frozen=True)
class OptimizedInstance:
    hx: np.ndarray
    hz: np.ndarray
    lx: np.ndarray
    lz: np.ndarray
    basis_checks: np.ndarray
    active_logical: np.ndarray
    cnf: dict[str, Any]
    dimacs: bytes
    report: dict[str, Any]


def canonical_bytes(value: Any) -> bytes:
    return json.dumps(
        value, sort_keys=True, separators=(",", ":"), ensure_ascii=False,
        allow_nan=False,
    ).encode("utf-8")


def canonical_sha256(value: Any) -> str:
    return hashlib.sha256(canonical_bytes(value)).hexdigest()


def seal(value: Mapping[str, Any], field: str) -> dict[str, Any]:
    result = dict(value)
    result.pop(field, None)
    result[field] = canonical_sha256(result)
    return result


def json_type_equal(actual: Any, expected: Any) -> bool:
    """Recursive JSON equality with exact bool/int/float/container types."""

    if type(actual) is not type(expected):
        return False
    if type(expected) is dict:
        return set(actual) == set(expected) and all(
            json_type_equal(actual[key], expected[key]) for key in expected
        )
    if type(expected) is list:
        return len(actual) == len(expected) and all(
            json_type_equal(left, right)
            for left, right in zip(actual, expected, strict=True)
        )
    if type(expected) is float:
        return math.isfinite(actual) and math.isfinite(expected) and actual == expected
    return actual == expected


def file_sha256(path: Path) -> str:
    target = Path(path)
    if target.is_symlink() or not target.is_file():
        raise Dic5OptimizedCnfFinalV13Error(f"not a regular file: {target}")
    before = target.stat()
    payload = target.read_bytes()
    after = target.stat()
    before_id = (
        before.st_dev, before.st_ino, before.st_size, before.st_mtime_ns,
        before.st_ctime_ns,
    )
    after_id = (
        after.st_dev, after.st_ino, after.st_size, after.st_mtime_ns,
        after.st_ctime_ns,
    )
    if before_id != after_id or len(payload) != before.st_size:
        raise Dic5OptimizedCnfFinalV13Error(f"file changed while hashing: {target}")
    return hashlib.sha256(payload).hexdigest()


def _matrix_sha256(matrix: np.ndarray) -> str:
    return baseline._matrix_sha256(np.asarray(matrix, dtype=np.uint8) & 1)


def _array_sha256(name: str, matrix: np.ndarray) -> str:
    return baseline._array_sha256(name, np.asarray(matrix, dtype=np.uint8) & 1)


def _rank_f2(matrix: np.ndarray) -> int:
    return baseline._rank_f2(np.asarray(matrix, dtype=np.uint8) & 1)


def _pack_bits(bits: np.ndarray) -> dict[str, Any]:
    vector = np.asarray(bits, dtype=np.uint8).reshape(-1) & 1
    packed = np.packbits(vector, bitorder="little").tobytes()
    return {
        "length": int(vector.size), "weight": int(vector.sum()),
        "packed_hex": packed.hex(),
        "sha256": hashlib.sha256(f"{vector.size}:".encode() + packed).hexdigest(),
    }


def _unpack_bits(record: Any, *, expected_length: int) -> np.ndarray:
    if type(record) is not dict or set(record) != {
        "length", "weight", "packed_hex", "sha256",
    }:
        raise Dic5OptimizedCnfFinalV13Error("packed vector field set/type mismatch")
    if type(record["length"]) is not int or record["length"] != expected_length:
        raise Dic5OptimizedCnfFinalV13Error("packed vector length mismatch")
    if type(record["weight"]) is not int or not 0 <= record["weight"] <= expected_length:
        raise Dic5OptimizedCnfFinalV13Error("packed vector weight mismatch")
    if type(record["packed_hex"]) is not str or type(record["sha256"]) is not str:
        raise Dic5OptimizedCnfFinalV13Error("packed vector string type mismatch")
    try:
        packed = bytes.fromhex(record["packed_hex"])
    except ValueError as exc:
        raise Dic5OptimizedCnfFinalV13Error("invalid packed vector hex") from exc
    if len(packed) != (expected_length + 7) // 8:
        raise Dic5OptimizedCnfFinalV13Error("packed vector byte length mismatch")
    vector = np.unpackbits(
        np.frombuffer(packed, dtype=np.uint8), bitorder="little"
    )[:expected_length].astype(np.uint8)
    if not json_type_equal(record, _pack_bits(vector)):
        raise Dic5OptimizedCnfFinalV13Error("packed vector canonical replay mismatch")
    return vector


def _solve_row_coefficients(basis: np.ndarray, target: np.ndarray) -> np.ndarray:
    rows = np.asarray(basis, dtype=np.uint8) & 1
    rhs = np.asarray(target, dtype=np.uint8).reshape(-1) & 1
    augmented = np.column_stack((rows.T.copy(), rhs))
    equation = 0
    pivots: list[int] = []
    for variable in range(rows.shape[0]):
        candidates = np.flatnonzero(augmented[equation:, variable])
        if candidates.size == 0:
            continue
        pivot = equation + int(candidates[0])
        augmented[[equation, pivot]] = augmented[[pivot, equation]]
        others = np.flatnonzero(augmented[:, variable])
        others = others[others != equation]
        augmented[others] ^= augmented[equation]
        pivots.append(variable)
        equation += 1
        if equation == augmented.shape[0]:
            break
    inconsistent = np.logical_and(
        np.logical_not(augmented[:, :-1].any(axis=1)), augmented[:, -1] == 1
    )
    if np.any(inconsistent) or len(pivots) != rows.shape[0]:
        raise Dic5OptimizedCnfFinalV13Error("row outside selected rowspace")
    solution = np.zeros(rows.shape[0], dtype=np.uint8)
    for row_index, variable in enumerate(pivots):
        solution[variable] = augmented[row_index, -1]
    if not np.array_equal((solution @ rows) & 1, rhs):
        raise Dic5OptimizedCnfFinalV13Error("rowspace replay failed")
    return solution


def _rowspace_certificate(hx: np.ndarray) -> tuple[np.ndarray, dict[str, Any]]:
    full = np.asarray(hx, dtype=np.uint8) & 1
    if full.shape != (200, 400):
        raise Dic5OptimizedCnfFinalV13Error("unexpected Hx shape")
    basis = np.ascontiguousarray(full[:BASIS_ROWS])
    records = []
    for row_index in range(BASIS_ROWS, full.shape[0]):
        coefficients = _solve_row_coefficients(basis, full[row_index])
        records.append({
            "row_index": row_index, "coefficients": _pack_bits(coefficients),
            "replayed": bool(np.array_equal((coefficients @ basis) & 1, full[row_index])),
        })
    indices = list(range(BASIS_ROWS))
    full_rank, basis_rank = _rank_f2(full), _rank_f2(basis)
    report = seal({
        "schema_version": 1,
        "method": "subset-rank-plus-explicit-dropped-row-coefficients-v1",
        "full_shape": [200, 400], "basis_shape": [192, 400],
        "basis_indices": indices, "basis_indices_sha256": canonical_sha256(indices),
        "full_matrix_sha256": _matrix_sha256(full),
        "basis_matrix_sha256": _matrix_sha256(basis),
        "full_rank": full_rank, "basis_rank": basis_rank,
        "basis_is_literal_row_subset": bool(np.array_equal(basis, full[:192])),
        "dropped_row_coefficients": records,
        "rowspace_equal": bool(
            full_rank == basis_rank == BASIS_ROWS
            and all(item["replayed"] for item in records)
        ),
    }, "report_sha256")
    if (
        report["basis_indices_sha256"] != EXPECTED_BASIS_INDICES_SHA256
        or report["basis_matrix_sha256"] != EXPECTED_BASIS_MATRIX_SHA256
        or report["rowspace_equal"] is not True
    ):
        raise Dic5OptimizedCnfFinalV13Error("Hx rowspace certificate mismatch")
    return basis, report


def _xor_truth_table() -> dict[str, Any]:
    rows = []
    verified = True
    for left, right, output in product((0, 1), repeat=3):
        clauses = (
            (left, right, not output), (not left, not right, not output),
            (left, not right, output), (not left, right, output),
        )
        holds = all(any(clause) for clause in clauses)
        intended = output == (left ^ right)
        rows.append({
            "left": left, "right": right, "output": output,
            "cnf_holds": holds, "intended": intended,
        })
        verified = verified and holds == intended
    return {
        "assignments_checked": 8, "rows_sha256": canonical_sha256(rows),
        "verified": bool(verified),
    }


def _logical_projection_certificate(
    full_cnf: Mapping[str, Any], active_cnf: Mapping[str, Any],
    hx: np.ndarray, lx: np.ndarray,
) -> dict[str, Any]:
    check_weights = [int(value) for value in np.asarray(hx).sum(axis=1)]
    logical_weights = [int(value) for value in np.asarray(lx).sum(axis=1)]
    check_clause_count = sum(4 * (weight - 1) + 1 for weight in check_weights)
    logical_clause_counts = [4 * (weight - 1) for weight in logical_weights]
    partition_clause_index = check_clause_count + sum(logical_clause_counts)
    if full_cnf["clauses"][partition_clause_index] != [full_cnf["logical_variables"][0]]:
        raise Dic5OptimizedCnfFinalV13Error("partition-zero clause changed")
    dropped_variables = sum(weight - 1 for weight in logical_weights[1:])
    full_pre_cardinality = (
        OPERATOR_VARIABLES + sum(weight - 1 for weight in check_weights)
        + sum(weight - 1 for weight in logical_weights)
    )
    projected = list(full_cnf["clauses"][: check_clause_count + logical_clause_counts[0]])
    projected.append(list(full_cnf["clauses"][partition_clause_index]))
    for clause in full_cnf["clauses"][partition_clause_index + 1 :]:
        mapped = []
        for literal in clause:
            variable = abs(int(literal))
            if variable > full_pre_cardinality:
                variable -= dropped_variables
            mapped.append(variable if literal > 0 else -variable)
        projected.append(mapped)
    exact = bool(
        projected == active_cnf["clauses"]
        and int(full_cnf["num_variables"]) - dropped_variables
        == int(active_cnf["num_variables"])
    )
    truth = _xor_truth_table()
    report = seal({
        "schema_version": 1,
        "method": "drop-unused-definitional-logical-xors-and-renumber-cardinality-v1",
        "full_logical_count": 16, "active_logical_indices": [0],
        "dropped_logical_indices": list(range(1, 16)), "partition_index": 0,
        "partition_clause": list(full_cnf["clauses"][partition_clause_index]),
        "full_logical_matrix_sha256": _matrix_sha256(lx),
        "active_logical_matrix_sha256": _matrix_sha256(lx[:1]),
        "dropped_definitional_variables": dropped_variables,
        "dropped_definitional_clauses": sum(logical_clause_counts[1:]),
        "full_pre_cardinality_variables": full_pre_cardinality,
        "reduced_pre_cardinality_variables": full_pre_cardinality - dropped_variables,
        "full_cnf_sha256": full_cnf["cnf_sha256"],
        "active_cnf_sha256": active_cnf["cnf_sha256"],
        "projected_clauses_sha256": canonical_sha256(projected),
        "active_clauses_sha256": canonical_sha256(active_cnf["clauses"]),
        "xor_gate_truth_table": truth,
        "projected_formula_byte_equal_after_canonical_aux_renumbering": exact,
        "operator_projection_equisatisfiable": bool(exact and truth["verified"] is True),
    }, "report_sha256")
    if report["operator_projection_equisatisfiable"] is not True:
        raise Dic5OptimizedCnfFinalV13Error("logical projection replay failed")
    return report


def _clauses_hold(clauses: Sequence[Sequence[int]], bits: Sequence[int]) -> bool:
    return all(any(
        (bits[abs(lit) - 1] == 1) if lit > 0 else (bits[abs(lit) - 1] == 0)
        for lit in clause
    ) for clause in clauses)


def _coset_minimal_certificate(
    hz: np.ndarray, hx: np.ndarray, lx: np.ndarray,
) -> tuple[list[list[int]], dict[str, Any]]:
    rows = np.asarray(hz, dtype=np.uint8) & 1
    if rows.shape != (200, 400) or not np.all(rows.sum(axis=1) == 6):
        raise Dic5OptimizedCnfFinalV13Error("expected 200 weight-six Z stabilizers")
    preserves_checks = not np.any((np.asarray(hx) @ rows.T) & 1)
    preserves_logicals = not np.any((np.asarray(lx) @ rows.T) & 1)
    original: list[list[int]] = []
    reduced: list[list[int]] = []
    subsumption = []
    for row_index, row in enumerate(rows):
        support = [int(index) + 1 for index in np.flatnonzero(row)]
        first, *remaining = support
        old_four = [[-v for v in subset] for subset in combinations(support, 4)]
        tie = [[-first, -a, -b] for a, b in combinations(remaining, 2)]
        new_four = [[-v for v in subset] for subset in combinations(remaining, 4)]
        original.extend(old_four)
        original.extend(tie)
        reduced.extend(new_four)
        reduced.extend(tie)
        for removed in old_four:
            if -first not in removed:
                continue
            tail = [literal for literal in removed if literal != -first]
            subsuming = [-first, *tail[:2]]
            if subsuming not in tie or not set(subsuming).issubset(removed):
                raise Dic5OptimizedCnfFinalV13Error("subsumption replay failed")
            subsumption.append({
                "row_index": row_index, "removed_clause": removed,
                "subsuming_clause": subsuming,
            })
    if len(original) != 5000 or len(set(map(tuple, original))) != 5000:
        raise Dic5OptimizedCnfFinalV13Error("original clause plan changed")
    if len(reduced) != 3000 or len(set(map(tuple, reduced))) != 3000:
        raise Dic5OptimizedCnfFinalV13Error("reduced clause plan changed")
    local_old = [
        [-index - 1 for index in subset] for subset in combinations(range(6), 4)
    ] + [[-1, -a - 1, -b - 1] for a, b in combinations(range(1, 6), 2)]
    local_new = [
        [-index - 1 for index in subset]
        for subset in combinations(range(1, 6), 4)
    ] + [[-1, -a - 1, -b - 1] for a, b in combinations(range(1, 6), 2)]
    truth_rows = []
    verified = True
    for bits in product((0, 1), repeat=6):
        old_holds = _clauses_hold(local_old, bits)
        new_holds = _clauses_hold(local_new, bits)
        intended = sum(bits) < 3 or (sum(bits) == 3 and bits[0] == 0)
        truth_rows.append({
            "bits": list(bits), "old_holds": old_holds,
            "new_holds": new_holds, "intended": intended,
        })
        verified = verified and old_holds == new_holds == intended
    report = seal({
        "schema_version": 1,
        "method": "weight6-coset-minimal-25-to-15-prime-clause-reduction-v1",
        "stabilizer_matrix_sha256": _matrix_sha256(rows), "row_count": 200,
        "row_weights": sorted(set(int(value) for value in rows.sum(axis=1))),
        "stabilizers_preserve_full_check_syndrome": preserves_checks,
        "stabilizers_preserve_full_logical_syndrome": preserves_logicals,
        "original_clause_count": len(original),
        "original_clause_sha256": canonical_sha256(original),
        "reduced_clause_count": len(reduced),
        "reduced_clause_sha256": canonical_sha256(reduced),
        "removed_subsumed_clause_count": len(subsumption),
        "subsumption_records_sha256": canonical_sha256(subsumption),
        "truth_table_assignments_checked": len(truth_rows),
        "truth_table_sha256": canonical_sha256(truth_rows),
        "truth_table_equivalent": bool(verified),
        "minimum_representative_lemma": (
            "a minimum-weight representative has overlap <=3 with each weight-6 "
            "stabilizer; a globally lexicographically least minimum representative "
            "has its smallest flipped coordinate zero whenever overlap is three"
        ),
        "coset_representative_reduction_sound": bool(
            preserves_checks and preserves_logicals and verified
            and len(subsumption) == 2000
        ),
    }, "report_sha256")
    if (
        report["original_clause_sha256"] != baseline.EXPECTED_OPTIONAL_COSET_EXTRA_SHA256
        or report["reduced_clause_sha256"] != EXPECTED_REDUCED_EXTRA_SHA256
        or report["coset_representative_reduction_sound"] is not True
    ):
        raise Dic5OptimizedCnfFinalV13Error("coset certificate mismatch")
    return reduced, report


def render_dimacs(cnf: Mapping[str, Any]) -> bytes:
    if cnf.get("native_atmost") is not None:
        raise Dic5OptimizedCnfFinalV13Error("native cardinality cannot be DIMACS")
    clauses = cnf["clauses"]
    chunks = [f"p cnf {int(cnf['num_variables'])} {len(clauses)}\n".encode()]
    chunks.extend(
        (" ".join(str(int(lit)) for lit in clause) + " 0\n").encode()
        for clause in clauses
    )
    return b"".join(chunks)


def build_optimized_instance() -> OptimizedInstance:
    prepared = baseline.prepare_instance()
    if prepared.report.get("preflight_sha256") != EXPECTED_BASELINE_PREFLIGHT_SHA256:
        raise Dic5OptimizedCnfFinalV13Error("final_v5 preflight changed")
    hx, hz, lx, lz = prepared.hx, prepared.hz, prepared.lx, prepared.lz
    full = baseline.build_css_threshold_cnf(
        hx, lx, max_weight=MAX_WEIGHT, sector=SECTOR,
        cardinality_encoding=CARDINALITY_ENCODING,
        partition_index=PARTITION_INDEX, anchor_indices=ANCHOR_INDICES,
    )
    if full["cnf_sha256"] != EXPECTED_BASELINE_CNF_SHA256:
        raise Dic5OptimizedCnfFinalV13Error("full final_v5 CNF changed")
    basis, rowspace = _rowspace_certificate(hx)
    active_logical = np.ascontiguousarray(lx[:1])
    active_full = baseline.build_css_threshold_cnf(
        hx, active_logical, max_weight=MAX_WEIGHT, sector=SECTOR,
        cardinality_encoding=CARDINALITY_ENCODING,
        partition_index=PARTITION_INDEX, anchor_indices=ANCHOR_INDICES,
    )
    projection = _logical_projection_certificate(full, active_full, hx, lx)
    reduced_plain = baseline.build_css_threshold_cnf(
        basis, active_logical, max_weight=MAX_WEIGHT, sector=SECTOR,
        cardinality_encoding=CARDINALITY_ENCODING,
        partition_index=PARTITION_INDEX, anchor_indices=ANCHOR_INDICES,
    )
    if (
        reduced_plain["cnf_sha256"] != EXPECTED_REDUCED_PLAIN_CNF_SHA256
        or reduced_plain["num_variables"] != EXPECTED_OPTIMIZED_NUM_VARIABLES
        or reduced_plain["num_clauses"] != 9022
    ):
        raise Dic5OptimizedCnfFinalV13Error("reduced official CNF changed")
    extra, coset = _coset_minimal_certificate(hz, hx, lx)
    optimized_cnf = dict(reduced_plain)
    optimized_cnf["clauses"] = list(reduced_plain["clauses"]) + extra
    optimized_cnf["num_clauses"] = len(optimized_cnf["clauses"])
    optimized_cnf["cnf_sha256"] = canonical_sha256({
        "num_variables": optimized_cnf["num_variables"],
        "clauses": optimized_cnf["clauses"],
        "native_atmost": optimized_cnf["native_atmost"],
    })
    dimacs = render_dimacs(optimized_cnf)
    dimacs_sha256 = hashlib.sha256(dimacs).hexdigest()
    if (
        optimized_cnf["num_variables"] != EXPECTED_OPTIMIZED_NUM_VARIABLES
        or optimized_cnf["num_clauses"] != EXPECTED_OPTIMIZED_NUM_CLAUSES
        or optimized_cnf["cnf_sha256"] != EXPECTED_OPTIMIZED_CNF_SHA256
        or len(dimacs) != EXPECTED_OPTIMIZED_DIMACS_BYTES
        or dimacs_sha256 != EXPECTED_OPTIMIZED_DIMACS_SHA256
    ):
        raise Dic5OptimizedCnfFinalV13Error("optimized CNF/DIMACS mismatch")
    report = seal({
        "schema_version": SCHEMA_VERSION, "gate": GATE, "solver_invoked": False,
        "baseline": {
            "name": "scripts.run_paper400_dic5_w6_lower_final_v5",
            "preflight": prepared.report,
            "preflight_sha256": prepared.report["preflight_sha256"],
            "default_timeout_s": baseline.DEFAULT_TIMEOUT_PER_SECTOR_S,
        },
        "candidate_bindings": {
            "matrix_sha256": prepared.report["matrix_sha256"],
            "logical_detector": prepared.report["logical_detector"],
            "w6": prepared.report["w6"], "parity": prepared.report["parity"],
            "logical_symmetry": prepared.report["logical_symmetry"],
            "xz_isometry": prepared.report["xz_isometry"],
            "target": prepared.report["target"],
        },
        "rowspace_certificate": rowspace,
        "logical_projection_certificate": projection,
        "coset_minimal_certificate": coset,
        "solver_contract": {
            "sector": SECTOR, "max_weight": MAX_WEIGHT,
            "partition_index": PARTITION_INDEX, "anchor_indices": [],
            "solver": SOLVER, "cardinality_encoding": CARDINALITY_ENCODING,
            "resume": False, "workers": 1,
            "execution_mode": "single-process-in-process-v1",
            "solver_budget_s": SOLVER_BUDGET_S,
            "required_outer_hard_timeout_s": REQUIRED_OUTER_HARD_TIMEOUT_S,
            "outer_watchdog_policy": OUTER_WATCHDOG_POLICY,
            "full_matrix_witness_replay": {"checks": "H_X", "logicals": "L_X"},
        },
        "cnf": {
            "formulation": FORMULATION,
            "official_reduced_plain_cnf_sha256": reduced_plain["cnf_sha256"],
            "extra_clause_sha256": coset["reduced_clause_sha256"],
            "cnf_sha256": optimized_cnf["cnf_sha256"],
            "num_variables": optimized_cnf["num_variables"],
            "num_clauses": optimized_cnf["num_clauses"],
            "dimacs_sha256": dimacs_sha256, "dimacs_bytes": len(dimacs),
        },
        "authority": {
            "sat_requires_full_matrix_official_replay": True,
            "unsat_is_current_source_lower_only": True,
            "hard_timeout_produces_no_valid_authoritative_terminal": True,
            "outer_watchdog_internally_enforced": False,
            "durable_drat_present": False, "durable_lrat_present": False,
            "publication_certificate": False, "upload_authorized": False,
            "unknown_is_unresolved": True,
        },
    }, "report_sha256")
    return OptimizedInstance(
        np.ascontiguousarray(hx), np.ascontiguousarray(hz),
        np.ascontiguousarray(lx), np.ascontiguousarray(lz), basis,
        active_logical, optimized_cnf, dimacs, report,
    )


EXPLICIT_SOURCE_RELATIVE_PATHS = (
    "evaluation/__init__.py", "evaluation/admissibility_policy.py",
    "evaluation/css_logical_detector.py", "evaluation/distance_milp.py",
    "evaluation/distance_sat.py",
    "evaluation/paper400_dic5_logical_symmetry/__init__.py",
    "evaluation/paper400_dic5_logical_symmetry_final.py",
    "evaluation/paper400_dic5_optimized_cnf_final_v13.py",
    "evaluation/paper400_dic5_xz_isometry.py", "evaluation/proof_runtime.py",
    "evaluation/strict_fom1525_policy.py", "evaluation/tanner_equivalence.py",
    "scripts/run_paper400_dic5_w6_lower_final_v5.py",
    "scripts/run_paper400_dic5_w6_optimized_cnf_final_v13.py",
)
CANONICAL_MODULE_BINDINGS = {
    "evaluation": "evaluation/__init__.py",
    "evaluation.admissibility_policy": "evaluation/admissibility_policy.py",
    "evaluation.css_logical_detector": "evaluation/css_logical_detector.py",
    "evaluation.distance_milp": "evaluation/distance_milp.py",
    "evaluation.distance_sat": "evaluation/distance_sat.py",
    "evaluation.paper400_dic5_logical_symmetry": (
        "evaluation/paper400_dic5_logical_symmetry/__init__.py"
    ),
    "evaluation.paper400_dic5_logical_symmetry_final": (
        "evaluation/paper400_dic5_logical_symmetry_final.py"
    ),
    "evaluation.paper400_dic5_optimized_cnf_final_v13": (
        "evaluation/paper400_dic5_optimized_cnf_final_v13.py"
    ),
    "evaluation.paper400_dic5_xz_isometry": "evaluation/paper400_dic5_xz_isometry.py",
    "evaluation.proof_runtime": "evaluation/proof_runtime.py",
    "evaluation.strict_fom1525_policy": "evaluation/strict_fom1525_policy.py",
    "evaluation.tanner_equivalence": "evaluation/tanner_equivalence.py",
    "scripts.run_paper400_dic5_w6_lower_final_v5": (
        "scripts/run_paper400_dic5_w6_lower_final_v5.py"
    ),
    "scripts.run_paper400_dic5_w6_optimized_cnf_final_v13": (
        "scripts/run_paper400_dic5_w6_optimized_cnf_final_v13.py"
    ),
}
RUNNER_RELATIVE_PATH = "scripts/run_paper400_dic5_w6_optimized_cnf_final_v13.py"
ALLOWED_ORIGINLESS_PROJECT_MODULES = frozenset({"scripts"})


def deterministic_source_closure() -> dict[str, Any]:
    expected_paths = set(EXPLICIT_SOURCE_RELATIVE_PATHS)
    files = {relative: file_sha256(PROJECT / relative) for relative in EXPLICIT_SOURCE_RELATIVE_PATHS}
    actual_paths: set[str] = set()
    canonical_runner_loaded = False
    for name, module in sorted(sys.modules.items()):
        if not (
            name == "evaluation" or name.startswith("evaluation.")
            or name == "scripts" or name.startswith("scripts.")
        ):
            continue
        origin = getattr(module, "__file__", None)
        if origin is None:
            if name not in ALLOWED_ORIGINLESS_PROJECT_MODULES:
                raise Dic5OptimizedCnfFinalV13Error(
                    f"unapproved originless project module: {name}"
                )
            continue
        path = Path(origin).resolve()
        if path.suffix == ".pyc" and Path(str(path)[:-1]).is_file():
            path = Path(str(path)[:-1])
        try:
            relative = path.relative_to(PROJECT.resolve()).as_posix()
        except ValueError as exc:
            raise Dic5OptimizedCnfFinalV13Error(
                f"project-named module outside project: {name}"
            ) from exc
        if CANONICAL_MODULE_BINDINGS.get(name) != relative:
            raise Dic5OptimizedCnfFinalV13Error(
                f"unapproved project module alias/source: {name}={relative}"
            )
        if relative not in expected_paths or file_sha256(path) != files[relative]:
            raise Dic5OptimizedCnfFinalV13Error("loaded source hash/path mismatch")
        actual_paths.add(relative)
        canonical_runner_loaded = canonical_runner_loaded or relative == RUNNER_RELATIVE_PATH
    main_origin = getattr(sys.modules.get("__main__"), "__file__", None)
    main_runner_alias = False
    if main_origin is not None:
        main_path = Path(main_origin).resolve()
        try:
            main_relative = main_path.relative_to(PROJECT.resolve()).as_posix()
        except ValueError:
            main_relative = None
        if main_relative is not None:
            if main_relative != RUNNER_RELATIVE_PATH:
                raise Dic5OptimizedCnfFinalV13Error(
                    f"unapproved project __main__ source: {main_relative}"
                )
            if file_sha256(main_path) != files[RUNNER_RELATIVE_PATH]:
                raise Dic5OptimizedCnfFinalV13Error("runner __main__ hash mismatch")
            main_runner_alias = True
            actual_paths.add(RUNNER_RELATIVE_PATH)
    if canonical_runner_loaded and main_runner_alias:
        raise Dic5OptimizedCnfFinalV13Error("runner loaded under two aliases")
    if actual_paths != expected_paths:
        raise Dic5OptimizedCnfFinalV13Error(
            "loaded physical source set mismatch: "
            f"missing={sorted(expected_paths - actual_paths)}, "
            f"extra={sorted(actual_paths - expected_paths)}"
        )
    return seal({
        "schema_version": SCHEMA_VERSION,
        "method": "deterministic-exact-physical-source-closure-v11",
        "files_sha256": files, "loaded_physical_sources": sorted(actual_paths),
        "canonical_module_bindings": CANONICAL_MODULE_BINDINGS,
        "allowed_originless_project_modules": sorted(ALLOWED_ORIGINLESS_PROJECT_MODULES),
        "allowed_runner_alias": {
            "canonical": "scripts.run_paper400_dic5_w6_optimized_cnf_final_v13",
            "direct_cli": "__main__", "relative_path": RUNNER_RELATIVE_PATH,
            "same_realpath_and_sha256_required": True,
        },
        "complete": True,
        "baseline": "scripts/run_paper400_dic5_w6_lower_final_v5.py",
    }, "closure_sha256")


def deterministic_runtime_seal() -> dict[str, Any]:
    modules: dict[str, dict[str, Any]] = {}
    for name in ("pysat", "pysat.solvers", "pysolvers"):
        spec = importlib.util.find_spec(name)
        origin = None if spec is None else spec.origin
        if origin is None:
            raise Dic5OptimizedCnfFinalV13Error(f"runtime module unavailable: {name}")
        path = Path(origin).resolve()
        modules[name] = {
            "origin_realpath": str(path),
            "file_sha256": file_sha256(path),
        }
    executable = Path(sys.executable).resolve(strict=True)
    return seal({
        "schema_version": 2,
        "method": "python-pysat-cadical-runtime-physical-seal-v2",
        "python_version": list(sys.version_info[:3]),
        "python_executable_realpath": str(executable),
        "python_executable_file_sha256": file_sha256(executable),
        "python_sat_version": importlib.metadata.version("python-sat"),
        "modules": modules,
    }, "runtime_sha256")


def _package_version(name: str) -> str | None:
    try:
        return importlib.metadata.version(name)
    except importlib.metadata.PackageNotFoundError:
        return None


def build_instance_binding(
    instance: OptimizedInstance, checkpoint_identity: Mapping[str, Any],
) -> dict[str, Any]:
    if type(checkpoint_identity) is not dict:
        raise Dic5OptimizedCnfFinalV13Error("checkpoint identity must be exact dict")
    return seal({
        "schema_version": SCHEMA_VERSION, "formulation": FORMULATION,
        "sector": SECTOR, "max_weight": MAX_WEIGHT,
        "partition_index": PARTITION_INDEX, "anchor_indices": [],
        "cardinality_encoding": CARDINALITY_ENCODING, "solver": SOLVER,
        "backend": {
            "distribution": "python-sat", "version": _package_version("python-sat"),
            "solver": SOLVER,
        },
        "workers": 1, "resume": False,
        "execution_mode": "single-process-in-process-v1",
        "solver_budget_s": SOLVER_BUDGET_S,
        "required_outer_hard_timeout_s": REQUIRED_OUTER_HARD_TIMEOUT_S,
        "outer_watchdog_policy": OUTER_WATCHDOG_POLICY,
        "candidate_preflight_sha256": instance.report["baseline"]["preflight_sha256"],
        "optimized_report_sha256": instance.report["report_sha256"],
        "full_check_matrix_sha256": _array_sha256("checks", instance.hx),
        "full_logical_matrix_sha256": _array_sha256("logicals", instance.lx),
        "basis_check_matrix_sha256": _array_sha256("checks", instance.basis_checks),
        "active_logical_matrix_sha256": _array_sha256("logicals", instance.active_logical),
        "cnf_sha256": instance.cnf["cnf_sha256"],
        "dimacs_sha256": hashlib.sha256(instance.dimacs).hexdigest(),
        "num_variables": instance.cnf["num_variables"],
        "num_clauses": instance.cnf["num_clauses"],
        "checkpoint_identity": json.loads(canonical_bytes(checkpoint_identity)),
        "native_thread_environment": {
            name: "1" for name in baseline.SAT_NATIVE_THREAD_ENV
        },
    }, "binding_sha256")


def _cnf_record(instance: OptimizedInstance) -> dict[str, Any]:
    return {
        "cnf_sha256": instance.cnf["cnf_sha256"],
        "dimacs_sha256": hashlib.sha256(instance.dimacs).hexdigest(),
        "num_variables": instance.cnf["num_variables"],
        "num_clauses": instance.cnf["num_clauses"],
        "extra_clause_sha256": instance.report["coset_minimal_certificate"]["reduced_clause_sha256"],
    }


def build_terminal_evidence(
    instance: OptimizedInstance, checkpoint_identity: Mapping[str, Any], *,
    outcome: str, full_model: np.ndarray | None = None,
    elapsed_s: float = 0.0, solver_time_s: float = 0.0,
    solver_stats: Mapping[str, int] | None = None,
    message: str | None = None,
) -> dict[str, Any]:
    if type(outcome) is not str:
        raise Dic5OptimizedCnfFinalV13Error("outcome must be exact string")
    if type(elapsed_s) is not float or type(solver_time_s) is not float:
        raise Dic5OptimizedCnfFinalV13Error("timings must be exact floats")
    statistics = {} if solver_stats is None else solver_stats
    if type(statistics) is not dict or any(
        type(key) is not str or type(value) is not int or value < 0
        for key, value in statistics.items()
    ):
        raise Dic5OptimizedCnfFinalV13Error("invalid solver stats types")
    model = None
    operator = objective = syndrome = None
    if full_model is not None:
        array = np.asarray(full_model)
        if array.ndim != 1 or array.size != int(instance.cnf["num_variables"]):
            raise Dic5OptimizedCnfFinalV13Error("full model must be exact one-dimensional size")
        if not np.all(np.logical_or(array == 0, array == 1)):
            raise Dic5OptimizedCnfFinalV13Error("full model must be binary")
        model = np.ascontiguousarray(array, dtype=np.uint8)
    if outcome == "sat":
        if model is None:
            raise Dic5OptimizedCnfFinalV13Error("SAT needs complete CNF model")
        vector = model[:OPERATOR_VARIABLES]
        operator = _pack_bits(vector)
        objective = int(vector.sum())
        syndrome = ((instance.lx @ vector) & 1).astype(int).tolist()
    elif model is not None:
        raise Dic5OptimizedCnfFinalV13Error("non-SAT evidence cannot carry model")
    terminal = outcome in {"sat", "unsat"}
    binding = build_instance_binding(instance, checkpoint_identity)
    return seal({
        "schema_version": SCHEMA_VERSION, "evidence_kind": EVIDENCE_KIND,
        "formulation": FORMULATION, "instance": binding,
        "cnf": _cnf_record(instance), "sector": SECTOR,
        "max_weight": MAX_WEIGHT, "cardinality_encoding": CARDINALITY_ENCODING,
        "backend": binding["backend"], "partition_index": PARTITION_INDEX,
        "anchor_indices": [], "solver_budget_s": SOLVER_BUDGET_S,
        "required_outer_hard_timeout_s": REQUIRED_OUTER_HARD_TIMEOUT_S,
        "outer_watchdog_policy": OUTER_WATCHDOG_POLICY,
        "resumed": False, "timed_out": False, "workers": 1,
        "random_seed": 0, "solver_invocations": 1,
        "execution_mode": "single-process-in-process-v1",
        "outcome": outcome, "status_name": outcome.upper(),
        "decision_complete": terminal, "threshold_infeasible": outcome == "unsat",
        "success": outcome == "sat", "retryable": not terminal,
        "message": message, "operator": operator, "objective": objective,
        "logical_syndrome": syndrome,
        "full_model": None if model is None else _pack_bits(model),
        "elapsed_s": elapsed_s, "solver_time_s": solver_time_s,
        "solver_stats": dict(statistics),
        "durable_proof": {"drat": False, "lrat": False},
        "publication_certificate": False, "upload_authorized": False,
    }, "evidence_sha256")


def _model_satisfies(instance: OptimizedInstance, model: np.ndarray) -> bool:
    if model.ndim != 1 or model.size != int(instance.cnf["num_variables"]):
        return False
    return all(any(
        bool(model[abs(int(literal)) - 1]) == (int(literal) > 0)
        for literal in clause
    ) for clause in instance.cnf["clauses"])


def _valid_timing(value: Any) -> bool:
    return type(value) is float and math.isfinite(value) and value >= 0.0


def _valid_solver_stats(value: Any) -> bool:
    return type(value) is dict and all(
        type(key) is str and type(counter) is int and counter >= 0
        for key, counter in value.items()
    )


def _valid_syndrome(value: Any, length: int) -> bool:
    return bool(
        type(value) is list and len(value) == length
        and all(type(bit) is int and bit in {0, 1} for bit in value)
    )


def classify_evidence(
    evidence: Mapping[str, Any], instance: OptimizedInstance,
    checkpoint_identity: Mapping[str, Any],
) -> dict[str, Any]:
    raw = dict(evidence) if type(evidence) is dict else {}
    failures: list[str] = []
    if set(raw) != EVIDENCE_FIELDS:
        failures.append("evidence field set mismatch")
    unsigned = dict(raw)
    stored_hash = unsigned.pop("evidence_sha256", None)
    try:
        if type(stored_hash) is not str or stored_hash != canonical_sha256(unsigned):
            failures.append("evidence self-hash mismatch")
    except (TypeError, ValueError):
        failures.append("evidence is not canonical JSON")
    expected_instance = build_instance_binding(instance, checkpoint_identity)
    common = {
        "schema_version": SCHEMA_VERSION, "evidence_kind": EVIDENCE_KIND,
        "formulation": FORMULATION, "instance": expected_instance,
        "cnf": _cnf_record(instance), "sector": SECTOR,
        "max_weight": MAX_WEIGHT, "cardinality_encoding": CARDINALITY_ENCODING,
        "backend": expected_instance["backend"], "partition_index": PARTITION_INDEX,
        "anchor_indices": [], "solver_budget_s": SOLVER_BUDGET_S,
        "required_outer_hard_timeout_s": REQUIRED_OUTER_HARD_TIMEOUT_S,
        "outer_watchdog_policy": OUTER_WATCHDOG_POLICY,
        "resumed": False, "timed_out": False, "workers": 1,
        "random_seed": 0, "solver_invocations": 1,
        "execution_mode": "single-process-in-process-v1",
        "durable_proof": {"drat": False, "lrat": False},
        "publication_certificate": False, "upload_authorized": False,
    }
    for key, expected in common.items():
        if not json_type_equal(raw.get(key), expected):
            failures.append(f"{key} binding/type mismatch")
    for key in ("elapsed_s", "solver_time_s"):
        if not _valid_timing(raw.get(key)):
            failures.append(f"{key} must be finite nonnegative float")
    if _valid_timing(raw.get("elapsed_s")) and raw["elapsed_s"] > SOLVER_BUDGET_S:
        failures.append("elapsed_s exceeds solver budget")
    if (
        _valid_timing(raw.get("elapsed_s"))
        and _valid_timing(raw.get("solver_time_s"))
        and raw["solver_time_s"] > raw["elapsed_s"]
    ):
        failures.append("solver_time_s exceeds elapsed_s")
    if not _valid_solver_stats(raw.get("solver_stats")):
        failures.append("solver_stats type mismatch")
    outcome = raw.get("outcome")
    if type(outcome) is not str:
        failures.append("outcome must be string")
    if type(raw.get("status_name")) is not str or raw.get("status_name") != str(outcome).upper():
        failures.append("status_name mismatch")
    witness_failures: list[str] = []
    model_valid = False
    syndrome_valid = False
    if outcome == "sat":
        try:
            model = _unpack_bits(raw.get("full_model"), expected_length=int(instance.cnf["num_variables"]))
            operator = _unpack_bits(raw.get("operator"), expected_length=OPERATOR_VARIABLES)
        except Dic5OptimizedCnfFinalV13Error as exc:
            failures.append(f"invalid SAT model/operator: {exc}")
        else:
            model_valid = bool(
                _model_satisfies(instance, model)
                and np.array_equal(model[:OPERATOR_VARIABLES], operator)
            )
            if not model_valid:
                failures.append("complete model does not satisfy optimized CNF")
        syndrome_valid = _valid_syndrome(raw.get("logical_syndrome"), instance.lx.shape[0])
        if not syndrome_valid:
            failures.append("logical_syndrome type mismatch")
        witness_failures = baseline.verify_css_threshold_sat_witness(
            raw, instance.hx, instance.lx
        )
    strict_sat = bool(
        outcome == "sat" and raw.get("decision_complete") is True
        and raw.get("threshold_infeasible") is False
        and raw.get("success") is True and raw.get("retryable") is False
        and raw.get("message") is None and type(raw.get("objective")) is int
        and 0 <= raw.get("objective") <= MAX_WEIGHT and model_valid
        and syndrome_valid and not failures and not witness_failures
    )
    strict_unsat = bool(
        outcome == "unsat" and raw.get("decision_complete") is True
        and raw.get("threshold_infeasible") is True
        and raw.get("success") is False and raw.get("retryable") is False
        and raw.get("message") is None and raw.get("operator") is None
        and raw.get("objective") is None and raw.get("logical_syndrome") is None
        and raw.get("full_model") is None and not failures
    )
    if strict_sat:
        status, lower_bound = "REJECTED_LOW_OPERATOR", None
    elif strict_unsat:
        status, lower_bound = "CURRENT_SOURCE_LOWER_20", 20
    else:
        status, lower_bound = "UNRESOLVED", None
    return seal({
        "schema_version": SCHEMA_VERSION, "gate": GATE, "status": status,
        "distance_lower_bound": lower_bound,
        "strict_verified_sat_rejection": strict_sat,
        "strict_current_source_unsat": strict_unsat,
        "official_full_matrix_witness_verifier_invoked": outcome == "sat",
        "official_full_matrix_witness_failures": witness_failures,
        "binding_failures": failures, "evidence": raw,
        "publication_certificate": False, "upload_authorized": False,
        "publication_blocker": (
            "durable independently checked DRAT/LRAT proof is absent"
            if strict_unsat else None
        ),
    }, "record_sha256")


def solve_optimized_instance_in_process(
    instance: OptimizedInstance, checkpoint_identity: Mapping[str, Any],
) -> dict[str, Any]:
    bad_environment = {
        name: os.environ.get(name) for name in baseline.THREAD_ENV
        if os.environ.get(name) != "1"
    }
    if bad_environment:
        raise Dic5OptimizedCnfFinalV13Error(
            f"native thread environment is not sealed: {bad_environment}"
        )
    from pysat.solvers import Solver

    started = time.monotonic()
    with Solver(
        name=SOLVER, bootstrap_with=instance.cnf["clauses"], use_timer=True,
    ) as solver:
        satisfiable = solver.solve()
        model_literals = solver.get_model() if satisfiable is True else None
        solver_time = float(solver.time())
        try:
            statistics = solver.accum_stats()
        except (AttributeError, RuntimeError):
            statistics = {}
    if satisfiable is True:
        outcome = "sat"
    elif satisfiable is False:
        outcome = "unsat"
    else:
        raise Dic5OptimizedCnfFinalV13Error("solver returned non-bool/UNKNOWN")
    assignment = None
    if outcome == "sat":
        assignment = np.zeros(instance.cnf["num_variables"], dtype=np.uint8)
        for literal in model_literals or []:
            variable = abs(int(literal))
            if 1 <= variable <= assignment.size:
                assignment[variable - 1] = int(literal > 0)
    return build_terminal_evidence(
        instance, checkpoint_identity, outcome=outcome, full_model=assignment,
        elapsed_s=float(time.monotonic() - started), solver_time_s=solver_time,
        solver_stats=statistics, message=None,
    )


SolverCallback = Callable[..., Mapping[str, Any]]


__all__ = [
    "Dic5OptimizedCnfFinalV13Error", "EVIDENCE_FIELDS",
    "EXPECTED_OPTIMIZED_CNF_SHA256", "EXPECTED_OPTIMIZED_DIMACS_SHA256",
    "OptimizedInstance", "OUTER_WATCHDOG_POLICY",
    "REQUIRED_OUTER_HARD_TIMEOUT_S", "SOLVER_BUDGET_S",
    "build_instance_binding", "build_optimized_instance",
    "build_terminal_evidence", "canonical_bytes", "canonical_sha256",
    "classify_evidence", "deterministic_runtime_seal",
    "deterministic_source_closure", "file_sha256", "json_type_equal",
    "render_dimacs", "seal", "solve_optimized_instance_in_process",
]
