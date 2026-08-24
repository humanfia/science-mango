#!/usr/bin/env python3
"""No-solver 16-cube cover for the paper400 Dic5 optimized final_v13 CNF.

This module never imports a solver class and never calls a solver.  It binds a
fixed final_v13 base CNF, appends four physical-operator unit clauses for each
of all 2**4 assignments, and emits/verifies a self-hashed coverage manifest.

The cover certificate and solver-result aggregation are deliberately
separate.  A verified SAT result must contain a complete cube-CNF model and is
replayed with the full H_X/L_X official witness verifier.  A lower-bound
classification requires one clean UNSAT terminal for every cube.  Any missing,
duplicate, UNKNOWN, timeout, malformed, or unbound terminal is UNRESOLVED.

Proofless UNSAT remains current-source evidence.  The production manifest
binds the exact final_v13 module/runner/test sources independently audited
PASS, but never upgrades proofless UNSAT into a publication certificate.
"""

from __future__ import annotations

import argparse
import hashlib
import json
import math
import os
import sys
from itertools import combinations, product
from pathlib import Path
from typing import Any, Mapping, Sequence

import numpy as np


PROJECT = Path(__file__).resolve().parent.parent
if str(PROJECT) not in sys.path:
    sys.path.insert(0, str(PROJECT))

from evaluation import paper400_dic5_optimized_cnf_final_v13 as optimized  # noqa: E402


SCHEMA_VERSION = 1
MANIFEST_KIND = "paper400-dic5-final-v13-physical-cube-cover-v1"
RESULT_KIND = "paper400-dic5-final-v13-cube-terminal-v1"
AGGREGATE_KIND = "paper400-dic5-final-v13-cube-aggregate-v1"
COVER_FORMULATION = "all-assignments-four-physical-unit-cubes-v1"

EXPECTED_BASE_CNF_SHA256 = (
    "3ca7bbc31792b27363af4dd56ca79facf1501a1a97d66d64b5684b3597191537"
)
EXPECTED_BASE_DIMACS_SHA256 = (
    "0e4c96f4f002f956d12ff9d3f50d6487d389afcea63d02177fc2a29c4755bd07"
)
EXPECTED_BASE_NUM_VARIABLES = 2955
EXPECTED_BASE_NUM_CLAUSES = 12022
EXPECTED_OPERATOR_VARIABLES = 400
EXPECTED_MAX_WEIGHT = 18
EXPECTED_DISTANCE_LOWER_BOUND = 20

# DIMACS variables, hence physical qubit indices are one less.  These are the
# deterministic outcome of the static selection certificate below.
DEFAULT_SPLIT_VARIABLES = (173, 180, 195, 212)

AUTHORITY_AUDITED_BASE = "AUDITED_BASE"
AUTHORITY_TEST_ONLY = "SYNTHETIC_TEST_ONLY"

AUDITED_SOURCE_FILES = (
    (
        "evaluation/paper400_dic5_optimized_cnf_final_v13.py",
        "5f55709382a7f6d2087199440d9e53351114e0a32129eaabc584464409ce6ee2",
    ),
    (
        "scripts/run_paper400_dic5_w6_optimized_cnf_final_v13.py",
        "f1f89ff6996d92b38a855660d2d1d70a18793095961c3ebd9f9bae3d64376e2b",
    ),
    (
        "tests/test_paper400_dic5_optimized_cnf_final_v13_final2.py",
        "7b0fe015c7fefdafdcf9367d63524ba7a56a0a32498ce125742c367ba910e672",
    ),
)

MANIFEST_FIELDS = frozenset({
    "schema_version", "manifest_kind", "cover_formulation", "base",
    "split", "coverage", "cubes", "aggregation_policy",
    "resource_estimate", "test_only", "manifest_sha256",
})
RESULT_FIELDS = frozenset({
    "schema_version", "evidence_kind", "manifest_sha256",
    "base_cnf_sha256", "cube_index", "cube_id", "cube_sha256",
    "cube_cnf_sha256", "solver", "invocation_sha256", "outcome",
    "status_name", "decision_complete", "clean_exit", "timed_out",
    "solver_invocations", "full_model", "operator", "objective",
    "logical_syndrome", "elapsed_s", "solver_time_s", "solver_stats",
    "durable_proof", "test_only", "result_sha256",
})


class Cube16Error(RuntimeError):
    """The cube cover, artifact, terminal, or binding is malformed."""


def _canonical_bytes(value: Any) -> bytes:
    return json.dumps(
        value,
        sort_keys=True,
        separators=(",", ":"),
        ensure_ascii=False,
        allow_nan=False,
    ).encode("utf-8")


def _canonical_sha256(value: Any) -> str:
    return hashlib.sha256(_canonical_bytes(value)).hexdigest()


def _seal(value: Mapping[str, Any], field: str) -> dict[str, Any]:
    result = dict(value)
    result.pop(field, None)
    result[field] = _canonical_sha256(result)
    return result


def _is_sha256(value: Any) -> bool:
    if type(value) is not str or len(value) != 64:
        return False
    try:
        return bytes.fromhex(value).hex() == value
    except ValueError:
        return False


def _file_sha256(path: Path) -> str:
    target = Path(path)
    if target.is_symlink() or not target.is_file():
        raise Cube16Error(f"not a regular file: {target}")
    before = target.stat()
    payload = target.read_bytes()
    after = target.stat()
    identity_before = (
        before.st_dev, before.st_ino, before.st_size, before.st_mtime_ns,
        before.st_ctime_ns,
    )
    identity_after = (
        after.st_dev, after.st_ino, after.st_size, after.st_mtime_ns,
        after.st_ctime_ns,
    )
    if identity_before != identity_after or len(payload) != before.st_size:
        raise Cube16Error(f"file changed while hashing: {target}")
    return hashlib.sha256(payload).hexdigest()


def _audited_base_binding() -> dict[str, Any]:
    files = []
    for relative_path, expected_sha256 in AUDITED_SOURCE_FILES:
        actual_sha256 = _file_sha256(PROJECT / relative_path)
        if actual_sha256 != expected_sha256:
            raise Cube16Error(
                f"independently audited source changed: {relative_path}"
            )
        files.append({
            "relative_path": relative_path,
            "sha256": actual_sha256,
        })
    return _seal({
        "schema_version": 1,
        "status": "PASS",
        "authority": AUTHORITY_AUDITED_BASE,
        "method": "independent-clean-preflight-and-focused-fake-fixture-audit-v1",
        "audited_files": files,
        "clean_preflight_passed": True,
        "focused_pytest": {
            "passed": 21,
            "failed": 0,
            "test_file": (
                "tests/test_paper400_dic5_optimized_cnf_final_v13_final2.py"
            ),
        },
        "base_cnf_sha256": EXPECTED_BASE_CNF_SHA256,
        "base_dimacs_sha256": EXPECTED_BASE_DIMACS_SHA256,
        "solver_invoked_by_audit": False,
        "publication_certificate": False,
    }, "audit_binding_sha256")


def _cnf_sha256(
    *, num_variables: int, clauses: Sequence[Sequence[int]], native_atmost: Any,
) -> str:
    return _canonical_sha256({
        "num_variables": int(num_variables),
        "clauses": [[int(literal) for literal in clause] for clause in clauses],
        "native_atmost": native_atmost,
    })


def _render_dimacs(
    *, num_variables: int, clauses: Sequence[Sequence[int]],
) -> bytes:
    chunks = [f"p cnf {int(num_variables)} {len(clauses)}\n".encode("ascii")]
    chunks.extend(
        (" ".join(str(int(literal)) for literal in clause) + " 0\n").encode(
            "ascii"
        )
        for clause in clauses
    )
    return b"".join(chunks)


def _pack_bits(bits: Sequence[int] | np.ndarray) -> dict[str, Any]:
    vector = np.asarray(bits, dtype=np.uint8).reshape(-1)
    if not np.all(np.logical_or(vector == 0, vector == 1)):
        raise Cube16Error("packed vector must be binary")
    packed = np.packbits(vector, bitorder="little").tobytes()
    return {
        "length": int(vector.size),
        "weight": int(vector.sum()),
        "packed_hex": packed.hex(),
        "sha256": hashlib.sha256(
            f"{vector.size}:".encode("ascii") + packed
        ).hexdigest(),
    }


def _unpack_bits(record: Any, *, expected_length: int) -> np.ndarray:
    if type(record) is not dict or set(record) != {
        "length", "weight", "packed_hex", "sha256",
    }:
        raise Cube16Error("packed vector field set mismatch")
    if type(record["length"]) is not int or record["length"] != expected_length:
        raise Cube16Error("packed vector length mismatch")
    if type(record["weight"]) is not int:
        raise Cube16Error("packed vector weight type mismatch")
    if type(record["packed_hex"]) is not str or type(record["sha256"]) is not str:
        raise Cube16Error("packed vector string type mismatch")
    try:
        payload = bytes.fromhex(record["packed_hex"])
    except ValueError as exc:
        raise Cube16Error("packed vector hex is invalid") from exc
    if len(payload) != (expected_length + 7) // 8:
        raise Cube16Error("packed vector byte length mismatch")
    vector = np.unpackbits(
        np.frombuffer(payload, dtype=np.uint8), bitorder="little"
    )[:expected_length].astype(np.uint8)
    if not optimized.json_type_equal(record, _pack_bits(vector)):
        raise Cube16Error("packed vector canonical replay mismatch")
    return vector


def _literal_occurrences(
    clauses: Sequence[Sequence[int]], *, physical_variables: int,
) -> tuple[dict[int, int], dict[int, int], dict[int, frozenset[int]]]:
    positive = {variable: 0 for variable in range(1, physical_variables + 1)}
    negative = {variable: 0 for variable in range(1, physical_variables + 1)}
    incidence: dict[int, set[int]] = {
        variable: set() for variable in range(1, physical_variables + 1)
    }
    for clause_index, clause in enumerate(clauses):
        for raw_literal in clause:
            literal = int(raw_literal)
            variable = abs(literal)
            if not 1 <= variable <= physical_variables:
                continue
            if literal > 0:
                positive[variable] += 1
            else:
                negative[variable] += 1
            incidence[variable].add(clause_index)
    return positive, negative, {
        variable: frozenset(indices) for variable, indices in incidence.items()
    }


def _select_split_variables(
    clauses: Sequence[Sequence[int]],
) -> tuple[tuple[int, ...], dict[str, Any]]:
    """Select high two-sided-occurrence, minimally skewed, disjoint variables."""

    positive, negative, incidence = _literal_occurrences(
        clauses, physical_variables=EXPECTED_OPERATOR_VARIABLES
    )
    balance_floor = max(
        min(positive[variable], negative[variable])
        for variable in range(1, EXPECTED_OPERATOR_VARIABLES + 1)
    )
    first_pool = [
        variable for variable in range(1, EXPECTED_OPERATOR_VARIABLES + 1)
        if min(positive[variable], negative[variable]) == balance_floor
    ]
    minimum_imbalance = min(
        abs(positive[variable] - negative[variable]) for variable in first_pool
    )
    eligible = [
        variable for variable in first_pool
        if abs(positive[variable] - negative[variable]) == minimum_imbalance
    ]
    selected: list[int] = []
    for variable in eligible:
        if all(not (incidence[variable] & incidence[prior]) for prior in selected):
            selected.append(variable)
            if len(selected) == 4:
                break
    if len(selected) != 4:
        raise Cube16Error("static selector found fewer than four disjoint variables")
    pair_records = [
        {
            "left": left,
            "right": right,
            "shared_clause_count": len(incidence[left] & incidence[right]),
        }
        for left, right in combinations(selected, 2)
    ]
    records = [
        {
            "dimacs_variable": variable,
            "physical_qubit_index_zero_based": variable - 1,
            "positive_occurrences": positive[variable],
            "negative_occurrences": negative[variable],
            "total_occurrences": positive[variable] + negative[variable],
            "sign_imbalance": abs(positive[variable] - negative[variable]),
            "incident_clause_count": len(incidence[variable]),
        }
        for variable in selected
    ]
    certificate = _seal({
        "schema_version": 1,
        "method": (
            "maximize-min-sign-occurrence-then-minimize-sign-imbalance-"
            "then-lexicographic-pairwise-clause-disjoint-v1"
        ),
        "physical_variable_interval_dimacs": [1, EXPECTED_OPERATOR_VARIABLES],
        "maximum_min_sign_occurrence": balance_floor,
        "minimum_sign_imbalance_at_maximum": minimum_imbalance,
        "eligible_variable_count": len(eligible),
        "eligible_variables_sha256": _canonical_sha256(eligible),
        "selected_variables": selected,
        "selected_occurrences": records,
        "pairwise_clause_overlap": pair_records,
        "pairwise_clause_disjoint": all(
            record["shared_clause_count"] == 0 for record in pair_records
        ),
    }, "certificate_sha256")
    return tuple(selected), certificate


def _direct_restriction_profile(
    clauses: Sequence[Sequence[int]], assignment: Mapping[int, int],
) -> dict[str, Any]:
    satisfied_clause_count = 0
    touched_clause_count = 0
    falsified_literal_count = 0
    residual_literal_count = 0
    residual_unit_clause_count = 0
    residual_empty_clause_count = 0
    for clause in clauses:
        touched = False
        satisfied = False
        residual: list[int] = []
        for raw_literal in clause:
            literal = int(raw_literal)
            variable = abs(literal)
            if variable not in assignment:
                residual.append(literal)
                continue
            touched = True
            value = assignment[variable]
            if bool(value) == (literal > 0):
                satisfied = True
            else:
                falsified_literal_count += 1
        if touched:
            touched_clause_count += 1
        if satisfied:
            satisfied_clause_count += 1
            continue
        residual_literal_count += len(residual)
        if len(residual) == 1:
            residual_unit_clause_count += 1
        elif len(residual) == 0:
            residual_empty_clause_count += 1
    return {
        "method": "direct-four-variable-restriction-without-propagation-v1",
        "satisfied_base_clause_count": satisfied_clause_count,
        "touched_base_clause_count": touched_clause_count,
        "falsified_selected_literal_count": falsified_literal_count,
        "residual_clause_count": len(clauses) - satisfied_clause_count,
        "residual_literal_count": residual_literal_count,
        "residual_unit_clause_count": residual_unit_clause_count,
        "residual_empty_clause_count": residual_empty_clause_count,
        "unit_propagation_performed": False,
        "solver_invoked": False,
    }


def _cube_record(
    *,
    base_clauses: Sequence[Sequence[int]],
    num_variables: int,
    split_variables: Sequence[int],
    cube_index: int,
    bits: Sequence[int],
) -> tuple[dict[str, Any], bytes]:
    bit_list = [int(bit) for bit in bits]
    variables = [int(variable) for variable in split_variables]
    if len(bit_list) != len(variables) or any(bit not in {0, 1} for bit in bit_list):
        raise Cube16Error("invalid cube assignment")
    expected_index = sum(
        bit << (len(bit_list) - position - 1)
        for position, bit in enumerate(bit_list)
    )
    if cube_index != expected_index:
        raise Cube16Error("cube index/binary assignment mismatch")
    assignment = dict(zip(variables, bit_list, strict=True))
    unit_clauses = [
        [variable if assignment[variable] else -variable]
        for variable in variables
    ]
    cube_clauses = [list(map(int, clause)) for clause in base_clauses]
    cube_clauses.extend(unit_clauses)
    cnf_sha256 = _cnf_sha256(
        num_variables=num_variables,
        clauses=cube_clauses,
        native_atmost=None,
    )
    dimacs = _render_dimacs(
        num_variables=num_variables,
        clauses=cube_clauses,
    )
    bit_string = "".join(str(bit) for bit in bit_list)
    record = _seal({
        "schema_version": 1,
        "cube_index": cube_index,
        "cube_id": f"cube-{bit_string}",
        "assignment_bits": bit_list,
        "assignment_by_dimacs_variable": [
            {"dimacs_variable": variable, "value": assignment[variable]}
            for variable in variables
        ],
        "unit_clauses": unit_clauses,
        "unit_clauses_sha256": _canonical_sha256(unit_clauses),
        "cube_cnf_sha256": cnf_sha256,
        "cube_dimacs_sha256": hashlib.sha256(dimacs).hexdigest(),
        "cube_num_variables": num_variables,
        "cube_num_clauses": len(cube_clauses),
        "cube_dimacs_bytes": len(dimacs),
        "dimacs_relative_path": f"cubes/cube-{bit_string}.cnf",
        "static_restriction_profile": _direct_restriction_profile(
            base_clauses, assignment
        ),
    }, "cube_sha256")
    return record, dimacs


def _strict_base_failures(instance: optimized.OptimizedInstance) -> list[str]:
    failures: list[str] = []
    cnf = instance.cnf
    dimacs_sha256 = hashlib.sha256(instance.dimacs).hexdigest()
    expected = {
        "cnf_sha256": EXPECTED_BASE_CNF_SHA256,
        "num_variables": EXPECTED_BASE_NUM_VARIABLES,
        "num_clauses": EXPECTED_BASE_NUM_CLAUSES,
        "native_atmost": None,
        "operator_variables": list(range(1, EXPECTED_OPERATOR_VARIABLES + 1)),
    }
    for key, value in expected.items():
        if not optimized.json_type_equal(cnf.get(key), value):
            failures.append(f"base {key} mismatch")
    if dimacs_sha256 != EXPECTED_BASE_DIMACS_SHA256:
        failures.append("base DIMACS SHA-256 mismatch")
    if instance.dimacs != _render_dimacs(
        num_variables=int(cnf.get("num_variables", -1)),
        clauses=cnf.get("clauses", []),
    ):
        failures.append("base DIMACS byte replay mismatch")
    if cnf.get("cnf_sha256") != _cnf_sha256(
        num_variables=int(cnf.get("num_variables", -1)),
        clauses=cnf.get("clauses", []),
        native_atmost=cnf.get("native_atmost"),
    ):
        failures.append("base canonical CNF SHA-256 replay mismatch")
    if instance.hx.shape != (200, 400) or instance.lx.shape != (16, 400):
        failures.append("full H_X/L_X shape mismatch")
    if instance.report.get("solver_invoked") is not False:
        failures.append("optimized builder did not report zero-solver construction")
    return failures


def build_coverage_manifest(
    instance: optimized.OptimizedInstance,
    *,
    authority_status: str = AUTHORITY_AUDITED_BASE,
    strict_base: bool = True,
    split_variables: Sequence[int] | None = None,
) -> dict[str, Any]:
    """Build the canonical zero-solver cover manifest in memory."""

    if strict_base:
        failures = _strict_base_failures(instance)
        if failures:
            raise Cube16Error("; ".join(failures))
        selected, selection = _select_split_variables(instance.cnf["clauses"])
        if selected != DEFAULT_SPLIT_VARIABLES:
            raise Cube16Error(
                f"frozen split variables changed: {selected!r}"
            )
        if split_variables is not None and tuple(split_variables) != selected:
            raise Cube16Error("production split variables are frozen")
        test_only = False
        if authority_status != AUTHORITY_AUDITED_BASE:
            raise Cube16Error("production base must match the frozen independent audit")
        audit_binding = _audited_base_binding()
    else:
        selected = tuple(
            int(variable) for variable in (
                split_variables if split_variables is not None else (1, 2, 3, 4)
            )
        )
        if (
            len(selected) != 4 or len(set(selected)) != 4
            or any(not 1 <= variable <= EXPECTED_OPERATOR_VARIABLES for variable in selected)
        ):
            raise Cube16Error("test split needs four distinct physical variables")
        positive, negative, incidence = _literal_occurrences(
            instance.cnf["clauses"],
            physical_variables=EXPECTED_OPERATOR_VARIABLES,
        )
        selection = _seal({
            "schema_version": 1,
            "method": "explicit-synthetic-test-only-v1",
            "selected_variables": list(selected),
            "selected_occurrences": [
                {
                    "dimacs_variable": variable,
                    "physical_qubit_index_zero_based": variable - 1,
                    "positive_occurrences": positive[variable],
                    "negative_occurrences": negative[variable],
                    "total_occurrences": positive[variable] + negative[variable],
                    "sign_imbalance": abs(positive[variable] - negative[variable]),
                    "incident_clause_count": len(incidence[variable]),
                }
                for variable in selected
            ],
            "pairwise_clause_overlap": [
                {
                    "left": left,
                    "right": right,
                    "shared_clause_count": len(incidence[left] & incidence[right]),
                }
                for left, right in combinations(selected, 2)
            ],
            "pairwise_clause_disjoint": all(
                not (incidence[left] & incidence[right])
                for left, right in combinations(selected, 2)
            ),
        }, "certificate_sha256")
        test_only = True
        authority_status = AUTHORITY_TEST_ONLY
        audit_binding = None

    base_clauses = [list(map(int, clause)) for clause in instance.cnf["clauses"]]
    num_variables = int(instance.cnf["num_variables"])
    cubes: list[dict[str, Any]] = []
    cube_dimacs: list[bytes] = []
    assignments = [list(bits) for bits in product((0, 1), repeat=4)]
    for cube_index, bits in enumerate(assignments):
        cube, dimacs = _cube_record(
            base_clauses=base_clauses,
            num_variables=num_variables,
            split_variables=selected,
            cube_index=cube_index,
            bits=bits,
        )
        cubes.append(cube)
        cube_dimacs.append(dimacs)

    pairwise_separation = []
    for left, right in combinations(cubes, 2):
        differences = [
            index for index, (left_bit, right_bit) in enumerate(zip(
                left["assignment_bits"], right["assignment_bits"], strict=True
            ))
            if left_bit != right_bit
        ]
        pairwise_separation.append({
            "left_cube_index": left["cube_index"],
            "right_cube_index": right["cube_index"],
            "differing_positions": differences,
        })
    mutually_exclusive = bool(
        len(pairwise_separation) == 120
        and all(record["differing_positions"] for record in pairwise_separation)
    )
    exhaustive = assignments == [list(bits) for bits in product((0, 1), repeat=4)]

    profiles = [cube["static_restriction_profile"] for cube in cubes]
    source_path = Path(optimized.__file__).resolve()
    distance_sat_path = PROJECT / "evaluation/distance_sat.py"
    report = instance.report
    base = {
        "gate": optimized.GATE,
        "formulation": optimized.FORMULATION,
        "authority_status": authority_status,
        "audit_binding": audit_binding,
        "optimized_module_relative_path": source_path.relative_to(PROJECT).as_posix(),
        "optimized_module_sha256": _file_sha256(source_path),
        "variable_semantics_source_relative_path": "evaluation/distance_sat.py",
        "variable_semantics_source_sha256": _file_sha256(distance_sat_path),
        "operator_variable_semantics": (
            "DIMACS variable v in 1..400 is the support bit of physical qubit "
            "index v-1; variables 401..num_variables are definitional/cardinality auxiliaries"
        ),
        "operator_variable_interval_dimacs": [1, EXPECTED_OPERATOR_VARIABLES],
        "auxiliary_variable_interval_dimacs": [
            EXPECTED_OPERATOR_VARIABLES + 1, num_variables,
        ],
        "full_matrix_witness_replay": {"checks": "H_X", "logicals": "L_X"},
        "full_check_matrix_sha256": optimized._array_sha256("checks", instance.hx),
        "full_logical_matrix_sha256": optimized._array_sha256("logicals", instance.lx),
        "optimized_report_sha256": report.get("report_sha256"),
        "candidate_preflight_sha256": report.get("baseline", {}).get(
            "preflight_sha256"
        ),
        "cnf_sha256": instance.cnf["cnf_sha256"],
        "dimacs_sha256": hashlib.sha256(instance.dimacs).hexdigest(),
        "num_variables": num_variables,
        "num_clauses": len(base_clauses),
        "dimacs_bytes": len(instance.dimacs),
        "native_atmost": instance.cnf.get("native_atmost"),
        "base_dimacs_relative_path": "base/optimized-final-v13.cnf",
    }
    split = {
        "variable_count": 4,
        "variables_dimacs": list(selected),
        "physical_qubit_indices_zero_based": [variable - 1 for variable in selected],
        "selection_certificate": selection,
    }
    coverage = {
        "method": "explicit-cartesian-product-replay-v1",
        "assignment_domain": [0, 1],
        "assignment_order": "lexicographic bits; leftmost bit is most significant",
        "cube_index_formula": (
            "sum(assignment_bits[j] * 2**(3-j) for j in range(4))"
        ),
        "expected_assignment_count": 16,
        "observed_assignment_count": len(assignments),
        "assignments_sha256": _canonical_sha256(assignments),
        "cube_sha256_sequence_sha256": _canonical_sha256([
            cube["cube_sha256"] for cube in cubes
        ]),
        "cube_cnf_sha256_sequence_sha256": _canonical_sha256([
            cube["cube_cnf_sha256"] for cube in cubes
        ]),
        "pair_count_checked": len(pairwise_separation),
        "pairwise_separation_sha256": _canonical_sha256(pairwise_separation),
        "mutually_exclusive": mutually_exclusive,
        "exhaustive": exhaustive,
        "equivalence_statement": "F iff OR_i(F AND cube_i)",
        "proof": (
            "every total Boolean valuation has exactly one restriction to the four "
            "selected variables; distinct 4-bit restrictions disagree on at least "
            "one variable"
        ),
    }
    aggregation_policy = {
        "sat_rule": (
            "complete cube-CNF model plus full H_X/L_X official matrix replay "
            "is required before candidate rejection"
        ),
        "lower_rule": (
            "exactly one bound clean UNSAT terminal for each of all 16 cubes is "
            "required for a current-source distance lower bound"
        ),
        "unknown_rule": (
            "any UNKNOWN, timeout, missing, duplicate, malformed, or unbound cube "
            "leaves the aggregate UNRESOLVED"
        ),
        "all_unsat_distance_lower_bound": EXPECTED_DISTANCE_LOWER_BOUND,
        "proofless_unsat_authority": "current-source-only",
        "durable_publication_proof_required_separately": True,
    }
    resource_estimate = {
        "method": "static-artifact-and-direct-restriction-profile-v1",
        "base_dimacs_bytes": len(instance.dimacs),
        "all_16_cube_dimacs_bytes": sum(len(payload) for payload in cube_dimacs),
        "min_cube_dimacs_bytes": min(map(len, cube_dimacs)),
        "max_cube_dimacs_bytes": max(map(len, cube_dimacs)),
        "min_residual_clause_count_without_propagation": min(
            profile["residual_clause_count"] for profile in profiles
        ),
        "max_residual_clause_count_without_propagation": max(
            profile["residual_clause_count"] for profile in profiles
        ),
        "min_residual_literal_count_without_propagation": min(
            profile["residual_literal_count"] for profile in profiles
        ),
        "max_residual_literal_count_without_propagation": max(
            profile["residual_literal_count"] for profile in profiles
        ),
        "planning_rss_reservation_per_worker_bytes": 1 << 30,
        "planning_rss_reservation_is_proof": False,
        "recommended_initial_parallelism": 2,
        "fresh_runtime_resource_gate_required": True,
        "warning": (
            "SAT search memory is data-dependent and cannot be certified from "
            "DIMACS size or occurrence counts"
        ),
    }
    manifest = _seal({
        "schema_version": SCHEMA_VERSION,
        "manifest_kind": MANIFEST_KIND,
        "cover_formulation": COVER_FORMULATION,
        "base": base,
        "split": split,
        "coverage": coverage,
        "cubes": cubes,
        "aggregation_policy": aggregation_policy,
        "resource_estimate": resource_estimate,
        "test_only": test_only,
    }, "manifest_sha256")
    return manifest


def verify_coverage_manifest(
    manifest: Mapping[str, Any],
    instance: optimized.OptimizedInstance,
    *,
    strict_base: bool = True,
) -> dict[str, Any]:
    """Rebuild and byte-compare the complete manifest from the current source."""

    raw = dict(manifest) if type(manifest) is dict else {}
    failures: list[str] = []
    if set(raw) != MANIFEST_FIELDS:
        failures.append("manifest field set mismatch")
    unsigned = dict(raw)
    stored_hash = unsigned.pop("manifest_sha256", None)
    try:
        if not _is_sha256(stored_hash) or stored_hash != _canonical_sha256(unsigned):
            failures.append("manifest self-hash mismatch")
    except (TypeError, ValueError):
        failures.append("manifest is not canonical JSON")
    base = raw.get("base") if type(raw.get("base")) is dict else {}
    split = raw.get("split") if type(raw.get("split")) is dict else {}
    try:
        expected = build_coverage_manifest(
            instance,
            authority_status=base.get("authority_status", AUTHORITY_AUDITED_BASE),
            strict_base=strict_base,
            split_variables=(
                None if strict_base else split.get("variables_dimacs", (1, 2, 3, 4))
            ),
        )
    except (Cube16Error, KeyError, TypeError, ValueError) as exc:
        failures.append(f"manifest replay failed: {exc}")
        expected = None
    if expected is not None and not optimized.json_type_equal(raw, expected):
        failures.append("manifest is not exact current-source canonical replay")
    valid = not failures
    authority_pass = bool(
        valid
        and not raw.get("test_only")
        and base.get("authority_status") == AUTHORITY_AUDITED_BASE
        and type(base.get("audit_binding")) is dict
        and base["audit_binding"].get("status") == "PASS"
    )
    return _seal({
        "schema_version": SCHEMA_VERSION,
        "manifest_kind": MANIFEST_KIND,
        "valid": valid,
        "binding_failures": failures,
        "coverage_mutually_exclusive": bool(
            valid and raw.get("coverage", {}).get("mutually_exclusive") is True
        ),
        "coverage_exhaustive": bool(
            valid and raw.get("coverage", {}).get("exhaustive") is True
        ),
        "base_audit_pass_bound": authority_pass,
        "launch_authorized_by_this_record": False,
        "solver_invoked": False,
    }, "record_sha256")


def _cube_clauses(
    instance: optimized.OptimizedInstance, cube: Mapping[str, Any],
) -> list[list[int]]:
    return [list(map(int, clause)) for clause in instance.cnf["clauses"]] + [
        list(map(int, clause)) for clause in cube["unit_clauses"]
    ]


def _model_satisfies(
    clauses: Sequence[Sequence[int]], model: np.ndarray,
) -> bool:
    return all(any(
        bool(model[abs(int(literal)) - 1]) == (int(literal) > 0)
        for literal in clause
    ) for clause in clauses)


def build_cube_terminal(
    manifest: Mapping[str, Any],
    instance: optimized.OptimizedInstance,
    *,
    cube_index: int,
    outcome: str,
    full_model: np.ndarray | None = None,
    solver: Mapping[str, Any] | None = None,
    invocation_sha256: str = "0" * 64,
    elapsed_s: float = 0.0,
    solver_time_s: float = 0.0,
    solver_stats: Mapping[str, int] | None = None,
    clean_exit: bool = True,
    timed_out: bool = False,
) -> dict[str, Any]:
    """Build a terminal envelope; this function does not establish UNSAT."""

    if type(cube_index) is not int or not 0 <= cube_index < 16:
        raise Cube16Error("cube index out of range")
    if type(outcome) is not str or outcome not in {"sat", "unsat", "unknown"}:
        raise Cube16Error("outcome must be sat, unsat, or unknown")
    if not _is_sha256(invocation_sha256):
        raise Cube16Error("invocation SHA-256 is invalid")
    if type(elapsed_s) is not float or type(solver_time_s) is not float:
        raise Cube16Error("timings must be exact floats")
    if not math.isfinite(elapsed_s) or not math.isfinite(solver_time_s):
        raise Cube16Error("timings must be finite")
    if elapsed_s < 0.0 or solver_time_s < 0.0 or solver_time_s > elapsed_s:
        raise Cube16Error("timings are inconsistent")
    statistics = {} if solver_stats is None else dict(solver_stats)
    if any(
        type(key) is not str or type(value) is not int or value < 0
        for key, value in statistics.items()
    ):
        raise Cube16Error("solver stats are invalid")
    solver_record = dict(solver or {
        "name": "fake-no-solver",
        "version": "test-only",
        "executable_sha256": "0" * 64,
    })
    if set(solver_record) != {"name", "version", "executable_sha256"}:
        raise Cube16Error("solver record field set mismatch")
    if (
        type(solver_record["name"]) is not str
        or type(solver_record["version"]) is not str
        or not _is_sha256(solver_record["executable_sha256"])
    ):
        raise Cube16Error("solver record type mismatch")
    cubes = manifest.get("cubes")
    if type(cubes) is not list or len(cubes) != 16:
        raise Cube16Error("manifest does not contain 16 cubes")
    cube = cubes[cube_index]
    model = None
    operator = objective = syndrome = None
    if full_model is not None:
        model = np.asarray(full_model)
        if (
            model.ndim != 1
            or model.size != int(instance.cnf["num_variables"])
            or not np.all(np.logical_or(model == 0, model == 1))
        ):
            raise Cube16Error("full model has wrong shape or domain")
        model = np.ascontiguousarray(model, dtype=np.uint8)
    if outcome == "sat":
        if model is None:
            raise Cube16Error("SAT terminal needs a complete model")
        vector = model[:EXPECTED_OPERATOR_VARIABLES]
        operator = _pack_bits(vector)
        objective = int(vector.sum())
        syndrome = ((instance.lx @ vector) & 1).astype(int).tolist()
    elif model is not None:
        raise Cube16Error("non-SAT terminal cannot carry a model")
    terminal = outcome in {"sat", "unsat"}
    return _seal({
        "schema_version": SCHEMA_VERSION,
        "evidence_kind": RESULT_KIND,
        "manifest_sha256": manifest.get("manifest_sha256"),
        "base_cnf_sha256": manifest.get("base", {}).get("cnf_sha256"),
        "cube_index": cube_index,
        "cube_id": cube.get("cube_id"),
        "cube_sha256": cube.get("cube_sha256"),
        "cube_cnf_sha256": cube.get("cube_cnf_sha256"),
        "solver": solver_record,
        "invocation_sha256": invocation_sha256,
        "outcome": outcome,
        "status_name": {
            "sat": "SATISFIABLE", "unsat": "UNSATISFIABLE", "unknown": "UNKNOWN",
        }[outcome],
        "decision_complete": terminal,
        "clean_exit": bool(clean_exit),
        "timed_out": bool(timed_out),
        "solver_invocations": 1,
        "full_model": None if model is None else _pack_bits(model),
        "operator": operator,
        "objective": objective,
        "logical_syndrome": syndrome,
        "elapsed_s": elapsed_s,
        "solver_time_s": solver_time_s,
        "solver_stats": statistics,
        "durable_proof": {
            "format": "none", "sha256": None, "independently_verified": False,
        },
        "test_only": manifest.get("test_only"),
    }, "result_sha256")


def classify_cube_terminal(
    result: Mapping[str, Any],
    manifest: Mapping[str, Any],
    instance: optimized.OptimizedInstance,
) -> dict[str, Any]:
    raw = dict(result) if type(result) is dict else {}
    failures: list[str] = []
    if set(raw) != RESULT_FIELDS:
        failures.append("result field set mismatch")
    unsigned = dict(raw)
    stored_hash = unsigned.pop("result_sha256", None)
    try:
        if not _is_sha256(stored_hash) or stored_hash != _canonical_sha256(unsigned):
            failures.append("result self-hash mismatch")
    except (TypeError, ValueError):
        failures.append("result is not canonical JSON")
    cube_index = raw.get("cube_index")
    cubes = manifest.get("cubes") if type(manifest) is dict else None
    cube = None
    if (
        type(cube_index) is int and type(cubes) is list
        and 0 <= cube_index < len(cubes)
    ):
        cube = cubes[cube_index]
    else:
        failures.append("cube index is invalid")
    if cube is not None:
        common = {
            "schema_version": SCHEMA_VERSION,
            "evidence_kind": RESULT_KIND,
            "manifest_sha256": manifest.get("manifest_sha256"),
            "base_cnf_sha256": manifest.get("base", {}).get("cnf_sha256"),
            "cube_id": cube.get("cube_id"),
            "cube_sha256": cube.get("cube_sha256"),
            "cube_cnf_sha256": cube.get("cube_cnf_sha256"),
            "solver_invocations": 1,
            "durable_proof": {
                "format": "none", "sha256": None, "independently_verified": False,
            },
            "test_only": manifest.get("test_only"),
        }
        for key, expected in common.items():
            if not optimized.json_type_equal(raw.get(key), expected):
                failures.append(f"{key} binding/type mismatch")
    solver = raw.get("solver")
    if (
        type(solver) is not dict
        or set(solver) != {"name", "version", "executable_sha256"}
        or type(solver.get("name")) is not str
        or type(solver.get("version")) is not str
        or not _is_sha256(solver.get("executable_sha256"))
    ):
        failures.append("solver binding is invalid")
    if not _is_sha256(raw.get("invocation_sha256")):
        failures.append("invocation SHA-256 is invalid")
    if manifest.get("test_only") is False:
        if type(solver) is not dict or solver.get("name") != optimized.SOLVER:
            failures.append("production cube solver must be cadical195")
        if type(solver) is dict and solver.get("executable_sha256") == "0" * 64:
            failures.append("production solver executable hash cannot be zero")
        if raw.get("invocation_sha256") == "0" * 64:
            failures.append("production invocation hash cannot be zero")
    for key in ("elapsed_s", "solver_time_s"):
        value = raw.get(key)
        if type(value) is not float or not math.isfinite(value) or value < 0.0:
            failures.append(f"{key} is invalid")
    if (
        type(raw.get("elapsed_s")) is float
        and type(raw.get("solver_time_s")) is float
        and raw["solver_time_s"] > raw["elapsed_s"]
    ):
        failures.append("solver time exceeds elapsed time")
    stats = raw.get("solver_stats")
    if type(stats) is not dict or any(
        type(key) is not str or type(value) is not int or value < 0
        for key, value in (stats.items() if type(stats) is dict else ())
    ):
        failures.append("solver stats are invalid")

    outcome = raw.get("outcome")
    official_failures: list[str] = []
    model_valid = False
    if outcome == "sat" and cube is not None:
        if raw.get("status_name") != "SATISFIABLE":
            failures.append("SAT status name mismatch")
        try:
            model = _unpack_bits(
                raw.get("full_model"),
                expected_length=int(instance.cnf["num_variables"]),
            )
            operator = _unpack_bits(
                raw.get("operator"), expected_length=EXPECTED_OPERATOR_VARIABLES
            )
        except Cube16Error as exc:
            failures.append(f"SAT model/operator invalid: {exc}")
        else:
            model_valid = bool(
                np.array_equal(model[:EXPECTED_OPERATOR_VARIABLES], operator)
                and _model_satisfies(_cube_clauses(instance, cube), model)
            )
            if not model_valid:
                failures.append("complete model does not satisfy bound cube CNF")
            replay_evidence = {
                "outcome": "sat",
                "operator": _pack_bits(operator),
                "logical_syndrome": raw.get("logical_syndrome"),
                "partition_index": 0,
                "anchor_indices": [],
                "zero_anchor_indices": [],
                "one_anchor_index": None,
                "anchor_cube_sha256": None,
                "objective": raw.get("objective"),
                "max_weight": EXPECTED_MAX_WEIGHT,
            }
            official_failures = optimized.baseline.verify_css_threshold_sat_witness(
                replay_evidence, instance.hx, instance.lx
            )
    elif outcome == "unsat":
        if raw.get("status_name") != "UNSATISFIABLE":
            failures.append("UNSAT status name mismatch")
    elif outcome == "unknown":
        if raw.get("status_name") != "UNKNOWN":
            failures.append("UNKNOWN status name mismatch")
    else:
        failures.append("outcome is invalid")

    strict_sat = bool(
        outcome == "sat"
        and raw.get("decision_complete") is True
        and raw.get("clean_exit") is True
        and raw.get("timed_out") is False
        and model_valid
        and not failures
        and not official_failures
    )
    clean_unsat = bool(
        outcome == "unsat"
        and raw.get("decision_complete") is True
        and raw.get("clean_exit") is True
        and raw.get("timed_out") is False
        and raw.get("full_model") is None
        and raw.get("operator") is None
        and raw.get("objective") is None
        and raw.get("logical_syndrome") is None
        and not failures
    )
    strict_unknown = bool(
        outcome == "unknown"
        and raw.get("decision_complete") is False
        and raw.get("full_model") is None
        and raw.get("operator") is None
        and raw.get("objective") is None
        and raw.get("logical_syndrome") is None
        and not failures
    )
    if strict_sat:
        classification = "VERIFIED_SAT_LOW_OPERATOR"
    elif clean_unsat:
        classification = "BOUND_CLEAN_UNSAT_CURRENT_SOURCE"
    elif strict_unknown:
        classification = "UNKNOWN"
    else:
        classification = "INVALID"
    return _seal({
        "schema_version": SCHEMA_VERSION,
        "evidence_kind": RESULT_KIND,
        "cube_index": cube_index,
        "classification": classification,
        "strict_verified_sat": strict_sat,
        "clean_current_source_unsat": clean_unsat,
        "official_full_matrix_witness_verifier_invoked": outcome == "sat",
        "official_full_matrix_witness_failures": official_failures,
        "binding_failures": failures,
    }, "record_sha256")


def aggregate_cube_terminals(
    manifest: Mapping[str, Any],
    results: Sequence[Mapping[str, Any]],
    instance: optimized.OptimizedInstance,
    *,
    strict_base: bool = True,
) -> dict[str, Any]:
    manifest_record = verify_coverage_manifest(
        manifest, instance, strict_base=strict_base
    )
    classifications = [
        classify_cube_terminal(result, manifest, instance) for result in results
    ]
    valid_sat = [
        record for record in classifications if record["strict_verified_sat"] is True
    ]
    indices = [record.get("cube_index") for record in classifications]
    exact_indices = bool(
        len(indices) == 16
        and all(type(index) is int for index in indices)
        and sorted(indices) == list(range(16))
    )
    all_clean_unsat = bool(
        exact_indices
        and all(
            record["clean_current_source_unsat"] is True
            for record in classifications
        )
    )
    test_only = bool(manifest.get("test_only"))
    audit_pass = manifest_record["base_audit_pass_bound"] is True
    if manifest_record["valid"] is not True:
        status, lower_bound = "UNRESOLVED", None
    elif valid_sat:
        status, lower_bound = "REJECTED_LOW_OPERATOR", None
    elif all_clean_unsat and test_only:
        status, lower_bound = "TEST_ONLY_ALL_CUBES_UNSAT_NO_SCIENTIFIC_CLAIM", None
    elif all_clean_unsat and audit_pass:
        status, lower_bound = "CURRENT_SOURCE_LOWER_20", 20
    elif all_clean_unsat:
        status, lower_bound = "CANDIDATE_ALL_CUBES_UNSAT_AWAITING_BASE_AUDIT", None
    else:
        status, lower_bound = "UNRESOLVED", None
    return _seal({
        "schema_version": SCHEMA_VERSION,
        "aggregate_kind": AGGREGATE_KIND,
        "manifest_sha256": manifest.get("manifest_sha256"),
        "status": status,
        "distance_lower_bound": lower_bound,
        "strict_verified_sat_count": len(valid_sat),
        "all_16_indices_exactly_once": exact_indices,
        "all_16_clean_current_source_unsat": all_clean_unsat,
        "unknown_or_invalid_count": sum(
            record["classification"] in {"UNKNOWN", "INVALID"}
            for record in classifications
        ),
        "manifest_verification": manifest_record,
        "cube_classifications": classifications,
        "publication_certificate": False,
        "upload_authorized": False,
        "publication_blocker": (
            "independently replayed durable UNSAT proofs are absent"
            if all_clean_unsat and not test_only else None
        ),
    }, "aggregate_sha256")


def _write_new(path: Path, payload: bytes) -> None:
    target = Path(path)
    target.parent.mkdir(parents=True, exist_ok=True)
    descriptor = os.open(
        target,
        os.O_WRONLY | os.O_CREAT | os.O_EXCL | getattr(os, "O_NOFOLLOW", 0),
        0o600,
    )
    try:
        view = memoryview(payload)
        while view:
            count = os.write(descriptor, view)
            if count <= 0:
                raise OSError("short write")
            view = view[count:]
        os.fsync(descriptor)
    finally:
        os.close(descriptor)


def write_bundle(
    root: Path,
    manifest: Mapping[str, Any],
    instance: optimized.OptimizedInstance,
    *,
    strict_base: bool = True,
) -> Path:
    """Write base/cube DIMACS first and the authoritative manifest last."""

    verification = verify_coverage_manifest(
        manifest, instance, strict_base=strict_base
    )
    if verification["valid"] is not True:
        raise Cube16Error(f"invalid manifest: {verification['binding_failures']}")
    output = Path(root)
    output.mkdir(mode=0o700, parents=False, exist_ok=False)
    _write_new(output / manifest["base"]["base_dimacs_relative_path"], instance.dimacs)
    for cube in manifest["cubes"]:
        payload = _render_dimacs(
            num_variables=int(instance.cnf["num_variables"]),
            clauses=_cube_clauses(instance, cube),
        )
        _write_new(output / cube["dimacs_relative_path"], payload)
    _write_new(output / "manifest.json", _canonical_bytes(manifest) + b"\n")
    return output


def _load_strict_json(path: Path) -> dict[str, Any]:
    target = Path(path)
    if target.is_symlink() or not target.is_file():
        raise Cube16Error(f"not a regular JSON file: {target}")
    try:
        value = json.loads(target.read_bytes())
    except (UnicodeDecodeError, json.JSONDecodeError) as exc:
        raise Cube16Error(f"invalid JSON: {target}") from exc
    if type(value) is not dict:
        raise Cube16Error("JSON root must be an object")
    return value


def verify_bundle(
    root: Path,
    instance: optimized.OptimizedInstance,
    *,
    strict_base: bool = True,
) -> dict[str, Any]:
    output = Path(root)
    manifest = _load_strict_json(output / "manifest.json")
    record = verify_coverage_manifest(manifest, instance, strict_base=strict_base)
    failures = list(record["binding_failures"])
    artifacts = [
        (
            manifest.get("base", {}).get("base_dimacs_relative_path"),
            instance.dimacs,
            manifest.get("base", {}).get("dimacs_sha256"),
        )
    ]
    for cube in manifest.get("cubes", []):
        if type(cube) is not dict:
            failures.append("non-object cube record")
            continue
        try:
            payload = _render_dimacs(
                num_variables=int(instance.cnf["num_variables"]),
                clauses=_cube_clauses(instance, cube),
            )
        except (KeyError, TypeError, ValueError) as exc:
            failures.append(f"cube DIMACS replay failed: {exc}")
            continue
        artifacts.append((
            cube.get("dimacs_relative_path"), payload,
            cube.get("cube_dimacs_sha256"),
        ))
    for relative, expected_payload, expected_hash in artifacts:
        if type(relative) is not str or relative.startswith("/") or ".." in Path(relative).parts:
            failures.append("unsafe artifact relative path")
            continue
        path = output / relative
        if path.is_symlink() or not path.is_file():
            failures.append(f"missing regular artifact: {relative}")
            continue
        payload = path.read_bytes()
        if payload != expected_payload:
            failures.append(f"artifact byte replay mismatch: {relative}")
        if hashlib.sha256(payload).hexdigest() != expected_hash:
            failures.append(f"artifact SHA-256 mismatch: {relative}")
    return _seal({
        "schema_version": SCHEMA_VERSION,
        "manifest_sha256": manifest.get("manifest_sha256"),
        "valid": not failures,
        "binding_failures": failures,
        "artifact_count_checked": len(artifacts),
        "solver_invoked": False,
    }, "record_sha256")


def _build_current_instance() -> optimized.OptimizedInstance:
    return optimized.build_optimized_instance()


def _command_generate(args: argparse.Namespace) -> int:
    instance = _build_current_instance()
    manifest = build_coverage_manifest(
        instance,
        strict_base=True,
    )
    write_bundle(Path(args.output), manifest, instance, strict_base=True)
    print(json.dumps({
        "status": "GENERATED_NO_SOLVER",
        "root": str(Path(args.output).resolve()),
        "manifest_sha256": manifest["manifest_sha256"],
        "base_cnf_sha256": manifest["base"]["cnf_sha256"],
        "cube_count": len(manifest["cubes"]),
        "authority_status": manifest["base"]["authority_status"],
    }, sort_keys=True))
    return 0


def _command_verify(args: argparse.Namespace) -> int:
    instance = _build_current_instance()
    record = verify_bundle(Path(args.root), instance, strict_base=True)
    print(json.dumps(record, sort_keys=True))
    return 0 if record["valid"] else 2


def _parser() -> argparse.ArgumentParser:
    parser = argparse.ArgumentParser(description=__doc__)
    subparsers = parser.add_subparsers(dest="command", required=True)
    generate = subparsers.add_parser("generate")
    generate.add_argument("--output", required=True)
    generate.set_defaults(callback=_command_generate)
    verify = subparsers.add_parser("verify")
    verify.add_argument("--root", required=True)
    verify.set_defaults(callback=_command_verify)
    return parser


def main(argv: Sequence[str] | None = None) -> int:
    args = _parser().parse_args(argv)
    return int(args.callback(args))


if __name__ == "__main__":
    raise SystemExit(main())


__all__ = [
    "AGGREGATE_KIND", "AUTHORITY_AUDITED_BASE", "AUTHORITY_TEST_ONLY",
    "AUDITED_SOURCE_FILES", "COVER_FORMULATION", "Cube16Error",
    "DEFAULT_SPLIT_VARIABLES", "EXPECTED_BASE_CNF_SHA256",
    "EXPECTED_BASE_DIMACS_SHA256", "MANIFEST_KIND", "RESULT_KIND",
    "aggregate_cube_terminals", "build_coverage_manifest",
    "build_cube_terminal", "classify_cube_terminal", "main",
    "verify_bundle", "verify_coverage_manifest", "write_bundle",
]
