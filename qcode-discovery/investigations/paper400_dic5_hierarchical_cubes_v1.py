#!/usr/bin/env python3
"""Deterministic exact refinement of one paper400 Dic5 cube.

This module is deliberately solver-free.  It takes one already authenticated
leaf of :mod:`paper400_dic5_cube16`, chooses additional *physical operator*
variables deterministically, and enumerates every Boolean assignment to those
variables.  Each child formula is the unchanged optimized base CNF plus the
parent units plus the new refinement units.

Consequently, for a parent formula ``P`` and refinement variables ``R``, the
manifest certifies the purely propositional identity

    P <=> OR_{a in {0,1}^R} (P AND R=a).

The children are mutually exclusive and exhaustive.  This partitions SAT
search; it does not construct a different quantum code and it does not, by
itself, establish the global distance lower bound.  A proof-carrying
aggregator must still authenticate every terminal leaf.
"""

from __future__ import annotations

import hashlib
import json
from itertools import combinations, product
from pathlib import Path
from typing import Any, Mapping, Sequence

from investigations import paper400_dic5_cube16 as cube16


SCHEMA_VERSION = 1
MANIFEST_KIND = "paper400-dic5-hierarchical-physical-cube-refinement-v1"
COVER_FORMULATION = "exact-parent-cube-cartesian-refinement-v1"
DEFAULT_REFINEMENT_WIDTH = 2
MAX_REFINEMENT_WIDTH = 8

MANIFEST_FIELDS = frozenset({
    "schema_version",
    "manifest_kind",
    "cover_formulation",
    "parent",
    "base",
    "refinement",
    "coverage",
    "children",
    "claim_preservation",
    "source_binding",
    "test_only",
    "manifest_sha256",
})


class HierarchicalCubeError(RuntimeError):
    """A parent binding, refinement cover, or child artifact is malformed."""


def canonical_bytes(value: Any) -> bytes:
    return json.dumps(
        value,
        sort_keys=True,
        separators=(",", ":"),
        ensure_ascii=False,
        allow_nan=False,
    ).encode("utf-8")


def canonical_sha256(value: Any) -> str:
    return hashlib.sha256(canonical_bytes(value)).hexdigest()


def seal(value: Mapping[str, Any], field: str) -> dict[str, Any]:
    result = dict(value)
    result.pop(field, None)
    result[field] = canonical_sha256(result)
    return result


def _is_sha256(value: Any) -> bool:
    if type(value) is not str or len(value) != 64:
        return False
    try:
        return bytes.fromhex(value).hex() == value
    except ValueError:
        return False


def _strict_parent(
    parent_manifest: Mapping[str, Any],
    instance: cube16.optimized.OptimizedInstance,
    *,
    parent_cube_index: int,
    strict_base: bool,
) -> tuple[dict[str, Any], dict[str, Any]]:
    if type(parent_manifest) is not dict:
        raise HierarchicalCubeError("parent manifest must be an object")
    if type(parent_cube_index) is not int:
        raise HierarchicalCubeError("parent cube index must be an integer")
    replay = cube16.verify_coverage_manifest(
        parent_manifest, instance, strict_base=strict_base
    )
    if replay.get("valid") is not True:
        raise HierarchicalCubeError(
            f"parent manifest failed exact replay: {replay.get('binding_failures')}"
        )
    if (
        replay.get("coverage_mutually_exclusive") is not True
        or replay.get("coverage_exhaustive") is not True
    ):
        raise HierarchicalCubeError("parent cover is not exact")
    cubes = parent_manifest.get("cubes")
    if (
        type(cubes) is not list
        or not 0 <= parent_cube_index < len(cubes)
        or type(cubes[parent_cube_index]) is not dict
    ):
        raise HierarchicalCubeError("parent cube index is out of range")
    return dict(cubes[parent_cube_index]), replay


def _assignment_from_records(records: Any) -> dict[int, int]:
    if type(records) is not list:
        raise HierarchicalCubeError("assignment record list is missing")
    assignment: dict[int, int] = {}
    for record in records:
        if type(record) is not dict or set(record) != {
            "dimacs_variable", "value"
        }:
            raise HierarchicalCubeError("assignment record field set mismatch")
        variable = record["dimacs_variable"]
        value = record["value"]
        if (
            type(variable) is not int
            or type(value) is not int
            or not 1 <= variable <= cube16.EXPECTED_OPERATOR_VARIABLES
            or value not in {0, 1}
            or variable in assignment
        ):
            raise HierarchicalCubeError("assignment record is invalid")
        assignment[variable] = value
    return assignment


def _restrict_without_propagation(
    clauses: Sequence[Sequence[int]], assignment: Mapping[int, int],
) -> tuple[list[list[int]], dict[str, Any]]:
    residual: list[list[int]] = []
    satisfied_count = 0
    removed_literal_count = 0
    for raw_clause in clauses:
        clause = [int(literal) for literal in raw_clause]
        kept: list[int] = []
        satisfied = False
        for literal in clause:
            variable = abs(literal)
            if variable not in assignment:
                kept.append(literal)
                continue
            removed_literal_count += 1
            if bool(assignment[variable]) == (literal > 0):
                satisfied = True
        if satisfied:
            satisfied_count += 1
        else:
            residual.append(kept)
    profile = {
        "method": "direct-parent-unit-restriction-without-propagation-v1",
        "base_clause_count": len(clauses),
        "parent_assigned_variable_count": len(assignment),
        "satisfied_base_clause_count": satisfied_count,
        "residual_clause_count": len(residual),
        "residual_literal_count": sum(map(len, residual)),
        "residual_empty_clause_count": sum(not clause for clause in residual),
        "removed_assigned_literal_occurrences": removed_literal_count,
        "unit_propagation_performed": False,
        "solver_invoked": False,
    }
    return residual, profile


def _select_refinement_variables(
    base_clauses: Sequence[Sequence[int]],
    parent_assignment: Mapping[int, int],
    *,
    split_width: int,
) -> tuple[tuple[int, ...], dict[str, Any]]:
    if (
        type(split_width) is not int
        or not 1 <= split_width <= MAX_REFINEMENT_WIDTH
    ):
        raise HierarchicalCubeError(
            f"refinement width must be in 1..{MAX_REFINEMENT_WIDTH}"
        )
    residual, profile = _restrict_without_propagation(
        base_clauses, parent_assignment
    )
    candidates = [
        variable
        for variable in range(1, cube16.EXPECTED_OPERATOR_VARIABLES + 1)
        if variable not in parent_assignment
    ]
    if len(candidates) < split_width:
        raise HierarchicalCubeError("not enough unassigned physical variables")

    positive = {variable: 0 for variable in candidates}
    negative = {variable: 0 for variable in candidates}
    incidence = {variable: set() for variable in candidates}
    candidate_set = set(candidates)
    for clause_index, clause in enumerate(residual):
        for literal in clause:
            variable = abs(int(literal))
            if variable not in candidate_set:
                continue
            if literal > 0:
                positive[variable] += 1
            else:
                negative[variable] += 1
            incidence[variable].add(clause_index)

    ranking = [
        {
            "dimacs_variable": variable,
            "positive_occurrences": positive[variable],
            "negative_occurrences": negative[variable],
            "min_sign_occurrences": min(
                positive[variable], negative[variable]
            ),
            "sign_imbalance": abs(
                positive[variable] - negative[variable]
            ),
            "total_occurrences": positive[variable] + negative[variable],
            "incident_clause_count": len(incidence[variable]),
        }
        for variable in candidates
    ]
    ranking.sort(key=lambda record: (
        -record["min_sign_occurrences"],
        record["sign_imbalance"],
        -record["total_occurrences"],
        record["dimacs_variable"],
    ))
    selected = tuple(
        int(record["dimacs_variable"])
        for record in ranking[:split_width]
    )
    selected_records = [dict(record) for record in ranking[:split_width]]
    pairwise_overlap = [
        {
            "left": left,
            "right": right,
            "shared_residual_clause_count": len(
                incidence[left] & incidence[right]
            ),
        }
        for left, right in combinations(selected, 2)
    ]
    certificate = seal({
        "schema_version": SCHEMA_VERSION,
        "method": (
            "residual-descending-min-sign-occurrence-then-ascending-"
            "imbalance-then-descending-total-then-dimacs-v1"
        ),
        "physical_variable_interval_dimacs": [
            1, cube16.EXPECTED_OPERATOR_VARIABLES,
        ],
        "parent_assigned_variables": sorted(parent_assignment),
        "candidate_count": len(ranking),
        "candidate_ranking_sha256": canonical_sha256(ranking),
        "split_width": split_width,
        "selected_variables": list(selected),
        "selected_records": selected_records,
        "pairwise_residual_clause_overlap": pairwise_overlap,
        "parent_restriction_profile": profile,
        "selection_depends_on_solver_state": False,
        "solver_invoked": False,
    }, "certificate_sha256")
    return selected, certificate


def _parent_binding(
    parent_manifest: Mapping[str, Any], parent_cube: Mapping[str, Any],
) -> dict[str, Any]:
    return seal({
        "schema_version": SCHEMA_VERSION,
        "manifest_kind": parent_manifest.get("manifest_kind"),
        "manifest_sha256": parent_manifest.get("manifest_sha256"),
        "cube_index": parent_cube.get("cube_index"),
        "cube_id": parent_cube.get("cube_id"),
        "cube_sha256": parent_cube.get("cube_sha256"),
        "cube_cnf_sha256": parent_cube.get("cube_cnf_sha256"),
        "cube_dimacs_sha256": parent_cube.get("cube_dimacs_sha256"),
        "cube_num_variables": parent_cube.get("cube_num_variables"),
        "cube_num_clauses": parent_cube.get("cube_num_clauses"),
        "assignment_by_dimacs_variable": parent_cube.get(
            "assignment_by_dimacs_variable"
        ),
        "unit_clauses": parent_cube.get("unit_clauses"),
    }, "parent_binding_sha256")


def _child_record(
    *,
    instance: cube16.optimized.OptimizedInstance,
    parent: Mapping[str, Any],
    parent_assignment: Mapping[int, int],
    refinement_variables: Sequence[int],
    child_index: int,
    bits: Sequence[int],
) -> tuple[dict[str, Any], bytes]:
    bit_list = [int(bit) for bit in bits]
    variables = [int(variable) for variable in refinement_variables]
    if len(bit_list) != len(variables) or any(bit not in {0, 1} for bit in bit_list):
        raise HierarchicalCubeError("invalid refinement assignment")
    expected_index = sum(
        bit << (len(bit_list) - position - 1)
        for position, bit in enumerate(bit_list)
    )
    if type(child_index) is not int or child_index != expected_index:
        raise HierarchicalCubeError("child index/binary assignment mismatch")
    refinement_assignment = dict(zip(variables, bit_list, strict=True))
    if set(refinement_assignment) & set(parent_assignment):
        raise HierarchicalCubeError("refinement reassigns a parent variable")
    refinement_units = [
        [variable if refinement_assignment[variable] else -variable]
        for variable in variables
    ]
    parent_units = [
        [int(literal) for literal in clause]
        for clause in parent["unit_clauses"]
    ]
    combined_units = parent_units + refinement_units
    clauses = [
        [int(literal) for literal in clause]
        for clause in instance.cnf["clauses"]
    ] + combined_units
    num_variables = int(instance.cnf["num_variables"])
    dimacs = cube16._render_dimacs(
        num_variables=num_variables, clauses=clauses
    )
    child_cnf_sha256 = cube16._cnf_sha256(
        num_variables=num_variables, clauses=clauses, native_atmost=None
    )
    bit_string = "".join(str(bit) for bit in bit_list)
    combined_assignment = dict(parent_assignment)
    combined_assignment.update(refinement_assignment)
    record = seal({
        "schema_version": SCHEMA_VERSION,
        "child_index": child_index,
        "child_id": f"{parent['cube_id']}.refine-{bit_string}",
        "parent_cube_index": parent["cube_index"],
        "parent_cube_id": parent["cube_id"],
        "parent_cube_sha256": parent["cube_sha256"],
        "assignment_bits": bit_list,
        "assignment_by_dimacs_variable": [
            {"dimacs_variable": variable, "value": refinement_assignment[variable]}
            for variable in variables
        ],
        "combined_assignment_by_dimacs_variable": [
            {"dimacs_variable": variable, "value": combined_assignment[variable]}
            for variable in sorted(combined_assignment)
        ],
        "parent_unit_clauses": parent_units,
        "refinement_unit_clauses": refinement_units,
        "combined_unit_clauses": combined_units,
        "combined_unit_clauses_sha256": canonical_sha256(combined_units),
        "child_cnf_sha256": child_cnf_sha256,
        "child_dimacs_sha256": hashlib.sha256(dimacs).hexdigest(),
        "child_num_variables": num_variables,
        "child_num_clauses": len(clauses),
        "child_dimacs_bytes": len(dimacs),
        "dimacs_relative_path": f"children/child-{child_index:04d}.cnf",
    }, "child_sha256")
    return record, dimacs


def _source_binding() -> dict[str, Any]:
    project = Path(__file__).resolve().parent.parent
    this_path = Path(__file__).resolve()
    parent_path = Path(cube16.__file__).resolve()
    optimized_path = Path(cube16.optimized.__file__).resolve()
    return seal({
        "schema_version": SCHEMA_VERSION,
        "hierarchical_source_relative_path": this_path.relative_to(project).as_posix(),
        "hierarchical_source_sha256": cube16._file_sha256(this_path),
        "parent_cover_source_relative_path": parent_path.relative_to(project).as_posix(),
        "parent_cover_source_sha256": cube16._file_sha256(parent_path),
        "optimized_source_relative_path": optimized_path.relative_to(project).as_posix(),
        "optimized_source_sha256": cube16._file_sha256(optimized_path),
    }, "source_binding_sha256")


def build_refinement_manifest(
    parent_manifest: Mapping[str, Any],
    instance: cube16.optimized.OptimizedInstance,
    *,
    parent_cube_index: int,
    split_width: int = DEFAULT_REFINEMENT_WIDTH,
    strict_base: bool = True,
) -> dict[str, Any]:
    """Build a canonical exact child cover for one authenticated parent cube."""

    parent, _ = _strict_parent(
        parent_manifest,
        instance,
        parent_cube_index=parent_cube_index,
        strict_base=strict_base,
    )
    parent_assignment = _assignment_from_records(
        parent["assignment_by_dimacs_variable"]
    )
    selected, selection = _select_refinement_variables(
        instance.cnf["clauses"],
        parent_assignment,
        split_width=split_width,
    )
    assignments = [
        list(bits) for bits in product((0, 1), repeat=split_width)
    ]
    children: list[dict[str, Any]] = []
    child_dimacs: list[bytes] = []
    for child_index, bits in enumerate(assignments):
        child, payload = _child_record(
            instance=instance,
            parent=parent,
            parent_assignment=parent_assignment,
            refinement_variables=selected,
            child_index=child_index,
            bits=bits,
        )
        children.append(child)
        child_dimacs.append(payload)

    separations = []
    for left, right in combinations(children, 2):
        differing_positions = [
            position
            for position, (left_bit, right_bit) in enumerate(zip(
                left["assignment_bits"],
                right["assignment_bits"],
                strict=True,
            ))
            if left_bit != right_bit
        ]
        separations.append({
            "left_child_index": left["child_index"],
            "right_child_index": right["child_index"],
            "differing_positions": differing_positions,
        })
    expected_pair_count = len(children) * (len(children) - 1) // 2
    mutually_exclusive = bool(
        len(separations) == expected_pair_count
        and all(record["differing_positions"] for record in separations)
    )
    exhaustive = assignments == [
        list(bits) for bits in product((0, 1), repeat=split_width)
    ]

    base = parent_manifest["base"]
    parent_binding = _parent_binding(parent_manifest, parent)
    refinement = {
        "variable_count": split_width,
        "variables_dimacs": list(selected),
        "physical_qubit_indices_zero_based": [
            variable - 1 for variable in selected
        ],
        "selection_certificate": selection,
    }
    coverage = {
        "method": "explicit-parent-local-cartesian-product-replay-v1",
        "assignment_domain": [0, 1],
        "assignment_order": "lexicographic bits; leftmost bit is most significant",
        "expected_child_count": 1 << split_width,
        "observed_child_count": len(children),
        "assignments_sha256": canonical_sha256(assignments),
        "child_sha256_sequence_sha256": canonical_sha256([
            child["child_sha256"] for child in children
        ]),
        "child_cnf_sha256_sequence_sha256": canonical_sha256([
            child["child_cnf_sha256"] for child in children
        ]),
        "expected_pair_count": expected_pair_count,
        "pair_count_checked": len(separations),
        "pairwise_separation_sha256": canonical_sha256(separations),
        "mutually_exclusive": mutually_exclusive,
        "exhaustive": exhaustive,
        "equivalence_statement": "P iff OR_a(P AND refinement_assignment_a)",
        "proof": (
            "every valuation satisfying the parent has exactly one restriction "
            "to the selected refinement variables; two different restrictions "
            "disagree on at least one physical operator variable"
        ),
        "solver_invoked": False,
    }
    claim_preservation = {
        "quantum_code_changed": False,
        "base_cnf_changed": False,
        "only_physical_operator_unit_clauses_added": True,
        "parent_formula_equivalence_certified": bool(
            mutually_exclusive and exhaustive
        ),
        "all_children_unsat_implies_parent_unsat": True,
        "verified_sat_child_implies_parent_sat": True,
        "this_manifest_alone_proves_parent_unsat": False,
        "this_manifest_alone_proves_global_distance_lower_bound": False,
        "inherited_all_root_unsat_distance_lower_bound": parent_manifest[
            "aggregation_policy"
        ]["all_unsat_distance_lower_bound"],
        "required_global_composition": (
            "replace this parent leaf by all authenticated child terminals, then "
            "retain authenticated terminals for every other root-cover leaf"
        ),
    }
    manifest = seal({
        "schema_version": SCHEMA_VERSION,
        "manifest_kind": MANIFEST_KIND,
        "cover_formulation": COVER_FORMULATION,
        "parent": parent_binding,
        "base": {
            "cnf_sha256": base["cnf_sha256"],
            "dimacs_sha256": base["dimacs_sha256"],
            "num_variables": base["num_variables"],
            "num_clauses": base["num_clauses"],
            "native_atmost": base["native_atmost"],
            "operator_variable_interval_dimacs": base[
                "operator_variable_interval_dimacs"
            ],
        },
        "refinement": refinement,
        "coverage": coverage,
        "children": children,
        "claim_preservation": claim_preservation,
        "source_binding": _source_binding(),
        "test_only": parent_manifest["test_only"],
    }, "manifest_sha256")
    return manifest


def verify_refinement_manifest(
    manifest: Mapping[str, Any],
    parent_manifest: Mapping[str, Any],
    instance: cube16.optimized.OptimizedInstance,
    *,
    strict_base: bool = True,
    expected_parent_cube_index: int | None = None,
    expected_split_width: int | None = None,
) -> dict[str, Any]:
    """Rebuild and exact-compare a refinement against its supplied parent."""

    raw = dict(manifest) if type(manifest) is dict else {}
    failures: list[str] = []
    if set(raw) != MANIFEST_FIELDS:
        failures.append("manifest field set mismatch")
    unsigned = dict(raw)
    stored_hash = unsigned.pop("manifest_sha256", None)
    try:
        if not _is_sha256(stored_hash) or stored_hash != canonical_sha256(unsigned):
            failures.append("manifest self-hash mismatch")
    except (TypeError, ValueError):
        failures.append("manifest is not canonical JSON")

    parent = raw.get("parent") if type(raw.get("parent")) is dict else {}
    refinement = (
        raw.get("refinement") if type(raw.get("refinement")) is dict else {}
    )
    parent_cube_index = parent.get("cube_index")
    split_width = refinement.get("variable_count")
    if (
        expected_parent_cube_index is not None
        and parent_cube_index != expected_parent_cube_index
    ):
        failures.append("parent cube index does not match caller expectation")
    if expected_split_width is not None and split_width != expected_split_width:
        failures.append("refinement width does not match caller expectation")
    try:
        expected = build_refinement_manifest(
            parent_manifest,
            instance,
            parent_cube_index=parent_cube_index,
            split_width=split_width,
            strict_base=strict_base,
        )
    except (HierarchicalCubeError, KeyError, TypeError, ValueError) as exc:
        failures.append(f"refinement replay failed: {exc}")
        expected = None
    if expected is not None and not cube16.optimized.json_type_equal(raw, expected):
        failures.append("manifest is not exact current-source canonical replay")
    valid = not failures
    return seal({
        "schema_version": SCHEMA_VERSION,
        "manifest_kind": MANIFEST_KIND,
        "manifest_sha256": raw.get("manifest_sha256"),
        "parent_manifest_sha256": parent_manifest.get("manifest_sha256")
        if type(parent_manifest) is dict else None,
        "parent_cube_index": parent_cube_index,
        "valid": valid,
        "binding_failures": failures,
        "coverage_mutually_exclusive": bool(
            valid and raw.get("coverage", {}).get("mutually_exclusive") is True
        ),
        "coverage_exhaustive": bool(
            valid and raw.get("coverage", {}).get("exhaustive") is True
        ),
        "quantum_code_changed": bool(
            not valid
            or raw.get("claim_preservation", {}).get("quantum_code_changed")
            is not False
        ),
        "launch_authorized_by_this_record": False,
        "solver_invoked": False,
    }, "record_sha256")


def _child_clauses(
    manifest: Mapping[str, Any],
    instance: cube16.optimized.OptimizedInstance,
    *,
    child_index: int,
) -> list[list[int]]:
    """Replay one child formula from the unchanged base and bound units."""

    if type(child_index) is not int:
        raise HierarchicalCubeError("child index must be an integer")
    children = manifest.get("children") if type(manifest) is dict else None
    if (
        type(children) is not list
        or not 0 <= child_index < len(children)
        or type(children[child_index]) is not dict
    ):
        raise HierarchicalCubeError("child index is out of range")
    return [
        [int(literal) for literal in clause]
        for clause in instance.cnf["clauses"]
    ] + [
        [int(literal) for literal in clause]
        for clause in children[child_index]["combined_unit_clauses"]
    ]


def _child_dimacs(
    manifest: Mapping[str, Any],
    instance: cube16.optimized.OptimizedInstance,
    *,
    child_index: int,
) -> bytes:
    return cube16._render_dimacs(
        num_variables=int(instance.cnf["num_variables"]),
        clauses=_child_clauses(manifest, instance, child_index=child_index),
    )


def verified_child_dimacs(
    manifest: Mapping[str, Any],
    parent_manifest: Mapping[str, Any],
    instance: cube16.optimized.OptimizedInstance,
    *,
    child_index: int,
    strict_base: bool = True,
    expected_parent_cube_index: int | None = None,
    expected_split_width: int | None = None,
) -> bytes:
    """Return solver input only after full parent/manifest/current-source replay."""

    replay = verify_refinement_manifest(
        manifest,
        parent_manifest,
        instance,
        strict_base=strict_base,
        expected_parent_cube_index=expected_parent_cube_index,
        expected_split_width=expected_split_width,
    )
    if replay["valid"] is not True:
        raise HierarchicalCubeError(
            f"refinement failed exact replay: {replay['binding_failures']}"
        )
    if type(child_index) is not int:
        raise HierarchicalCubeError("child index must be an integer")
    children = manifest.get("children")
    if (
        type(children) is not list
        or not 0 <= child_index < len(children)
        or type(children[child_index]) is not dict
    ):
        raise HierarchicalCubeError("child index is out of range")
    child = children[child_index]
    clauses = _child_clauses(manifest, instance, child_index=child_index)
    payload = _child_dimacs(manifest, instance, child_index=child_index)
    failures: list[str] = []
    if child.get("child_index") != child_index:
        failures.append("child record index mismatch")
    if child.get("child_num_variables") != int(instance.cnf["num_variables"]):
        failures.append("child variable count mismatch")
    if child.get("child_num_clauses") != len(clauses):
        failures.append("child clause count mismatch")
    if child.get("child_dimacs_bytes") != len(payload):
        failures.append("child DIMACS byte count mismatch")
    if child.get("child_dimacs_sha256") != hashlib.sha256(payload).hexdigest():
        failures.append("child DIMACS SHA-256 mismatch")
    if child.get("child_cnf_sha256") != cube16._cnf_sha256(
        num_variables=int(instance.cnf["num_variables"]),
        clauses=clauses,
        native_atmost=None,
    ):
        failures.append("child canonical CNF SHA-256 mismatch")
    if failures:
        raise HierarchicalCubeError("; ".join(failures))
    return payload


__all__ = [
    "COVER_FORMULATION",
    "DEFAULT_REFINEMENT_WIDTH",
    "HierarchicalCubeError",
    "MANIFEST_KIND",
    "MAX_REFINEMENT_WIDTH",
    "build_refinement_manifest",
    "canonical_bytes",
    "canonical_sha256",
    "verified_child_dimacs",
    "seal",
    "verify_refinement_manifest",
]
