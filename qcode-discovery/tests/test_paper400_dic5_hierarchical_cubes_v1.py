from __future__ import annotations

import ast
import copy
import hashlib
from itertools import combinations, product
from pathlib import Path

import numpy as np
import pytest

from evaluation import paper400_dic5_optimized_cnf_final_v13 as optimized
from investigations import paper400_dic5_cube16 as cube16
from investigations import paper400_dic5_hierarchical_cubes_v1 as hierarchy


def _synthetic_instance() -> optimized.OptimizedInstance:
    hx = np.zeros((200, 400), dtype=np.uint8)
    hz = np.zeros_like(hx)
    lx = np.zeros((16, 400), dtype=np.uint8)
    lx[0, 0] = 1
    lz = np.zeros_like(lx)
    cnf = {
        "num_variables": 400,
        "num_clauses": 1,
        "operator_variables": list(range(1, 401)),
        "logical_variables": [1],
        "native_atmost": None,
        "clauses": [[1]],
    }
    cnf["cnf_sha256"] = optimized.canonical_sha256({
        "num_variables": cnf["num_variables"],
        "clauses": cnf["clauses"],
        "native_atmost": None,
    })
    report = optimized.seal({
        "schema_version": 1,
        "solver_invoked": False,
        "baseline": {"preflight_sha256": "a" * 64},
    }, "report_sha256")
    return optimized.OptimizedInstance(
        hx=hx,
        hz=hz,
        lx=lx,
        lz=lz,
        basis_checks=hx[:192].copy(),
        active_logical=lx[:1].copy(),
        cnf=cnf,
        dimacs=optimized.render_dimacs(cnf),
        report=report,
    )


@pytest.fixture()
def synthetic() -> optimized.OptimizedInstance:
    return _synthetic_instance()


@pytest.fixture()
def parent(synthetic: optimized.OptimizedInstance) -> dict:
    return cube16.build_coverage_manifest(
        synthetic,
        strict_base=False,
        split_variables=(1, 2, 3, 4),
    )


@pytest.fixture()
def refinement(
    synthetic: optimized.OptimizedInstance, parent: dict,
) -> dict:
    return hierarchy.build_refinement_manifest(
        parent,
        synthetic,
        parent_cube_index=8,
        split_width=2,
        strict_base=False,
    )


def test_source_is_solver_free() -> None:
    path = Path(hierarchy.__file__)
    source = path.read_text(encoding="utf-8")
    tree = ast.parse(source)
    imports: set[str] = set()
    for node in ast.walk(tree):
        if isinstance(node, ast.Import):
            imports.update(alias.name for alias in node.names)
        elif isinstance(node, ast.ImportFrom) and node.module:
            imports.add(node.module)
    assert "pysat" not in imports
    assert "pysat.solvers" not in imports
    assert "subprocess" not in imports
    assert "multiprocessing" not in imports
    assert ".solve(" not in source


def test_refinement_is_deterministic_and_bound_to_exact_parent(
    synthetic: optimized.OptimizedInstance,
    parent: dict,
    refinement: dict,
) -> None:
    rebuilt = hierarchy.build_refinement_manifest(
        parent,
        synthetic,
        parent_cube_index=8,
        split_width=2,
        strict_base=False,
    )
    assert rebuilt == refinement
    assert refinement["test_only"] is True
    assert refinement["parent"]["manifest_sha256"] == parent["manifest_sha256"]
    assert refinement["parent"]["cube_index"] == 8
    assert refinement["parent"]["cube_sha256"] == parent["cubes"][8][
        "cube_sha256"
    ]
    assert refinement["refinement"]["variables_dimacs"] == [5, 6]
    claim = refinement["claim_preservation"]
    assert claim["quantum_code_changed"] is False
    assert claim["base_cnf_changed"] is False
    assert claim["only_physical_operator_unit_clauses_added"] is True
    assert claim["parent_formula_equivalence_certified"] is True
    assert claim["this_manifest_alone_proves_global_distance_lower_bound"] is False
    assert claim["inherited_all_root_unsat_distance_lower_bound"] == 20

    replay = hierarchy.verify_refinement_manifest(
        refinement,
        parent,
        synthetic,
        strict_base=False,
        expected_parent_cube_index=8,
        expected_split_width=2,
    )
    assert replay["valid"] is True
    assert replay["coverage_mutually_exclusive"] is True
    assert replay["coverage_exhaustive"] is True
    assert replay["quantum_code_changed"] is False
    assert replay["solver_invoked"] is False


def test_children_are_pairwise_exclusive_and_exhaust_parent(
    synthetic: optimized.OptimizedInstance,
    parent: dict,
    refinement: dict,
) -> None:
    children = refinement["children"]
    assert [child["assignment_bits"] for child in children] == [
        list(bits) for bits in product((0, 1), repeat=2)
    ]
    assert len(children) == 4
    assert refinement["coverage"]["pair_count_checked"] == 6

    variables = refinement["refinement"]["variables_dimacs"]
    child_assignments = [
        dict(zip(variables, child["assignment_bits"], strict=True))
        for child in children
    ]
    for left, right in combinations(child_assignments, 2):
        assert any(left[variable] != right[variable] for variable in variables)

    for bits in product((0, 1), repeat=2):
        valuation = dict(zip(variables, bits, strict=True))
        matching = [
            assignment for assignment in child_assignments
            if all(
                valuation[variable] == value
                for variable, value in assignment.items()
            )
        ]
        assert len(matching) == 1

    parent_units = parent["cubes"][8]["unit_clauses"]
    for child in children:
        assert child["parent_unit_clauses"] == parent_units
        assert child["combined_unit_clauses"] == (
            parent_units + child["refinement_unit_clauses"]
        )
        assert child["child_num_clauses"] == 7
        payload = hierarchy.verified_child_dimacs(
            refinement,
            parent,
            synthetic,
            child_index=child["child_index"],
            strict_base=False,
            expected_parent_cube_index=8,
            expected_split_width=2,
        )
        assert hashlib.sha256(payload).hexdigest() == child[
            "child_dimacs_sha256"
        ]


def test_resealed_parent_binding_tamper_fails_closed(
    synthetic: optimized.OptimizedInstance,
    parent: dict,
    refinement: dict,
) -> None:
    changed = copy.deepcopy(refinement)
    changed["parent"]["cube_sha256"] = "f" * 64
    changed["parent"] = hierarchy.seal(
        changed["parent"], "parent_binding_sha256"
    )
    changed = hierarchy.seal(changed, "manifest_sha256")
    replay = hierarchy.verify_refinement_manifest(
        changed,
        parent,
        synthetic,
        strict_base=False,
        expected_parent_cube_index=8,
        expected_split_width=2,
    )
    assert replay["valid"] is False
    assert "exact current-source canonical replay" in " ".join(
        replay["binding_failures"]
    )


def test_valid_parent_substitution_needs_explicit_caller_authority(
    synthetic: optimized.OptimizedInstance,
    parent: dict,
) -> None:
    other = hierarchy.build_refinement_manifest(
        parent,
        synthetic,
        parent_cube_index=9,
        split_width=2,
        strict_base=False,
    )
    replay = hierarchy.verify_refinement_manifest(
        other,
        parent,
        synthetic,
        strict_base=False,
        expected_parent_cube_index=8,
        expected_split_width=2,
    )
    assert replay["valid"] is False
    assert "caller expectation" in " ".join(replay["binding_failures"])


def test_tampered_parent_manifest_and_child_record_fail_closed(
    synthetic: optimized.OptimizedInstance,
    parent: dict,
    refinement: dict,
) -> None:
    bad_parent = copy.deepcopy(parent)
    bad_parent["cubes"][8]["unit_clauses"][0] = [-1]
    bad_parent["cubes"][8] = cube16._seal(
        bad_parent["cubes"][8], "cube_sha256"
    )
    bad_parent = cube16._seal(bad_parent, "manifest_sha256")
    with pytest.raises(
        hierarchy.HierarchicalCubeError,
        match="parent manifest failed exact replay",
    ):
        hierarchy.build_refinement_manifest(
            bad_parent,
            synthetic,
            parent_cube_index=8,
            strict_base=False,
        )

    bad_child = copy.deepcopy(refinement)
    bad_child["children"][0]["refinement_unit_clauses"][0] = [5]
    bad_child["children"][0] = hierarchy.seal(
        bad_child["children"][0], "child_sha256"
    )
    bad_child = hierarchy.seal(bad_child, "manifest_sha256")
    replay = hierarchy.verify_refinement_manifest(
        bad_child,
        parent,
        synthetic,
        strict_base=False,
        expected_parent_cube_index=8,
    )
    assert replay["valid"] is False
    assert "exact current-source canonical replay" in " ".join(
        replay["binding_failures"]
    )


@pytest.mark.parametrize("bad_width", [False, 0, 9, 1.0])
def test_invalid_refinement_width_is_rejected(
    bad_width: object,
    synthetic: optimized.OptimizedInstance,
    parent: dict,
) -> None:
    with pytest.raises(hierarchy.HierarchicalCubeError, match="width"):
        hierarchy.build_refinement_manifest(
            parent,
            synthetic,
            parent_cube_index=8,
            split_width=bad_width,  # type: ignore[arg-type]
            strict_base=False,
        )
