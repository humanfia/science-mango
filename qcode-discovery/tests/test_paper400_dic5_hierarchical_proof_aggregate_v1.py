from __future__ import annotations

import copy
from pathlib import Path

import numpy as np
import pytest

from evaluation import paper400_dic5_optimized_cnf_final_v13 as optimized
from investigations import paper400_dic5_cube16 as cube16
from investigations import paper400_dic5_cube16_proof_aggregate_v1 as root_aggregate
from investigations import paper400_dic5_hierarchical_cubes_v1 as hierarchy
from investigations import paper400_dic5_hierarchical_proof_aggregate_v1 as aggregate


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


def _artifact(role: str, filename: str, marker: str) -> dict:
    return {
        "role": role,
        "relative_path": f"artifacts/{filename}",
        "file_sha256": marker * 64,
        "bytes": 17,
    }


def _identity(refinement: dict, index: int) -> dict:
    parent = refinement["parent"]
    child = refinement["children"][index]
    return {
        "refinement_manifest_sha256": refinement["manifest_sha256"],
        "parent_manifest_sha256": parent["manifest_sha256"],
        "parent_cube_index": parent["cube_index"],
        "parent_cube_id": parent["cube_id"],
        "parent_cube_sha256": parent["cube_sha256"],
        "parent_cube_cnf_sha256": parent["cube_cnf_sha256"],
        "parent_cube_dimacs_sha256": parent["cube_dimacs_sha256"],
        "child_index": index,
        "child_id": child["child_id"],
        "child_sha256": child["child_sha256"],
        "child_cnf_sha256": child["child_cnf_sha256"],
        "child_dimacs_sha256": child["child_dimacs_sha256"],
        "combined_unit_clauses": child["combined_unit_clauses"],
        "combined_unit_clauses_sha256": child[
            "combined_unit_clauses_sha256"
        ],
    }


def _proof_chain() -> dict:
    return aggregate.seal({
        "format": "binary-drat+converted-lrat-v1",
        "binary_drat": _artifact("raw-binary-drat", "child.drat", "1"),
        "converted_lrat": _artifact("converted-lrat", "child.lrat", "2"),
        "drat_checker_sha256": root_aggregate.EXPECTED_DRAT_CHECKER_SHA256,
        "lrat_checker_sha256": root_aggregate.EXPECTED_LRAT_CHECKER_SHA256,
        "trusted_policy_sha256": root_aggregate.EXPECTED_POLICY_SHA256,
        "drat_independently_verified": True,
        "lrat_independently_verified": True,
        "fresh_drat_replay": True,
        "fresh_lrat_replay": True,
        "drat_record_sha256": "3" * 64,
        "lrat_record_sha256": "4" * 64,
        "fresh_replay_record_sha256": "5" * 64,
    }, "chain_sha256")


def _certificate(refinement: dict, index: int) -> dict:
    child = refinement["children"][index]
    authority = (
        aggregate.AUTHORITY_TEST_ONLY
        if refinement["test_only"] else aggregate.AUTHORITY_PRODUCTION
    )
    return aggregate.seal({
        "schema_version": aggregate.SCHEMA_VERSION,
        "kind": aggregate.CHILD_CERTIFICATE_KIND,
        "gate": aggregate.RUNNER_GATE,
        "state": aggregate.STATE_PROOF_UNSAT,
        "authority": authority,
        "test_only": authority == aggregate.AUTHORITY_TEST_ONLY,
        "production_eligible": authority == aggregate.AUTHORITY_PRODUCTION,
        **_identity(refinement, index),
        "child_num_variables": child["child_num_variables"],
        "child_num_clauses": child["child_num_clauses"],
        "child_dimacs_bytes": child["child_dimacs_bytes"],
        "solver": {
            "name": root_aggregate.EXPECTED_SOLVER_NAME,
            "version": root_aggregate.EXPECTED_SOLVER_VERSION,
            "executable_sha256": root_aggregate.EXPECTED_SOLVER_SHA256,
        },
        "decision": {
            "outcome": "unsat",
            "status_name": "UNSATISFIABLE",
            "decision_complete": True,
            "clean_exit": True,
            "timed_out": False,
        },
        "proof_chain": _proof_chain(),
        "source_binding_sha256": "6" * 64,
        "toolchain_binding_sha256": "7" * 64,
        "predecessor_chain_sha256": "8" * 64,
        "parent_cube_unsat_claim": False,
        "global_distance_claim": None,
        "publication_certificate": False,
        "upload_authorized": False,
    }, "certificate_sha256")


def _validation(refinement: dict, index: int, tmp_path: Path) -> dict:
    authority = (
        aggregate.AUTHORITY_TEST_ONLY
        if refinement["test_only"] else aggregate.AUTHORITY_PRODUCTION
    )
    return aggregate.seal({
        "schema_version": aggregate.SCHEMA_VERSION,
        "kind": aggregate.CHILD_VALIDATION_KIND,
        "gate": aggregate.RUNNER_GATE,
        "root": str((tmp_path / f"child-{index:04d}").absolute()),
        **_identity(refinement, index),
        "state": aggregate.STATE_PROOF_UNSAT,
        "authority": authority,
        "test_only": authority == aggregate.AUTHORITY_TEST_ONLY,
        "valid": True,
        "strict_proof_unsat": True,
        "fresh_proof_replay": True,
        "source_toolchain_fresh": True,
        "certificate": _certificate(refinement, index),
        "failures": [],
    }, "validation_sha256")


def _aggregate(
    refinement: dict,
    parent: dict,
    validations: list[dict],
    synthetic: optimized.OptimizedInstance,
) -> dict:
    return aggregate.aggregate_child_validations(
        refinement,
        parent,
        validations,
        synthetic,
        expected_parent_cube_index=8,
        expected_split_width=2,
        strict_base=False,
    )


def test_complete_proof_carrying_children_derive_parent_only(
    refinement: dict,
    parent: dict,
    synthetic: optimized.OptimizedInstance,
    tmp_path: Path,
) -> None:
    validations = [
        _validation(refinement, index, tmp_path) for index in range(4)
    ]
    result = _aggregate(refinement, parent, validations, synthetic)
    assert result["manifest_authenticated"] is True
    assert result["all_child_indices_exactly_once"] is True
    assert result["all_children_proof_carrying_unsat"] is True
    assert result["status"] == aggregate.STATE_PARENT_UNSAT
    assert result["parent_cube_unsat"] is True
    assert result["claim_scope"] == "one-parent-cube-only"
    assert result["global_distance_claim"] is None
    assert result["distance_lower_bound"] is None
    assert result["publication_certificate"] is False
    assert result["upload_authorized"] is False
    assert [item["child_index"] for item in result[
        "ordered_child_certificate_bindings"
    ]] == list(range(4))


@pytest.mark.parametrize("mode", ["missing", "duplicate"])
def test_missing_or_duplicate_child_fails_closed(
    mode: str,
    refinement: dict,
    parent: dict,
    synthetic: optimized.OptimizedInstance,
    tmp_path: Path,
) -> None:
    validations = [
        _validation(refinement, index, tmp_path) for index in range(4)
    ]
    if mode == "missing":
        validations.pop()
    else:
        validations[-1] = copy.deepcopy(validations[0])
    result = _aggregate(refinement, parent, validations, synthetic)
    assert result["all_child_indices_exactly_once"] is False
    assert result["status"] == aggregate.STATE_UNRESOLVED
    assert result["parent_cube_unsat"] is False
    assert result["global_distance_claim"] is None


@pytest.mark.parametrize("state", ["VERIFIED_CHILD_SAT", "UNRESOLVED"])
def test_sat_or_unresolved_child_is_never_promoted(
    state: str,
    refinement: dict,
    parent: dict,
    synthetic: optimized.OptimizedInstance,
    tmp_path: Path,
) -> None:
    validations = [
        _validation(refinement, index, tmp_path) for index in range(4)
    ]
    candidate = validations[2]
    candidate.update({
        "state": state,
        "valid": False,
        "strict_proof_unsat": False,
        "fresh_proof_replay": False,
        "certificate": None,
        "failures": ["verified SAT child" if state != "UNRESOLVED" else "timeout"],
    })
    validations[2] = aggregate.seal(candidate, "validation_sha256")
    result = _aggregate(refinement, parent, validations, synthetic)
    assert result["all_child_indices_exactly_once"] is True
    assert result["all_children_proof_carrying_unsat"] is False
    assert result["status"] == aggregate.STATE_UNRESOLVED
    assert result["parent_cube_unsat"] is False
    assert result["global_distance_claim"] is None


def test_resealed_child_units_and_hash_tamper_fails_closed(
    refinement: dict,
    parent: dict,
    synthetic: optimized.OptimizedInstance,
    tmp_path: Path,
) -> None:
    validations = [
        _validation(refinement, index, tmp_path) for index in range(4)
    ]
    candidate = validations[1]
    certificate = candidate["certificate"]
    bad_units = copy.deepcopy(candidate["combined_unit_clauses"])
    bad_units[-1] = [-abs(bad_units[-1][0])]
    bad_hash = aggregate.canonical_sha256(bad_units)
    candidate["combined_unit_clauses"] = bad_units
    candidate["combined_unit_clauses_sha256"] = bad_hash
    certificate["combined_unit_clauses"] = copy.deepcopy(bad_units)
    certificate["combined_unit_clauses_sha256"] = bad_hash
    candidate["certificate"] = aggregate.seal(
        certificate, "certificate_sha256"
    )
    validations[1] = aggregate.seal(candidate, "validation_sha256")

    result = _aggregate(refinement, parent, validations, synthetic)
    assert result["status"] == aggregate.STATE_UNRESOLVED
    failures = result["child_records"][1]["binding_failures"]
    assert "combined_unit_clauses binding mismatch" in failures
    assert "combined_unit_clauses_sha256 binding mismatch" in failures


def test_resealed_refinement_manifest_tamper_fails_authentication(
    refinement: dict,
    parent: dict,
    synthetic: optimized.OptimizedInstance,
    tmp_path: Path,
) -> None:
    validations = [
        _validation(refinement, index, tmp_path) for index in range(4)
    ]
    changed = copy.deepcopy(refinement)
    changed["coverage"]["exhaustive"] = False
    changed = hierarchy.seal(changed, "manifest_sha256")
    result = _aggregate(changed, parent, validations, synthetic)
    assert result["manifest_authenticated"] is False
    assert result["status"] == aggregate.STATE_UNRESOLVED
    assert result["parent_cube_unsat"] is False
    assert result["global_distance_claim"] is None


def test_certificate_for_one_child_cannot_be_substituted_for_another(
    refinement: dict,
    parent: dict,
    synthetic: optimized.OptimizedInstance,
    tmp_path: Path,
) -> None:
    validations = [
        _validation(refinement, index, tmp_path) for index in range(4)
    ]
    validations[3]["certificate"] = copy.deepcopy(validations[0]["certificate"])
    validations[3] = aggregate.seal(validations[3], "validation_sha256")
    result = _aggregate(refinement, parent, validations, synthetic)
    assert result["status"] == aggregate.STATE_UNRESOLVED
    failures = result["child_records"][3]["binding_failures"]
    assert "certificate/validation child_index binding mismatch" in failures
    assert "certificate/validation child_cnf_sha256 binding mismatch" in failures
    assert "certificate/validation child_dimacs_sha256 binding mismatch" in failures
