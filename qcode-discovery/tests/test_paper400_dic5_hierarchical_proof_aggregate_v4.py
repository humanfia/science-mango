from __future__ import annotations

import copy
from pathlib import Path

import numpy as np
import pytest

from evaluation import paper400_dic5_optimized_cnf_final_v13 as optimized
from investigations import paper400_dic5_cube16 as cube16
from investigations import paper400_dic5_hierarchical_cubes_v1 as hierarchy
from investigations import paper400_dic5_hierarchical_proof_aggregate_v4 as aggregate


PARENT_INDEX = 8
SPLIT_WIDTH = 2


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
def material() -> tuple[optimized.OptimizedInstance, dict, dict]:
    instance = _synthetic_instance()
    parent = cube16.build_coverage_manifest(
        instance,
        strict_base=False,
        split_variables=(1, 2, 3, 4),
    )
    refinement = hierarchy.build_refinement_manifest(
        parent,
        instance,
        parent_cube_index=PARENT_INDEX,
        split_width=SPLIT_WIDTH,
        strict_base=False,
    )
    return instance, parent, refinement


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
    root = aggregate.v1.root_aggregate
    return aggregate.seal({
        "format": "binary-drat+converted-lrat-v1",
        "binary_drat": _artifact("raw-binary-drat", "child.drat", "1"),
        "converted_lrat": _artifact("converted-lrat", "child.lrat", "2"),
        "drat_checker_sha256": root.EXPECTED_DRAT_CHECKER_SHA256,
        "lrat_checker_sha256": root.EXPECTED_LRAT_CHECKER_SHA256,
        "trusted_policy_sha256": root.EXPECTED_POLICY_SHA256,
        "drat_independently_verified": True,
        "lrat_independently_verified": True,
        "fresh_drat_replay": True,
        "fresh_lrat_replay": True,
        "drat_record_sha256": "3" * 64,
        "lrat_record_sha256": "4" * 64,
        "fresh_replay_record_sha256": "5" * 64,
    }, "chain_sha256")


def _quiescence(
    proof_chain: dict,
    state: str = aggregate.TRANSPORT_STATE_CHECKPOINTED,
) -> dict:
    proof = {
        "role": "raw-binary-drat",
        "relative_path": "runtime/dmtcp/proof.drat",
        "file_sha256": proof_chain["binary_drat"]["file_sha256"],
        "bytes": proof_chain["binary_drat"]["bytes"],
        "mode": 0o600,
        "device": 11,
        "inode": 12,
        "uid": 0,
        "links": 1,
    }
    attempted = state == aggregate.TRANSPORT_STATE_INACTIVE
    observation = {
        "attempted": attempted,
        "reachable": True if attempted else None,
        "peer_count": 0 if attempted else None,
        "running": False if attempted else None,
    }
    return {
        "method": (
            "dmtcp-inactive-exit-harvest-v1"
            if attempted else "dmtcp-checkpoint-stop-v1"
        ),
        "transport_state": state,
        "latest_generation": 1,
        "latest_pid": 12345,
        "latest_proc_start_ticks": 67890,
        "latest_pid_identity_alive": False,
        "coordinator_observations": [
            copy.deepcopy(observation), copy.deepcopy(observation),
        ],
        "writable_holders_before": [],
        "writable_holders_after": [],
        "proof_before": copy.deepcopy(proof),
        "proof_after": copy.deepcopy(proof),
    }


def _certificate(
    refinement: dict, index: int,
    *,
    profile: str = aggregate.TRANSPORT_PROFILE_NATIVE_V4,
    source_certificate_sha256: str = "b" * 64,
    state: str = aggregate.TRANSPORT_STATE_CHECKPOINTED,
) -> dict:
    child = refinement["children"][index]
    authority = (
        aggregate.AUTHORITY_TEST_ONLY
        if refinement["test_only"]
        else aggregate.AUTHORITY_PRODUCTION
    )
    root = aggregate.v1.root_aggregate
    proof_chain = _proof_chain()
    payload = {
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
            "name": root.EXPECTED_SOLVER_NAME,
            "version": root.EXPECTED_SOLVER_VERSION,
            "executable_sha256": root.EXPECTED_SOLVER_SHA256,
        },
        "decision": aggregate.expected_unsat_decision(state),
        "proof_chain": proof_chain,
        "resume_static_sha256": "6" * 64,
        "transport_chain_sha256": "7" * 64,
        "transport_quiescence": _quiescence(proof_chain, state),
        "source_binding_sha256": "8" * 64,
        "toolchain_binding_sha256": "9" * 64,
        "predecessor_chain_sha256": "a" * 64,
        "parent_cube_unsat_claim": False,
        "global_distance_claim": None,
        "publication_certificate": False,
        "upload_authorized": False,
    }
    if profile == aggregate.TRANSPORT_PROFILE_NATIVE_V4:
        payload["transport_provenance"] = (
            aggregate.native_transport_provenance()
        )
    elif profile == aggregate.TRANSPORT_PROFILE_ADOPTED_FROZEN_V3:
        payload["transport_provenance"] = (
            aggregate.adopted_transport_provenance(
                payload,
                source_certificate_sha256=source_certificate_sha256,
            )
        )
    else:
        raise ValueError("unsupported test profile")
    return aggregate.seal(payload, "certificate_sha256")


def _validation(
    refinement: dict, index: int, tmp_path: Path,
    *,
    profile: str = aggregate.TRANSPORT_PROFILE_NATIVE_V4,
) -> dict:
    authority = (
        aggregate.AUTHORITY_TEST_ONLY
        if refinement["test_only"]
        else aggregate.AUTHORITY_PRODUCTION
    )
    certificate = _certificate(refinement, index, profile=profile)
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
        "transport_provenance": copy.deepcopy(
            certificate["transport_provenance"]
        ),
        "certificate": certificate,
        "failures": [],
        "global_distance_claim": None,
        "publication_certificate": False,
        "upload_authorized": False,
    }, "validation_sha256")


def _all_validations(refinement: dict, tmp_path: Path) -> list[dict]:
    return [
        _validation(refinement, index, tmp_path)
        for index in range(len(refinement["children"]))
    ]


def _aggregate(material: tuple, validations: list[dict]) -> dict:
    instance, parent, refinement = material
    return aggregate.aggregate_child_validations(
        refinement,
        parent,
        validations,
        instance,
        expected_parent_cube_index=PARENT_INDEX,
        expected_split_width=SPLIT_WIDTH,
        strict_base=False,
    )


def _reseal_certificate(validation: dict, certificate: dict) -> dict:
    result = copy.deepcopy(validation)
    result["certificate"] = aggregate.seal(
        certificate, "certificate_sha256",
    )
    result["transport_provenance"] = copy.deepcopy(
        result["certificate"]["transport_provenance"]
    )
    return aggregate.seal(result, "validation_sha256")


def test_native_v4_complete_set_derives_parent_only(
    material: tuple, tmp_path: Path,
) -> None:
    refinement = material[2]
    validations = _all_validations(refinement, tmp_path)
    result = _aggregate(material, validations)

    first = validations[0]
    assert first["transport_provenance"] == (
        aggregate.native_transport_provenance()
    )
    assert first["certificate"]["transport_provenance"] == (
        first["transport_provenance"]
    )
    assert aggregate.validate_child_run_record(first, refinement) == []
    assert first["certificate"]["decision"]["decision_basis"].endswith(
        "exact-child-cnf-v4"
    )
    assert first["certificate"]["proof_chain"]["fresh_drat_replay"] is True
    assert first["certificate"]["proof_chain"]["fresh_lrat_replay"] is True
    assert result["status"] == aggregate.STATE_PARENT_UNSAT
    assert result["all_transport_provenance_profiles_complete"] is True
    assert result["all_children_proof_carrying_unsat"] is True
    assert result["parent_cube_unsat"] is True
    assert result["global_distance_claim"] is None
    assert {
        item["transport_profile"]
        for item in result["ordered_child_certificate_bindings"]
    } == {aggregate.TRANSPORT_PROFILE_NATIVE_V4}


def test_frozen_v3_adoption_profile_is_source_bound_and_accepted(
    material: tuple, tmp_path: Path,
) -> None:
    refinement = material[2]
    validations = [
        _validation(
            refinement, index, tmp_path,
            profile=aggregate.TRANSPORT_PROFILE_ADOPTED_FROZEN_V3,
        )
        for index in range(len(refinement["children"]))
    ]
    first = validations[0]
    certificate = first["certificate"]
    provenance = certificate["transport_provenance"]
    assert provenance["source_schema_version"] == 3
    assert provenance["source_runner_gate"] == aggregate.FROZEN_V3_RUNNER_GATE
    assert provenance["source_runner_sha256"] == (
        "7088126800ff618629fb059ec002df09c9a127f57609326ff2857cf793eaf54a"
    )
    assert provenance["source_certificate_sha256"] == "b" * 64
    assert provenance["adoption_record_sha256"] == (
        aggregate.expected_adoption_record_sha256(
            certificate, source_certificate_sha256="b" * 64,
        )
    )
    assert aggregate.validate_child_run_record(first, refinement) == []

    result = _aggregate(material, validations)
    assert result["parent_cube_unsat"] is True
    assert result["all_transport_provenance_profiles_complete"] is True
    assert all(
        item["adoption_record_sha256"] is not None
        for item in result["ordered_child_certificate_bindings"]
    )


@pytest.mark.parametrize(
    ("field", "bad_value"),
    [
        ("source_runner_sha256", "c" * 64),
        ("source_certificate_sha256", "c" * 64),
        ("adoption_record_sha256", "c" * 64),
    ],
)
def test_native_profile_requires_exact_none_truth_table(
    field: str, bad_value: object, material: tuple, tmp_path: Path,
) -> None:
    refinement = material[2]
    validations = _all_validations(refinement, tmp_path)
    certificate = copy.deepcopy(validations[0]["certificate"])
    certificate["transport_provenance"][field] = bad_value
    validations[0] = _reseal_certificate(validations[0], certificate)

    result = _aggregate(material, validations)
    failures = result["child_records"][0]["binding_failures"]
    assert "native v4 transport provenance truth table mismatch" in failures
    assert result["all_transport_provenance_profiles_complete"] is False
    assert result["status"] == aggregate.STATE_UNRESOLVED
    assert result["parent_cube_unsat"] is False


@pytest.mark.parametrize(
    ("field", "bad_value", "message"),
    [
        ("source_schema_version", 4, "source_schema_version mismatch"),
        ("source_runner_gate", aggregate.RUNNER_GATE, "source_runner_gate mismatch"),
        ("source_runner_sha256", "c" * 64, "source_runner_sha256 mismatch"),
        ("source_certificate_sha256", "bad", "source certificate SHA-256 invalid"),
        ("adoption_record_sha256", "c" * 64, "source binding mismatch"),
    ],
)
def test_adopted_profile_truth_table_fails_closed(
    field: str, bad_value: object, message: str,
    material: tuple, tmp_path: Path,
) -> None:
    refinement = material[2]
    candidate = _validation(
        refinement, 0, tmp_path,
        profile=aggregate.TRANSPORT_PROFILE_ADOPTED_FROZEN_V3,
    )
    certificate = copy.deepcopy(candidate["certificate"])
    certificate["transport_provenance"][field] = bad_value
    candidate = _reseal_certificate(candidate, certificate)

    failures = aggregate.validate_child_run_record(candidate, refinement)
    assert any(message in failure for failure in failures)


def test_adoption_record_binds_target_transport_evidence(
    material: tuple, tmp_path: Path,
) -> None:
    refinement = material[2]
    candidate = _validation(
        refinement, 0, tmp_path,
        profile=aggregate.TRANSPORT_PROFILE_ADOPTED_FROZEN_V3,
    )
    certificate = copy.deepcopy(candidate["certificate"])
    original = certificate["transport_provenance"]["adoption_record_sha256"]
    certificate["transport_chain_sha256"] = "c" * 64
    candidate = _reseal_certificate(candidate, certificate)

    failures = aggregate.validate_child_run_record(candidate, refinement)
    assert "adoption record source binding mismatch" in failures
    assert candidate["certificate"]["transport_provenance"][
        "adoption_record_sha256"
    ] == original


def test_validation_must_embed_the_same_profile_as_certificate(
    material: tuple, tmp_path: Path,
) -> None:
    refinement = material[2]
    candidate = _validation(refinement, 0, tmp_path)
    certificate = candidate["certificate"]
    candidate["transport_provenance"] = (
        aggregate.adopted_transport_provenance(
            certificate, source_certificate_sha256="b" * 64,
        )
    )
    candidate = aggregate.seal(candidate, "validation_sha256")

    failures = aggregate.validate_child_run_record(candidate, refinement)
    assert (
        "certificate/validation transport_provenance binding mismatch"
        in failures
    )


def test_v3_schema_gate_and_decision_basis_cannot_enter_v4(
    material: tuple, tmp_path: Path,
) -> None:
    refinement = material[2]
    candidate = _validation(refinement, 0, tmp_path)
    certificate = copy.deepcopy(candidate["certificate"])
    certificate["schema_version"] = 3
    certificate["kind"] = (
        "paper400-dic5-proof-carrying-refined-child-unsat-v3"
    )
    certificate["gate"] = aggregate.FROZEN_V3_RUNNER_GATE
    certificate["decision"]["decision_basis"] = (
        "complete-drat+lrat+fresh-replay-from-exact-child-cnf-v3"
    )
    candidate = _reseal_certificate(candidate, certificate)

    failures = aggregate.validate_child_run_record(candidate, refinement)
    assert "certificate schema version mismatch" in failures
    assert "certificate kind/gate mismatch" in failures
    assert "UNSAT proof-replay decision semantics mismatch" in failures


@pytest.mark.parametrize("field", ["fresh_drat_replay", "fresh_lrat_replay"])
def test_profile_never_waives_fresh_proof_replay(
    field: str, material: tuple, tmp_path: Path,
) -> None:
    refinement = material[2]
    candidate = _validation(
        refinement, 0, tmp_path,
        profile=aggregate.TRANSPORT_PROFILE_ADOPTED_FROZEN_V3,
    )
    certificate = copy.deepcopy(candidate["certificate"])
    chain = copy.deepcopy(certificate["proof_chain"])
    chain[field] = False
    certificate["proof_chain"] = aggregate.seal(chain, "chain_sha256")
    certificate["transport_provenance"] = (
        aggregate.adopted_transport_provenance(
            certificate, source_certificate_sha256="b" * 64,
        )
    )
    candidate = _reseal_certificate(candidate, certificate)

    failures = aggregate.validate_child_run_record(candidate, refinement)
    assert f"{field} is not true" in failures


@pytest.mark.parametrize(
    "field", ["fresh_proof_replay", "source_toolchain_fresh"]
)
def test_validation_freshness_truth_table_remains_mandatory(
    field: str, material: tuple, tmp_path: Path,
) -> None:
    refinement = material[2]
    candidate = _validation(refinement, 0, tmp_path)
    candidate[field] = False
    candidate = aggregate.seal(candidate, "validation_sha256")
    failures = aggregate.validate_child_run_record(candidate, refinement)
    assert "proof-UNSAT validation truth table mismatch" in failures


def test_production_eligibility_requires_a_complete_profile(
    material: tuple,
) -> None:
    refinement = copy.deepcopy(material[2])
    refinement["test_only"] = False
    native = _certificate(refinement, 0)
    adopted = _certificate(
        refinement, 0,
        profile=aggregate.TRANSPORT_PROFILE_ADOPTED_FROZEN_V3,
    )
    assert native["production_eligible"] is True
    assert adopted["production_eligible"] is True
    assert aggregate.validate_child_certificate(native, refinement) == []
    assert aggregate.validate_child_certificate(adopted, refinement) == []

    bad = copy.deepcopy(native)
    bad.pop("certificate_sha256")
    bad["transport_provenance"]["adoption_record_sha256"] = "c" * 64
    bad = aggregate.seal(bad, "certificate_sha256")
    failures = aggregate.validate_child_certificate(bad, refinement)
    assert "native v4 transport provenance truth table mismatch" in failures
    assert "certificate production eligibility mismatch" in failures


@pytest.mark.parametrize("mode", ["missing", "duplicate"])
def test_exact_child_set_is_still_required(
    mode: str, material: tuple, tmp_path: Path,
) -> None:
    validations = _all_validations(material[2], tmp_path)
    if mode == "missing":
        validations.pop()
    else:
        validations[-1] = copy.deepcopy(validations[0])
    result = _aggregate(material, validations)
    assert result["all_child_indices_exactly_once"] is False
    assert result["parent_cube_unsat"] is False
    assert result["status"] == aggregate.STATE_UNRESOLVED


def test_noncanonical_adoption_target_fails_closed_without_raising(
    material: tuple,
) -> None:
    refinement = material[2]
    certificate = _certificate(
        refinement, 0,
        profile=aggregate.TRANSPORT_PROFILE_ADOPTED_FROZEN_V3,
    )
    certificate["decision"] = {"opaque": object()}
    failures = aggregate.validate_child_certificate(certificate, refinement)
    assert "certificate self-hash mismatch" in failures
    assert "adoption record target binding is not canonical" in failures


def test_transport_provenance_envelope_is_a_closed_schema(
    material: tuple, tmp_path: Path,
) -> None:
    refinement = material[2]
    original = _validation(refinement, 0, tmp_path)
    variants = []

    unknown = copy.deepcopy(original["certificate"])
    unknown["transport_provenance"]["profile"] = "UNKNOWN"
    variants.append((unknown, "unsupported transport provenance profile"))

    extra = copy.deepcopy(original["certificate"])
    extra["transport_provenance"]["unexpected"] = None
    variants.append((extra, "transport provenance field set mismatch"))

    missing = copy.deepcopy(original["certificate"])
    missing["transport_provenance"].pop("adoption_record_sha256")
    variants.append((missing, "transport provenance field set mismatch"))

    for certificate, message in variants:
        candidate = _reseal_certificate(original, certificate)
        failures = aggregate.validate_child_run_record(
            candidate, refinement,
        )
        assert message in failures
