from __future__ import annotations

import copy
import hashlib
from pathlib import Path

import numpy as np
import pytest

from evaluation import paper400_dic5_optimized_cnf_final_v13 as optimized
from investigations import paper400_dic5_cube16 as cube16
from investigations import paper400_dic5_cube16_proof_aggregate_v1 as aggregate


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
def manifest(synthetic: optimized.OptimizedInstance) -> dict:
    return cube16.build_coverage_manifest(
        synthetic, strict_base=False, split_variables=(1, 2, 3, 4),
    )


def _artifact(role: str, name: str, marker: str) -> dict:
    return {
        "role": role,
        "relative_path": f"artifacts/{name}",
        "file_sha256": marker * 64,
        "bytes": 17,
    }


def _certificate(manifest: dict, index: int) -> dict:
    cube = manifest["cubes"][index]
    authority = (
        aggregate.AUTHORITY_PRODUCTION if manifest["test_only"] is False
        else aggregate.AUTHORITY_TEST_ONLY
    )
    proof_chain = aggregate.seal({
        "format": "binary-drat+converted-lrat-v1",
        "binary_drat": _artifact("raw-binary-drat", "cube.drat", "1"),
        "converted_lrat": _artifact("converted-lrat", "cube.lrat", "2"),
        "drat_checker_sha256": aggregate.EXPECTED_DRAT_CHECKER_SHA256,
        "lrat_checker_sha256": aggregate.EXPECTED_LRAT_CHECKER_SHA256,
        "trusted_policy_sha256": aggregate.EXPECTED_POLICY_SHA256,
        "drat_independently_verified": True,
        "lrat_independently_verified": True,
        "fresh_drat_replay": True,
        "fresh_lrat_replay": True,
        "drat_record_sha256": "3" * 64,
        "lrat_record_sha256": "4" * 64,
        "fresh_replay_record_sha256": "5" * 64,
    }, "chain_sha256")
    return aggregate.seal({
        "schema_version": aggregate.SCHEMA_VERSION,
        "kind": aggregate.CUBE_CERTIFICATE_KIND,
        "gate": aggregate.RUNNER_GATE,
        "state": aggregate.STATE_PROOF_UNSAT,
        "authority": authority,
        "test_only": authority != aggregate.AUTHORITY_PRODUCTION,
        "production_eligible": authority == aggregate.AUTHORITY_PRODUCTION,
        "manifest_sha256": manifest["manifest_sha256"],
        "base_cnf_sha256": manifest["base"]["cnf_sha256"],
        "base_dimacs_sha256": manifest["base"]["dimacs_sha256"],
        "cube_index": index,
        "cube_id": cube["cube_id"],
        "cube_sha256": cube["cube_sha256"],
        "cube_cnf_sha256": cube["cube_cnf_sha256"],
        "cube_dimacs_sha256": cube["cube_dimacs_sha256"],
        "cube_num_variables": cube["cube_num_variables"],
        "cube_num_clauses": cube["cube_num_clauses"],
        "cube_dimacs_bytes": cube["cube_dimacs_bytes"],
        "unit_clauses": cube["unit_clauses"],
        "solver": {
            "name": aggregate.EXPECTED_SOLVER_NAME,
            "version": aggregate.EXPECTED_SOLVER_VERSION,
            "executable_sha256": aggregate.EXPECTED_SOLVER_SHA256,
        },
        "decision": {
            "outcome": "unsat",
            "status_name": "UNSATISFIABLE",
            "decision_complete": True,
            "clean_exit": True,
            "timed_out": False,
            "solver_invocations": 1,
        },
        "proof_chain": proof_chain,
        "cube16_source_sha256": aggregate.EXPECTED_CUBE16_SOURCE_SHA256,
        "aggregate_source_sha256": hashlib.sha256(
            Path(aggregate.__file__).read_bytes()
        ).hexdigest(),
        "source_binding_sha256": "6" * 64,
        "toolchain_binding_sha256": "7" * 64,
        "predecessor_chain_sha256": "8" * 64,
        "global_distance_claim": None,
        "publication_certificate": False,
        "upload_authorized": False,
    }, "certificate_sha256")


def _proof_validation(manifest: dict, index: int, tmp_path: Path) -> dict:
    cube = manifest["cubes"][index]
    authority = (
        aggregate.AUTHORITY_PRODUCTION if manifest["test_only"] is False
        else aggregate.AUTHORITY_TEST_ONLY
    )
    certificate = _certificate(manifest, index)
    return aggregate.seal({
        "schema_version": aggregate.SCHEMA_VERSION,
        "kind": aggregate.CUBE_VALIDATION_KIND,
        "gate": aggregate.RUNNER_GATE,
        "root": str((tmp_path / f"cube-{index:02d}").absolute()),
        "manifest_sha256": manifest["manifest_sha256"],
        "cube_index": index,
        "cube_id": cube["cube_id"],
        "cube_sha256": cube["cube_sha256"],
        "cube_cnf_sha256": cube["cube_cnf_sha256"],
        "cube_dimacs_sha256": cube["cube_dimacs_sha256"],
        "state": aggregate.STATE_PROOF_UNSAT,
        "authority": authority,
        "test_only": authority != aggregate.AUTHORITY_PRODUCTION,
        "valid": True,
        "strict_proof_unsat": True,
        "strict_verified_sat": False,
        "fresh_proof_replay": True,
        "source_toolchain_fresh": True,
        "certificate": certificate,
        "sat_terminal": None,
        "failures": [],
    }, "validation_sha256")


def _sat_validation(manifest: dict, index: int, tmp_path: Path) -> dict:
    cube = manifest["cubes"][index]
    authority = (
        aggregate.AUTHORITY_PRODUCTION if manifest["test_only"] is False
        else aggregate.AUTHORITY_TEST_ONLY
    )
    terminal = {
        "cube_index": index,
        "classification": "VERIFIED_SAT_LOW_OPERATOR",
        "strict_verified_sat": True,
        "record_sha256": "9" * 64,
    }
    return aggregate.seal({
        "schema_version": aggregate.SCHEMA_VERSION,
        "kind": aggregate.CUBE_VALIDATION_KIND,
        "gate": aggregate.RUNNER_GATE,
        "root": str((tmp_path / f"sat-{index:02d}").absolute()),
        "manifest_sha256": manifest["manifest_sha256"],
        "cube_index": index,
        "cube_id": cube["cube_id"],
        "cube_sha256": cube["cube_sha256"],
        "cube_cnf_sha256": cube["cube_cnf_sha256"],
        "cube_dimacs_sha256": cube["cube_dimacs_sha256"],
        "state": aggregate.STATE_VERIFIED_SAT,
        "authority": authority,
        "test_only": authority != aggregate.AUTHORITY_PRODUCTION,
        "valid": True,
        "strict_proof_unsat": False,
        "strict_verified_sat": True,
        "fresh_proof_replay": False,
        "source_toolchain_fresh": True,
        "certificate": None,
        "sat_terminal": terminal,
        "failures": [],
    }, "validation_sha256")


def _reseal_validation(value: dict) -> dict:
    return aggregate.seal(value, "validation_sha256")


def _reseal_certificate(value: dict) -> dict:
    return aggregate.seal(value, "certificate_sha256")


def test_all_16_durable_test_certificates_are_exactly_once_but_non_scientific(
    manifest: dict,
    synthetic: optimized.OptimizedInstance,
    tmp_path: Path,
) -> None:
    validations = [_proof_validation(manifest, index, tmp_path) for index in range(16)]
    result = aggregate.aggregate_cube_validations(
        manifest, validations, synthetic, strict_base=False,
    )
    assert result["all_16_indices_exactly_once"] is True
    assert result["all_16_proof_carrying_unsat"] is True
    assert result["status"] == (
        "TEST_ONLY_ALL_CUBES_PROOF_UNSAT_NO_SCIENTIFIC_CLAIM"
    )
    assert result["distance_lower_bound"] is None
    assert result["publication_certificate"] is False
    assert len(result["ordered_certificate_bindings"]) == 16


@pytest.mark.parametrize("mode", ["missing", "duplicate", "unbound"])
def test_missing_duplicate_or_unbound_cube_is_unresolved(
    mode: str,
    manifest: dict,
    synthetic: optimized.OptimizedInstance,
    tmp_path: Path,
) -> None:
    values = [_proof_validation(manifest, index, tmp_path) for index in range(16)]
    if mode == "missing":
        values.pop()
    elif mode == "duplicate":
        values[-1] = copy.deepcopy(values[0])
    else:
        values[6]["cube_cnf_sha256"] = "f" * 64
        values[6] = _reseal_validation(values[6])
    result = aggregate.aggregate_cube_validations(
        manifest, values, synthetic, strict_base=False,
    )
    assert result["status"] == aggregate.STATE_UNRESOLVED
    assert result["distance_lower_bound"] is None
    assert result["publication_certificate"] is False


def test_checker_boolean_or_artifact_tamper_fails_even_when_resealed(
    manifest: dict,
    synthetic: optimized.OptimizedInstance,
    tmp_path: Path,
) -> None:
    values = [_proof_validation(manifest, index, tmp_path) for index in range(16)]
    certificate = copy.deepcopy(values[4]["certificate"])
    certificate["proof_chain"]["fresh_lrat_replay"] = False
    certificate["proof_chain"] = aggregate.seal(
        certificate["proof_chain"], "chain_sha256",
    )
    certificate = _reseal_certificate(certificate)
    values[4]["certificate"] = certificate
    values[4] = _reseal_validation(values[4])
    result = aggregate.aggregate_cube_validations(
        manifest, values, synthetic, strict_base=False,
    )
    assert result["status"] == aggregate.STATE_UNRESOLVED
    assert any(
        "fresh_lrat_replay" in failure
        for failure in result["cube_records"][4]["binding_failures"]
    )


def test_one_certificate_cannot_be_substituted_for_all_16_cubes(
    manifest: dict,
    synthetic: optimized.OptimizedInstance,
    tmp_path: Path,
) -> None:
    values = [_proof_validation(manifest, index, tmp_path) for index in range(16)]
    cube_zero_certificate = copy.deepcopy(values[0]["certificate"])
    for index in range(1, 16):
        values[index]["certificate"] = copy.deepcopy(cube_zero_certificate)
        values[index] = _reseal_validation(values[index])

    failures = aggregate.validate_cube_run_record(
        values[1], manifest, require_production=False,
    )
    assert "certificate/validation cube_index binding mismatch" in failures
    assert "certificate/validation cube_sha256 binding mismatch" in failures
    assert "certificate/validation cube_cnf_sha256 binding mismatch" in failures
    assert "certificate/validation cube_dimacs_sha256 binding mismatch" in failures

    result = aggregate.aggregate_cube_validations(
        manifest, values, synthetic, strict_base=False,
    )
    assert result["all_16_indices_exactly_once"] is True
    assert result["all_16_proof_carrying_unsat"] is False
    assert result["status"] == aggregate.STATE_UNRESOLVED
    assert result["distance_lower_bound"] is None
    assert result["publication_certificate"] is False


def test_single_cube_global_claim_is_rejected(manifest: dict) -> None:
    certificate = _certificate(manifest, 3)
    certificate["global_distance_claim"] = "d>=20"
    certificate = _reseal_certificate(certificate)
    failures = aggregate.validate_cube_certificate(
        certificate, manifest, require_production=False,
    )
    assert "a single cube certificate cannot make a global distance claim" in failures


def test_strict_sat_short_circuits_missing_unsat_roots(
    manifest: dict,
    synthetic: optimized.OptimizedInstance,
    tmp_path: Path,
) -> None:
    result = aggregate.aggregate_cube_validations(
        manifest, [_sat_validation(manifest, 8, tmp_path)],
        synthetic, strict_base=False,
    )
    assert result["status"] == "TEST_ONLY_VERIFIED_SAT_NO_SCIENTIFIC_CLAIM"
    assert result["strict_verified_sat_count"] == 1
    assert result["distance_lower_bound"] is None


def test_unknown_is_never_promoted(
    manifest: dict,
    synthetic: optimized.OptimizedInstance,
    tmp_path: Path,
) -> None:
    value = _proof_validation(manifest, 0, tmp_path)
    value.update({
        "state": aggregate.STATE_UNRESOLVED,
        "valid": False,
        "strict_proof_unsat": False,
        "fresh_proof_replay": False,
        "certificate": None,
        "failures": ["solver timeout"],
    })
    value = _reseal_validation(value)
    result = aggregate.aggregate_cube_validations(
        manifest, [value], synthetic, strict_base=False,
    )
    assert result["status"] == aggregate.STATE_UNRESOLVED
    assert result["publication_certificate"] is False


def test_manifest_reseal_tamper_fails_before_certificate_aggregation(
    manifest: dict,
    synthetic: optimized.OptimizedInstance,
    tmp_path: Path,
) -> None:
    changed = copy.deepcopy(manifest)
    changed["coverage"]["exhaustive"] = False
    changed = cube16._seal(changed, "manifest_sha256")
    values = [_proof_validation(changed, index, tmp_path) for index in range(16)]
    result = aggregate.aggregate_cube_validations(
        changed, values, synthetic, strict_base=False,
    )
    assert result["status"] == aggregate.STATE_UNRESOLVED
    assert result["production_manifest"] is False


def test_aggregate_module_has_no_process_launch_surface() -> None:
    source = Path(aggregate.__file__).read_text(encoding="utf-8")
    assert "import subprocess" not in source
    assert "Popen(" not in source
    assert "check_call(" not in source


def test_schema_numbers_reject_bool_aliases_after_reseal(
    manifest: dict,
    tmp_path: Path,
) -> None:
    certificate = _certificate(manifest, 0)
    certificate["schema_version"] = True
    certificate = _reseal_certificate(certificate)
    certificate_failures = aggregate.validate_cube_certificate(
        certificate, manifest, require_production=False,
    )
    assert "certificate schema version mismatch" in certificate_failures

    validation = _proof_validation(manifest, 0, tmp_path)
    validation["schema_version"] = True
    validation = _reseal_validation(validation)
    validation_failures = aggregate.validate_cube_run_record(
        validation, manifest, require_production=False,
    )
    assert "validation schema version mismatch" in validation_failures


def test_fixed_cube_and_aggregate_source_hashes_cannot_be_resealed_away(
    manifest: dict,
) -> None:
    certificate = _certificate(manifest, 0)
    certificate["cube16_source_sha256"] = "d" * 64
    certificate["aggregate_source_sha256"] = "e" * 64
    certificate = _reseal_certificate(certificate)
    failures = aggregate.validate_cube_certificate(
        certificate, manifest, require_production=False,
    )
    assert "cube16 source hash mismatch" in failures
    assert "aggregate source hash mismatch" in failures
    assert len(failures) == len(set(failures))


def test_actual_production_manifest_rebuild_is_zero_solver() -> None:
    instance = optimized.build_optimized_instance()
    assert instance.report["solver_invoked"] is False
    production = cube16.build_coverage_manifest(instance, strict_base=True)
    replay = cube16.verify_coverage_manifest(
        production, instance, strict_base=True,
    )
    assert replay["valid"] is True
    assert replay["base_audit_pass_bound"] is True
    assert replay["solver_invoked"] is False
    assert production["test_only"] is False
    assert len(production["cubes"]) == 16


def test_injected_validator_cannot_promote_production_manifest(
    tmp_path: Path,
) -> None:
    instance = optimized.build_optimized_instance()
    production = cube16.build_coverage_manifest(instance, strict_base=True)
    validations = [
        _proof_validation(production, index, tmp_path) for index in range(16)
    ]
    by_root = {
        validation["root"]: validation for validation in validations
    }

    def injected(path: Path, bound_manifest: dict) -> dict:
        assert bound_manifest["manifest_sha256"] == production["manifest_sha256"]
        return by_root[str(path.absolute())]

    result = aggregate.aggregate_cube_roots(
        production,
        [Path(validation["root"]) for validation in validations],
        instance,
        strict_base=True,
        validator=injected,
    )
    assert result["all_16_proof_carrying_unsat"] is True
    assert result["roots_freshly_validated"] is False
    assert result["status"] == (
        "CANDIDATE_PROOF_CARRYING_LOWER_20_REQUIRES_FRESH_ROOT_REPLAY"
    )
    assert result["distance_lower_bound"] is None
    assert result["publication_certificate"] is False


def test_injected_validator_cannot_scientifically_reject_production_manifest(
    tmp_path: Path,
) -> None:
    instance = optimized.build_optimized_instance()
    production = cube16.build_coverage_manifest(instance, strict_base=True)
    fake_sat = _sat_validation(production, 1, tmp_path)

    def injected(path: Path, bound_manifest: dict) -> dict:
        assert path == Path(fake_sat["root"])
        assert bound_manifest["manifest_sha256"] == production["manifest_sha256"]
        return fake_sat

    result = aggregate.aggregate_cube_roots(
        production,
        [Path(fake_sat["root"])],
        instance,
        strict_base=True,
        validator=injected,
    )
    assert result["roots_freshly_validated"] is False
    assert result["strict_verified_sat_count"] == 1
    assert result["status"] == "CANDIDATE_VERIFIED_SAT_REQUIRES_FRESH_ROOT_REPLAY"
    assert result["distance_lower_bound"] is None
    assert result["publication_certificate"] is False
    assert result["claim_semantics"]["distance_claim"] is None


def test_sat_terminal_cube_index_rejects_bool_alias_after_reseal(
    manifest: dict,
    tmp_path: Path,
) -> None:
    validation = _sat_validation(manifest, 1, tmp_path)
    validation["sat_terminal"]["cube_index"] = True
    validation = _reseal_validation(validation)
    failures = aggregate.validate_cube_run_record(
        validation, manifest, require_production=False,
    )
    assert "verified SAT terminal binding invalid" in failures
