from __future__ import annotations

import ast
import copy
import hashlib
import importlib.util
from pathlib import Path

import pytest

from evaluation import paper400_dic5_optimized_cnf_final_v13 as optimized
from investigations import paper400_dic5_cube16 as cube16
from investigations import paper400_dic5_cube16_proof_aggregate_v1 as aggregate


SOURCE = (
    Path(__file__).resolve().parents[1]
    / "scripts"
    / "run_paper400_dic5_cube16_standalone_proof_v1.py"
)
SPEC = importlib.util.spec_from_file_location("cube_proof_runner_v1", SOURCE)
assert SPEC is not None and SPEC.loader is not None
runner = importlib.util.module_from_spec(SPEC)
SPEC.loader.exec_module(runner)


@pytest.fixture(scope="module")
def production_material() -> tuple[optimized.OptimizedInstance, dict]:
    instance = optimized.build_optimized_instance()
    assert instance.report["solver_invoked"] is False
    manifest = cube16.build_coverage_manifest(instance, strict_base=True)
    return instance, manifest


def _artifact(role: str, name: str, marker: str) -> dict:
    return {
        "role": role,
        "relative_path": f"artifacts/{name}",
        "file_sha256": marker * 64,
        "bytes": 19,
    }


def _fake_chain(manifest: dict, index: int) -> tuple[dict, dict]:
    cube = manifest["cubes"][index]
    static_record = {
        "record_sha256": "1" * 64,
        "source_binding": {"record_sha256": "2" * 64},
        "toolchain_binding": {"record_sha256": "3" * 64},
    }
    raw_record = {"record_sha256": "4" * 64}
    drat_record = {"record_sha256": "5" * 64}
    lrat_record = {
        "record_sha256": "6" * 64,
        "lrat_artifact": _artifact("converted-lrat", "cube.lrat", "7"),
    }
    chain = {
        "raw": {
            "static": {
                "static": static_record,
                "manifest": manifest,
                "cube": cube,
            },
            "raw": raw_record,
            "proof": _artifact("raw-binary-drat", "cube.drat", "8"),
        },
        "drat": drat_record,
        "lrat": lrat_record,
    }
    fresh = {"record_sha256": "9" * 64}
    return chain, fresh


def test_import_uses_pinned_v2_safety_layer_without_science_or_process_launch(
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    source = SOURCE.read_text(encoding="utf-8")
    tree = ast.parse(source)
    prefix = source.split("def _cube_builder_helper", 1)[0]
    assert "import numpy" not in prefix
    assert "import pysat" not in prefix
    assert runner.EXPECTED_V2_SHA256 == hashlib.sha256(
        (runner.PROJECT / runner.V2_RELATIVE_PATH).read_bytes()
    ).hexdigest()
    assert runner.EXPECTED_CUBE_SHA256 == hashlib.sha256(
        (runner.PROJECT / runner.CUBE_RELATIVE_PATH).read_bytes()
    ).hexdigest()
    assert runner.EXPECTED_AGGREGATE_SHA256 == hashlib.sha256(
        (runner.PROJECT / runner.AGGREGATE_RELATIVE_PATH).read_bytes()
    ).hexdigest()
    assert isinstance(tree, ast.Module)


def test_source_binding_fixes_cube_aggregate_v2_and_optimized_hashes() -> None:
    binding = runner._source_binding()
    by_path = {
        record["relative_path"]: record["sha256"]
        for record in binding["files"]
    }
    assert by_path[runner.V2_RELATIVE_PATH] == runner.EXPECTED_V2_SHA256
    assert by_path[runner.CUBE_RELATIVE_PATH] == runner.EXPECTED_CUBE_SHA256
    assert by_path[runner.AGGREGATE_RELATIVE_PATH] == (
        runner.EXPECTED_AGGREGATE_SHA256
    )
    assert by_path[runner.OPTIMIZED_RELATIVE_PATH] == (
        runner.EXPECTED_OPTIMIZED_SHA256
    )


def test_four_worker_capacity_formulas_are_exact_and_type_strict() -> None:
    cap = 1 << 40
    value = runner.four_worker_capacity_requirement(cap)
    assert value == {
        "parallel_workers": 4,
        "per_worker_output_cap_bytes": cap,
        "shared_output_cap_bytes": 4 * cap,
        "shared_disk_required_bytes": 4 * cap + (128 << 30),
        "shared_raw_headroom_bytes": 0,
        "shared_effective_headroom_bytes": 64 << 30,
    }
    with pytest.raises(runner.CubeProofRunnerError):
        runner.four_worker_capacity_requirement(True)
    with pytest.raises(runner.CubeProofRunnerError):
        runner.four_worker_capacity_requirement(-1)


def test_campaign_local_caps_fit_four_workers_without_mutating_pinned_v2() -> None:
    assert runner.PROOF_MAX_BYTES == 128 << 30
    assert runner.LRAT_MAX_BYTES == 128 << 30
    assert runner.v2.PROOF_MAX_BYTES == 1 << 40
    assert runner.v2.LRAT_MAX_BYTES == 1 << 40
    expected = {
        "parallel_workers": 4,
        "per_worker_output_cap_bytes": 128 << 30,
        "shared_output_cap_bytes": 512 << 30,
        "shared_disk_required_bytes": 640 << 30,
        "shared_raw_headroom_bytes": 0,
        "shared_effective_headroom_bytes": 64 << 30,
    }
    assert runner.four_worker_capacity_requirement(
        runner.PROOF_MAX_BYTES,
    ) == expected
    assert runner.four_worker_capacity_requirement(
        runner.LRAT_MAX_BYTES,
    ) == expected


def test_four_worker_gate_rejects_individually_safe_but_shared_unsafe(
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    cap = 1 << 40
    individual_only = {
        "raw_headroom_bytes": 9 << 30,
        "effective_headroom_bytes": 17 << 30,
        "filesystem_bavail_bytes": cap + (128 << 30),
    }
    monkeypatch.setattr(
        runner.v2, "_resource_gate", lambda root, output_cap: individual_only,
    )
    with pytest.raises(runner.CubeProofRunnerError, match="four-worker"):
        runner._four_worker_resource_gate(Path("/unused"), output_cap=cap)

    shared_safe = dict(individual_only)
    shared_safe.update({
        "raw_headroom_bytes": 9 << 30,
        "effective_headroom_bytes": 64 << 30,
        "filesystem_bavail_bytes": 4 * cap + (128 << 30),
    })
    monkeypatch.setattr(
        runner.v2, "_resource_gate", lambda root, output_cap: shared_safe,
    )
    replay = runner._four_worker_resource_gate(Path("/unused"), output_cap=cap)
    assert replay["passed"] is True
    assert replay["global_slot_limit_required_by_coordinator"] == 4


def test_per_cube_certificate_matches_strict_aggregate_schema_and_no_global_claim(
    production_material: tuple[optimized.OptimizedInstance, dict],
) -> None:
    _, manifest = production_material
    chain, fresh = _fake_chain(manifest, 7)
    certificate = runner._certificate_value(chain, fresh)
    assert aggregate.validate_cube_certificate(
        certificate, manifest, require_production=True,
    ) == []
    assert certificate["cube16_source_sha256"] == runner.EXPECTED_CUBE_SHA256
    assert certificate["aggregate_source_sha256"] == (
        runner.EXPECTED_AGGREGATE_SHA256
    )
    assert certificate["global_distance_claim"] is None
    assert certificate["publication_certificate"] is False


def test_per_cube_certificate_resealed_source_or_global_claim_tamper_fails(
    production_material: tuple[optimized.OptimizedInstance, dict],
) -> None:
    _, manifest = production_material
    chain, fresh = _fake_chain(manifest, 2)
    certificate = runner._certificate_value(chain, fresh)
    certificate["aggregate_source_sha256"] = "a" * 64
    certificate["global_distance_claim"] = "d>=20"
    certificate = runner.seal(certificate, "certificate_sha256")
    failures = aggregate.validate_cube_certificate(
        certificate, manifest, require_production=True,
    )
    assert "aggregate source hash mismatch" in failures
    assert "a single cube certificate cannot make a global distance claim" in failures


def test_validation_envelope_sat_unknown_and_unsat_truth_table(
    production_material: tuple[optimized.OptimizedInstance, dict],
) -> None:
    _, manifest = production_material
    cube = manifest["cubes"][0]
    classification = {
        "cube_index": 0,
        "classification": "VERIFIED_SAT_LOW_OPERATOR",
        "strict_verified_sat": True,
        "record_sha256": "b" * 64,
    }
    sat = runner._validation_record(
        root=Path("/tmp/cube-sat"), manifest=manifest, cube=cube,
        state=runner.STATE_SAT, certificate=None,
        sat_terminal=classification, failures=[], fresh_proof_replay=False,
    )
    assert aggregate.validate_cube_run_record(
        sat, manifest, require_production=True,
    ) == []
    unresolved = runner._validation_record(
        root=Path("/tmp/cube-unknown"), manifest=manifest, cube=cube,
        state=runner.STATE_UNRESOLVED, certificate=None,
        sat_terminal=None, failures=["timeout"], fresh_proof_replay=False,
    )
    assert aggregate.validate_cube_run_record(
        unresolved, manifest, require_production=True,
    ) == []


def test_parser_has_no_abbreviation_and_all_production_stages() -> None:
    parser = runner.build_parser()
    assert parser.allow_abbrev is False
    for argv, action in (
        (["preflight", "--cube-index", "0"], "preflight"),
        (["prepare", "--root", "/tmp/x", "--cube-index", "0"], "prepare"),
        (["solve", "--root", "/tmp/x"], "solve"),
        (["verify", "--root", "/tmp/x"], "verify"),
        (["finalize", "--root", "/tmp/x"], "finalize"),
        (["validate", "--root", "/tmp/x"], "validate"),
    ):
        assert parser.parse_args(argv).action == action


def test_toolchain_binding_is_hash_only_and_does_not_run_n400() -> None:
    record = runner._toolchain_binding()
    assert record["solver"]["sha256"] == runner.v2.EXPECTED_SOLVER_SHA256
    assert record["drat_trim"]["sha256"] == runner.v2.EXPECTED_DRAT_TRIM_SHA256
    assert record["lrat_check"]["sha256"] == runner.v2.EXPECTED_LRAT_CHECK_SHA256
