"""Focused fail-closed tests for the production DistQLDPC release exporter."""

from __future__ import annotations

import hashlib
import json
import shutil
import subprocess
import sys
import types
from copy import deepcopy
from pathlib import Path

import numpy as np
import pytest

from evaluation import distance_distqldpc
from evaluation import distqldpc_release_replay_v4 as replay
from evaluation import distqldpc_sector_adapter as adapter
from evaluation import distqldpc_sector_certificate as certificate_module
from evaluation import sector_certificate
from evaluation.release_gate import canonical_sha256
from humanize import distqldpc_release_export_final5 as release


def _write_json(path: Path, value):
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_text(
        json.dumps(value, indent=2, sort_keys=True) + "\n",
        encoding="utf-8",
    )


def _file_sha(path: Path) -> str:
    return hashlib.sha256(path.read_bytes()).hexdigest()


def _fixture(tmp_path: Path, monkeypatch: pytest.MonkeyPatch):
    repo = Path(release.__file__).resolve().parent.parent
    environment = {"python": "test", "numpy": "test", "scipy": "test", "qldpc": "test"}
    candidate_digest = "b" * 64
    candidate = {
        "canonical_digest": candidate_digest,
        "n": 4,
        "k": 2,
        "d": 2,
        "fom": 2.0,
        "d_is_exact": True,
        "required_distance": 2,
    }
    detector = {"verified": True, "report_sha256": "c" * 64}
    translation = {
        "verified": True,
        "method": "test-translation",
        "orbit_representatives": [0, 2],
    }
    isometry = {
        "verified": True,
        "canonical_sector": "X",
        "covered_sectors": ["X", "Z"],
        "report_sha256": "d" * 64,
    }
    stage3_identity = adapter.stage3_distqldpc_checkpoint_identity(
        candidate,
        cardinality_mode="mto",
        coverage_mode="first-nonzero",
        logical_detector=detector,
        translation_symmetry=translation,
        construction_symmetry=None,
        xz_sector_isometry=isometry,
    )
    stage3_identity_sha = canonical_sha256(stage3_identity)
    upper = {
        "sector": "X",
        "partition_index": None,
        "anchor_cube": None,
        "solver_evidence": {
            "outcome": "sat",
            "objective": 2,
            "anchor_indices": [0, 2],
        },
    }
    proof = {
        "proof_type": certificate_module.PROOF_TYPE,
        "source_stage3_checkpoint_identity_sha256": stage3_identity_sha,
        "upper_witness": upper,
    }
    claim = {**candidate, "exact_distance_proof": proof}

    known = tmp_path / "known.json"
    _write_json(known, {
        "schema_version": 1,
        "gate": "qldpc-known-answer-baselines",
        "passed": True,
        "environment": environment,
    })
    known_sha = _file_sha(known)
    semantic_sha = "9" * 64
    trust = tmp_path / "trust.json"
    _write_json(trust, {
        "schema_version": 1,
        "trust_policy": replay.TRUST_POLICY,
        "artifact_sha256": known_sha,
        "semantic_sha256": semantic_sha,
        "environment": environment,
        "required_baselines": replay.REQUIRED_BASELINES,
    })
    runtime = {
        "interpreter": {
            "reported_sys_executable": sys.executable,
            "realpath": str(Path(sys.executable).resolve()),
        },
    }
    integrity = tmp_path / "integrity.json"
    integrity_value = {
        "passed": True,
        "mode": "strict",
        "artifact_sha256": known_sha,
        "semantic_sha256": semantic_sha,
        "rerun_semantic_sha256": semantic_sha,
        "environment": environment,
        "rerun_command": [
            sys.executable,
            "-I",
            "-B",
            str(repo / replay.KNOWN_ANSWER_RUNNER),
            "--output",
            str(tmp_path / "strict-rerun.json"),
            "--timeout-per-logical",
            "3",
            "--total-timeout-per-code",
            "10",
        ],
        "rerun_wall_timeout_s": 90,
        "rerun_output_tail": "",
        "failures": [],
    }
    _write_json(integrity, integrity_value)

    stage3 = tmp_path / "stage3.json"
    stage3_value = {
        "schema_version": 1,
        "gate": adapter.STAGE3_GATE,
        "status": "EXACT_PROVEN",
        "candidate": {"canonical_digest": candidate_digest},
    }
    stage3_value["artifact_sha256"] = canonical_sha256(
        stage3_value,
        omit="artifact_sha256",
    )
    _write_json(stage3, stage3_value)
    stage3_artifact_sha = canonical_sha256(stage3_value)
    handoff = {
        "canonical_digest": candidate_digest,
        sector_certificate.REQUEST_FIELD: {
            "stage3_artifact_sha256": stage3_artifact_sha,
            "stage3_status": "EXACT_PROVEN",
            "lower_bound_backend": "distqldpc",
            "requested_lower_backend": "distqldpc",
        },
    }

    final_checks = {
        "known_answer_gate": True,
        "typed_exact_sector_distqldpc_proof": True,
        "typed_proof_dispatch_transparent": True,
        "structural_audit_present": True,
        "structural_audit_reproduced": True,
        "expanded_registry_novel": True,
        "challenge_win": True,
        "reported_fom_matches": True,
    }
    final_gate = {
        "schema_version": 1,
        "gate": certificate_module.FINAL_GATE,
        "accepted": True,
        "checks": final_checks,
        "failures": [],
        "known_answer": {
            "passed": True,
            "path": str(known),
            "failures": [],
            "generated_at": "2026-08-20T00:00:00+00:00",
        },
    }
    certificate = {
        "schema_version": 1,
        "certificate_type": certificate_module.CERTIFICATE_TYPE,
        "formulation": certificate_module.FORMULATION,
        "passed": True,
        "claim": claim,
        "known_answer": {"artifact_sha256": known_sha},
        "lower_proof_backend": {"backend": "distqldpc"},
        "source_stage3": {
            "gate": adapter.STAGE3_GATE,
            "status": "EXACT_PROVEN",
            "artifact_sha256": stage3_artifact_sha,
            "checkpoint_identity_sha256": stage3_identity_sha,
        },
        "final_gate": final_gate,
    }
    certificate["certificate_sha256"] = canonical_sha256(
        certificate,
        omit="certificate_sha256",
    )
    certificate_sha = certificate["certificate_sha256"]
    expected_fresh_identity = adapter.certificate_bound_distqldpc_checkpoint_identity(
        certificate_type=certificate_module.CERTIFICATE_TYPE,
        certificate_sha256=certificate_sha,
        candidate=candidate,
        cardinality_mode="mto",
        required_distance=2,
        exact_distance=2,
        max_weight=1,
        logical_detector=detector,
        translation_symmetry=translation,
        xz_sector_isometry=isometry,
        source_stage3_checkpoint_identity=stage3_identity,
    )
    fresh_evidence = {
        "outcome": "exact",
        "exact_distance": 2,
        "evidence_sha256": "e" * 64,
    }
    checks = {name: True for name in replay.REQUIRED_VERIFICATION_CHECKS}
    verification = {
        "passed": True,
        "replay_complete": True,
        "checks": checks,
        "failures": [],
        "distance": 2,
        "lower_bound_backend": "distqldpc",
        "typed_lower": True,
        "upper": True,
        "novelty": True,
        "fom_target": True,
        "distqldpc_decisions_verified": 1,
        "distqldpc_decisions_total": 1,
        "logical_partitions_verified": 1,
        "logical_partitions_total": 1,
        "final_gate": final_gate,
        "distqldpc_rerun": {
            "verified": True,
            "failures": [],
            "lower_bound_backend": "distqldpc",
            "cardinality_mode": "mto",
            "max_weight": 1,
            "exact_distance": 2,
            "checkpoint_identity": expected_fresh_identity,
            "source_stage3_checkpoint_identity_sha256": stage3_identity_sha,
            "solver_evidence": fresh_evidence,
        },
    }
    static_checks = dict(checks)
    static_checks["distqldpc_rerun"] = False
    static = {
        "passed": False,
        "replay_complete": False,
        "checks": static_checks,
        "failures": ["distqldpc_rerun"],
        "typed_lower": True,
        "upper": True,
        "novelty": True,
        "fom_target": True,
        "distqldpc_decisions_verified": 0,
        "distqldpc_decisions_total": 1,
        "logical_partitions_verified": 0,
        "logical_partitions_total": 1,
        "final_gate": final_gate,
    }
    matrices = tuple(np.zeros((1, 4), dtype=np.uint8) for _ in range(4))
    context = {
        "claim": candidate,
        "distance": 2,
        "required_distance": 2,
        "cardinality_mode": "mto",
        "stage3_checkpoint_identity": stage3_identity,
        "proof": proof,
        "upper_witness": upper,
        "anchors": (0, 2),
        "detector": detector,
        "translation": translation,
        "xz_isometry": isometry,
        "fom": 2.0,
        "hx": matrices[0],
        "hz": matrices[1],
        "lx": matrices[2],
        "lz": matrices[3],
    }
    monkeypatch.setattr(
        sector_certificate,
        "claim_from_sector_sat_artifact",
        lambda _artifact: deepcopy(handoff),
    )
    monkeypatch.setattr(
        certificate_module,
        "build_distqldpc_sector_certificate",
        lambda *_args, **_kwargs: deepcopy(certificate),
    )
    monkeypatch.setattr(
        certificate_module,
        "validate_distqldpc_exact_proof",
        lambda _claim: context,
    )
    monkeypatch.setattr(
        certificate_module,
        "verify_distqldpc_sector_certificate",
        lambda *_args, **_kwargs: deepcopy(static),
    )
    monkeypatch.setattr(
        distance_distqldpc,
        "verify_distqldpc_exact_evidence",
        lambda *_args, **_kwargs: [],
    )
    monkeypatch.setattr(
        distance_distqldpc,
        "verify_distqldpc_lower_evidence",
        lambda *_args, **_kwargs: [],
    )
    monkeypatch.setattr(replay._v2, "_runtime_binding", lambda: deepcopy(runtime))
    monkeypatch.setattr(
        replay._v2,
        "known_answer_environment",
        lambda _runtime=None: dict(environment),
    )
    monkeypatch.setattr(
        release._known_integrity,
        "check_fast",
        lambda *_args, **_kwargs: {
            "passed": True,
            "mode": "fast",
            "artifact_sha256": known_sha,
            "semantic_sha256": semantic_sha,
            "environment": dict(environment),
            "failures": [],
        },
    )
    certificate_path = tmp_path / "certificate.json"
    verification_path = tmp_path / "verification.json"
    _write_json(certificate_path, certificate)
    _write_json(verification_path, verification)
    return {
        "repo": repo,
        "candidate_digest": candidate_digest,
        "stage3_artifact_sha": stage3_artifact_sha,
        "certificate_sha": certificate_sha,
        "certificate": certificate,
        "verification": verification,
        "static": static,
        "certificate_path": certificate_path,
        "verification_path": verification_path,
        "stage3": stage3,
        "known": known,
        "trust": trust,
        "integrity": integrity,
        "environment": environment,
        "semantic_sha": semantic_sha,
        "physical": {
            "stage3_file_sha256": _file_sha(stage3),
            "certificate_file_sha256": _file_sha(certificate_path),
            "verification_file_sha256": _file_sha(verification_path),
            "known_answer_integrity_file_sha256": _file_sha(integrity),
        },
    }


def _argv(fixture, run_id, physical, output):
    return [
        str(fixture["repo"] / release.CLI_SOURCE),
        "export",
        "--repo-dir", str(fixture["repo"]),
        "--stage3-artifact", str(fixture["stage3"]),
        "--certificate", str(fixture["certificate_path"]),
        "--verification", str(fixture["verification_path"]),
        "--output-dir", str(output),
        "--known-answer-artifact", str(fixture["known"]),
        "--known-answer-trust", str(fixture["trust"]),
        "--known-answer-integrity", str(fixture["integrity"]),
        "--run-id", run_id,
        "--expected-candidate-digest", fixture["candidate_digest"],
        "--expected-certificate-sha256", fixture["certificate_sha"],
        "--expected-stage3-artifact-sha256", fixture["stage3_artifact_sha"],
        "--expected-stage3-file-sha256", physical["stage3_file_sha256"],
        "--expected-certificate-file-sha256",
        physical["certificate_file_sha256"],
        "--expected-verification-file-sha256",
        physical["verification_file_sha256"],
        "--expected-known-answer-integrity-file-sha256",
        physical["known_answer_integrity_file_sha256"],
    ]

def _export(tmp_path, fixture, *, output=None, physical=None, repo=None):
    physical = dict(fixture["physical"] if physical is None else physical)
    output = tmp_path / "release-output" if output is None else output
    result = release.export_typed_distqldpc_release(
        repo_dir=fixture["repo"] if repo is None else repo,
        stage3_artifact=fixture["stage3"],
        certificate_path=fixture["certificate_path"],
        verification_path=fixture["verification_path"],
        output_dir=output,
        run_id="typed-release-test",
        known_answer_artifact=fixture["known"],
        known_answer_trust=fixture["trust"],
        known_answer_integrity=fixture["integrity"],
        expected_candidate_digest=fixture["candidate_digest"],
        expected_certificate_sha256=fixture["certificate_sha"],
        expected_stage3_artifact_sha256=fixture["stage3_artifact_sha"],
        expected_stage3_file_sha256=physical["stage3_file_sha256"],
        expected_certificate_file_sha256=physical["certificate_file_sha256"],
        expected_verification_file_sha256=physical["verification_file_sha256"],
        expected_known_answer_integrity_file_sha256=(
            physical["known_answer_integrity_file_sha256"]
        ),
        invocation_argv=_argv(fixture, "typed-release-test", physical, output),
    )
    return output, result


def _validate(fixture, manifest_path, *, physical=None, repo=None):
    physical = dict(fixture["physical"] if physical is None else physical)
    return release.validate_typed_distqldpc_release(
        manifest_path,
        repo_dir=fixture["repo"] if repo is None else repo,
        stage3_artifact=fixture["stage3"],
        certificate_path=fixture["certificate_path"],
        verification_path=fixture["verification_path"],
        known_answer_artifact=fixture["known"],
        known_answer_trust=fixture["trust"],
        known_answer_integrity=fixture["integrity"],
        expected_run_id="typed-release-test",
        expected_candidate_digest=fixture["candidate_digest"],
        expected_certificate_sha256=fixture["certificate_sha"],
        expected_stage3_artifact_sha256=fixture["stage3_artifact_sha"],
        expected_stage3_file_sha256=physical["stage3_file_sha256"],
        expected_certificate_file_sha256=physical["certificate_file_sha256"],
        expected_verification_file_sha256=physical["verification_file_sha256"],
        expected_known_answer_integrity_file_sha256=(
            physical["known_answer_integrity_file_sha256"]
        ),
    )


def test_export_validate_binds_four_physical_sources_and_all_loaded_code(
    tmp_path,
    monkeypatch,
):
    fixture = _fixture(tmp_path, monkeypatch)
    output, result = _export(tmp_path, fixture)
    manifest_path = output / release.MANIFEST_FILENAME
    manifest = json.loads(manifest_path.read_text(encoding="utf-8"))
    before = {path.relative_to(output): path.read_bytes() for path in output.rglob("*") if path.is_file()}
    validation = _validate(fixture, manifest_path)
    after = {path.relative_to(output): path.read_bytes() for path in output.rglob("*") if path.is_file()}
    assert result["status"] == "EXPORTED"
    assert result["solver_invocations"] == 0
    assert result["physical_source_pins"] == 4
    assert validation["passed"] is True
    assert before == after
    assert manifest["expected_physical_bindings"] == fixture["physical"]
    assert manifest["generic_pipeline_registration"]["registered"] is False
    assert manifest["known_answer_integrity"]["mode"] == "strict"
    assert "sat_rerun" not in json.dumps(manifest)
    sources = manifest["source_pipeline"]["loaded_project_source"]["files"]
    for path in release.REQUIRED_SOURCE_FILES:
        assert path in sources


@pytest.mark.parametrize("field", tuple({
    "stage3_file_sha256",
    "certificate_file_sha256",
    "verification_file_sha256",
    "known_answer_integrity_file_sha256",
}))
def test_export_rejects_each_wrong_physical_sha(tmp_path, monkeypatch, field):
    fixture = _fixture(tmp_path, monkeypatch)
    physical = dict(fixture["physical"])
    physical[field] = "0" * 64
    with pytest.raises(
        release.TypedDistQLDPCFinal5ReleaseError,
        match="explicitly pinned input differs",
    ):
        _export(tmp_path, fixture, physical=physical)
    assert not (tmp_path / "release-output").exists()


def test_export_rejects_fresh_exact_or_lower_failure(tmp_path, monkeypatch):
    fixture = _fixture(tmp_path, monkeypatch)
    monkeypatch.setattr(
        distance_distqldpc,
        "verify_distqldpc_exact_evidence",
        lambda *_args, **_kwargs: ["exact rejected"],
    )
    with pytest.raises(release.TypedDistQLDPCFinal5ReleaseError, match="fresh DistQLDPC"):
        _export(tmp_path, fixture)
    monkeypatch.setattr(
        distance_distqldpc,
        "verify_distqldpc_exact_evidence",
        lambda *_args, **_kwargs: [],
    )
    monkeypatch.setattr(
        distance_distqldpc,
        "verify_distqldpc_lower_evidence",
        lambda *_args, **_kwargs: ["lower rejected"],
    )
    with pytest.raises(release.TypedDistQLDPCFinal5ReleaseError, match="fresh DistQLDPC"):
        _export(tmp_path, fixture)


def test_export_rejects_count_semantic_environment_and_wall_tamper(
    tmp_path,
    monkeypatch,
):
    fixture = _fixture(tmp_path, monkeypatch)
    forged = deepcopy(fixture["verification"])
    forged["distqldpc_decisions_total"] = 2
    _write_json(fixture["verification_path"], forged)
    fixture["physical"]["verification_file_sha256"] = _file_sha(
        fixture["verification_path"],
    )
    with pytest.raises(release.TypedDistQLDPCFinal5ReleaseError, match="verification contract"):
        _export(tmp_path, fixture)

    _write_json(fixture["verification_path"], fixture["verification"])
    fixture["physical"]["verification_file_sha256"] = _file_sha(
        fixture["verification_path"],
    )
    monkeypatch.setattr(
        release._known_integrity,
        "check_fast",
        lambda *_args, **_kwargs: {
            "passed": True,
            "mode": "fast",
            "artifact_sha256": _file_sha(fixture["known"]),
            "semantic_sha256": "0" * 64,
            "environment": fixture["environment"],
            "failures": [],
        },
    )
    with pytest.raises(release.TypedDistQLDPCFinal5ReleaseError, match="fast/strict"):
        _export(tmp_path, fixture)

    monkeypatch.setattr(
        release._known_integrity,
        "check_fast",
        lambda *_args, **_kwargs: {
            "passed": True,
            "mode": "fast",
            "artifact_sha256": _file_sha(fixture["known"]),
            "semantic_sha256": fixture["semantic_sha"],
            "environment": fixture["environment"],
            "failures": [],
        },
    )
    integrity = json.loads(fixture["integrity"].read_text(encoding="utf-8"))
    integrity["rerun_wall_timeout_s"] = 91
    _write_json(fixture["integrity"], integrity)
    fixture["physical"]["known_answer_integrity_file_sha256"] = _file_sha(
        fixture["integrity"],
    )
    with pytest.raises(release.TypedDistQLDPCFinal5ReleaseError, match="fast/strict"):
        _export(tmp_path, fixture)


def test_source_repo_guard_rejects_fake_repo(tmp_path):
    fake = tmp_path / "fake-repo"
    actual = Path(release.__file__).resolve().parent.parent
    for relative in release._CRITICAL_MODULE_PATHS.values():
        destination = fake / relative
        destination.parent.mkdir(parents=True, exist_ok=True)
        shutil.copy2(actual / relative, destination)
    with pytest.raises(
        release.TypedDistQLDPCFinal5ReleaseError,
        match="not executed from bound repo",
    ):
        release._bound_repo(fake)


def test_validator_rejects_leaf_symlink_and_resealed_argv_tamper(
    tmp_path,
    monkeypatch,
):
    fixture = _fixture(tmp_path, monkeypatch)
    output, _result = _export(tmp_path, fixture)
    manifest_path = output / release.MANIFEST_FILENAME
    manifest = json.loads(manifest_path.read_text(encoding="utf-8"))
    certificate_path = output / manifest["certificates"][0]["file"]
    outside = tmp_path / "outside-certificate.json"
    outside.write_bytes(certificate_path.read_bytes())
    certificate_path.unlink()
    certificate_path.symlink_to(outside)
    validation = _validate(fixture, manifest_path)
    assert validation["passed"] is False
    assert validation["classification"] == "MANIFEST_INVALID"

    certificate_path.unlink()
    certificate_path.write_bytes(outside.read_bytes())
    manifest = json.loads(manifest_path.read_text(encoding="utf-8"))
    invocation = manifest["normalized_invocation"]
    invocation["run_id"] = "tampered"
    invocation["normalized_sha256"] = canonical_sha256(
        invocation, omit="normalized_sha256",
    )
    manifest["manifest_sha256"] = canonical_sha256(
        manifest,
        omit="manifest_sha256",
    )
    _write_json(manifest_path, manifest)
    validation = _validate(fixture, manifest_path)
    assert validation["passed"] is False
    assert validation["classification"] == "MANIFEST_INVALID"


def test_atomic_no_replace_preserves_competitor(tmp_path):
    source = tmp_path / "source"
    destination = tmp_path / "destination"
    source.mkdir()
    destination.mkdir()
    (source / "ours").write_text("ours", encoding="utf-8")
    (destination / "competitor").write_text("competitor", encoding="utf-8")
    assert release._rename_noreplace(
        source, destination,
        expected_parent_identity=release._inode(tmp_path.lstat()),
        expected_source_identity=release._inode(source.lstat()),
    ) is False
    assert (source / "ours").read_text(encoding="utf-8") == "ours"
    assert (destination / "competitor").read_text(encoding="utf-8") == "competitor"


def test_midwrite_failure_has_no_final_and_cleans_owned_staging(
    tmp_path,
    monkeypatch,
):
    fixture = _fixture(tmp_path, monkeypatch)
    original = release._write_new
    calls = 0

    def fail_second(path, raw):
        nonlocal calls
        calls += 1
        if calls == 2:
            raise release.TypedDistQLDPCFinal5ReleaseError("INJECTED", "midwrite")
        return original(path, raw)

    monkeypatch.setattr(release, "_write_new", fail_second)
    with pytest.raises(release.TypedDistQLDPCFinal5ReleaseError, match="midwrite"):
        _export(tmp_path, fixture)
    assert not (tmp_path / "release-output").exists()
    assert list(tmp_path.glob(".release-output.staging-*")) == []


def test_real_t142532_stage3_rebuilds_exact_sourcebound_certificate():
    repo = Path(release.__file__).resolve().parent.parent
    stage3 = repo / (
        "results/fom13-w6-native254-r2-1371-distqldpc-mto-parameterized-merge-"
        "d90a0ce-20260820T142532Z/stage3-exact-proven.json"
    )
    certificate_path = repo / (
        "results/fom13-w6-native254-r2-1371-distqldpc-stage4-sourcebound-static-"
        "d90a0ce-20260820T1450Z/certificate.json"
    )
    if not stage3.is_file() or not certificate_path.is_file():
        pytest.skip("local production Stage3/Stage4 artifacts are not present")
    certificate = json.loads(certificate_path.read_text(encoding="utf-8"))
    result, _rebuilt, _normalization = replay._stage3_relocated_rebuild(
        certificate,
        stage3_artifact=stage3,
        known_answer_artifact=repo / "results/known_answer_gate.json",
        expected_stage3_artifact_sha256=(
            "3a3fdbd8bf576cc728868db56621333a799b3e676a9bd148f7c14dcc9295d505"
        ),
        phase="export",
    )
    assert result["static_rebuild_equal_after_path_normalization"] is True
    assert result["file_sha256"] == (
        "dbc31816793c86a2dfd06e380461f06bc5481e817495e589c054789e71934b60"
    )


def test_final_cli_bootstraps_under_isolated_pinned_python():
    script = Path(release.__file__).resolve().parent.parent / release.CLI_SOURCE
    completed = subprocess.run(
        [sys.executable, "-I", "-B", str(script), "--help"],
        text=True,
        stdout=subprocess.PIPE,
        stderr=subprocess.STDOUT,
        timeout=60,
        check=False,
    )
    assert completed.returncode == 0, completed.stdout
    assert "{export,validate}" in completed.stdout




_BOUND_FLAGS = (
    "--repo-dir",
    "--stage3-artifact",
    "--certificate",
    "--verification",
    "--output-dir",
    "--known-answer-artifact",
    "--known-answer-trust",
    "--known-answer-integrity",
    "--run-id",
    "--expected-candidate-digest",
    "--expected-certificate-sha256",
    "--expected-stage3-artifact-sha256",
    "--expected-stage3-file-sha256",
    "--expected-certificate-file-sha256",
    "--expected-verification-file-sha256",
    "--expected-known-answer-integrity-file-sha256",
)


@pytest.mark.parametrize("flag", _BOUND_FLAGS)
def test_every_export_flag_is_required_unique_and_exact(tmp_path, monkeypatch, flag):
    fixture = _fixture(tmp_path, monkeypatch)
    output = tmp_path / "release-output"
    paths = release._input_paths(
        repo_dir=fixture["repo"],
        stage3_artifact=fixture["stage3"],
        certificate_path=fixture["certificate_path"],
        verification_path=fixture["verification_path"],
        known_answer_artifact=fixture["known"],
        known_answer_trust=fixture["trust"],
        known_answer_integrity=fixture["integrity"],
    )
    complete = _argv(fixture, "typed-release-test", fixture["physical"], output)
    call = {
        "repo": fixture["repo"],
        "paths": paths,
        "output": output,
        "run_id": "typed-release-test",
        "expected_candidate_digest": fixture["candidate_digest"],
        "expected_certificate_sha256": fixture["certificate_sha"],
        "expected_stage3_artifact_sha256": fixture["stage3_artifact_sha"],
        "physical": fixture["physical"],
    }
    index = complete.index(flag)
    missing = complete[:index] + complete[index + 2:]
    with pytest.raises(release.TypedDistQLDPCFinal5ReleaseError):
        release._parse_export_argv(missing, **call)
    duplicate = complete + [flag, complete[index + 1]]
    with pytest.raises(release.TypedDistQLDPCFinal5ReleaseError):
        release._parse_export_argv(duplicate, **call)
    mismatched = list(complete)
    mismatched[index + 1] = "definitely-wrong"
    with pytest.raises(release.TypedDistQLDPCFinal5ReleaseError):
        release._parse_export_argv(mismatched, **call)


def test_argv0_must_be_exact_bound_cli(tmp_path, monkeypatch):
    fixture = _fixture(tmp_path, monkeypatch)
    output = tmp_path / "release-output"
    argv = _argv(fixture, "typed-release-test", fixture["physical"], output)
    argv[0] = str(fixture["certificate_path"])
    with pytest.raises(release.TypedDistQLDPCFinal5ReleaseError, match="argv\\[0\\]"):
        _export_with_argv(tmp_path, fixture, argv)


def _export_with_argv(tmp_path, fixture, argv, *, output=None):
    output = tmp_path / "release-output" if output is None else output
    return release.export_typed_distqldpc_release(
        repo_dir=fixture["repo"],
        stage3_artifact=fixture["stage3"],
        certificate_path=fixture["certificate_path"],
        verification_path=fixture["verification_path"],
        output_dir=output,
        run_id="typed-release-test",
        known_answer_artifact=fixture["known"],
        known_answer_trust=fixture["trust"],
        known_answer_integrity=fixture["integrity"],
        expected_candidate_digest=fixture["candidate_digest"],
        expected_certificate_sha256=fixture["certificate_sha"],
        expected_stage3_artifact_sha256=fixture["stage3_artifact_sha"],
        expected_stage3_file_sha256=fixture["physical"]["stage3_file_sha256"],
        expected_certificate_file_sha256=(
            fixture["physical"]["certificate_file_sha256"]
        ),
        expected_verification_file_sha256=(
            fixture["physical"]["verification_file_sha256"]
        ),
        expected_known_answer_integrity_file_sha256=(
            fixture["physical"]["known_answer_integrity_file_sha256"]
        ),
        invocation_argv=argv,
    )


def test_resealed_stage3_semantic_tamper_is_rejected(tmp_path, monkeypatch):
    fixture = _fixture(tmp_path, monkeypatch)
    stage3 = json.loads(fixture["stage3"].read_text(encoding="utf-8"))
    stage3["candidate"]["canonical_digest"] = "a" * 64
    stage3["artifact_sha256"] = canonical_sha256(stage3, omit="artifact_sha256")
    _write_json(fixture["stage3"], stage3)
    fixture["physical"]["stage3_file_sha256"] = _file_sha(fixture["stage3"])
    with pytest.raises(release.TypedDistQLDPCFinal5ReleaseError, match="Stage-3"):
        _export(tmp_path, fixture)


def _tamper_nonpath(certificate, name):
    if name == "passed":
        certificate["final_gate"]["known_answer"]["passed"] = False
    elif name == "generated_at":
        certificate["final_gate"]["known_answer"]["generated_at"] = "tampered"
    elif name == "checks":
        first = next(iter(certificate["final_gate"]["checks"]))
        certificate["final_gate"]["checks"][first] = False
    elif name == "known_sha":
        certificate["known_answer"]["artifact_sha256"] = "0" * 64
    elif name == "claim":
        certificate["claim"]["fom"] = 999.0
    elif name == "source":
        certificate["source_stage3"]["status"] = "BAD"
    elif name == "matrix":
        certificate.setdefault("matrix_sha256", {})["hx"] = "0" * 64
    else:
        raise AssertionError(name)


@pytest.mark.parametrize(
    "name",
    ("passed", "generated_at", "checks", "known_sha", "claim", "source", "matrix"),
)
def test_path_normalization_rejects_every_nonpath_change(
    tmp_path, monkeypatch, name,
):
    fixture = _fixture(tmp_path, monkeypatch)
    forged = deepcopy(fixture["certificate"])
    _tamper_nonpath(forged, name)
    forged["certificate_sha256"] = canonical_sha256(
        forged, omit="certificate_sha256",
    )
    with pytest.raises(replay.DistQLDPCReleaseReplayError):
        replay._stage3_relocated_rebuild(
            forged,
            stage3_artifact=fixture["stage3"],
            known_answer_artifact=fixture["known"],
            expected_stage3_artifact_sha256=fixture["stage3_artifact_sha"],
            phase="relocated-validate",
        )


def test_path_only_relocation_is_the_single_allowed_certificate_delta(
    tmp_path, monkeypatch,
):
    fixture = _fixture(tmp_path, monkeypatch)
    relocated = deepcopy(fixture["certificate"])
    relocated["final_gate"]["known_answer"]["path"] = str(
        tmp_path / "missing-old-checkout" / "known.json"
    )
    relocated["certificate_sha256"] = canonical_sha256(
        relocated, omit="certificate_sha256",
    )
    stage3, _rebuilt, normalization = replay._stage3_relocated_rebuild(
        relocated,
        stage3_artifact=fixture["stage3"],
        known_answer_artifact=fixture["known"],
        expected_stage3_artifact_sha256=fixture["stage3_artifact_sha"],
        phase="relocated-validate",
    )
    assert stage3["static_rebuild_equal_after_path_normalization"] is True
    assert normalization["allowed_nonsemantic_fields"] == [
        "certificate_sha256",
        "final_gate.known_answer.path",
    ]


def test_source_hash_ignores_external_library_but_rejects_project_poison(
    tmp_path, monkeypatch,
):
    fixture = _fixture(tmp_path, monkeypatch)
    external = tmp_path / "external.py"
    external.write_text("VALUE = 1\n", encoding="utf-8")
    ordinary = types.ModuleType("ordinary_external_probe")
    ordinary.__file__ = str(external)
    monkeypatch.setitem(sys.modules, ordinary.__name__, ordinary)
    assert release._source_hashes(fixture["repo"])["files"]
    poison = types.ModuleType("evaluation.poison_probe")
    poison.__file__ = str(external)
    monkeypatch.setitem(sys.modules, poison.__name__, poison)
    with pytest.raises(
        release.TypedDistQLDPCFinal5ReleaseError,
        match="outside bound repo",
    ):
        release._source_hashes(fixture["repo"])


def test_validator_rejects_intermediate_symlink(tmp_path, monkeypatch):
    fixture = _fixture(tmp_path, monkeypatch)
    output, _ = _export(tmp_path, fixture)
    manifest_path = output / release.MANIFEST_FILENAME
    certificate_dir = output / "certificates"
    outside = tmp_path / "outside-certificates"
    certificate_dir.rename(outside)
    certificate_dir.symlink_to(outside, target_is_directory=True)
    validation = _validate(fixture, manifest_path)
    assert validation["passed"] is False
    assert validation["classification"] == "MANIFEST_INVALID"


def test_existing_destination_and_publish_race_preserve_competitor(
    tmp_path, monkeypatch,
):
    fixture = _fixture(tmp_path, monkeypatch)
    output = tmp_path / "release-output"
    output.mkdir()
    (output / "competitor").write_text("first", encoding="utf-8")
    with pytest.raises(release.TypedDistQLDPCFinal5ReleaseError):
        _export(tmp_path, fixture, output=output)
    assert (output / "competitor").read_text(encoding="utf-8") == "first"

    second_output = tmp_path / "race-output"
    original = release._rename_noreplace

    def race(source, destination, **kwargs):
        destination.mkdir()
        (destination / "competitor").write_text("racer", encoding="utf-8")
        return original(source, destination, **kwargs)

    monkeypatch.setattr(release, "_rename_noreplace", race)
    with pytest.raises(release.TypedDistQLDPCFinal5ReleaseError, match="raced"):
        _export(tmp_path, fixture, output=second_output)
    assert (second_output / "competitor").read_text(encoding="utf-8") == "racer"
    assert list(tmp_path.glob(".race-output.staging-*")) == []


def test_rename_rejects_wrong_staging_identity(tmp_path):
    source = tmp_path / "source-identity"
    destination = tmp_path / "destination-identity"
    source.mkdir()
    with pytest.raises(
        release.TypedDistQLDPCFinal5ReleaseError,
        match="identity changed",
    ):
        release._rename_noreplace(
            source,
            destination,
            expected_parent_identity=release._inode(tmp_path.lstat()),
            expected_source_identity=(0, 0),
        )
    assert source.is_dir()
    assert not destination.exists()


def test_selfvalidation_failure_cleans_only_owned_staging(tmp_path, monkeypatch):
    fixture = _fixture(tmp_path, monkeypatch)
    monkeypatch.setattr(
        release,
        "validate_typed_distqldpc_release",
        lambda *_args, **_kwargs: {
            "passed": False,
            "failures": ["injected selfvalidation"],
        },
    )
    with pytest.raises(
        release.TypedDistQLDPCFinal5ReleaseError,
        match="injected selfvalidation",
    ):
        _export(tmp_path, fixture)
    assert not (tmp_path / "release-output").exists()
    assert list(tmp_path.glob(".release-output.staging-*")) == []


def test_resealed_source_manifest_tamper_is_rejected(tmp_path, monkeypatch):
    fixture = _fixture(tmp_path, monkeypatch)
    output, _ = _export(tmp_path, fixture)
    manifest_path = output / release.MANIFEST_FILENAME
    manifest = json.loads(manifest_path.read_text(encoding="utf-8"))
    loaded = manifest["source_pipeline"]["loaded_project_source"]
    first = next(iter(loaded["files"]))
    loaded["files"][first] = "0" * 64
    loaded["fingerprint_sha256"] = canonical_sha256(loaded["files"])
    manifest["manifest_sha256"] = canonical_sha256(
        manifest, omit="manifest_sha256",
    )
    _write_json(manifest_path, manifest)
    validation = _validate(fixture, manifest_path)
    assert validation["passed"] is False
    assert validation["classification"] == "MANIFEST_INVALID"


def test_solver_helper_is_never_called(tmp_path, monkeypatch):
    fixture = _fixture(tmp_path, monkeypatch)

    def forbidden(*_args, **_kwargs):
        raise AssertionError("large solver was invoked")

    monkeypatch.setattr(adapter, "solve_css_distance_distqldpc_lower", forbidden)
    output, result = _export(tmp_path, fixture)
    assert result["solver_invocations"] == 0
    assert output.is_dir()



_PORTABILITY_HARNESS_SOURCE = r'''from __future__ import annotations

import hashlib
import json
import sys
from copy import deepcopy
from pathlib import Path

import numpy as np


repo = Path(sys.argv[1]).resolve()
mode = sys.argv[2]
data = Path(sys.argv[3]).resolve()
output = Path(sys.argv[4]).resolve()
sys.path.insert(0, str(repo))

from evaluation import distance_distqldpc
from evaluation import distqldpc_release_replay_v4 as replay
from evaluation import distqldpc_sector_adapter as adapter
from evaluation import distqldpc_sector_certificate as certificate_module
from evaluation import sector_certificate
from evaluation.release_gate import canonical_sha256
from humanize import distqldpc_release_export_final5 as release


def write_json(path: Path, value):
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_text(json.dumps(value, indent=2, sort_keys=True) + "\n", encoding="utf-8")


def file_sha(path: Path) -> str:
    return hashlib.sha256(path.read_bytes()).hexdigest()


known = data / "known.json"
trust = data / "trust.json"
integrity = data / "integrity.json"
stage3_path = data / "stage3.json"
certificate_path = data / "certificate.json"
verification_path = data / "verification.json"
environment = {"python": "test", "numpy": "test", "scipy": "test", "qldpc": "test"}
candidate_digest = "b" * 64
candidate = {
    "canonical_digest": candidate_digest,
    "n": 4,
    "k": 2,
    "d": 2,
    "fom": 2.0,
    "d_is_exact": True,
    "required_distance": 2,
}
detector = {"verified": True, "report_sha256": "c" * 64}
translation = {
    "verified": True,
    "method": "test-translation",
    "orbit_representatives": [0, 2],
}
isometry = {
    "verified": True,
    "canonical_sector": "X",
    "covered_sectors": ["X", "Z"],
    "report_sha256": "d" * 64,
}
stage3_identity = adapter.stage3_distqldpc_checkpoint_identity(
    candidate,
    cardinality_mode="mto",
    coverage_mode="first-nonzero",
    logical_detector=detector,
    translation_symmetry=translation,
    construction_symmetry=None,
    xz_sector_isometry=isometry,
)
stage3_identity_sha = canonical_sha256(stage3_identity)
upper = {
    "sector": "X",
    "partition_index": None,
    "anchor_cube": None,
    "solver_evidence": {
        "outcome": "sat",
        "objective": 2,
        "anchor_indices": [0, 2],
    },
}
proof = {
    "proof_type": certificate_module.PROOF_TYPE,
    "source_stage3_checkpoint_identity_sha256": stage3_identity_sha,
    "upper_witness": upper,
}
claim = {**candidate, "exact_distance_proof": proof}
runtime = {
    "interpreter": {
        "reported_sys_executable": sys.executable,
        "realpath": str(Path(sys.executable).resolve()),
    },
}

if mode == "export":
    data.mkdir(parents=True, exist_ok=True)
    write_json(known, {
        "schema_version": 1,
        "gate": "qldpc-known-answer-baselines",
        "passed": True,
        "environment": environment,
    })
    known_sha = file_sha(known)
    semantic_sha = "9" * 64
    write_json(trust, {
        "schema_version": 1,
        "trust_policy": replay.TRUST_POLICY,
        "artifact_sha256": known_sha,
        "semantic_sha256": semantic_sha,
        "environment": environment,
        "required_baselines": replay.REQUIRED_BASELINES,
    })
    write_json(integrity, {
        "passed": True,
        "mode": "strict",
        "artifact_sha256": known_sha,
        "semantic_sha256": semantic_sha,
        "rerun_semantic_sha256": semantic_sha,
        "environment": environment,
        "rerun_command": [
            sys.executable,
            "-I",
            "-B",
            str(repo / replay.KNOWN_ANSWER_RUNNER),
            "--output",
            str(data / "strict-rerun.json"),
            "--timeout-per-logical",
            "3",
            "--total-timeout-per-code",
            "10",
        ],
        "rerun_wall_timeout_s": 90,
        "rerun_output_tail": "",
        "failures": [],
    })
    stage3 = {
        "schema_version": 1,
        "gate": adapter.STAGE3_GATE,
        "status": "EXACT_PROVEN",
        "candidate": {"canonical_digest": candidate_digest},
    }
    stage3["artifact_sha256"] = canonical_sha256(stage3, omit="artifact_sha256")
    write_json(stage3_path, stage3)
    stage3_artifact_sha = canonical_sha256(stage3)
    final_checks = {
        "known_answer_gate": True,
        "typed_exact_sector_distqldpc_proof": True,
        "typed_proof_dispatch_transparent": True,
        "structural_audit_present": True,
        "structural_audit_reproduced": True,
        "expanded_registry_novel": True,
        "challenge_win": True,
        "reported_fom_matches": True,
    }
    final_gate = {
        "schema_version": 1,
        "gate": certificate_module.FINAL_GATE,
        "accepted": True,
        "checks": final_checks,
        "failures": [],
        "known_answer": {
            "passed": True,
            "path": str(known),
            "failures": [],
            "generated_at": "2026-08-20T00:00:00+00:00",
        },
    }
    certificate = {
        "schema_version": 1,
        "certificate_type": certificate_module.CERTIFICATE_TYPE,
        "formulation": certificate_module.FORMULATION,
        "passed": True,
        "claim": claim,
        "known_answer": {"artifact_sha256": known_sha},
        "lower_proof_backend": {"backend": "distqldpc"},
        "source_stage3": {
            "gate": adapter.STAGE3_GATE,
            "status": "EXACT_PROVEN",
            "artifact_sha256": stage3_artifact_sha,
            "checkpoint_identity_sha256": stage3_identity_sha,
        },
        "final_gate": final_gate,
    }
    certificate["certificate_sha256"] = canonical_sha256(
        certificate, omit="certificate_sha256",
    )
    expected_fresh_identity = adapter.certificate_bound_distqldpc_checkpoint_identity(
        certificate_type=certificate_module.CERTIFICATE_TYPE,
        certificate_sha256=certificate["certificate_sha256"],
        candidate=candidate,
        cardinality_mode="mto",
        required_distance=2,
        exact_distance=2,
        max_weight=1,
        logical_detector=detector,
        translation_symmetry=translation,
        xz_sector_isometry=isometry,
        source_stage3_checkpoint_identity=stage3_identity,
    )
    checks = {name: True for name in replay.REQUIRED_VERIFICATION_CHECKS}
    verification = {
        "passed": True,
        "replay_complete": True,
        "checks": checks,
        "failures": [],
        "distance": 2,
        "lower_bound_backend": "distqldpc",
        "typed_lower": True,
        "upper": True,
        "novelty": True,
        "fom_target": True,
        "distqldpc_decisions_verified": 1,
        "distqldpc_decisions_total": 1,
        "logical_partitions_verified": 1,
        "logical_partitions_total": 1,
        "final_gate": final_gate,
        "distqldpc_rerun": {
            "verified": True,
            "failures": [],
            "lower_bound_backend": "distqldpc",
            "cardinality_mode": "mto",
            "max_weight": 1,
            "exact_distance": 2,
            "checkpoint_identity": expected_fresh_identity,
            "source_stage3_checkpoint_identity_sha256": stage3_identity_sha,
            "solver_evidence": {
                "outcome": "exact",
                "exact_distance": 2,
                "evidence_sha256": "e" * 64,
            },
        },
    }
    write_json(certificate_path, certificate)
    write_json(verification_path, verification)
else:
    certificate = json.loads(certificate_path.read_text(encoding="utf-8"))
    verification = json.loads(verification_path.read_text(encoding="utf-8"))
    stage3 = json.loads(stage3_path.read_text(encoding="utf-8"))
    stage3_artifact_sha = canonical_sha256(stage3)
    semantic_sha = json.loads(trust.read_text(encoding="utf-8"))["semantic_sha256"]
    final_gate = certificate["final_gate"]

handoff = {
    "canonical_digest": candidate_digest,
    sector_certificate.REQUEST_FIELD: {
        "stage3_artifact_sha256": stage3_artifact_sha,
        "stage3_status": "EXACT_PROVEN",
        "lower_bound_backend": "distqldpc",
        "requested_lower_backend": "distqldpc",
    },
}
static_checks = dict(verification["checks"])
static_checks["distqldpc_rerun"] = False
static = {
    "passed": False,
    "replay_complete": False,
    "checks": static_checks,
    "failures": ["distqldpc_rerun"],
    "typed_lower": True,
    "upper": True,
    "novelty": True,
    "fom_target": True,
    "distqldpc_decisions_verified": 0,
    "distqldpc_decisions_total": 1,
    "logical_partitions_verified": 0,
    "logical_partitions_total": 1,
    "final_gate": final_gate,
}
matrices = tuple(np.zeros((1, 4), dtype=np.uint8) for _ in range(4))
context = {
    "claim": candidate,
    "distance": 2,
    "required_distance": 2,
    "cardinality_mode": "mto",
    "stage3_checkpoint_identity": stage3_identity,
    "proof": proof,
    "upper_witness": upper,
    "anchors": (0, 2),
    "detector": detector,
    "translation": translation,
    "xz_isometry": isometry,
    "fom": 2.0,
    "hx": matrices[0],
    "hz": matrices[1],
    "lx": matrices[2],
    "lz": matrices[3],
}
rebuilt_certificate = deepcopy(certificate)
rebuilt_certificate["final_gate"]["known_answer"]["path"] = str(known)
rebuilt_certificate["certificate_sha256"] = canonical_sha256(
    rebuilt_certificate, omit="certificate_sha256",
)
rebuilt_static = deepcopy(static)
rebuilt_static["final_gate"] = deepcopy(rebuilt_certificate["final_gate"])
sector_certificate.claim_from_sector_sat_artifact = lambda _artifact: deepcopy(handoff)
certificate_module.build_distqldpc_sector_certificate = lambda *_a, **_k: deepcopy(rebuilt_certificate)
certificate_module.validate_distqldpc_exact_proof = lambda _claim: context
certificate_module.verify_distqldpc_sector_certificate = lambda *_a, **_k: deepcopy(rebuilt_static)
distance_distqldpc.verify_distqldpc_exact_evidence = lambda *_a, **_k: []
distance_distqldpc.verify_distqldpc_lower_evidence = lambda *_a, **_k: []
replay._v2._runtime_binding = lambda: deepcopy(runtime)
replay._v2.known_answer_environment = lambda _runtime=None: dict(environment)
known_sha = file_sha(known)
release._known_integrity.check_fast = lambda *_a, **_k: {
    "passed": True,
    "mode": "fast",
    "artifact_sha256": known_sha,
    "semantic_sha256": semantic_sha,
    "environment": dict(environment),
    "failures": [],
}
physical = {
    "stage3_file_sha256": file_sha(stage3_path),
    "certificate_file_sha256": file_sha(certificate_path),
    "verification_file_sha256": file_sha(verification_path),
    "known_answer_integrity_file_sha256": file_sha(integrity),
}
common = {
    "repo_dir": repo,
    "stage3_artifact": stage3_path,
    "certificate_path": certificate_path,
    "verification_path": verification_path,
    "known_answer_artifact": known,
    "known_answer_trust": trust,
    "known_answer_integrity": integrity,
    "expected_candidate_digest": candidate_digest,
    "expected_certificate_sha256": certificate["certificate_sha256"],
    "expected_stage3_artifact_sha256": stage3_artifact_sha,
    "expected_stage3_file_sha256": physical["stage3_file_sha256"],
    "expected_certificate_file_sha256": physical["certificate_file_sha256"],
    "expected_verification_file_sha256": physical["verification_file_sha256"],
    "expected_known_answer_integrity_file_sha256": physical["known_answer_integrity_file_sha256"],
}
if mode == "export":
    argv = [str(repo / release.CLI_SOURCE), "export"]
    args = {
        "--repo-dir": str(repo),
        "--stage3-artifact": str(stage3_path),
        "--certificate": str(certificate_path),
        "--verification": str(verification_path),
        "--output-dir": str(output),
        "--known-answer-artifact": str(known),
        "--known-answer-trust": str(trust),
        "--known-answer-integrity": str(integrity),
        "--run-id": "portable-smoke",
        "--expected-candidate-digest": candidate_digest,
        "--expected-certificate-sha256": certificate["certificate_sha256"],
        "--expected-stage3-artifact-sha256": stage3_artifact_sha,
        "--expected-stage3-file-sha256": physical["stage3_file_sha256"],
        "--expected-certificate-file-sha256": physical["certificate_file_sha256"],
        "--expected-verification-file-sha256": physical["verification_file_sha256"],
        "--expected-known-answer-integrity-file-sha256": physical["known_answer_integrity_file_sha256"],
    }
    for key, value in args.items():
        argv.extend([key, value])
    result = release.export_typed_distqldpc_release(
        output_dir=output,
        run_id="portable-smoke",
        invocation_argv=argv,
        **common,
    )
else:
    result = release.validate_typed_distqldpc_release(
        output / release.MANIFEST_FILENAME,
        expected_run_id="portable-smoke",
        **common,
    )
print(json.dumps(result, sort_keys=True))
raise SystemExit(0 if result.get("status") == "EXPORTED" or result.get("passed") else 1)


'''


def test_clean_clone_a_export_then_removed_a_and_clone_b_validate(
    tmp_path,
):
    repo = Path(release.__file__).resolve().parent.parent
    clone_a = tmp_path / "clone-a"
    clone_b = tmp_path / "clone-b"
    ignored = shutil.ignore_patterns("__pycache__", "*.pyc", "*.pyo")
    for source_name in ("evaluation", "humanize", "scripts", "tests"):
        shutil.copytree(
            repo / source_name,
            clone_a / source_name,
            ignore=ignored,
        )
        shutil.copytree(
            repo / source_name,
            clone_b / source_name,
            ignore=ignored,
        )
    harness_path = tmp_path / "relocation-harness.py"
    harness_path.write_text(_PORTABILITY_HARNESS_SOURCE, encoding="utf-8")
    data_a = tmp_path / "data-a"
    data_b = tmp_path / "data-b"
    output = tmp_path / "release"
    command_a = [
        sys.executable,
        "-I",
        "-B",
        str(harness_path),
        str(clone_a),
        "export",
        str(data_a),
        str(output),
    ]
    exported = subprocess.run(
        command_a,
        text=True,
        stdout=subprocess.PIPE,
        stderr=subprocess.STDOUT,
        timeout=120,
        check=False,
    )
    assert exported.returncode == 0, exported.stdout
    export_result = json.loads(exported.stdout.strip().splitlines()[-1])
    assert export_result["status"] == "EXPORTED"
    assert export_result["solver_invocations"] == 0
    shutil.copytree(data_a, data_b)
    clone_a.rename(tmp_path / "clone-a-removed")
    data_a.rename(tmp_path / "data-a-removed")
    command_b = [
        sys.executable,
        "-I",
        "-B",
        str(harness_path),
        str(clone_b),
        "validate",
        str(data_b),
        str(output),
    ]
    validated = subprocess.run(
        command_b,
        text=True,
        stdout=subprocess.PIPE,
        stderr=subprocess.STDOUT,
        timeout=120,
        check=False,
    )
    assert validated.returncode == 0, validated.stdout
    validation = json.loads(validated.stdout.strip().splitlines()[-1])
    assert validation["passed"] is True
    assert validation["verified"] == 1
    manifest = json.loads(
        (output / release.MANIFEST_FILENAME).read_text(encoding="utf-8")
    )
    normalization = manifest["nonsemantic_path_normalization"]
    assert normalization["mode"] == "known-answer-path-only-relocation-v1"
    assert normalization["official_rebuild_equivalent"] is True
    assert "repo_realpath" not in json.dumps(
        manifest["source_pipeline"]["loaded_project_source"]
    )


