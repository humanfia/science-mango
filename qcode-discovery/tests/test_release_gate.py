"""Tests for immutable release manifests."""

import json

from evaluation.proof_runtime import proof_runtime_fingerprint
from evaluation.release_gate import canonical_sha256, validate_release_manifest
from scripts.verify_release import compare_strict_provenance


_MISSING = object()
_ARTIFACT_SHA = "c" * 64
_SEMANTIC_SHA = "a" * 64
_ENVIRONMENT = {"python": "test"}


def _strict_integrity():
    return {
        "passed": True,
        "mode": "strict",
        "artifact_sha256": _ARTIFACT_SHA,
        "semantic_sha256": _SEMANTIC_SHA,
        "rerun_semantic_sha256": _SEMANTIC_SHA,
        "environment": _ENVIRONMENT,
    }


def _write_release(tmp_path, *, integrity=_MISSING, trust=_MISSING):
    tmp_path.mkdir(parents=True, exist_ok=True)
    if trust is _MISSING:
        trust = {
            "schema_version": 1,
            "artifact_sha256": _ARTIFACT_SHA,
            "semantic_sha256": _SEMANTIC_SHA,
            "environment": _ENVIRONMENT,
        }
    trust_path = tmp_path / "known_answer_trust.json"
    trust_path.write_text(json.dumps(trust))
    certificate = {"passed": True, "value": 1}
    certificate["certificate_sha256"] = canonical_sha256(
        certificate, omit="certificate_sha256",
    )
    cert_path = tmp_path / "certificate.json"
    cert_path.write_text(json.dumps(certificate))
    runtime = proof_runtime_fingerprint()
    manifest = {
        "schema_version": 1,
        "gate": "qldpc-challenge-release",
        "run_id": "test-run",
        "passed": True,
        "source_evaluations": 1,
        "source_total": 1,
        "accepted": 1,
        "rejected": 0,
        "incomplete": 0,
        "eligible_candidates": 1,
        "stage5_artifact_sha256": "b" * 64,
        "source_pipeline": {
            "stage5": {
                "final_gate_sha256": "b" * 64,
                "proof_runtime": runtime,
                "proof_interpreter": runtime["interpreter"],
            },
        },
        "certificates": [{
            "file": "certificate.json",
            "certificate_sha256": certificate["certificate_sha256"],
            "verification": {"passed": True},
        }],
    }
    if integrity is _MISSING:
        integrity = _strict_integrity()
    if integrity is not None:
        manifest["known_answer_integrity"] = integrity
    manifest["manifest_sha256"] = canonical_sha256(
        manifest, omit="manifest_sha256",
    )
    path = tmp_path / "manifest.json"
    path.write_text(json.dumps(manifest))
    return path, cert_path, trust_path


def test_release_manifest_accepts_strict_known_answer_provenance(tmp_path):
    path, _, trust = _write_release(tmp_path)
    assert validate_release_manifest(path, known_answer_trust_path=trust, expected_run_id="test-run")["passed"]


def test_release_manifest_rejects_missing_worker_runtime_provenance(tmp_path):
    path, _, trust = _write_release(tmp_path)
    manifest = json.loads(path.read_text())
    manifest["source_pipeline"]["stage5"].pop("proof_runtime")
    manifest["manifest_sha256"] = canonical_sha256(
        manifest,
        omit="manifest_sha256",
    )
    path.write_text(json.dumps(manifest))

    result = validate_release_manifest(
        path,
        known_answer_trust_path=trust,
    )

    assert result["passed"] is False
    assert any("proof runtime" in failure for failure in result["failures"])


def test_release_manifest_rejects_missing_known_answer_provenance(tmp_path):
    path, _, trust = _write_release(tmp_path, integrity=None)
    assert not validate_release_manifest(path, known_answer_trust_path=trust)["passed"]


def test_release_manifest_rejects_fast_known_answer_provenance(tmp_path):
    integrity = _strict_integrity()
    integrity["mode"] = "fast"
    path, _, trust = _write_release(tmp_path, integrity=integrity)
    assert not validate_release_manifest(path, known_answer_trust_path=trust)["passed"]


def test_release_manifest_rejects_strict_semantic_hash_mismatch(tmp_path):
    integrity = _strict_integrity()
    integrity["rerun_semantic_sha256"] = "b" * 64
    path, _, trust = _write_release(tmp_path, integrity=integrity)
    assert not validate_release_manifest(path, known_answer_trust_path=trust)["passed"]


def test_release_manifest_rejects_invalid_strict_semantic_hash(tmp_path):
    integrity = _strict_integrity()
    integrity["semantic_sha256"] = "A" * 64
    integrity["rerun_semantic_sha256"] = "A" * 64
    path, _, trust = _write_release(tmp_path, integrity=integrity)
    assert not validate_release_manifest(path, known_answer_trust_path=trust)["passed"]


def test_release_manifest_rejects_certificate_tamper(tmp_path):
    path, certificate, trust = _write_release(tmp_path)
    value = json.loads(certificate.read_text())
    value["value"] = 2
    certificate.write_text(json.dumps(value))
    assert not validate_release_manifest(path, known_answer_trust_path=trust)["passed"]


def test_release_manifest_rejects_repository_trust_mismatch(tmp_path):
    path, _, trust_path = _write_release(tmp_path)
    trust = json.loads(trust_path.read_text())
    trust["semantic_sha256"] = "d" * 64
    trust_path.write_text(json.dumps(trust))
    assert not validate_release_manifest(
        path, known_answer_trust_path=trust_path,
    )["passed"]


def test_fresh_strict_provenance_must_match_release_manifest():
    recorded = _strict_integrity()
    assert compare_strict_provenance(recorded, dict(recorded)) == []

    fresh = dict(recorded)
    fresh["semantic_sha256"] = "d" * 64
    failures = compare_strict_provenance(recorded, fresh)

    assert any(
        "semantic_sha256" in failure
        for failure in failures
    )


def test_release_manifest_rejects_parent_path_escape(tmp_path):
    release_root = tmp_path / "release"
    path, certificate, trust = _write_release(release_root)
    outside = tmp_path / "outside.json"
    outside.write_text(certificate.read_text())
    manifest = json.loads(path.read_text())
    manifest["certificates"][0]["file"] = "../outside.json"
    manifest["manifest_sha256"] = canonical_sha256(
        manifest, omit="manifest_sha256",
    )
    path.write_text(json.dumps(manifest))

    result = validate_release_manifest(
        path,
        known_answer_trust_path=trust,
    )

    assert not result["passed"]
    assert any("path is unsafe" in failure for failure in result["failures"])
