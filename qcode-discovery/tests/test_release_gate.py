"""Tests for immutable release manifests."""

import json

from evaluation.release_gate import canonical_sha256, validate_release_manifest


def _write_release(tmp_path):
    certificate = {"passed": True, "value": 1}
    certificate["certificate_sha256"] = canonical_sha256(
        certificate, omit="certificate_sha256",
    )
    cert_path = tmp_path / "certificate.json"
    cert_path.write_text(json.dumps(certificate))
    manifest = {
        "schema_version": 1,
        "gate": "qldpc-challenge-release",
        "run_id": "test-run",
        "passed": True,
        "certificates": [{
            "file": "certificate.json",
            "certificate_sha256": certificate["certificate_sha256"],
            "verification": {"passed": True},
        }],
    }
    manifest["manifest_sha256"] = canonical_sha256(
        manifest, omit="manifest_sha256",
    )
    path = tmp_path / "manifest.json"
    path.write_text(json.dumps(manifest))
    return path, cert_path


def test_release_manifest_accepts_bound_verified_certificate(tmp_path):
    path, _ = _write_release(tmp_path)
    assert validate_release_manifest(path, expected_run_id="test-run")["passed"]


def test_release_manifest_rejects_certificate_tamper(tmp_path):
    path, certificate = _write_release(tmp_path)
    value = json.loads(certificate.read_text())
    value["value"] = 2
    certificate.write_text(json.dumps(value))
    assert not validate_release_manifest(path)["passed"]
