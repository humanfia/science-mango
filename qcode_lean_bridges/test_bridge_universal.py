import json

import pytest

from bridge_universal import (
    canonical_sha256,
    certificate_payload,
    load_verified_release,
    render_module,
)


def packed(bits):
    value = 0
    for index, bit in enumerate(bits):
        value |= bit << index
    raw = value.to_bytes((len(bits) + 7) // 8, "little")
    import hashlib
    return {
        "length": len(bits),
        "weight": sum(bits),
        "packed_hex": raw.hex(),
        "sha256": hashlib.sha256(f"{len(bits)}:".encode() + raw).hexdigest(),
    }


def matrix(rows):
    return {"rows": len(rows), "cols": len(rows[0]), "data": [packed(row) for row in rows]}


_DEFAULT_INTEGRITY = object()
_ARTIFACT_SHA = "c" * 64
_SEMANTIC_SHA = "b" * 64
_ENVIRONMENT = {"python": "test", "qldpc": "test"}


def sample_certificate():
    return {
        "certificate_type": "qldpc-noncss-matrix-exact",
        "certificate_sha256": "a" * 64,
        "passed": True,
        "claim": {
            "n": 2, "k": 1, "d": 1,
            "symplectic_stabilizer": matrix([[1, 1, 0, 0]]),
        },
        "milp": {"directions": [
            {"target_logical": packed([1, 0, 0, 0])},
            {"target_logical": packed([0, 0, 1, 1])},
        ]},
        "upper_witness": {"operator": packed([1, 0, 0, 0])},
    }


def strict_integrity():
    return {
        "passed": True,
        "mode": "strict",
        "artifact_sha256": _ARTIFACT_SHA,
        "semantic_sha256": _SEMANTIC_SHA,
        "rerun_semantic_sha256": _SEMANTIC_SHA,
        "environment": _ENVIRONMENT,
    }


def write_release(root, *, integrity=_DEFAULT_INTEGRITY):
    root.mkdir(parents=True)
    trust = {
        "schema_version": 1,
        "artifact_sha256": _ARTIFACT_SHA,
        "semantic_sha256": _SEMANTIC_SHA,
        "environment": _ENVIRONMENT,
    }
    trust_path = root / "known_answer_trust.json"
    trust_path.write_text(json.dumps(trust))
    certificate = sample_certificate()
    certificate["certificate_sha256"] = canonical_sha256(
        certificate, omit="certificate_sha256",
    )
    certificate_path = root / "certificate.json"
    certificate_path.write_text(json.dumps(certificate))
    manifest = {
        "schema_version": 1,
        "gate": "qldpc-challenge-release",
        "run_id": "bridge-test",
        "passed": True,
        "certificates": [{
            "file": "certificate.json",
            "certificate_sha256": certificate["certificate_sha256"],
            "verification": {"passed": True},
        }],
    }
    if integrity is _DEFAULT_INTEGRITY:
        integrity = strict_integrity()
    if integrity is not None:
        manifest["known_answer_integrity"] = integrity
    manifest["manifest_sha256"] = canonical_sha256(
        manifest, omit="manifest_sha256",
    )
    manifest_path = root / "manifest.json"
    manifest_path.write_text(json.dumps(manifest))
    return manifest_path, certificate_path, trust_path


def test_generic_symplectic_certificate_renders_exact_theorem():
    certificate = sample_certificate()
    payload = certificate_payload(certificate)
    source = render_module(payload, "Smoke", sat_timeout=30)
    assert payload["n"] == 2
    assert len(payload["logicals"]) == 2
    assert "theorem distance_lower" in source
    assert "bv_decide" in source
    assert "theorem exact_parameters" in source


def test_release_loader_accepts_strict_bound_manifest(tmp_path):
    manifest_path, certificate_path, trust_path = write_release(
        tmp_path / "valid",
    )
    manifest, certificates = load_verified_release(manifest_path, trust_path)
    assert manifest["known_answer_integrity"]["mode"] == "strict"
    assert len(certificates) == 1
    assert certificates[0][1] == certificate_path.resolve()


@pytest.mark.parametrize(("case", "integrity"), [
    ("missing", None),
    ("fast", {
        "passed": True,
        "mode": "fast",
        "artifact_sha256": _ARTIFACT_SHA,
        "semantic_sha256": "b" * 64,
        "rerun_semantic_sha256": "b" * 64,
        "environment": _ENVIRONMENT,
    }),
    ("mismatch", {
        "passed": True,
        "mode": "strict",
        "artifact_sha256": _ARTIFACT_SHA,
        "semantic_sha256": "b" * 64,
        "rerun_semantic_sha256": "c" * 64,
        "environment": _ENVIRONMENT,
    }),
    ("invalid", {
        "passed": True,
        "mode": "strict",
        "artifact_sha256": _ARTIFACT_SHA,
        "semantic_sha256": "B" * 64,
        "rerun_semantic_sha256": "B" * 64,
        "environment": _ENVIRONMENT,
    }),
])
def test_release_loader_rejects_invalid_integrity(tmp_path, case, integrity):
    manifest_path, _, trust_path = write_release(tmp_path / case, integrity=integrity)
    with pytest.raises(ValueError):
        load_verified_release(manifest_path, trust_path)


def test_release_loader_rejects_manifest_tamper(tmp_path):
    manifest_path, _, trust_path = write_release(tmp_path / "manifest-tamper")
    manifest = json.loads(manifest_path.read_text())
    manifest["run_id"] = "tampered"
    manifest_path.write_text(json.dumps(manifest))
    with pytest.raises(ValueError, match="manifest SHA-256"):
        load_verified_release(manifest_path, trust_path)


def test_release_loader_rejects_certificate_tamper(tmp_path):
    manifest_path, certificate_path, trust_path = write_release(
        tmp_path / "certificate-tamper",
    )
    certificate = json.loads(certificate_path.read_text())
    certificate["tampered"] = True
    certificate_path.write_text(json.dumps(certificate))
    with pytest.raises(ValueError, match="internal SHA-256"):
        load_verified_release(manifest_path, trust_path)


def test_release_loader_rejects_unverified_entry(tmp_path):
    manifest_path, _, trust_path = write_release(tmp_path / "unverified")
    manifest = json.loads(manifest_path.read_text())
    manifest["certificates"][0]["verification"]["passed"] = False
    manifest["manifest_sha256"] = canonical_sha256(
        manifest, omit="manifest_sha256",
    )
    manifest_path.write_text(json.dumps(manifest))
    with pytest.raises(ValueError, match="not fully verified"):
        load_verified_release(manifest_path, trust_path)


def test_release_loader_rejects_path_escape(tmp_path):
    manifest_path, certificate_path, trust_path = write_release(tmp_path / "release")
    outside = tmp_path / "outside.json"
    outside.write_text(certificate_path.read_text())
    manifest = json.loads(manifest_path.read_text())
    manifest["certificates"][0]["file"] = "../outside.json"
    manifest["manifest_sha256"] = canonical_sha256(
        manifest, omit="manifest_sha256",
    )
    manifest_path.write_text(json.dumps(manifest))
    with pytest.raises(ValueError, match="must not contain"):
        load_verified_release(manifest_path, trust_path)


def test_release_loader_rejects_repository_trust_mismatch(tmp_path):
    manifest_path, _, trust_path = write_release(tmp_path / "trust-mismatch")
    trust = json.loads(trust_path.read_text())
    trust["semantic_sha256"] = "d" * 64
    trust_path.write_text(json.dumps(trust))

    with pytest.raises(ValueError, match="differs from trust"):
        load_verified_release(manifest_path, trust_path)
