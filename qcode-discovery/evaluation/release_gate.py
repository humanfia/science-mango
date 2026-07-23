"""Immutable manifest guard for formalization, publication, and CI."""

from __future__ import annotations

import hashlib
import json
from pathlib import Path
from typing import Any


def canonical_sha256(value: Any, *, omit: str | None = None) -> str:
    if isinstance(value, dict) and omit:
        value = {key: item for key, item in value.items() if key != omit}
    encoded = json.dumps(
        value, sort_keys=True, separators=(",", ":"), ensure_ascii=False,
        allow_nan=False,
    ).encode()
    return hashlib.sha256(encoded).hexdigest()


def validate_release_manifest(
    manifest_path: Path | str,
    *,
    expected_run_id: str | None = None,
) -> dict[str, Any]:
    """Fail closed unless every published certificate is immutable and verified."""
    path = Path(manifest_path)
    failures: list[str] = []
    try:
        manifest = json.loads(path.read_text())
    except (OSError, json.JSONDecodeError) as exc:
        return {"passed": False, "failures": [f"release manifest unavailable: {exc}"]}
    if manifest.get("schema_version") != 1:
        failures.append("release manifest schema_version must be 1")
    if manifest.get("gate") != "qldpc-challenge-release":
        failures.append("unexpected release gate identifier")
    if expected_run_id is not None and manifest.get("run_id") != expected_run_id:
        failures.append("release manifest run_id mismatch")
    if manifest.get("manifest_sha256") != canonical_sha256(
        manifest, omit="manifest_sha256",
    ):
        failures.append("release manifest SHA-256 mismatch")
    entries = manifest.get("certificates")
    if not isinstance(entries, list) or not entries:
        failures.append("release manifest has no certificates")
        entries = []
    verified = 0
    for index, entry in enumerate(entries):
        if not isinstance(entry, dict):
            failures.append(f"certificate[{index}] is malformed")
            continue
        certificate_path = path.parent / str(entry.get("file", ""))
        try:
            certificate = json.loads(certificate_path.read_text())
        except (OSError, json.JSONDecodeError) as exc:
            failures.append(f"certificate[{index}] unavailable: {exc}")
            continue
        actual_sha = canonical_sha256(certificate, omit="certificate_sha256")
        if actual_sha != certificate.get("certificate_sha256"):
            failures.append(f"certificate[{index}] internal SHA-256 mismatch")
        if actual_sha != entry.get("certificate_sha256"):
            failures.append(f"certificate[{index}] manifest SHA-256 mismatch")
        verification = entry.get("verification") or {}
        if certificate.get("passed") is not True or verification.get("passed") is not True:
            failures.append(f"certificate[{index}] was not fully verified")
        else:
            verified += 1
    if manifest.get("passed") is not True or verified != len(entries):
        failures.append("release manifest is not fully passed")
    return {
        "passed": not failures,
        "run_id": manifest.get("run_id"),
        "certificates": len(entries),
        "verified": verified,
        "failures": failures,
    }
