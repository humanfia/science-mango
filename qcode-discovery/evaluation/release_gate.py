"""Immutable manifest guard for formalization, publication, and CI."""

from __future__ import annotations

import hashlib
import json
from pathlib import Path
from typing import Any


def _is_lower_sha256(value: Any) -> bool:
    return (
        isinstance(value, str)
        and len(value) == 64
        and all(character in "0123456789abcdef" for character in value)
    )


def canonical_sha256(value: Any, *, omit: str | None = None) -> str:
    if isinstance(value, dict) and omit:
        value = {key: item for key, item in value.items() if key != omit}
    encoded = json.dumps(
        value, sort_keys=True, separators=(",", ":"), ensure_ascii=False,
        allow_nan=False,
    ).encode()
    return hashlib.sha256(encoded).hexdigest()


def resolve_release_certificate_path(
    manifest_path: Path | str,
    entry_file: Any,
) -> Path:
    """Resolve one certificate below the real manifest directory."""
    if not isinstance(entry_file, str) or not entry_file:
        raise ValueError("release certificate path must be a non-empty string")
    relative = Path(entry_file)
    if relative.is_absolute():
        raise ValueError("release certificate path must be relative")
    if ".." in relative.parts:
        raise ValueError("release certificate path must not contain '..'")
    root = Path(manifest_path).resolve().parent
    certificate_path = (root / relative).resolve()
    try:
        certificate_path.relative_to(root)
    except ValueError as exc:
        raise ValueError("release certificate path escapes manifest directory") from exc
    return certificate_path


def validate_release_manifest(
    manifest_path: Path | str,
    *,
    known_answer_trust_path: Path | str,
    expected_run_id: str | None = None,
) -> dict[str, Any]:
    """Fail closed unless every published certificate is immutable and verified."""
    path = Path(manifest_path)
    failures: list[str] = []
    try:
        manifest = json.loads(path.read_text())
    except (OSError, UnicodeError, json.JSONDecodeError) as exc:
        return {"passed": False, "failures": [f"release manifest unavailable: {exc}"]}
    if not isinstance(manifest, dict):
        return {
            "passed": False,
            "failures": ["release manifest must be a JSON object"],
        }
    try:
        trust = json.loads(Path(known_answer_trust_path).read_text())
    except (OSError, UnicodeError, json.JSONDecodeError) as exc:
        trust = None
        failures.append(f"known-answer trust unavailable or invalid: {exc}")
    if not isinstance(trust, dict):
        if trust is not None:
            failures.append("known-answer trust must be a JSON object")
        trust = {}
    if trust.get("schema_version") != 1:
        failures.append("known-answer trust schema_version must be 1")
    trust_artifact_sha = trust.get("artifact_sha256")
    trust_semantic_sha = trust.get("semantic_sha256")
    if not _is_lower_sha256(trust_artifact_sha):
        failures.append("known-answer trust artifact SHA-256 is invalid")
    if not _is_lower_sha256(trust_semantic_sha):
        failures.append("known-answer trust semantic SHA-256 is invalid")
    if not isinstance(trust.get("environment"), dict):
        failures.append("known-answer trust environment must be an object")
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
    integrity = manifest.get("known_answer_integrity")
    if not isinstance(integrity, dict):
        failures.append("release manifest has no known-answer integrity evidence")
    else:
        if integrity.get("passed") is not True:
            failures.append("known-answer integrity did not pass")
        if integrity.get("mode") != "strict":
            failures.append("known-answer integrity mode must be strict")
        artifact_sha = integrity.get("artifact_sha256")
        semantic_sha = integrity.get("semantic_sha256")
        rerun_semantic_sha = integrity.get("rerun_semantic_sha256")
        if not _is_lower_sha256(artifact_sha):
            failures.append("known-answer artifact SHA-256 is invalid")
        if not _is_lower_sha256(semantic_sha):
            failures.append("known-answer semantic SHA-256 is invalid")
        if not _is_lower_sha256(rerun_semantic_sha):
            failures.append("known-answer rerun semantic SHA-256 is invalid")
        if semantic_sha != rerun_semantic_sha:
            failures.append("known-answer strict rerun semantic SHA-256 mismatch")
        if artifact_sha != trust_artifact_sha:
            failures.append("known-answer artifact SHA-256 differs from repository trust")
        if semantic_sha != trust_semantic_sha:
            failures.append("known-answer semantic SHA-256 differs from repository trust")
        if rerun_semantic_sha != trust_semantic_sha:
            failures.append("known-answer rerun SHA-256 differs from repository trust")
        if integrity.get("environment") != trust.get("environment"):
            failures.append("known-answer environment differs from repository trust")
    entries = manifest.get("certificates")
    if not isinstance(entries, list) or not entries:
        failures.append("release manifest has no certificates")
        entries = []
    verified = 0
    for index, entry in enumerate(entries):
        if not isinstance(entry, dict):
            failures.append(f"certificate[{index}] is malformed")
            continue
        try:
            certificate_path = resolve_release_certificate_path(
                path, entry.get("file"),
            )
        except ValueError as exc:
            failures.append(f"certificate[{index}] path is unsafe: {exc}")
            continue
        try:
            certificate = json.loads(certificate_path.read_text())
        except (OSError, UnicodeError, json.JSONDecodeError) as exc:
            failures.append(f"certificate[{index}] unavailable: {exc}")
            continue
        if not isinstance(certificate, dict):
            failures.append(f"certificate[{index}] must be a JSON object")
            continue
        try:
            actual_sha = canonical_sha256(
                certificate, omit="certificate_sha256",
            )
        except (TypeError, ValueError) as exc:
            failures.append(f"certificate[{index}] cannot be hashed: {exc}")
            continue
        if actual_sha != certificate.get("certificate_sha256"):
            failures.append(f"certificate[{index}] internal SHA-256 mismatch")
        if actual_sha != entry.get("certificate_sha256"):
            failures.append(f"certificate[{index}] manifest SHA-256 mismatch")
        verification = entry.get("verification")
        if (
            certificate.get("passed") is not True
            or not isinstance(verification, dict)
            or verification.get("passed") is not True
        ):
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
