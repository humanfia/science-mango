"""Fail-closed readable view for ansatz-v3 mutation generation.

The Codex mutation backend must not see the repository that contains the
published-anchor manifest or the post-seal calibration implementation.  This
module materializes the only two non-sensitive files useful to mutation in a
small, immutable view and binds every byte.  Runtime code additionally places
that view in an OS chroot before invoking Codex; changing ``cwd`` alone would
not be a read-isolation boundary.
"""

from __future__ import annotations

import hashlib
import json
import os
import stat
import tempfile
from pathlib import Path
from typing import Any


VIEW_SCHEMA_VERSION = 1
VIEW_KIND = "qcode-ansatz-v3-codex-sanitized-view"
VIEW_MANIFEST_NAME = "ANSATZ_V3_CODEX_VIEW.json"
VIEW_DIRECTORY_NAME = "ansatz-v3-codex-sanitized-view-v1"
VIEW_SOURCE_ALLOWLIST = (
    "evolve/config_twisted_torus_ansatz_v3.yaml",
    "evolve/seed_solution_twisted_torus_ansatz_v3.py",
)
FORBIDDEN_READABLE_PATHS = (
    "evaluation/twisted_torus_published_anchors.v1.json",
    "scripts/verify_blind_ansatz_v3_calibration.py",
)


class AnsatzV3CodexViewError(ValueError):
    """The mutation view is absent, changed, or not physically isolated."""


def _canonical_bytes(value: Any) -> bytes:
    return json.dumps(
        value,
        sort_keys=True,
        separators=(",", ":"),
        ensure_ascii=False,
        allow_nan=False,
    ).encode("utf-8")


def _sha256(payload: bytes) -> str:
    return hashlib.sha256(payload).hexdigest()


def _safe_source(repo: Path, relative: str) -> tuple[Path, bytes]:
    relative_path = Path(relative)
    if relative_path.is_absolute() or ".." in relative_path.parts:
        raise AnsatzV3CodexViewError("sanitized-view allowlist path escapes repo")
    source = repo / relative_path
    if source.is_symlink() or not source.is_file():
        raise AnsatzV3CodexViewError(
            f"sanitized-view source must be a regular file: {relative}"
        )
    try:
        resolved = source.resolve(strict=True)
    except OSError as exc:
        raise AnsatzV3CodexViewError(
            f"cannot resolve sanitized-view source: {relative}"
        ) from exc
    if not resolved.is_relative_to(repo):
        raise AnsatzV3CodexViewError("sanitized-view source escapes repo")
    payload = source.read_bytes()
    if source.is_symlink() or source.resolve(strict=True) != resolved:
        raise AnsatzV3CodexViewError("sanitized-view source changed while read")
    return source, payload


def _expected_entries(repo: Path) -> list[dict[str, Any]]:
    entries = []
    for relative in VIEW_SOURCE_ALLOWLIST:
        _source, payload = _safe_source(repo, relative)
        entries.append({
            "path": relative,
            "source_path": relative,
            "bytes": len(payload),
            "sha256": _sha256(payload),
        })
    return entries


def _manifest_payload(entries: list[dict[str, Any]]) -> dict[str, Any]:
    source_fingerprint = _sha256(_canonical_bytes(entries))
    payload = {
        "schema_version": VIEW_SCHEMA_VERSION,
        "kind": VIEW_KIND,
        "allowlist": list(VIEW_SOURCE_ALLOWLIST),
        "forbidden_paths": list(FORBIDDEN_READABLE_PATHS),
        "files": entries,
        "source_fingerprint_sha256": source_fingerprint,
        "filesystem_boundary": "os-chroot-no-main-repository-mount",
        "symlinks_allowed": False,
        "path_escape_allowed": False,
        "write_access": False,
    }
    return {**payload, "manifest_sha256": _sha256(_canonical_bytes(payload))}


def _read_manifest(path: Path) -> tuple[dict[str, Any], str]:
    if path.is_symlink() or not path.is_file():
        raise AnsatzV3CodexViewError("sanitized-view manifest is not regular")
    payload = path.read_bytes()
    try:
        value = json.loads(payload)
    except (UnicodeDecodeError, json.JSONDecodeError) as exc:
        raise AnsatzV3CodexViewError("sanitized-view manifest is invalid") from exc
    if not isinstance(value, dict):
        raise AnsatzV3CodexViewError("sanitized-view manifest is not an object")
    return value, _sha256(payload)


def validate_sanitized_codex_view(
    repo_dir: Path,
    view_dir: Path,
) -> dict[str, Any]:
    """Replay the allowlist, every copied byte, and the exact view topology."""

    repo = repo_dir.resolve(strict=True)
    view = Path(os.path.abspath(view_dir))
    if view.is_symlink() or not view.is_dir():
        raise AnsatzV3CodexViewError("sanitized Codex view is not a directory")
    if stat.S_IMODE(view.stat().st_mode) != 0o555:
        raise AnsatzV3CodexViewError("sanitized Codex view root is not read-only")
    expected_entries = _expected_entries(repo)
    expected_manifest = _manifest_payload(expected_entries)
    manifest_path = view / VIEW_MANIFEST_NAME
    manifest, manifest_file_sha256 = _read_manifest(manifest_path)
    if manifest != expected_manifest:
        raise AnsatzV3CodexViewError(
            "sanitized-view manifest does not match current allowlisted sources"
        )

    expected_files = {VIEW_MANIFEST_NAME, *VIEW_SOURCE_ALLOWLIST}
    observed_files: set[str] = set()
    for root, directories, files in os.walk(view, followlinks=False):
        root_path = Path(root)
        for name in directories:
            directory = root_path / name
            if (
                directory.is_symlink()
                or stat.S_IMODE(directory.stat().st_mode) != 0o555
            ):
                raise AnsatzV3CodexViewError(
                    "sanitized Codex view contains an unsafe directory"
                )
        for name in files:
            path = root_path / name
            if path.is_symlink() or not path.is_file():
                raise AnsatzV3CodexViewError(
                    "sanitized Codex view contains a non-regular file"
                )
            if stat.S_IMODE(path.stat().st_mode) != 0o444:
                raise AnsatzV3CodexViewError(
                    "sanitized Codex view contains a writable file"
                )
            relative = path.relative_to(view).as_posix()
            if ".." in Path(relative).parts:
                raise AnsatzV3CodexViewError("sanitized-view file escapes root")
            observed_files.add(relative)
    if observed_files != expected_files:
        raise AnsatzV3CodexViewError(
            "sanitized Codex view has missing or unallowlisted files"
        )
    for entry in expected_entries:
        path = view / entry["path"]
        payload = path.read_bytes()
        if len(payload) != entry["bytes"] or _sha256(payload) != entry["sha256"]:
            raise AnsatzV3CodexViewError(
                f"sanitized-view file changed: {entry['path']}"
            )
    for forbidden in FORBIDDEN_READABLE_PATHS:
        path = view / forbidden
        if path.exists() or path.is_symlink():
            raise AnsatzV3CodexViewError(
                f"forbidden anchor/calibration path entered view: {forbidden}"
            )
    return {
        **manifest,
        "view_path": str(view),
        "manifest_path": str(manifest_path.resolve(strict=True)),
        "manifest_file_sha256": manifest_file_sha256,
        "manifest_file_bytes": manifest_path.stat().st_size,
    }


def materialize_sanitized_codex_view(
    repo_dir: Path,
    view_dir: Path,
) -> dict[str, Any]:
    """Create the immutable allowlisted view once, or replay an existing one."""

    repo = repo_dir.resolve(strict=True)
    view = Path(os.path.abspath(view_dir))
    if view.exists() or view.is_symlink():
        return validate_sanitized_codex_view(repo, view)
    view.parent.mkdir(parents=True, exist_ok=True)
    entries = _expected_entries(repo)
    manifest = _manifest_payload(entries)
    temporary = Path(tempfile.mkdtemp(
        prefix=f".{view.name}.",
        dir=view.parent,
    ))
    try:
        for entry in entries:
            relative = Path(entry["path"])
            destination = temporary / relative
            destination.parent.mkdir(parents=True, exist_ok=True)
            _source, payload = _safe_source(repo, entry["source_path"])
            if len(payload) != entry["bytes"] or _sha256(payload) != entry["sha256"]:
                raise AnsatzV3CodexViewError(
                    "allowlisted source changed during view materialization"
                )
            destination.write_bytes(payload)
            destination.chmod(0o444)
        manifest_path = temporary / VIEW_MANIFEST_NAME
        manifest_path.write_text(
            json.dumps(manifest, ensure_ascii=False, sort_keys=True, indent=2) + "\n",
            encoding="utf-8",
        )
        manifest_path.chmod(0o444)
        for root, directories, _files in os.walk(temporary, topdown=False):
            for name in directories:
                (Path(root) / name).chmod(0o555)
        temporary.chmod(0o555)
        try:
            os.rename(temporary, view)
        except FileExistsError:
            pass
        return validate_sanitized_codex_view(repo, view)
    finally:
        if temporary.exists():
            for root, directories, files in os.walk(temporary, topdown=False):
                for name in files:
                    (Path(root) / name).chmod(0o600)
                    (Path(root) / name).unlink()
                for name in directories:
                    (Path(root) / name).chmod(0o700)
                    (Path(root) / name).rmdir()
            temporary.chmod(0o700)
            temporary.rmdir()


__all__ = [
    "AnsatzV3CodexViewError",
    "FORBIDDEN_READABLE_PATHS",
    "VIEW_DIRECTORY_NAME",
    "VIEW_MANIFEST_NAME",
    "VIEW_SOURCE_ALLOWLIST",
    "materialize_sanitized_codex_view",
    "validate_sanitized_codex_view",
]
