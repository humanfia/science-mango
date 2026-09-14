"""Copy and verify research evidence, and run only the fixed baseline checks.

The copied working directory is an integrity boundary, not a host sandbox.
Credential-like and hidden filenames are excluded; this is not a content-level
secret scanner. No candidate code or model-supplied command is executed here.
"""

from __future__ import annotations

import hashlib
import json
import math
import os
from pathlib import Path
import re
import stat
import subprocess
import sys


BASELINE_CHECKERS = ("quantum_baseline_check.py",)
MAX_BASELINE_TIMEOUT = 600
OUTPUT_TAIL_CHARS = 16 * 1024
_METADATA = "_snapshot.json"
_RESEARCH_DIRECTORY = ("pipelines", "live-research-20260910")
_DIGEST = re.compile(r"[0-9a-f]{64}\Z")
_CREDENTIAL_NAME = re.compile(
    r"(^|[._-])(credentials?|secrets?|passwords?|tokens?|api[_-]?keys?|"
    r"access[_-]?tokens?|auth[_-]?tokens?|private[_-]?keys?)([._-]|$)",
    re.IGNORECASE,
)


def _input_name(name: str) -> bool:
    return (
        isinstance(name, str)
        and bool(name)
        and not any(character in name for character in ("/", "\\", "\0"))
        and not name.startswith(".")
        and not _CREDENTIAL_NAME.search(name)
        and (name == "MANIFEST.json" or Path(name).suffix in {".md", ".py"})
    )


def is_research_path(name: str) -> bool:
    """Whether a relative evidence path is in the fixed input namespace.

    This checks spelling only. Every filesystem operation separately refuses
    symlinks in the file and its complete ancestor chain. Nested Markdown is
    eligible only when explicitly selected, never by recursive discovery.
    """
    if not isinstance(name, str) or "\\" in name or "\0" in name:
        return False
    parts = name.split("/")
    if any(part in {"", ".", ".."} for part in parts):
        return False
    if len(parts) == 1:
        return _input_name(name)
    return (
        len(parts) == 2 and parts[0] in {"docs", "scripts", "tests", "evidence", "data"}
        and not parts[-1].startswith(".") and not _CREDENTIAL_NAME.search(parts[-1])
        and Path(parts[-1]).suffix in ({".md"} if parts[0] == "docs" else {".md", ".py", ".json", ".jsonl", ".csv"})
        and not any(ord(c) < 32 or ord(c) == 127 for c in parts[-1])
    )



def _directory(path: Path) -> None:
    absolute = path.absolute()
    for component in (*reversed(absolute.parents), absolute):
        mode = component.lstat().st_mode
        if stat.S_ISLNK(mode) or not stat.S_ISDIR(mode):
            raise ValueError(f"Not a regular directory (symlinks refused): {component}")


def _read_regular(path: Path) -> bytes:
    _directory(path.parent)
    if path.is_symlink():
        raise ValueError(f"Symlink refused: {path}")
    flags = os.O_RDONLY | getattr(os, "O_NOFOLLOW", 0) | getattr(os, "O_NONBLOCK", 0)
    descriptor = os.open(path, flags)
    if not stat.S_ISREG(os.fstat(descriptor).st_mode):
        os.close(descriptor)
        raise ValueError(f"Not a regular file: {path}")
    with os.fdopen(descriptor, "rb") as handle:
        return handle.read()


def _write_new(path: Path, data: bytes) -> None:
    _directory(path.parent)
    descriptor = os.open(path, os.O_WRONLY | os.O_CREAT | os.O_EXCL, 0o600)
    with os.fdopen(descriptor, "wb") as handle:
        handle.write(data)


def _input_destination(directory: Path, name: str) -> Path:
    """Create only the required safe parent directories for one input."""
    if not is_research_path(name):
        raise ValueError(f"Invalid snapshot path: {name!r}")
    parent = directory
    _directory(parent)
    for part in name.split("/")[:-1]:
        child = parent / part
        if not os.path.lexists(child):
            child.mkdir(mode=0o700)
        _directory(child)
        parent = child
    return parent / name.split("/")[-1]


def _entry(name: str, data: bytes) -> dict:
    return {"path": name, "sha256": hashlib.sha256(data).hexdigest(), "bytes": len(data)}


def _source_names(repo: Path) -> list[str]:
    _directory(repo)
    names = []
    for path in repo.iterdir():
        if not _input_name(path.name):
            continue
        mode = path.lstat().st_mode
        if stat.S_ISLNK(mode):
            raise ValueError(f"Symlink refused: {path}")
        if stat.S_ISDIR(mode):
            continue
        if not stat.S_ISREG(mode):
            raise ValueError(f"Not a regular input file: {path}")
        names.append(path.name)
    return sorted(names)


def _repository_head(repo: Path) -> str:
    # rev-parse is local and invokes no remote or credential helper.
    result = subprocess.run(
        ["git", "--no-optional-locks", "-C", str(repo), "rev-parse", "--verify", "HEAD"],
        capture_output=True,
        text=True,
        timeout=10,
        env={
            "PATH": os.environ.get("PATH", os.defpath),
            "GIT_CONFIG_NOSYSTEM": "1",
            "GIT_CONFIG_GLOBAL": os.devnull,
            "GIT_TERMINAL_PROMPT": "0",
        },
    )
    head = result.stdout.strip()
    if result.returncode or not re.fullmatch(r"[0-9a-f]{40}|[0-9a-f]{64}", head):
        raise ValueError("Cannot resolve the source repository HEAD")
    return head


def _manifest_files(manifest: dict) -> dict[str, dict]:
    if not isinstance(manifest, dict) or set(manifest) != {"head", "files"}:
        raise ValueError("Snapshot manifest must contain exactly head and files")
    if not isinstance(manifest["head"], str) or not manifest["head"]:
        raise ValueError("Snapshot manifest head must be a nonempty string")
    if not isinstance(manifest["files"], list):
        raise ValueError("Snapshot manifest files must be a list")
    entries = {}
    for entry in manifest["files"]:
        if not isinstance(entry, dict) or set(entry) != {"path", "sha256", "bytes"}:
            raise ValueError("Invalid snapshot file record")
        name = entry["path"]
        if not is_research_path(name) or name in entries:
            raise ValueError(f"Invalid or duplicate snapshot path: {name!r}")
        if not isinstance(entry["sha256"], str) or not _DIGEST.fullmatch(entry["sha256"]):
            raise ValueError(f"Invalid SHA-256: {name}")
        if type(entry["bytes"]) is not int or entry["bytes"] < 0:
            raise ValueError(f"Invalid byte count: {name}")
        entries[name] = entry
    return entries


def _metadata_bytes(manifest: dict) -> bytes:
    return (json.dumps(manifest, ensure_ascii=False, indent=2) + "\n").encode("utf-8")


def _mismatch(name: str, data: bytes, entry: dict) -> list[str]:
    errors = []
    if len(data) != entry["bytes"]:
        errors.append(f"Byte count changed: {name}")
    if hashlib.sha256(data).hexdigest() != entry["sha256"]:
        errors.append(f"SHA-256 changed: {name}")
    return errors


def snapshot_repository(repo: Path, destination: Path, *, extra_inputs=()) -> dict:
    """Capture all top-level research files and explicitly selected inputs.

    Uncommitted content is included. Extra inputs must use the fixed research
    namespace; no nested directory is scanned for additional evidence. Their
    original relative paths are retained in the unchanged head/files schema.
    The destination must not exist and its parent must already exist. On a
    write failure, a partial destination may remain for the caller to inspect.
    """
    repo, destination = Path(repo), Path(destination)
    if os.path.lexists(destination):
        raise FileExistsError(f"Snapshot destination already exists: {destination}")
    _directory(destination.parent)
    if isinstance(extra_inputs, (str, bytes)):
        raise ValueError("Extra inputs must be an explicit iterable of paths, not a string")
    try:
        extras = list(extra_inputs)
    except TypeError as exc:
        raise ValueError("Extra inputs must be an explicit iterable of paths") from exc
    if any(not is_research_path(name) for name in extras):
        raise ValueError("Invalid extra input path")
    if len(set(extras)) != len(extras):
        raise ValueError("Duplicate extra input path")
    names = sorted(set(_source_names(repo)) | set(extras))
    head = _repository_head(repo)
    contents = {name: _read_regular(repo / name) for name in names}
    manifest = {"head": head, "files": [_entry(name, contents[name]) for name in names]}
    errors = verify_source(repo, manifest)
    if errors:
        raise ValueError("Source changed during capture: " + "; ".join(errors))
    destination.mkdir(mode=0o700)
    for name, data in contents.items():
        _write_new(_input_destination(destination, name), data)
    _write_new(destination / _METADATA, _metadata_bytes(manifest))
    return manifest


def verify_snapshot(directory: Path, manifest: dict) -> list[str]:
    """Report missing, altered, extra, or symlinked snapshot entries."""
    directory = Path(directory)
    try:
        entries = _manifest_files(manifest)
        _directory(directory)
    except (OSError, ValueError) as exc:
        return [str(exc)]
    expected = set(entries) | {_METADATA}
    expected_directories = {
        "/".join(name.split("/")[:index])
        for name in entries
        for index in range(1, len(name.split("/")))
    }
    errors = []

    # The namespace permits only these two nested parent levels. Never walk
    # an unselected directory, even to inspect an unexpected entry inside it.
    for parent_name in ["", *sorted(expected_directories)]:
        parent = directory / parent_name
        try:
            _directory(parent)
            children = sorted(parent.iterdir())
        except (OSError, ValueError) as exc:
            errors.append(f"Cannot inspect snapshot directory {parent}: {exc}")
            continue
        for path in children:
            name = path.relative_to(directory).as_posix()
            try:
                mode = path.lstat().st_mode
                if stat.S_ISLNK(mode):
                    errors.append(f"Symlink refused in snapshot: {name}")
                elif stat.S_ISDIR(mode):
                    if name not in expected_directories:
                        errors.append(f"Unexpected snapshot entry: {name}")
                elif not stat.S_ISREG(mode):
                    errors.append(f"Not a regular snapshot entry: {name}")
                elif name not in expected:
                    errors.append(f"Unexpected snapshot entry: {name}")
            except (OSError, ValueError) as exc:
                errors.append(f"Cannot inspect snapshot entry {name}: {exc}")

    for name, entry in entries.items():
        try:
            errors.extend(_mismatch(name, _read_regular(directory / name), entry))
        except (OSError, ValueError) as exc:
            errors.append(f"Cannot verify {name}: {exc}")
    try:
        saved = json.loads(_read_regular(directory / _METADATA))
        _manifest_files(saved)
        if saved != manifest:
            errors.append("Saved _snapshot.json differs from the supplied manifest")
    except (OSError, ValueError, UnicodeError) as exc:
        errors.append(f"Cannot verify {_METADATA}: {exc}")
    return errors


def verify_source(repo: Path, manifest: dict) -> list[str]:
    """Verify HEAD, the complete top-level set, and only declared extra inputs."""
    repo = Path(repo)
    try:
        entries = _manifest_files(manifest)
        names = set(_source_names(repo))
    except (OSError, ValueError) as exc:
        return [str(exc)]
    top_level = {name for name in entries if "/" not in name}
    extras = set(entries) - top_level
    errors = [f"New source input: {name}" for name in sorted(names - top_level)]
    errors.extend(f"Missing source input: {name}" for name in sorted(top_level - names))
    for name in sorted((names & top_level) | extras):
        try:
            errors.extend(_mismatch(name, _read_regular(repo / name), entries[name]))
        except (OSError, ValueError) as exc:
            errors.append(f"Cannot verify source {name}: {exc}")
    try:
        if _repository_head(repo) != manifest["head"]:
            errors.append("Source HEAD changed")
    except (OSError, ValueError, subprocess.SubprocessError) as exc:
        errors.append(f"Cannot verify source HEAD: {exc}")
    return errors


def copy_inputs(snapshot: Path, destination: Path, manifest: dict, *, additional_inputs=None) -> dict:
    """Copy verified evidence plus optional content-addressed proof Markdown.

    Additions are in-memory bytes supplied by the current run's controller,
    never a directory scan. Return the session's manifest without modifying
    the base snapshot or its manifest; absent additions return the original.
    """
    snapshot, destination = Path(snapshot), Path(destination)
    if os.path.lexists(destination):
        raise FileExistsError(f"Input destination already exists: {destination}")
    _directory(destination.parent)
    errors = verify_snapshot(snapshot, manifest)
    if errors:
        raise ValueError("Snapshot integrity failure: " + "; ".join(errors))
    entries = _manifest_files(manifest)
    if additional_inputs is not None and not isinstance(additional_inputs, dict):
        raise ValueError("Additional inputs must be a dict of proof paths to bytes")
    additions = {} if additional_inputs is None else dict(additional_inputs)
    for name, data in additions.items():
        match = re.fullmatch(
            r"docs/proof-([0-9a-f]{64})\.md", name
        ) if isinstance(name, str) else None
        if match is None or not isinstance(data, bytes):
            raise ValueError(f"Invalid additional proof input: {name!r}")
        if hashlib.sha256(data).hexdigest() != match.group(1):
            raise ValueError(f"Additional proof SHA-256 does not match its path: {name}")
        if name in entries:
            raise ValueError(f"Additional proof path collides with base input: {name}")
    contents = {}
    for name, entry in entries.items():
        data = _read_regular(snapshot / name)
        errors.extend(_mismatch(name, data, entry))
        contents[name] = data
    errors.extend(verify_snapshot(snapshot, manifest))
    if errors:
        raise ValueError("Snapshot changed during copy: " + "; ".join(errors))
    merged = manifest
    if additions:
        contents.update(additions)
        merged = {
            "head": manifest["head"],
            "files": [dict(entry) for entry in manifest["files"]]
            + [_entry(name, additions[name]) for name in sorted(additions)],
        }
    destination.mkdir(mode=0o700)
    for name, data in contents.items():
        _write_new(_input_destination(destination, name), data)
    _write_new(destination / _METADATA, _metadata_bytes(merged))
    return merged


def _archive_path(repo: Path, name: str) -> Path:
    if not isinstance(name, str) or "\\" in name or "\0" in name:
        raise ValueError(f"Invalid archive path: {name!r}")
    parts = name.split("/")
    if any(part in {"", ".", ".."} for part in parts):
        raise ValueError(f"Archive path escapes or is ambiguous: {name!r}")
    if (
        any(part.startswith(".") or _CREDENTIAL_NAME.search(part) for part in parts)
        or not is_research_path(name)
    ):
        raise ValueError(f"Non-research archive path refused: {name!r}")
    path = repo
    for part in parts[:-1]:
        path /= part
        _directory(path)
    return path / parts[-1]


def validate_archive(repo: Path) -> list[str]:
    """Check every original MANIFEST.json record using its exported SHA-256."""
    repo = Path(repo)
    try:
        _directory(repo)
        archive = json.loads(_read_regular(repo / "MANIFEST.json"))
        if not isinstance(archive, dict) or not isinstance(archive.get("files"), list):
            raise ValueError("Archive MANIFEST.json must contain a files list")
    except (OSError, ValueError, UnicodeError) as exc:
        return [f"Cannot load archive manifest: {exc}"]
    errors, seen = [], set()
    for entry in archive["files"]:
        try:
            if not isinstance(entry, dict):
                raise ValueError("Invalid archive file record")
            name = entry.get("path")
            path = _archive_path(repo, name)
            if name in seen:
                raise ValueError(f"Duplicate archive path: {name}")
            seen.add(name)
            digest, size = entry.get("exportedSha256"), entry.get("bytes")
            if not isinstance(digest, str) or not _DIGEST.fullmatch(digest):
                raise ValueError(f"Invalid archive exported SHA-256: {name}")
            if type(size) is not int or size < 0:
                raise ValueError(f"Invalid archive byte count: {name}")
            errors.extend(_mismatch(name, _read_regular(path), {"sha256": digest, "bytes": size}))
        except (OSError, ValueError) as exc:
            errors.append(str(exc))
    return errors


def _tail(value: str | bytes | None) -> str:
    if isinstance(value, bytes):
        value = value.decode("utf-8", errors="replace")
    return (value or "")[-OUTPUT_TAIL_CHARS:]


def run_baseline_checks(
    snapshot: Path, manifest: dict, *, timeout: float = 120, checker_names=None
) -> list[dict]:
    """Run a selected subset of the eight fixed, manifest-verified checkers.

    Invalid requests or an initially damaged snapshot raise ValueError without
    executing any checker. Missing checks, process failures, and integrity
    changes become failed reports. A cwd copy does not isolate host access.
    """
    if (
        isinstance(timeout, bool)
        or not isinstance(timeout, (int, float))
        or not 0 < timeout <= MAX_BASELINE_TIMEOUT
        or not math.isfinite(timeout)
    ):
        raise ValueError(f"Checker timeout must be in (0, {MAX_BASELINE_TIMEOUT}] seconds")
    if isinstance(checker_names, (str, bytes)):
        raise ValueError("checker_names must be a sequence of whitelist filenames")
    names = list(BASELINE_CHECKERS if checker_names is None else checker_names)
    if any(not isinstance(name, str) or name not in BASELINE_CHECKERS for name in names):
        raise ValueError("Only the eight fixed baseline checker filenames are permitted")
    if len(set(names)) != len(names):
        raise ValueError("Duplicate baseline checker filename")
    errors = verify_snapshot(snapshot, manifest)
    if errors:
        raise ValueError("Snapshot integrity failure: " + "; ".join(errors))
    entries = _manifest_files(manifest)
    env = {key: os.environ[key] for key in ("PATH", "LANG", "LC_ALL", "LC_CTYPE", "TZ", "SYSTEMROOT") if key in os.environ}
    env.update({"PYTHONDONTWRITEBYTECODE": "1", "HUMANIZE_SENTRY": "off"})
    reports = []
    for name in names:
        report = {"name": name, "passed": False, "returncode": None, "stdout": "", "stderr": ""}
        errors = verify_snapshot(snapshot, manifest)
        if name not in entries:
            errors.append(f"Baseline checker absent from manifest: {name}")
        if errors:
            report["stderr"] = _tail("Snapshot integrity failure before execution: " + "; ".join(errors))
            reports.append(report)
            continue
        try:
            completed = subprocess.run(
                [sys.executable, "-B", name],
                cwd=Path(snapshot),
                env=env,
                timeout=timeout,
                capture_output=True,
                text=True,
                encoding="utf-8",
                errors="replace",
            )
            report.update(
                passed=completed.returncode == 0,
                returncode=completed.returncode,
                stdout=_tail(completed.stdout),
                stderr=_tail(completed.stderr),
            )
        except subprocess.TimeoutExpired as exc:
            report["stdout"] = _tail(exc.stdout)
            report["stderr"] = _tail(_tail(exc.stderr) + f"\nChecker timed out after {timeout} seconds")
        except (OSError, subprocess.SubprocessError) as exc:
            report["stderr"] = _tail(str(exc))
        errors = verify_snapshot(snapshot, manifest)
        if errors:
            report["passed"] = False
            report["stderr"] = _tail(report["stderr"] + "\nSnapshot integrity failure after execution: " + "; ".join(errors))
        reports.append(report)
    return reports
