#!/usr/bin/env python3
"""Build or validate the pinned GPT IPhO answer-blind runtime.

The builder makes the smallest possible derivative of the already-audited
Kimi runtime.  It copies that exact tree into a sibling staging directory,
rebases launch wrappers to the final GPT path, installs four reviewed physics
files, changes only ``CodexAgent.run``'s idle default, seals the tree, and then
atomically renames it into place.
"""

from __future__ import annotations

import argparse
import hashlib
import json
import os
import shutil
import stat
import tempfile
import uuid
from pathlib import Path
from typing import Any, Iterable


BASE_RUNTIME = Path(
    "/opt/icho-answer-blind-runtime-10b04c62-rebuilt1-idle1800"
)
GPT_RUNTIME = Path(
    "/opt/icho-answer-blind-runtime-10b04c62-rebuilt1-gpt-idle1800"
)
EXPECTED_BASE_COMMIT = "10b04c62f66af0815bfa0bfa3c5cb3cbd5ef5358"
SOURCE_MARKER = Path("answer-blind-source-commit.txt")
BUILD_MARKER = Path("ipho-answer-blind-gpt-runtime.json")
PROTOCOL = "ipho-2026-answer-blind-gpt-runtime-v1"
SCHEMA_VERSION = 1
REPO_ROOT = Path(__file__).resolve().parents[1]

OVERLAYS: tuple[tuple[Path, Path], ...] = (
    (
        Path("src/archon/.archon-src/prover-modes/physics-formalize.md"),
        Path(".archon-src/prover-modes/physics-formalize.md"),
    ),
    (
        Path("src/archon/.archon-src/prover-modes/physics.md"),
        Path(".archon-src/prover-modes/physics.md"),
    ),
    (
        Path("src/archon/.archon-src/subagents/physics-reviewer.md"),
        Path(".archon-src/subagents/physics-reviewer.md"),
    ),
    (
        Path("src/archon/commands/tooling/lean_explore_mcp_shim.py"),
        Path("commands/tooling/lean_explore_mcp_shim.py"),
    ),
)
CODEX_AGENT = Path("agents/codex.py")
CLAUDE_AGENT = Path("agent.py")
OLD_IDLE = b'        idle_timeout_s: float | None = 900,\n'
NEW_IDLE = b'        idle_timeout_s: float | None = 1800,\n'


class RuntimeBuildError(RuntimeError):
    """The base, build transaction, or resulting runtime is invalid."""


def _sha256(path: Path) -> str:
    digest = hashlib.sha256()
    with path.open("rb") as stream:
        for chunk in iter(lambda: stream.read(1024 * 1024), b""):
            digest.update(chunk)
    return digest.hexdigest()


def _lexists(path: Path) -> bool:
    return os.path.lexists(path)


def _plain_directory(path: Path, *, label: str) -> Path:
    if path.is_symlink() or not path.is_dir():
        raise RuntimeBuildError(f"{label} must be a plain directory: {path}")
    return path.resolve(strict=True)


def _plain_file(path: Path, *, label: str) -> Path:
    if path.is_symlink() or not path.is_file():
        raise RuntimeBuildError(f"{label} must be a plain file: {path}")
    return path


def _base_commit(base: Path) -> str:
    marker = _plain_file(base / SOURCE_MARKER, label="base source marker")
    value = marker.read_text(encoding="ascii").strip()
    if value != EXPECTED_BASE_COMMIT:
        raise RuntimeBuildError(
            f"base source marker is {value!r}, expected {EXPECTED_BASE_COMMIT}"
        )
    return value


def _installed_archon(runtime: Path) -> Path:
    candidates = sorted(
        runtime.glob("venv/lib/python*/site-packages/archon")
    )
    candidates = [path for path in candidates if path.is_dir() and not path.is_symlink()]
    if len(candidates) != 1:
        raise RuntimeBuildError(
            f"runtime must contain exactly one installed Archon tree, found {len(candidates)}"
        )
    return candidates[0]


def _prefix_regular_files(runtime: Path) -> tuple[Path, ...]:
    paths: set[Path] = {runtime / "venv/pyvenv.cfg"}
    for directory in (runtime / "bin", runtime / "venv/bin"):
        if not directory.is_dir() or directory.is_symlink():
            raise RuntimeBuildError(f"runtime prefix directory is invalid: {directory}")
        for path in directory.rglob("*"):
            if path.is_file() and not path.is_symlink():
                paths.add(path)
    for path in paths:
        _plain_file(path, label="prefix-bound runtime file")
    return tuple(sorted(paths))


def _symlinks(runtime: Path) -> tuple[Path, ...]:
    return tuple(sorted(path for path in runtime.rglob("*") if path.is_symlink()))


def _atomic_bytes(path: Path, payload: bytes, mode: int) -> None:
    descriptor, raw = tempfile.mkstemp(prefix=f".{path.name}.", dir=path.parent)
    temporary = Path(raw)
    try:
        with os.fdopen(descriptor, "wb") as stream:
            stream.write(payload)
            stream.flush()
            os.fsync(stream.fileno())
        temporary.chmod(mode)
        os.replace(temporary, path)
    except BaseException:
        temporary.unlink(missing_ok=True)
        raise


def _replace_prefixes(
    runtime: Path, *, old: Path, new: Path
) -> dict[str, int]:
    old_bytes = str(old).encode("utf-8")
    new_bytes = str(new).encode("utf-8")
    files_changed = file_occurrences = 0
    for path in _prefix_regular_files(runtime):
        payload = path.read_bytes()
        occurrences = payload.count(old_bytes)
        if not occurrences:
            continue
        _atomic_bytes(
            path,
            payload.replace(old_bytes, new_bytes),
            stat.S_IMODE(path.stat(follow_symlinks=False).st_mode),
        )
        files_changed += 1
        file_occurrences += occurrences

    symlinks_changed = symlink_occurrences = 0
    for path in _symlinks(runtime):
        target = os.readlink(path)
        occurrences = target.count(str(old))
        if not occurrences:
            continue
        path.unlink()
        path.symlink_to(target.replace(str(old), str(new)))
        symlinks_changed += 1
        symlink_occurrences += occurrences
    return {
        "regular_files_changed": files_changed,
        "regular_occurrences": file_occurrences,
        "symlinks_changed": symlinks_changed,
        "symlink_occurrences": symlink_occurrences,
    }


def _overlay_rows(repo: Path, installed: Path) -> list[dict[str, str]]:
    rows: list[dict[str, str]] = []
    for source_rel, destination_rel in OVERLAYS:
        source = _plain_file(repo / source_rel, label="runtime overlay source")
        destination = _plain_file(
            installed / destination_rel, label="runtime overlay destination"
        )
        rows.append(
            {
                "source": source_rel.as_posix(),
                "destination": destination_rel.as_posix(),
                "sha256": _sha256(source),
            }
        )
        _atomic_bytes(
            destination,
            source.read_bytes(),
            stat.S_IMODE(source.stat(follow_symlinks=False).st_mode),
        )
    return rows


def _patch_codex(installed: Path, base_installed: Path) -> dict[str, Any]:
    base = _plain_file(base_installed / CODEX_AGENT, label="base Codex agent")
    destination = _plain_file(installed / CODEX_AGENT, label="installed Codex agent")
    payload = base.read_bytes()
    if payload.count(OLD_IDLE) != 1 or NEW_IDLE in payload:
        raise RuntimeBuildError(
            "base Codex agent must contain exactly one 900-second run default"
        )
    expected = payload.replace(OLD_IDLE, NEW_IDLE)
    _atomic_bytes(
        destination,
        expected,
        stat.S_IMODE(destination.stat(follow_symlinks=False).st_mode),
    )
    return {
        "path": CODEX_AGENT.as_posix(),
        "idle_timeout_s": 1800,
        "base_sha256": _sha256(base),
        "built_sha256": _sha256(destination),
    }


def _manifest(
    *,
    base: Path,
    output: Path,
    overlays: list[dict[str, str]],
    codex: dict[str, Any],
    relocation: dict[str, int],
) -> dict[str, Any]:
    return {
        "schema_version": SCHEMA_VERSION,
        "protocol": PROTOCOL,
        "base_runtime": {
            "root": str(base),
            "source_commit": EXPECTED_BASE_COMMIT,
        },
        "runtime": {"root": str(output)},
        "overlays": overlays,
        "codex_agent": codex,
        "prefix_relocation": {
            "old": str(base),
            "new": str(output),
            **relocation,
        },
    }


def _write_manifest(runtime: Path, value: dict[str, Any]) -> None:
    payload = (
        json.dumps(value, ensure_ascii=True, sort_keys=True, indent=2) + "\n"
    ).encode("utf-8")
    path = runtime / BUILD_MARKER
    if _lexists(path):
        raise RuntimeBuildError(f"build marker already exists: {path}")
    _atomic_bytes(path, payload, 0o444)


def _load_manifest(runtime: Path) -> dict[str, Any]:
    path = _plain_file(runtime / BUILD_MARKER, label="GPT runtime build marker")
    try:
        value = json.loads(path.read_text(encoding="utf-8"))
    except (UnicodeError, json.JSONDecodeError) as exc:
        raise RuntimeBuildError("GPT runtime build marker is invalid JSON") from exc
    if not isinstance(value, dict):
        raise RuntimeBuildError("GPT runtime build marker must be a JSON object")
    return value


def _expected_codex(base_installed: Path) -> tuple[bytes, dict[str, Any]]:
    base = _plain_file(base_installed / CODEX_AGENT, label="base Codex agent")
    payload = base.read_bytes()
    if payload.count(OLD_IDLE) != 1 or NEW_IDLE in payload:
        raise RuntimeBuildError("base Codex idle default no longer matches 900 seconds")
    built = payload.replace(OLD_IDLE, NEW_IDLE)
    return built, {
        "path": CODEX_AGENT.as_posix(),
        "idle_timeout_s": 1800,
        "base_sha256": hashlib.sha256(payload).hexdigest(),
        "built_sha256": hashlib.sha256(built).hexdigest(),
    }


def _base_relocation_counts(base: Path) -> dict[str, int]:
    needle = str(base).encode("utf-8")
    regular = [(path, path.read_bytes().count(needle)) for path in _prefix_regular_files(base)]
    links = [(path, os.readlink(path).count(str(base))) for path in _symlinks(base)]
    return {
        "regular_files_changed": sum(bool(count) for _path, count in regular),
        "regular_occurrences": sum(count for _path, count in regular),
        "symlinks_changed": sum(bool(count) for _path, count in links),
        "symlink_occurrences": sum(count for _path, count in links),
    }


def _seal_tree(runtime: Path, *, owner_uid: int, owner_gid: int) -> None:
    paths = list(runtime.rglob("*"))
    for path in paths:
        os.chown(path, owner_uid, owner_gid, follow_symlinks=False)
        if path.is_symlink():
            continue
        current = stat.S_IMODE(path.stat(follow_symlinks=False).st_mode)
        path.chmod(0o555 if path.is_dir() or current & 0o111 else 0o444)
    os.chown(runtime, owner_uid, owner_gid, follow_symlinks=False)
    runtime.chmod(0o555)


def _validate_seal(runtime: Path, *, owner_uid: int, owner_gid: int) -> None:
    for path in (runtime, *runtime.rglob("*")):
        metadata = path.lstat()
        if metadata.st_uid != owner_uid or metadata.st_gid != owner_gid:
            raise RuntimeBuildError(f"runtime entry has wrong owner: {path}")
        if not stat.S_ISLNK(metadata.st_mode) and stat.S_IMODE(metadata.st_mode) & 0o022:
            raise RuntimeBuildError(f"runtime entry is group/world writable: {path}")


def validate_runtime(
    *,
    base: Path = BASE_RUNTIME,
    runtime: Path = GPT_RUNTIME,
    repo: Path = REPO_ROOT,
    logical_root: Path | None = None,
    owner_uid: int = 0,
    owner_gid: int = 0,
    require_sealed: bool = True,
) -> dict[str, Any]:
    base = _plain_directory(base, label="base runtime")
    runtime = _plain_directory(runtime, label="GPT runtime")
    repo = _plain_directory(repo, label="source repository")
    logical = (logical_root or runtime).absolute()
    _base_commit(base)
    base_installed = _installed_archon(base)
    installed = _installed_archon(runtime)

    expected_overlays: list[dict[str, str]] = []
    for source_rel, destination_rel in OVERLAYS:
        source = _plain_file(repo / source_rel, label="runtime overlay source")
        destination = _plain_file(
            installed / destination_rel, label="installed runtime overlay"
        )
        digest = _sha256(source)
        if _sha256(destination) != digest:
            raise RuntimeBuildError(f"runtime overlay hash mismatch: {destination_rel}")
        expected_overlays.append(
            {
                "source": source_rel.as_posix(),
                "destination": destination_rel.as_posix(),
                "sha256": digest,
            }
        )

    expected_codex_payload, expected_codex = _expected_codex(base_installed)
    installed_codex = _plain_file(installed / CODEX_AGENT, label="installed Codex agent")
    if installed_codex.read_bytes() != expected_codex_payload:
        raise RuntimeBuildError(
            "installed Codex agent differs from the base by more than idle 900->1800"
        )
    if _sha256(installed / CLAUDE_AGENT) != _sha256(base_installed / CLAUDE_AGENT):
        raise RuntimeBuildError("installed Claude agent was unexpectedly replaced")

    old_bytes = str(base).encode("utf-8")
    for path in _prefix_regular_files(runtime):
        if old_bytes in path.read_bytes():
            raise RuntimeBuildError(f"old runtime prefix remains in {path}")
    for path in _symlinks(runtime):
        target = os.readlink(path)
        if str(base) in target:
            raise RuntimeBuildError(f"old runtime prefix remains in symlink {path}")
        if os.path.isabs(target) and not target.startswith(str(logical) + os.sep):
            raise RuntimeBuildError(f"absolute symlink escapes GPT runtime: {path}")

    relocation = _base_relocation_counts(base)
    expected_manifest = _manifest(
        base=base,
        output=logical,
        overlays=expected_overlays,
        codex=expected_codex,
        relocation=relocation,
    )
    if _load_manifest(runtime) != expected_manifest:
        raise RuntimeBuildError("GPT runtime build marker does not match installed content")
    if require_sealed:
        _validate_seal(runtime, owner_uid=owner_uid, owner_gid=owner_gid)
    return expected_manifest


def _cleanup_staging(path: Path) -> None:
    if not _lexists(path):
        return
    for entry in (path, *path.rglob("*")):
        if not entry.is_symlink():
            try:
                entry.chmod(stat.S_IMODE(entry.stat().st_mode) | 0o700)
            except OSError:
                pass
    shutil.rmtree(path)


def build_runtime(
    *,
    base: Path = BASE_RUNTIME,
    output: Path = GPT_RUNTIME,
    repo: Path = REPO_ROOT,
    owner_uid: int = 0,
    owner_gid: int = 0,
) -> dict[str, Any]:
    base = _plain_directory(base, label="base runtime")
    repo = _plain_directory(repo, label="source repository")
    output = output.absolute()
    parent = _plain_directory(output.parent, label="GPT runtime parent")
    if _lexists(output):
        raise RuntimeBuildError(f"GPT runtime output must not exist: {output}")
    _base_commit(base)
    base_installed = _installed_archon(base)
    staging = parent / f".{output.name}.staging-{uuid.uuid4().hex}"
    renamed = False
    try:
        shutil.copytree(base, staging, symlinks=True)
        installed = _installed_archon(staging)
        relocation = _replace_prefixes(staging, old=base, new=output)
        overlays = _overlay_rows(repo, installed)
        codex = _patch_codex(installed, base_installed)
        marker = _manifest(
            base=base,
            output=output,
            overlays=overlays,
            codex=codex,
            relocation=relocation,
        )
        _write_manifest(staging, marker)
        validate_runtime(
            base=base,
            runtime=staging,
            repo=repo,
            logical_root=output,
            owner_uid=owner_uid,
            owner_gid=owner_gid,
            require_sealed=False,
        )
        _seal_tree(staging, owner_uid=owner_uid, owner_gid=owner_gid)
        validate_runtime(
            base=base,
            runtime=staging,
            repo=repo,
            logical_root=output,
            owner_uid=owner_uid,
            owner_gid=owner_gid,
        )
        if _lexists(output):
            raise RuntimeBuildError(f"GPT runtime output appeared during build: {output}")
        staging.rename(output)
        renamed = True
        try:
            validate_runtime(
                base=base,
                runtime=output,
                repo=repo,
                owner_uid=owner_uid,
                owner_gid=owner_gid,
            )
        except BaseException:
            output.rename(staging)
            renamed = False
            raise
        return marker
    finally:
        if not renamed:
            _cleanup_staging(staging)


def _parser() -> argparse.ArgumentParser:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument(
        "--validate-only",
        action="store_true",
        help="validate the pinned GPT runtime without changing it",
    )
    return parser


def main(argv: Iterable[str] | None = None) -> int:
    parser = _parser()
    args = parser.parse_args(argv)
    if os.geteuid() != 0:
        parser.error("the pinned GPT runtime builder must run as root")
    try:
        marker = validate_runtime() if args.validate_only else build_runtime()
    except (RuntimeBuildError, OSError, shutil.Error) as exc:
        parser.error(str(exc))
    print(json.dumps(marker, ensure_ascii=True, sort_keys=True))
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
