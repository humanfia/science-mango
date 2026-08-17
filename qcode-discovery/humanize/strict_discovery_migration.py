"""Explicit, fail-closed successor migration for strict Stage 2 discovery.

The normal strict-discovery resume path deliberately rejects any change to the
ranked-snapshot manifest.  This module provides the only exception: a sealed
successor certificate that preserves the original portfolio, progress, and
completed batch artifacts byte-for-byte while moving future progress into a
new, content-addressed sidecar directory.

This module is process control and provenance plumbing only.  It intentionally
has no scientific imports at module import time.
"""

from __future__ import annotations

import hashlib
import json
import os
import stat
from dataclasses import replace
from pathlib import Path
from typing import Any, Iterable, Mapping


SUCCESSOR_SCHEMA_VERSION = 1
SUCCESSOR_GATE = "qldpc-stage2-strict-discovery-successor-migration-v1"
IDENTITY_REBASE_SCHEMA_VERSION = 1
IDENTITY_REBASE_GATE = "qldpc-stage2-ranked-snapshot-identity-rebase-v1"
REBASE_EQUIVALENCE_METHOD = "verified-patched-scheduler-migration-package-v1"
LINEAGE_SCHEMA_VERSION = 1
LINEAGE_GATE = "qldpc-stage2-strict-discovery-successor-lineage-v1"
LINEAGE_NAME = "successor-lineage.json"


class StrictDiscoveryMigrationError(RuntimeError):
    """A successor migration or its bound evidence failed validation."""


def _canonical_bytes(value: Any) -> bytes:
    return json.dumps(
        value,
        sort_keys=True,
        separators=(",", ":"),
        ensure_ascii=False,
        allow_nan=False,
    ).encode("utf-8")


def _sha256(value: Any) -> str:
    return hashlib.sha256(_canonical_bytes(value)).hexdigest()


def _is_sha256(value: Any) -> bool:
    return bool(
        isinstance(value, str)
        and len(value) == 64
        and all(character in "0123456789abcdef" for character in value)
    )


def _lexically_confined_path(
    raw: Path | str,
    *,
    run_root: Path,
    label: str,
) -> tuple[Path, Path, tuple[str, ...]]:
    """Normalize an in-run path without following descendant symlinks."""

    root = run_root.resolve(strict=True)
    value = Path(os.path.abspath(os.fspath(Path(raw).expanduser())))
    try:
        relative = value.relative_to(root)
    except ValueError as exc:
        raise StrictDiscoveryMigrationError(
            f"{label} escapes the pipeline run"
        ) from exc
    if not relative.parts:
        raise StrictDiscoveryMigrationError(
            f"{label} must name a file below the run root"
        )
    return root, value, relative.parts


def _open_confined_regular(
    raw: Path | str,
    *,
    run_root: Path,
    label: str,
) -> tuple[Path, int]:
    """Open one regular file through O_NOFOLLOW directory descriptors."""

    root, value, parts = _lexically_confined_path(
        raw,
        run_root=run_root,
        label=label,
    )
    directory_flags = os.O_RDONLY | getattr(os, "O_DIRECTORY", 0)
    nofollow = getattr(os, "O_NOFOLLOW", 0)
    descriptor = os.open(root, directory_flags | nofollow)
    try:
        for component in parts[:-1]:
            child = os.open(
                component,
                directory_flags | nofollow,
                dir_fd=descriptor,
            )
            if not stat.S_ISDIR(os.fstat(child).st_mode):
                os.close(child)
                raise StrictDiscoveryMigrationError(
                    f"{label} ancestor is not a directory"
                )
            os.close(descriptor)
            descriptor = child
        file_descriptor = os.open(
            parts[-1],
            os.O_RDONLY | nofollow,
            dir_fd=descriptor,
        )
    except (OSError, StrictDiscoveryMigrationError) as exc:
        if isinstance(exc, StrictDiscoveryMigrationError):
            raise
        raise StrictDiscoveryMigrationError(
            f"{label} must be a regular file with no symlink ancestors"
        ) from exc
    finally:
        os.close(descriptor)
    if not stat.S_ISREG(os.fstat(file_descriptor).st_mode):
        os.close(file_descriptor)
        raise StrictDiscoveryMigrationError(
            f"{label} must be a regular non-symlink file"
        )
    return value, file_descriptor


def _read_regular_bytes(
    path: Path | str,
    *,
    run_root: Path,
    label: str,
) -> tuple[bytes, dict[str, Any]]:
    confined, descriptor = _open_confined_regular(
        path,
        run_root=run_root,
        label=label,
    )
    try:
        before = os.fstat(descriptor)
        digest = hashlib.sha256()
        chunks: list[bytes] = []
        while chunk := os.read(descriptor, 1024 * 1024):
            digest.update(chunk)
            chunks.append(chunk)
        after = os.fstat(descriptor)
    finally:
        os.close(descriptor)
    stable_fields = (
        "st_dev",
        "st_ino",
        "st_size",
        "st_mtime_ns",
        "st_ctime_ns",
    )
    if any(getattr(before, name) != getattr(after, name) for name in stable_fields):
        raise StrictDiscoveryMigrationError(f"{label} changed while reading")
    return b"".join(chunks), {
        "path": str(confined),
        "sha256": digest.hexdigest(),
        "device": int(after.st_dev),
        "inode": int(after.st_ino),
        "bytes": int(after.st_size),
        "mtime_ns": int(after.st_mtime_ns),
        "ctime_ns": int(after.st_ctime_ns),
    }


def _read_regular_json(
    path: Path,
    *,
    run_root: Path,
    label: str,
) -> tuple[dict[str, Any], dict[str, Any]]:
    payload, identity = _read_regular_bytes(
        path,
        run_root=run_root,
        label=label,
    )
    try:
        value = json.loads(payload)
    except (UnicodeDecodeError, json.JSONDecodeError) as exc:
        raise StrictDiscoveryMigrationError(f"{label} is malformed JSON") from exc
    if not isinstance(value, dict):
        raise StrictDiscoveryMigrationError(f"{label} must contain an object")
    return value, identity


def _stable_file_identity(
    path: Path,
    *,
    run_root: Path,
    label: str,
) -> dict[str, Any]:
    confined, descriptor = _open_confined_regular(
        path, run_root=run_root, label=label
    )
    try:
        before = os.fstat(descriptor)
        digest = hashlib.sha256()
        while chunk := os.read(descriptor, 1024 * 1024):
            digest.update(chunk)
        after = os.fstat(descriptor)
    finally:
        os.close(descriptor)
    stable_fields = (
        "st_dev",
        "st_ino",
        "st_size",
        "st_mtime_ns",
        "st_ctime_ns",
    )
    if any(getattr(before, name) != getattr(after, name) for name in stable_fields):
        raise StrictDiscoveryMigrationError(f"{label} changed while hashing")
    return {
        "path": str(confined),
        "sha256": digest.hexdigest(),
        "device": int(after.st_dev),
        "inode": int(after.st_ino),
        "bytes": int(after.st_size),
        "mtime_ns": int(after.st_mtime_ns),
        "ctime_ns": int(after.st_ctime_ns),
    }


def _confined_regular_path(
    raw: Path | str,
    *,
    run_root: Path,
    label: str,
) -> Path:
    confined, descriptor = _open_confined_regular(
        raw,
        run_root=run_root,
        label=label,
    )
    os.close(descriptor)
    return confined


def _open_confined_directory(
    raw: Path | str,
    *,
    run_root: Path,
    label: str,
    create: bool = False,
) -> tuple[Path, int]:
    root, value, parts = _lexically_confined_path(
        raw, run_root=run_root, label=label
    )
    flags = os.O_RDONLY | getattr(os, "O_DIRECTORY", 0)
    nofollow = getattr(os, "O_NOFOLLOW", 0)
    descriptor = os.open(root, flags | nofollow)
    try:
        for component in parts:
            try:
                child = os.open(
                    component, flags | nofollow, dir_fd=descriptor
                )
            except FileNotFoundError:
                if not create:
                    raise
                os.mkdir(component, mode=0o700, dir_fd=descriptor)
                child = os.open(
                    component, flags | nofollow, dir_fd=descriptor
                )
            if not stat.S_ISDIR(os.fstat(child).st_mode):
                os.close(child)
                raise StrictDiscoveryMigrationError(
                    f"{label} contains a non-directory ancestor"
                )
            os.close(descriptor)
            descriptor = child
    except (OSError, StrictDiscoveryMigrationError) as exc:
        os.close(descriptor)
        if isinstance(exc, StrictDiscoveryMigrationError):
            raise
        raise StrictDiscoveryMigrationError(
            f"{label} must have no symlink ancestors"
        ) from exc
    return value, descriptor


def _write_new_json(
    path: Path,
    value: Mapping[str, Any],
    *,
    run_root: Path,
    label: str,
) -> None:
    """Publish a complete JSON file without replacing any existing path."""

    parent, descriptor = _open_confined_directory(
        path.parent,
        run_root=run_root,
        label=f"{label} directory",
        create=True,
    )
    if parent / path.name != Path(os.path.abspath(path)):
        os.close(descriptor)
        raise StrictDiscoveryMigrationError(f"{label} path is not canonical")
    temporary = (
        f".{path.name}.{os.getpid()}.{os.urandom(16).hex()}.tmp"
    )
    payload = _canonical_bytes(dict(value)) + b"\n"
    file_descriptor = -1
    try:
        file_descriptor = os.open(
            temporary,
            os.O_WRONLY | os.O_CREAT | os.O_EXCL | getattr(os, "O_NOFOLLOW", 0),
            0o600,
            dir_fd=descriptor,
        )
        written = 0
        while written < len(payload):
            written += os.write(file_descriptor, payload[written:])
        os.fsync(file_descriptor)
        os.close(file_descriptor)
        file_descriptor = -1
        os.link(
            temporary,
            path.name,
            src_dir_fd=descriptor,
            dst_dir_fd=descriptor,
            follow_symlinks=False,
        )
        os.fsync(descriptor)
    except FileExistsError as exc:
        raise StrictDiscoveryMigrationError(
            f"{label} already exists; refusing to overwrite it"
        ) from exc
    finally:
        if file_descriptor >= 0:
            os.close(file_descriptor)
        try:
            os.unlink(temporary, dir_fd=descriptor)
        except FileNotFoundError:
            pass
        os.close(descriptor)


def _publish_or_verify_json(
    path: Path,
    value: Mapping[str, Any],
    *,
    run_root: Path,
    label: str,
) -> None:
    expected = _canonical_bytes(dict(value)) + b"\n"
    if _lexists(path):
        observed, _ = _read_regular_bytes(
            path, run_root=run_root, label=label
        )
        if observed != expected:
            raise StrictDiscoveryMigrationError(
                f"existing {label} differs from deterministic recovery"
            )
        return
    _write_new_json(path, value, run_root=run_root, label=label)


def _lexists(path: Path) -> bool:
    try:
        path.lstat()
    except FileNotFoundError:
        return False
    return True


def successor_lineage_path(paths: Any) -> Path:
    return paths.root / LINEAGE_NAME


def _successor_root_names(paths: Any, *, create: bool = False) -> list[str]:
    roots_path = paths.root / "successors"
    if not _lexists(roots_path):
        if not create:
            return []
    _, descriptor = _open_confined_directory(
        roots_path,
        run_root=paths.run_root,
        label="strict successor roots",
        create=create,
    )
    try:
        return sorted(os.listdir(descriptor))
    finally:
        os.close(descriptor)


def _recovery_temp_target(name: str) -> str | None:
    for target in ("migration.json", "progress.json"):
        prefix = f".{target}."
        suffix = ".tmp"
        if not name.startswith(prefix) or not name.endswith(suffix):
            continue
        middle = name[len(prefix) : -len(suffix)]
        pieces = middle.split(".")
        if (
            len(pieces) == 2
            and pieces[0].isdecimal()
            and int(pieces[0]) > 0
            and len(pieces[1]) == 32
            and all(character in "0123456789abcdef" for character in pieces[1])
        ):
            return target
    return None


def _validate_successor_root_set(paths: Any, expected: str) -> None:
    roots = _successor_root_names(paths, create=False)
    if roots and roots != [expected]:
        raise StrictDiscoveryMigrationError(
            "strict successor roots contain a fork or nondeterministic orphan"
        )
    if roots:
        expected_root = paths.root / "successors" / expected
        _, descriptor = _open_confined_directory(
            expected_root,
            run_root=paths.run_root,
            label="incomplete strict successor root",
        )
        unsafe: set[str] = set()
        try:
            entries = set(os.listdir(descriptor))
            for name in entries.difference({"migration.json", "progress.json"}):
                target = _recovery_temp_target(name)
                try:
                    metadata = os.stat(
                        name, dir_fd=descriptor, follow_symlinks=False,
                    )
                except OSError:
                    unsafe.add(name)
                    continue
                if (
                    target is None
                    or not stat.S_ISREG(metadata.st_mode)
                    or metadata.st_nlink not in {1, 2}
                ):
                    unsafe.add(name)
                    continue
                if metadata.st_nlink == 2:
                    try:
                        published = os.stat(
                            target, dir_fd=descriptor, follow_symlinks=False,
                        )
                    except OSError:
                        unsafe.add(name)
                        continue
                    if (
                        not stat.S_ISREG(published.st_mode)
                        or (published.st_dev, published.st_ino)
                        != (metadata.st_dev, metadata.st_ino)
                    ):
                        unsafe.add(name)
        finally:
            os.close(descriptor)
        if unsafe:
            raise StrictDiscoveryMigrationError(
                "incomplete strict successor root contains unexpected artifacts"
            )


def load_successor_lineage(
    paths: Any,
    *,
    required: bool = False,
    allow_incomplete: bool = False,
) -> dict[str, Any] | None:
    marker_path = successor_lineage_path(paths)
    if not _lexists(marker_path):
        roots = _successor_root_names(paths, create=False)
        if roots and not allow_incomplete:
            raise StrictDiscoveryMigrationError(
                "strict successor lineage is absent but successor artifacts exist"
            )
        if required:
            raise StrictDiscoveryMigrationError("strict successor lineage is absent")
        return None
    marker, _ = _read_regular_json(
        marker_path,
        run_root=paths.run_root,
        label="strict successor lineage",
    )
    unsigned = dict(marker)
    seal = unsigned.pop("lineage_sha256", None)
    migration_sha256 = marker.get("migration_sha256")
    expected_root = paths.root / "successors" / str(migration_sha256)
    if (
        marker.get("schema_version") != LINEAGE_SCHEMA_VERSION
        or marker.get("gate") != LINEAGE_GATE
        or not _is_sha256(seal)
        or seal != _sha256(unsigned)
        or not _is_sha256(migration_sha256)
        or marker.get("certificate") != str(expected_root / "migration.json")
        or marker.get("progress") != str(expected_root / "progress.json")
        or not _is_sha256(marker.get("predecessor_progress_sha256"))
        or not isinstance(marker.get("portfolio_manifest"), str)
        or not _is_sha256(marker.get("portfolio_manifest_file_sha256"))
        or _successor_root_names(paths, create=False) != [migration_sha256]
    ):
        raise StrictDiscoveryMigrationError(
            "strict successor lineage seal/schema/path/root set is invalid"
        )
    _confined_regular_path(
        str(marker["certificate"]),
        run_root=paths.run_root,
        label="strict successor certificate",
    )
    _confined_regular_path(
        str(marker["progress"]),
        run_root=paths.run_root,
        label="strict successor progress",
    )
    return marker


def _derived_snapshot_paths(manifest_path: Path) -> tuple[Path, Path]:
    suffix = ".manifest.json"
    if not manifest_path.name.endswith(suffix):
        raise StrictDiscoveryMigrationError(
            "successor snapshot manifest name is not canonical"
        )
    stem = manifest_path.name[: -len(suffix)]
    return (
        manifest_path.with_name(f"{stem}.jsonl"),
        manifest_path.with_name(f"{stem}.offsets"),
    )


def _validated_chunk_index(
    manifest: Mapping[str, Any],
    identity: Mapping[str, Any],
    *,
    rows: int,
    snapshot_bytes: int,
    offsets_bytes: int,
) -> list[dict[str, Any]]:
    chunks = manifest.get("chunks")
    chunk_rows = identity.get("chunk_rows")
    if (
        isinstance(chunk_rows, bool)
        or not isinstance(chunk_rows, int)
        or chunk_rows <= 0
        or manifest.get("chunk_rows") != chunk_rows
        or not isinstance(chunks, list)
        or len(chunks) != ((rows + chunk_rows - 1) // chunk_rows if rows else 0)
        or _sha256([dict(item) if isinstance(item, Mapping) else item for item in chunks])
        != identity.get("chunk_index_sha256")
    ):
        raise StrictDiscoveryMigrationError("ranked snapshot chunk index is invalid")
    normalized: list[dict[str, Any]] = []
    previous_snapshot_end = 0
    for number, raw in enumerate(chunks):
        if not isinstance(raw, Mapping):
            raise StrictDiscoveryMigrationError("ranked snapshot chunk is malformed")
        chunk = dict(raw)
        start = number * chunk_rows
        end = min(start + chunk_rows, rows)
        integers = tuple(
            chunk.get(name)
            for name in (
                "start_row",
                "end_row",
                "snapshot_start",
                "snapshot_end",
                "offsets_start",
                "offsets_end",
            )
        )
        if (
            any(isinstance(value, bool) or not isinstance(value, int) for value in integers)
            or chunk.get("start_row") != start
            or chunk.get("end_row") != end
            or chunk.get("snapshot_start") != previous_snapshot_end
            or not chunk["snapshot_start"] < chunk["snapshot_end"] <= snapshot_bytes
            or chunk.get("offsets_start") != start * 8
            or chunk.get("offsets_end") != (end + 1) * 8
            or chunk["offsets_end"] > offsets_bytes
            or not _is_sha256(chunk.get("snapshot_sha256"))
            or not _is_sha256(chunk.get("offsets_sha256"))
        ):
            raise StrictDiscoveryMigrationError("ranked snapshot chunk is malformed")
        previous_snapshot_end = int(chunk["snapshot_end"])
        normalized.append(chunk)
    if previous_snapshot_end != snapshot_bytes:
        raise StrictDiscoveryMigrationError("ranked snapshot chunk index is incomplete")
    return normalized


def _range_sha256(descriptor: int, start: int, end: int) -> str:
    digest = hashlib.sha256()
    position = start
    while position < end:
        payload = os.pread(descriptor, min(1024 * 1024, end - position), position)
        if not payload:
            raise StrictDiscoveryMigrationError(
                "ranked snapshot chunk ended before its sealed boundary"
            )
        digest.update(payload)
        position += len(payload)
    return digest.hexdigest()


def _validate_chunk_bytes(
    chunks: Iterable[Mapping[str, Any]],
    *,
    snapshot_path: Path,
    offsets_path: Path,
    run_root: Path,
    snapshot_identity: Mapping[str, Any],
    offsets_identity: Mapping[str, Any],
) -> None:
    _, snapshot_descriptor = _open_confined_regular(
        snapshot_path, run_root=run_root, label="successor snapshot chunks"
    )
    _, offsets_descriptor = _open_confined_regular(
        offsets_path, run_root=run_root, label="successor offset chunks"
    )
    try:
        snapshot_before = os.fstat(snapshot_descriptor)
        offsets_before = os.fstat(offsets_descriptor)
        for chunk in chunks:
            if (
                _range_sha256(
                    snapshot_descriptor,
                    int(chunk["snapshot_start"]),
                    int(chunk["snapshot_end"]),
                )
                != chunk["snapshot_sha256"]
                or _range_sha256(
                    offsets_descriptor,
                    int(chunk["offsets_start"]),
                    int(chunk["offsets_end"]),
                )
                != chunk["offsets_sha256"]
            ):
                raise StrictDiscoveryMigrationError(
                    "ranked snapshot chunk bytes disagree with the chunk index"
                )
        snapshot_after = os.fstat(snapshot_descriptor)
        offsets_after = os.fstat(offsets_descriptor)
    finally:
        os.close(snapshot_descriptor)
        os.close(offsets_descriptor)
    fields = (
        ("device", "st_dev"),
        ("inode", "st_ino"),
        ("bytes", "st_size"),
        ("mtime_ns", "st_mtime_ns"),
        ("ctime_ns", "st_ctime_ns"),
    )
    if any(
        snapshot_identity[name] != getattr(snapshot_before, stat_name)
        or snapshot_identity[name] != getattr(snapshot_after, stat_name)
        for name, stat_name in fields
    ) or any(
        offsets_identity[name] != getattr(offsets_before, stat_name)
        or offsets_identity[name] != getattr(offsets_after, stat_name)
        for name, stat_name in fields
    ):
        raise StrictDiscoveryMigrationError(
            "ranked snapshot changed while validating chunk bytes"
        )


def _validate_snapshot_manifest(
    manifest_path: Path,
    *,
    run_root: Path,
    label: str,
    require_manifest_stat: bool = True,
) -> dict[str, Any]:
    path = _confined_regular_path(
        manifest_path,
        run_root=run_root,
        label=f"{label} manifest",
    )
    manifest, manifest_file = _read_regular_json(
        path,
        run_root=run_root,
        label=f"{label} manifest",
    )
    unsigned = dict(manifest)
    manifest_sha256 = unsigned.pop("manifest_sha256", None)
    binding = manifest.get("binding")
    identity = manifest.get("identity")
    counts = manifest.get("counts")
    if isinstance(binding, Mapping):
        unsigned_binding = dict(binding)
        binding_sha256 = unsigned_binding.pop("binding_sha256", None)
    else:
        unsigned_binding = {}
        binding_sha256 = None
    rows = manifest.get("snapshot_rows")
    eligible_rows = (
        counts.get("eligible_candidates") if isinstance(counts, Mapping) else None
    )
    identity_hash_fields = (
        "binding_sha256",
        "snapshot_sha256",
        "offsets_sha256",
        "chunk_index_sha256",
        "counts_sha256",
    )
    if (
        manifest.get("schema_version") != 1
        or manifest.get("gate") != "qldpc-stage2-ranked-snapshot"
        or not _is_sha256(manifest_sha256)
        or manifest_sha256 != _sha256(unsigned)
        or not isinstance(binding, Mapping)
        or not _is_sha256(binding_sha256)
        or binding_sha256 != _sha256(unsigned_binding)
        or manifest.get("binding_sha256") != binding_sha256
        or not isinstance(identity, Mapping)
        or any(not _is_sha256(identity.get(name)) for name in identity_hash_fields)
        or identity.get("binding_sha256") != binding_sha256
        or not isinstance(counts, Mapping)
        or identity.get("counts_sha256") != _sha256(dict(counts))
        or isinstance(rows, bool)
        or not isinstance(rows, int)
        or rows < 0
        or isinstance(eligible_rows, bool)
        or not isinstance(eligible_rows, int)
        or not 0 <= eligible_rows <= rows
        or identity.get("rows") != rows
        or identity.get("eligible_rows") != eligible_rows
    ):
        raise StrictDiscoveryMigrationError(
            f"{label} ranked-snapshot manifest seal/schema is invalid"
        )
    snapshot_path, offsets_path = _derived_snapshot_paths(path)
    snapshot_path = _confined_regular_path(
        snapshot_path,
        run_root=run_root,
        label=f"{label} snapshot",
    )
    offsets_path = _confined_regular_path(
        offsets_path,
        run_root=run_root,
        label=f"{label} offsets",
    )
    snapshot = _stable_file_identity(
        snapshot_path, run_root=run_root, label=f"{label} snapshot"
    )
    offsets = _stable_file_identity(
        offsets_path, run_root=run_root, label=f"{label} offsets"
    )
    snapshot_stat = manifest.get("snapshot_stat")
    offsets_stat = manifest.get("offsets_stat")
    stat_fields = ("device", "inode", "bytes", "mtime_ns")
    if (
        snapshot["sha256"] != identity.get("snapshot_sha256")
        or offsets["sha256"] != identity.get("offsets_sha256")
        or offsets["bytes"] != (rows + 1) * 8
        or not isinstance(snapshot_stat, Mapping)
        or not isinstance(offsets_stat, Mapping)
        or (
            require_manifest_stat
            and any(snapshot_stat.get(name) != snapshot[name] for name in stat_fields)
        )
        or (
            require_manifest_stat
            and any(offsets_stat.get(name) != offsets[name] for name in stat_fields)
        )
    ):
        raise StrictDiscoveryMigrationError(
            f"{label} snapshot bytes disagree with its manifest identity"
        )
    chunks = _validated_chunk_index(
        manifest,
        identity,
        rows=rows,
        snapshot_bytes=int(snapshot["bytes"]),
        offsets_bytes=int(offsets["bytes"]),
    )
    if require_manifest_stat:
        _validate_chunk_bytes(
            chunks,
            snapshot_path=snapshot_path,
            offsets_path=offsets_path,
            run_root=run_root,
            snapshot_identity=snapshot,
            offsets_identity=offsets,
        )
    return {
        "manifest": {
            "path": str(path),
            "file_sha256": manifest_file["sha256"],
            "manifest_sha256": manifest_sha256,
        },
        "binding_sha256": binding_sha256,
        "identity": dict(identity),
        "snapshot_identity_sha256": _sha256(dict(identity)),
        "snapshot_rows": rows,
        "eligible_rows": eligible_rows,
        "counts": dict(counts),
        "chunks": chunks,
        "snapshot": snapshot,
        "offsets": offsets,
    }


def _compare_rowwise(
    old_snapshot: Path,
    new_snapshot: Path,
    *,
    run_root: Path,
    expected_rows: int,
) -> int:
    rows = 0
    _, old_descriptor = _open_confined_regular(
        old_snapshot, run_root=run_root, label="predecessor snapshot"
    )
    _, new_descriptor = _open_confined_regular(
        new_snapshot, run_root=run_root, label="successor snapshot"
    )
    with os.fdopen(old_descriptor, "rb") as old_stream, os.fdopen(
        new_descriptor, "rb"
    ) as new_stream:
        while True:
            old_row = old_stream.readline()
            new_row = new_stream.readline()
            if old_row != new_row:
                raise StrictDiscoveryMigrationError(
                    f"successor snapshot row {rows} differs from the sealed predecessor"
                )
            if not old_row:
                break
            if not old_row.endswith(b"\n"):
                raise StrictDiscoveryMigrationError(
                    "predecessor snapshot contains a partial JSONL row"
                )
            rows += 1
    if rows != expected_rows:
        raise StrictDiscoveryMigrationError(
            "rowwise successor comparison disagrees with snapshot row count"
        )
    return rows


def _compare_files(
    left: Path,
    right: Path,
    *,
    run_root: Path,
    label: str,
) -> None:
    _, left_descriptor = _open_confined_regular(
        left, run_root=run_root, label=f"predecessor {label}"
    )
    _, right_descriptor = _open_confined_regular(
        right, run_root=run_root, label=f"successor {label}"
    )
    with os.fdopen(left_descriptor, "rb") as left_stream, os.fdopen(
        right_descriptor, "rb"
    ) as right_stream:
        while True:
            left_chunk = left_stream.read(1024 * 1024)
            right_chunk = right_stream.read(1024 * 1024)
            if left_chunk != right_chunk:
                raise StrictDiscoveryMigrationError(
                    f"successor {label} bytes differ from the sealed predecessor"
                )
            if not left_chunk:
                return


def _portfolio_items_sha256(portfolio: Mapping[str, Any]) -> str:
    items = portfolio.get("items")
    if not isinstance(items, list):
        raise StrictDiscoveryMigrationError("portfolio item list is absent")
    normalized: list[dict[str, Any]] = []
    for item in items:
        if not isinstance(item, Mapping):
            raise StrictDiscoveryMigrationError("portfolio item is malformed")
        normalized.append({
            "portfolio_rank": item.get("portfolio_rank"),
            "snapshot_index": item.get("snapshot_index"),
            "canonical_digest": item.get("canonical_digest"),
        })
    return _sha256(normalized)


def _stable_external_sha256(path: Path, *, label: str) -> str:
    value = Path(os.path.abspath(path))
    _, descriptor = _open_confined_regular(
        value,
        run_root=Path(value.anchor),
        label=label,
    )
    try:
        before = os.fstat(descriptor)
        if not stat.S_ISREG(before.st_mode):
            raise StrictDiscoveryMigrationError(f"{label} is not a regular file")
        digest = hashlib.sha256()
        while chunk := os.read(descriptor, 1024 * 1024):
            digest.update(chunk)
        after = os.fstat(descriptor)
    finally:
        os.close(descriptor)
    if (
        before.st_dev,
        before.st_ino,
        before.st_size,
        before.st_mtime_ns,
        before.st_ctime_ns,
    ) != (
        after.st_dev,
        after.st_ino,
        after.st_size,
        after.st_mtime_ns,
        after.st_ctime_ns,
    ):
        raise StrictDiscoveryMigrationError(f"{label} changed while hashing")
    return digest.hexdigest()


def _validated_immutable_install_entries(
    entries: Any,
    *,
    solver_state: Path,
    live_ledger_path: Path,
    run_root: Path,
) -> list[dict[str, Any]]:
    """Rehash every installed package target except the live mutable ledger."""

    if not isinstance(entries, list) or not entries:
        raise StrictDiscoveryMigrationError(
            "COMMITTED receipt installed-file inventory is absent"
        )
    try:
        ledger_relative = live_ledger_path.relative_to(solver_state)
    except ValueError as exc:
        raise StrictDiscoveryMigrationError(
            "installed successor ledger escapes solver-state"
        ) from exc
    normalized: list[dict[str, Any]] = []
    seen: set[str] = set()
    ledger_entries = 0
    for raw in entries:
        if not isinstance(raw, Mapping):
            raise StrictDiscoveryMigrationError(
                "COMMITTED receipt installed-file entry is malformed"
            )
        entry = dict(raw)
        relative_text = entry.get("path")
        relative = Path(relative_text) if isinstance(relative_text, str) else None
        source_token = entry.get("source_token")
        size = entry.get("bytes")
        if (
            relative is None
            or relative.is_absolute()
            or not relative.parts
            or any(part in {"", ".", ".."} for part in relative.parts)
            or str(relative) != relative_text
            or relative_text in seen
            or not _is_sha256(entry.get("sha256"))
            or isinstance(size, bool)
            or not isinstance(size, int)
            or size < 0
            or not isinstance(source_token, list)
            or len(source_token) != 7
            or any(isinstance(value, bool) or not isinstance(value, int) for value in source_token)
        ):
            raise StrictDiscoveryMigrationError(
                "COMMITTED receipt installed-file entry is malformed"
            )
        seen.add(relative_text)
        if relative == ledger_relative:
            ledger_entries += 1
        else:
            identity = _stable_file_identity(
                solver_state / relative,
                run_root=run_root,
                label=f"immutable installed migration artifact {relative_text}",
            )
            if (
                identity["sha256"] != entry["sha256"]
                or identity["bytes"] != size
            ):
                raise StrictDiscoveryMigrationError(
                    "immutable installed migration artifact changed after COMMITTED install"
                )
        normalized.append(entry)
    if ledger_entries != 1:
        raise StrictDiscoveryMigrationError(
            "COMMITTED receipt must contain exactly one mutable live ledger"
        )
    return normalized


def _validate_identity_rebase(
    path: Path,
    *,
    run_root: Path,
    live_ledger_path: Path,
    portfolio: Mapping[str, Any],
    ranked_input: Mapping[str, Any],
    old_identity: Mapping[str, Any],
    old_identity_sha256: str,
    new_snapshot: Mapping[str, Any],
    require_live_install_exact: bool,
) -> dict[str, Any]:
    """Bind a trusted package to an immutable receipt and installed baseline."""

    certificate_path = _confined_regular_path(
        path,
        run_root=run_root,
        label="patched scheduler migration certificate",
    )
    if certificate_path.name != "scheduler-migration-certificate.json":
        raise StrictDiscoveryMigrationError(
            "identity rebase must be the main recovery scheduler certificate"
        )
    package_root = certificate_path.parent
    live_ledger_path = _confined_regular_path(
        live_ledger_path,
        run_root=run_root,
        label="installed successor Stage 2 ledger",
    )
    solver_state = live_ledger_path.parent
    try:
        from . import stage2_ledger_recovery as recovery

        normalized = recovery.validate_patched_scheduler_migration(
            package_root, same_filesystem_as=solver_state
        )
    except Exception as exc:
        raise StrictDiscoveryMigrationError(
            "patched scheduler migration is not a validated main recovery package"
        ) from exc
    if not isinstance(normalized, Mapping):
        raise StrictDiscoveryMigrationError(
            "patched scheduler migration validator returned malformed evidence"
        )
    reported_install: Mapping[str, Any] | None = None
    if require_live_install_exact:
        try:
            reported_install = recovery.validate_patched_scheduler_install(
                package_root, solver_state=solver_state
            )
        except Exception as exc:
            raise StrictDiscoveryMigrationError(
                "patched scheduler migration is not a validated COMMITTED live install"
            ) from exc

    recovery_source = Path(os.path.abspath(recovery.__file__))
    recovery_source_sha256 = _stable_external_sha256(
        recovery_source, label="Stage 2 recovery validator source"
    )
    marker_path = solver_state / recovery.INSTALL_COMMIT_NAME
    journal_path = solver_state / recovery.INSTALL_JOURNAL_NAME
    marker, marker_identity = _read_regular_json(
        marker_path,
        run_root=run_root,
        label="scheduler migration COMMITTED marker",
    )
    journal, journal_identity = _read_regular_json(
        journal_path,
        run_root=run_root,
        label="scheduler migration install journal",
    )
    marker_unsigned = dict(marker)
    marker_seal = marker_unsigned.pop("commit_sha256", None)
    journal_unsigned = dict(journal)
    journal_seal = journal_unsigned.pop("journal_sha256", None)
    if (
        not _is_sha256(marker_seal)
        or marker_seal != recovery.canonical_sha256(marker_unsigned)
        or not _is_sha256(journal_seal)
        or journal_seal != recovery.canonical_sha256(journal_unsigned)
    ):
        raise StrictDiscoveryMigrationError(
            "scheduler migration COMMITTED receipt seal is invalid"
        )
    committed = {
        **marker,
        "marker_path": str(marker_path),
        "journal_path": str(journal_path),
        "production_files_modified": True,
    }
    if reported_install is not None and dict(reported_install) != committed:
        raise StrictDiscoveryMigrationError(
            "COMMITTED receipt changed around public live validation"
        )

    new_identity = new_snapshot["identity"]
    content_fields = (
        "snapshot_sha256",
        "offsets_sha256",
        "chunk_index_sha256",
        "counts_sha256",
        "chunk_rows",
        "rows",
        "eligible_rows",
    )
    compiled_old = {
        "snapshot_sha256": recovery.EXPECTED["snapshot_sha256"],
        "offsets_sha256": recovery.OLD_OFFSETS_SHA256,
        "chunk_index_sha256": recovery.OLD_CHUNK_INDEX_SHA256,
        "counts_sha256": recovery.OLD_COUNTS_SHA256,
        "chunk_rows": recovery.RANKED_CHUNK_ROWS,
        "rows": recovery.EXPECTED["snapshot_rows"],
        "eligible_rows": recovery.EXPECTED["eligible_rows"],
    }
    live = committed.get("live")
    expected_live_paths = {
        "ledger_path": str(live_ledger_path),
        "manifest_path": str(new_snapshot["manifest"]["path"]),
        "snapshot_path": str(new_snapshot["snapshot"]["path"]),
        "offsets_path": str(new_snapshot["offsets"]["path"]),
    }
    expected_live_hashes = {
        "manifest_file_sha256": new_snapshot["manifest"]["file_sha256"],
        "snapshot_file_sha256": new_snapshot["snapshot"]["sha256"],
        "offsets_file_sha256": new_snapshot["offsets"]["sha256"],
        "binding_sha256": new_snapshot["binding_sha256"],
        "snapshot_identity_sha256": new_snapshot[
            "snapshot_identity_sha256"
        ],
        "manifest_content_sha256": new_snapshot["manifest"][
            "manifest_sha256"
        ],
        "snapshot_content_sha256": new_identity["snapshot_sha256"],
        "offsets_content_sha256": new_identity["offsets_sha256"],
        "progress_sha256": normalized.get(
            "active_ledger_progress_sha256"
        ),
        "ledger_content_sha256": normalized.get(
            "active_ledger_progress_sha256"
        ),
        "last_ack_sha256": normalized.get("active_last_ack_sha256"),
        "pending_page_sha256": normalized.get(
            "active_pending_page_sha256"
        ),
        "validator_source_sha256": recovery_source_sha256,
    }
    if (
        normalized.get("production_files_modified") is not False
        or normalized.get("validator_source_sha256") != recovery_source_sha256
        or normalized.get("binding_sha256") != new_snapshot["binding_sha256"]
        or normalized.get("snapshot_identity_sha256")
        != new_snapshot["snapshot_identity_sha256"]
        or old_identity_sha256
        != recovery.EXPECTED["snapshot_identity_sha256"]
        or any(old_identity.get(name) != value for name, value in compiled_old.items())
        or any(new_identity.get(name) != old_identity.get(name) for name in content_fields)
        or ranked_input.get("rows") != len(portfolio.get("items", []))
        or not _is_sha256(normalized.get("certificate_sha256"))
        or not _is_sha256(normalized.get("package_sha256"))
        or not _is_sha256(normalized.get("active_ledger_progress_sha256"))
        or not _is_sha256(normalized.get("active_last_ack_sha256"))
        or not _is_sha256(normalized.get("active_pending_page_sha256"))
        or not _is_sha256(normalized.get("terminal_report_sha256"))
        or committed.get("schema_version") != 1
        or committed.get("gate") != recovery.INSTALL_COMMIT_GATE
        or committed.get("state") != "COMMITTED"
        or committed.get("production_files_modified") is not True
        or committed.get("package_root") != str(package_root)
        or committed.get("solver_state") != str(solver_state)
        or committed.get("certificate_sha256")
        != normalized.get("certificate_sha256")
        or committed.get("package_sha256") != normalized.get("package_sha256")
        or committed.get("validator_source_sha256") != recovery_source_sha256
        or committed.get("marker_path") != str(marker_path)
        or committed.get("journal_path") != str(journal_path)
        or not _is_sha256(committed.get("commit_sha256"))
        or not isinstance(committed.get("committed_at"), str)
        or not committed.get("committed_at")
        or not isinstance(committed.get("installed_files"), list)
        or not isinstance(live, Mapping)
        or any(live.get(name) != value for name, value in expected_live_paths.items())
        or any(live.get(name) != value for name, value in expected_live_hashes.items())
        or not _is_sha256(live.get("ledger_file_sha256"))
        or not _is_sha256(live.get("scheduler_state_sha256"))
        or journal.get("schema_version") != 1
        or journal.get("gate") != recovery.INSTALL_JOURNAL_GATE
        or journal.get("state") != "COMMITTED"
        or journal.get("package_root") != str(package_root)
        or journal.get("solver_state") != str(solver_state)
        or journal.get("certificate_sha256")
        != normalized.get("certificate_sha256")
        or journal.get("package_sha256") != normalized.get("package_sha256")
        or journal.get("validator_source_sha256") != recovery_source_sha256
        or journal.get("install_files") != committed.get("installed_files")
        or journal.get("commit_sha256") != committed.get("commit_sha256")
        or journal.get("committed_at") != committed.get("committed_at")
    ):
        raise StrictDiscoveryMigrationError(
            "COMMITTED receipt does not bind the requested old/new identity"
        )
    installed_files = _validated_immutable_install_entries(
        committed["installed_files"],
        solver_state=solver_state,
        live_ledger_path=live_ledger_path,
        run_root=run_root,
    )
    certificate_identity = _stable_file_identity(
        certificate_path,
        run_root=run_root,
        label="patched scheduler migration certificate",
    )
    return {
        "path": str(certificate_path),
        "file_sha256": certificate_identity["sha256"],
        "package_root": str(package_root),
        "certificate_sha256": normalized["certificate_sha256"],
        "package_sha256": normalized["package_sha256"],
        "binding_sha256": normalized["binding_sha256"],
        "snapshot_identity_sha256": normalized["snapshot_identity_sha256"],
        "active_ledger_progress_sha256": normalized[
            "active_ledger_progress_sha256"
        ],
        "active_last_ack_sha256": normalized["active_last_ack_sha256"],
        "active_pending_page_sha256": normalized[
            "active_pending_page_sha256"
        ],
        "terminal_report_sha256": normalized["terminal_report_sha256"],
        "portfolio_items_sha256": _portfolio_items_sha256(portfolio),
        "install": {
            "state": "COMMITTED",
            "solver_state": str(solver_state),
            "commit_sha256": committed["commit_sha256"],
            "committed_at": committed["committed_at"],
            "marker": marker_identity,
            "journal": journal_identity,
            "installed_files": installed_files,
            "live": dict(live),
        },
        "validator": {
            "module": "humanize.stage2_ledger_recovery",
            "path": str(recovery_source),
            "source_sha256": recovery_source_sha256,
            "package_entrypoint": "validate_patched_scheduler_migration",
            "install_entrypoint": "validate_patched_scheduler_install",
        },
    }


def _json_object_from_payload(payload: bytes, *, label: str) -> dict[str, Any]:
    try:
        value = json.loads(payload)
    except (UnicodeDecodeError, json.JSONDecodeError) as exc:
        raise StrictDiscoveryMigrationError(f"{label} is malformed JSON") from exc
    if not isinstance(value, dict):
        raise StrictDiscoveryMigrationError(f"{label} must contain an object")
    return value


def _ranked_batch_semantics(
    payload: bytes,
    summary: Mapping[str, Any],
    *,
    expected_rows: int,
) -> tuple[
    list[dict[str, Any]],
    dict[str, int],
    bool,
    bool,
    list[str],
]:
    selected_rows = 0
    output_rows = 0
    status_counts: dict[str, int] = {}
    audited_digests: list[str] = []
    wins: list[dict[str, Any]] = []
    for line_number, raw in enumerate(payload.splitlines(keepends=True), start=1):
        if not raw.endswith(b"\n"):
            raise StrictDiscoveryMigrationError(
                f"ranked batch row {line_number} is partial"
            )
        try:
            row = json.loads(raw)
        except (UnicodeDecodeError, json.JSONDecodeError) as exc:
            raise StrictDiscoveryMigrationError(
                f"ranked batch row {line_number} is malformed"
            ) from exc
        if (
            not isinstance(row, Mapping)
            or row.get("campaign_selected") is not True
        ):
            raise StrictDiscoveryMigrationError(
                f"ranked batch row {line_number} is not an audited selection"
            )
        output_rows += 1
        selected_rows += 1
        audit = row.get("campaign_audit")
        if not isinstance(audit, Mapping):
            raise StrictDiscoveryMigrationError("ranked batch audit is absent")
        digest = audit.get("canonical_digest")
        if not _is_sha256(digest) or digest in audited_digests:
            raise StrictDiscoveryMigrationError(
                "ranked batch audited digest sequence is invalid"
            )
        audited_digests.append(str(digest))
        status = str(audit.get("status"))
        status_counts[status] = status_counts.get(status, 0) + 1
        certificate = audit.get("certificate")
        if (
            status == "THRESHOLD_PROVEN"
            and isinstance(certificate, Mapping)
            and certificate.get("attempted") is True
            and certificate.get("certificate_exact") is True
            and certificate.get("certificate_passed") is True
            and certificate.get("verification_attempted") is True
            and certificate.get("verification_passed") is True
            and _is_sha256(certificate.get("certificate_sha256"))
        ):
            wins.append({
                "canonical_digest": digest,
                "status": "STRICT_THRESHOLD_PROVEN",
                "backend_status": "THRESHOLD_PROVEN",
                "publication_certificate": False,
                "pipeline_promotion": False,
                "certificate_sha256": certificate.get("certificate_sha256"),
                "row": line_number,
            })
    selected = summary.get("selected_candidates")
    accounting_names = (
        "canonical_duplicates_skipped",
        "known_codes_skipped",
        "unsupported_candidates_skipped",
        "canonicalization_errors",
        "structural_unresolved_candidates",
        "unscanned_eligible_candidates",
        "certificate_operational_errors",
    )
    accounting = {name: summary.get(name) for name in accounting_names}
    complete = bool(
        summary.get("target_mode") == "scalar-fom-strict-v1"
        and summary.get("top") == expected_rows
        and summary.get("selection_exhausted") is True
        and isinstance(selected, int)
        and not isinstance(selected, bool)
        and selected >= 0
        and all(
            isinstance(value, int) and not isinstance(value, bool) and value >= 0
            for value in accounting.values()
        )
        and selected
        + accounting["canonical_duplicates_skipped"]
        + accounting["known_codes_skipped"]
        == expected_rows
        and accounting["unsupported_candidates_skipped"] == 0
        and accounting["canonicalization_errors"] == 0
        and accounting["structural_unresolved_candidates"] == 0
        and accounting["unscanned_eligible_candidates"] == 0
        and accounting["certificate_operational_errors"] == 0
        and output_rows == selected
        and selected_rows == selected == len(audited_digests)
        and set(status_counts).issubset({
            "REJECTED", "UNRESOLVED", "THRESHOLD_PROVEN",
        })
        and status_counts.get("THRESHOLD_PROVEN", 0) == len(wins)
        and "ERROR" not in status_counts
    )
    return (
        wins,
        status_counts,
        complete,
        status_counts.get("UNRESOLVED", 0) > 0,
        audited_digests,
    )


def _is_ordered_subsequence(
    selected: Iterable[str],
    candidates: Iterable[str],
) -> bool:
    remaining = iter(candidates)
    for wanted in selected:
        for observed in remaining:
            if observed == wanted:
                break
        else:
            return False
    return True


def _recorded_live_source_fence(
    source: Any,
    *,
    phase: str,
    candidate_digests: Iterable[str],
    expected_migration_sha256: str,
    expected_snapshot_identity_sha256: str,
    expected_ledger_generation: int,
) -> list[str] | None:
    candidates = list(candidate_digests)
    if (
        not isinstance(source, Mapping)
        or any(not _is_sha256(value) for value in candidates)
        or len(set(candidates)) != len(candidates)
    ):
        return None
    blocked = source.get("blocked_digests")
    pending_page_sha256 = source.get("pending_page_sha256")
    cursor = source.get("ledger_cursor")
    if (
        source.get("successor_migration_sha256")
        != expected_migration_sha256
        or source.get("snapshot_identity_sha256")
        != expected_snapshot_identity_sha256
        or source.get("ledger_generation") != expected_ledger_generation
        or not _is_sha256(source.get("ledger_file_sha256"))
        or not _is_sha256(source.get("ledger_progress_sha256"))
        or not _is_sha256(source.get("ledger_last_ack_sha256"))
        or isinstance(cursor, bool)
        or not isinstance(cursor, int)
        or cursor < 0
        or (
            pending_page_sha256 is not None
            and not _is_sha256(pending_page_sha256)
        )
        or not isinstance(source.get("check_scope"), str)
        or not source.get("check_scope")
        or source.get("fence_phase") != phase
        or source.get("checked_candidates") != len(candidates)
        or not isinstance(blocked, list)
        or any(not _is_sha256(value) for value in blocked)
        or len(set(blocked)) != len(blocked)
        or not set(blocked).issubset(set(candidates))
        or source.get("overlap") is not bool(blocked)
    ):
        return None
    return list(blocked)


def _completed_prefix_evidence(
    progress: Mapping[str, Any],
    portfolio: Mapping[str, Any],
    *,
    paths: Any,
    ranked_input_path: Path,
    successor_root: Path | None = None,
    predecessor_batches: int | None = None,
    require_inactive: bool = True,
    require_next_row: bool = True,
    expected_successor_snapshot_identity_sha256: str | None = None,
    expected_successor_ledger_generation: int | None = None,
) -> dict[str, Any]:
    """Replay every completed batch, not merely its progress-record hash."""

    from evaluation.selection_ledger import validate_selection_ledger

    batches = progress.get("batches")
    items = portfolio.get("items")
    if not isinstance(batches, list) or not isinstance(items, list) or not batches:
        raise StrictDiscoveryMigrationError(
            "successor migration requires a nonempty completed batch prefix"
        )
    if require_inactive and progress.get("active_batch") is not None:
        raise StrictDiscoveryMigrationError(
            "cannot migrate while a sealed strict batch is active"
        )
    ranked_payload, ranked_input_identity = _read_regular_bytes(
        ranked_input_path,
        run_root=paths.run_root,
        label="portfolio ranked input",
    )
    ranked_rows = ranked_payload.splitlines(keepends=True)
    if len(ranked_rows) != len(items) or any(
        not row.endswith(b"\n") for row in ranked_rows
    ):
        raise StrictDiscoveryMigrationError("portfolio ranked input rows diverge")
    artifacts: list[dict[str, Any]] = []
    expected_start = 0
    old_count = len(batches) if predecessor_batches is None else predecessor_batches
    for sequence, raw_batch in enumerate(batches):
        if not isinstance(raw_batch, Mapping):
            raise StrictDiscoveryMigrationError("completed strict batch is malformed")
        start = raw_batch.get("manifest_start_row")
        next_row = raw_batch.get("manifest_next_row")
        source_rows = raw_batch.get("selected_source_rows")
        ranks = raw_batch.get("selected_portfolio_ranks")
        digests = raw_batch.get("selected_digests")
        if (
            raw_batch.get("batch_index") != sequence
            or raw_batch.get("disposition") not in {"COMPLETED", "DEFERRED", "PROVEN"}
            or isinstance(start, bool)
            or not isinstance(start, int)
            or start != expected_start
            or isinstance(next_row, bool)
            or not isinstance(next_row, int)
            or not start < next_row <= len(items)
            or not isinstance(source_rows, list)
            or not isinstance(ranks, list)
            or not isinstance(digests, list)
            or not source_rows
            or not (len(source_rows) == len(ranks) == len(digests))
            or source_rows != sorted(set(source_rows))
            or source_rows[0] < start
            or source_rows[-1] >= next_row
            or ranks != [items[row].get("portfolio_rank") for row in source_rows]
            or digests != [items[row].get("canonical_digest") for row in source_rows]
        ):
            raise StrictDiscoveryMigrationError(
                f"completed strict batch {sequence} does not replay its portfolio rows"
            )
        selected_set = set(source_rows)
        expected_skips = [
            items[row].get("canonical_digest")
            for row in range(start, next_row)
            if row not in selected_set
        ]
        skipped = raw_batch.get("skipped_foreground_owned_digests")
        if (
            skipped != expected_skips
            or raw_batch.get("skipped_foreground_owned_count") != len(expected_skips)
            or raw_batch.get("skipped_foreground_owned_sha256") != _sha256(expected_skips)
            or not isinstance(raw_batch.get("live_source"), Mapping)
        ):
            raise StrictDiscoveryMigrationError(
                f"completed strict batch {sequence} skip evidence does not replay"
            )
        if successor_root is not None and sequence >= old_count:
            if (
                not _is_sha256(expected_successor_snapshot_identity_sha256)
                or isinstance(expected_successor_ledger_generation, bool)
                or not isinstance(expected_successor_ledger_generation, int)
            ):
                raise StrictDiscoveryMigrationError(
                    "successor live-source identity baseline is absent"
                )
            remaining_digests = [
                items[row].get("canonical_digest")
                for row in range(start, len(items))
            ]
            selection_blocked = _recorded_live_source_fence(
                raw_batch.get("live_source"),
                phase="selection",
                candidate_digests=remaining_digests,
                expected_migration_sha256=successor_root.name,
                expected_snapshot_identity_sha256=(
                    expected_successor_snapshot_identity_sha256
                ),
                expected_ledger_generation=expected_successor_ledger_generation,
            )
            launch_blocked = _recorded_live_source_fence(
                raw_batch.get("launch_live_source"),
                phase="pre-launch",
                candidate_digests=digests,
                expected_migration_sha256=successor_root.name,
                expected_snapshot_identity_sha256=(
                    expected_successor_snapshot_identity_sha256
                ),
                expected_ledger_generation=expected_successor_ledger_generation,
            )
            post_blocked = _recorded_live_source_fence(
                raw_batch.get("post_live_source"),
                phase="post-run",
                candidate_digests=digests,
                expected_migration_sha256=successor_root.name,
                expected_snapshot_identity_sha256=(
                    expected_successor_snapshot_identity_sha256
                ),
                expected_ledger_generation=expected_successor_ledger_generation,
            )
            if (
                selection_blocked is None
                or not set(expected_skips).issubset(set(selection_blocked))
                or set(digests).intersection(selection_blocked)
                or launch_blocked != []
                or post_blocked != []
                or not (
                    raw_batch["live_source"]["ledger_cursor"]
                    <= raw_batch["launch_live_source"]["ledger_cursor"]
                    <= raw_batch["post_live_source"]["ledger_cursor"]
                )
            ):
                raise StrictDiscoveryMigrationError(
                    f"successor strict batch {sequence} lacks overlap fences"
                )
        root = (
            paths.batches
            if successor_root is None or sequence < old_count
            else successor_root / "batches"
        ) / f"batch-{sequence:04d}"
        input_path = root / "input.jsonl"
        ranked_path = root / "ranked.jsonl"
        summary_path = root / "summary.json"
        ledger_path = root / "selection-ledger.json"
        input_payload, input_identity = _read_regular_bytes(
            input_path, run_root=paths.run_root, label=f"batch {sequence} input"
        )
        ranked_output, ranked_identity = _read_regular_bytes(
            ranked_path, run_root=paths.run_root, label=f"batch {sequence} ranked output"
        )
        summary_payload, summary_identity = _read_regular_bytes(
            summary_path, run_root=paths.run_root, label=f"batch {sequence} summary"
        )
        ledger_payload, ledger_identity = _read_regular_bytes(
            ledger_path, run_root=paths.run_root, label=f"batch {sequence} selection ledger"
        )
        expected_input = b"".join(
            _canonical_bytes(json.loads(ranked_rows[row])) + b"\n"
            for row in source_rows
        )
        if input_payload != expected_input:
            raise StrictDiscoveryMigrationError(
                f"completed strict batch {sequence} input does not replay"
            )
        summary = _json_object_from_payload(
            summary_payload, label=f"batch {sequence} summary"
        )
        (
            wins,
            status_counts,
            complete,
            unresolved,
            audited_digests,
        ) = _ranked_batch_semantics(
            ranked_output, summary, expected_rows=len(source_rows)
        )
        expected_disposition = (
            "PROVEN" if wins else ("DEFERRED" if unresolved else "COMPLETED")
        )
        if (
            not complete
            or raw_batch.get("disposition") != expected_disposition
            or raw_batch.get("status_counts") != status_counts
            or raw_batch.get("wins") != wins
            or raw_batch.get("rows") != len(source_rows)
            or raw_batch.get("input_path") != str(input_path)
            or raw_batch.get("input_sha256") != input_identity["sha256"]
            or raw_batch.get("ranked_output") != str(ranked_path)
            or raw_batch.get("summary_output") != str(summary_path)
        ):
            raise StrictDiscoveryMigrationError(
                f"completed strict batch {sequence} output semantics diverge"
            )
        ledger = _json_object_from_payload(
            ledger_payload, label=f"batch {sequence} selection ledger"
        )
        try:
            validated_ledger = validate_selection_ledger(
                ledger,
                binding_sha256=str(ledger.get("binding_sha256")),
                snapshot_identity_sha256_value=str(
                    ledger.get("snapshot_identity_sha256")
                ),
                snapshot_rows=ledger.get("snapshot_rows"),
                eligible_rows=ledger.get("eligible_rows"),
            )
        except (TypeError, ValueError) as exc:
            raise StrictDiscoveryMigrationError(
                f"completed strict batch {sequence} ledger does not replay"
            ) from exc
        ack_selected = [
            digest
            for ack in validated_ledger.get("ack_chain", [])
            for digest in ack.get("page", {}).get("selected_digests", [])
        ]
        if (
            validated_ledger.get("pending") is not None
            or validated_ledger.get("snapshot_rows") != len(digests)
            or validated_ledger.get("eligible_rows") != len(digests)
            or validated_ledger.get("cursor") != len(digests)
            or validated_ledger.get("committed_digests") != audited_digests
            or ack_selected != audited_digests
            or len(set(audited_digests)) != len(audited_digests)
            or not _is_ordered_subsequence(audited_digests, digests)
        ):
            raise StrictDiscoveryMigrationError(
                f"completed strict batch {sequence} ledger selected digests diverge"
            )
        batch_artifacts = {
            "batch_index": sequence,
            "batch_record_sha256": _sha256(dict(raw_batch)),
            "input": input_identity,
            "ranked_output": ranked_identity,
            "summary": summary_identity,
            "selection_ledger": ledger_identity,
            "audited_digests": audited_digests,
            "audited_digests_sha256": _sha256(audited_digests),
            "selection_ledger_seals": {
                "progress_sha256": validated_ledger.get("progress_sha256"),
                "last_ack_sha256": validated_ledger.get("last_ack_sha256"),
                "binding_sha256": validated_ledger.get("binding_sha256"),
                "snapshot_identity_sha256": validated_ledger.get(
                    "snapshot_identity_sha256"
                ),
            },
        }
        artifacts.append(batch_artifacts)
        expected_start = next_row
    if require_next_row and expected_start != progress.get("next_row"):
        raise StrictDiscoveryMigrationError(
            "completed strict batch prefix does not reach progress next_row"
        )
    last = artifacts[-1]
    return {
        "next_row": expected_start,
        "completed_batches": len(batches),
        "ranked_input": ranked_input_identity,
        "batch_records_sha256": _sha256([dict(batch) for batch in batches]),
        "artifact_identities": artifacts,
        "artifact_identities_sha256": _sha256(artifacts),
        "last_completed_batch": last,
        "last_completed_batch_sha256": _sha256(last),
    }


def _validate_successor_progress_extension(
    progress: Mapping[str, Any],
    *,
    predecessor: Mapping[str, Any],
    portfolio: Mapping[str, Any],
    ranked_input_path: Path,
    paths: Any,
    successor_root: Path,
    expected_snapshot_identity_sha256: str,
    expected_ledger_generation: int,
) -> dict[str, Any]:
    from . import strict_discovery_cli as cli

    items = portfolio.get("items")
    predecessor_batches = predecessor.get("batches")
    batches = progress.get("batches")
    if (
        not isinstance(items, list)
        or not isinstance(predecessor_batches, list)
        or not isinstance(batches, list)
        or batches[: len(predecessor_batches)] != predecessor_batches
        or progress.get("source") != predecessor.get("source")
        or progress.get("config") != predecessor.get("config")
        or progress.get("config_sha256") != predecessor.get("config_sha256")
    ):
        raise StrictDiscoveryMigrationError(
            "successor progress changed its predecessor prefix or policy"
        )
    evidence = _completed_prefix_evidence(
        progress,
        portfolio,
        paths=paths,
        ranked_input_path=ranked_input_path,
        successor_root=successor_root,
        predecessor_batches=len(predecessor_batches),
        require_inactive=False,
        require_next_row=False,
        expected_successor_snapshot_identity_sha256=(
            expected_snapshot_identity_sha256
        ),
        expected_successor_ledger_generation=expected_ledger_generation,
    )
    cursor = int(evidence["next_row"])
    old_skips = predecessor.get("foreground_skips", [])
    skips = progress.get("foreground_skips", [])
    if (
        not isinstance(old_skips, list)
        or not isinstance(skips, list)
        or skips[: len(old_skips)] != old_skips
    ):
        raise StrictDiscoveryMigrationError(
            "successor foreground-skip prefix changed"
        )
    for raw in skips[len(old_skips) :]:
        if not isinstance(raw, Mapping):
            raise StrictDiscoveryMigrationError(
                "successor foreground-skip record is malformed"
            )
        start = raw.get("manifest_start_row")
        next_row = raw.get("manifest_next_row")
        digests = raw.get("skipped_foreground_owned_digests")
        expected = (
            [items[row].get("canonical_digest") for row in range(cursor, next_row)]
            if isinstance(next_row, int) and not isinstance(next_row, bool)
            and cursor < next_row <= len(items)
            else None
        )
        recorded_blocked = (
            _recorded_live_source_fence(
                raw.get("live_source"),
                phase="selection",
                candidate_digests=expected,
                expected_migration_sha256=successor_root.name,
                expected_snapshot_identity_sha256=(
                    expected_snapshot_identity_sha256
                ),
                expected_ledger_generation=expected_ledger_generation,
            )
            if isinstance(expected, list)
            else None
        )
        if (
            start != cursor
            or digests != expected
            or raw.get("skipped_foreground_owned_count")
            != (len(expected) if isinstance(expected, list) else -1)
            or raw.get("skipped_foreground_owned_sha256")
            != (_sha256(expected) if isinstance(expected, list) else None)
            or recorded_blocked != expected
        ):
            raise StrictDiscoveryMigrationError(
                "successor foreground-skip record does not replay"
            )
        cursor = int(next_row)
    if progress.get("next_row") != cursor:
        raise StrictDiscoveryMigrationError(
            "successor next_row is not justified by batches or ownership skips"
        )

    active = progress.get("active_batch")
    if active is not None:
        try:
            config = cli.DiscoveryConfig.from_json(predecessor["config"])
        except (KeyError, TypeError, ValueError) as exc:
            raise StrictDiscoveryMigrationError(
                "successor active batch policy is invalid"
            ) from exc
        batch_index = len(batches)
        limit = (
            config.initial_batch_size
            if batch_index == 0
            else (
                config.expanded_top - config.initial_batch_size
                if batch_index == 1
                else config.batch_size
            )
        )
        expected_input = (
            successor_root / "batches" / f"batch-{batch_index:04d}" / "input.jsonl"
        )
        if not isinstance(active, Mapping):
            raise StrictDiscoveryMigrationError(
                "successor active batch is malformed"
            )
        start = active.get("manifest_start_row")
        next_row = active.get("manifest_next_row")
        source_rows = active.get("selected_source_rows")
        ranks = active.get("selected_portfolio_ranks")
        digests = active.get("selected_digests")
        skipped = active.get("skipped_foreground_owned_digests")
        count = active.get("rows")
        argv = active.get("argv")
        attempts = active.get("attempts")
        valid_range = bool(
            isinstance(start, int)
            and not isinstance(start, bool)
            and start == cursor
            and isinstance(next_row, int)
            and not isinstance(next_row, bool)
            and start < next_row <= len(items)
        )
        selected_rows_valid = bool(
            isinstance(source_rows, list)
            and source_rows
            and all(
                isinstance(row, int) and not isinstance(row, bool)
                for row in source_rows
            )
            and source_rows == sorted(set(source_rows))
            and valid_range
            and source_rows[0] >= start
            and source_rows[-1] < next_row
        )
        expected_ranks = (
            [items[row].get("portfolio_rank") for row in source_rows]
            if selected_rows_valid else None
        )
        expected_digests = (
            [items[row].get("canonical_digest") for row in source_rows]
            if selected_rows_valid else None
        )
        selected_set = set(source_rows) if selected_rows_valid else set()
        expected_skips = (
            [
                items[row].get("canonical_digest")
                for row in range(start, next_row)
                if row not in selected_set
            ]
            if valid_range else None
        )
        if (
            active.get("batch_index") != batch_index
            or not valid_range
            or not selected_rows_valid
            or isinstance(count, bool)
            or not isinstance(count, int)
            or count != len(source_rows)
            or not 0 < count <= limit
            or ranks != expected_ranks
            or digests != expected_digests
            or skipped != expected_skips
            or active.get("skipped_foreground_owned_count")
            != len(expected_skips)
            or active.get("skipped_foreground_owned_sha256")
            != _sha256(expected_skips)
            or active.get("input_path") != str(expected_input)
            or not isinstance(argv, list)
            or not argv
            or any(not isinstance(value, str) for value in argv)
            or isinstance(attempts, bool)
            or not isinstance(attempts, int)
            or attempts < 0
        ):
            raise StrictDiscoveryMigrationError(
                "successor active batch does not replay its portfolio cursor"
            )
        expected_argv = cli.build_audit_argv(
            python_executable=argv[0],
            paths=replace(
                paths,
                root=successor_root,
                progress=successor_root / "progress.json",
                batches=successor_root / "batches",
            ),
            config=config,
            batch_index=batch_index,
            count=count,
        )
        if argv != expected_argv:
            raise StrictDiscoveryMigrationError(
                "successor active batch argv changed"
            )
        ranked_payload, _ = _read_regular_bytes(
            ranked_input_path,
            run_root=paths.run_root,
            label="successor active portfolio input",
        )
        ranked_rows = ranked_payload.splitlines(keepends=True)
        if (
            len(ranked_rows) != len(items)
            or any(not row.endswith(b"\n") for row in ranked_rows)
        ):
            raise StrictDiscoveryMigrationError(
                "successor active portfolio input rows changed"
            )
        expected_payload = b"".join(
            _canonical_bytes(json.loads(ranked_rows[row])) + b"\n"
            for row in source_rows
        )
        input_payload, input_identity = _read_regular_bytes(
            expected_input,
            run_root=paths.run_root,
            label="successor active batch input",
        )
        if (
            input_payload != expected_payload
            or active.get("input_sha256") != input_identity["sha256"]
        ):
            raise StrictDiscoveryMigrationError(
                "successor active batch input changed"
            )
        remaining_digests = [
            items[row].get("canonical_digest")
            for row in range(start, len(items))
        ]
        selection_blocked = _recorded_live_source_fence(
            active.get("live_source"),
            phase="selection",
            candidate_digests=remaining_digests,
            expected_migration_sha256=successor_root.name,
            expected_snapshot_identity_sha256=expected_snapshot_identity_sha256,
            expected_ledger_generation=expected_ledger_generation,
        )
        launch = active.get("launch_live_source")
        launch_blocked = _recorded_live_source_fence(
            launch,
            phase="pre-launch",
            candidate_digests=digests,
            expected_migration_sha256=successor_root.name,
            expected_snapshot_identity_sha256=expected_snapshot_identity_sha256,
            expected_ledger_generation=expected_ledger_generation,
        )
        if (
            selection_blocked is None
            or not set(expected_skips).issubset(set(selection_blocked))
            or set(digests).intersection(selection_blocked)
            or launch_blocked is None
            or active["live_source"]["ledger_cursor"]
            > active["launch_live_source"]["ledger_cursor"]
        ):
            raise StrictDiscoveryMigrationError(
                "successor active batch overlap evidence is invalid"
            )
        conflict = active.get("ownership_conflict")
        if conflict is None:
            if launch_blocked or active.get("post_live_source") is not None:
                raise StrictDiscoveryMigrationError(
                    "successor active batch has inconsistent overlap evidence"
                )
        elif not isinstance(conflict, Mapping):
            raise StrictDiscoveryMigrationError(
                "successor active batch ownership conflict is malformed"
            )
        else:
            phase = conflict.get("phase")
            source = (
                launch if phase == "pre-launch"
                else active.get("post_live_source")
            )
            blocked = conflict.get("blocked_digests")
            source_blocked = (
                _recorded_live_source_fence(
                    source,
                    phase=phase,
                    candidate_digests=digests,
                    expected_migration_sha256=successor_root.name,
                    expected_snapshot_identity_sha256=(
                        expected_snapshot_identity_sha256
                    ),
                    expected_ledger_generation=expected_ledger_generation,
                )
                if phase in {"pre-launch", "post-run"}
                else None
            )
            if (
                progress.get("status") != "FAILED"
                or phase not in {"pre-launch", "post-run"}
                or source_blocked is None
                or conflict.get("live_source") != source
                or not isinstance(blocked, list)
                or not blocked
                or blocked != source_blocked
                or (
                    phase == "pre-launch"
                    and active.get("post_live_source") is not None
                )
                or (phase == "post-run" and launch_blocked != [])
                or (
                    phase == "post-run"
                    and active["launch_live_source"]["ledger_cursor"]
                    > source["ledger_cursor"]
                )
            ):
                raise StrictDiscoveryMigrationError(
                    "successor active ownership conflict does not replay"
                )

    status = progress.get("status")
    dispositions = [batch.get("disposition") for batch in batches]
    flattened_wins = [
        win
        for batch in batches
        if isinstance(batch, Mapping)
        for win in batch.get("wins", [])
    ]
    proven_positions = [
        index for index, disposition in enumerate(dispositions)
        if disposition == "PROVEN"
    ]
    if (
        progress.get("wins", []) != flattened_wins
        or (status == "FAILED" and active is None)
        or (status != "STRICT_THRESHOLD_PROVEN" and flattened_wins)
        or (
            status == "STRICT_THRESHOLD_PROVEN"
            and (
                active is not None
                or not flattened_wins
                or proven_positions != [len(batches) - 1]
                or batches[-1].get("wins") != flattened_wins
            )
        )
        or (
            status == "EXHAUSTED"
            and (
                active is not None
                or cursor != len(items)
                or "DEFERRED" in dispositions
                or "PROVEN" in dispositions
            )
        )
        or (
            status == "INCOMPLETE"
            and (
                active is not None
                or cursor != len(items)
                or "DEFERRED" not in dispositions
                or "PROVEN" in dispositions
            )
        )
    ):
        raise StrictDiscoveryMigrationError(
            "successor terminal/active status does not replay its evidence"
        )
    return evidence


def _validate_old_snapshot_identity(source: Mapping[str, Any]) -> dict[str, Any]:
    identity = source.get("snapshot_identity")
    identity_sha256 = source.get("snapshot_identity_sha256")
    required = (
        "binding_sha256",
        "snapshot_sha256",
        "offsets_sha256",
        "chunk_index_sha256",
        "counts_sha256",
    )
    if (
        not isinstance(identity, Mapping)
        or any(not _is_sha256(identity.get(name)) for name in required)
        or not _is_sha256(identity_sha256)
        or _sha256(dict(identity)) != identity_sha256
        or isinstance(identity.get("rows"), bool)
        or not isinstance(identity.get("rows"), int)
        or isinstance(identity.get("eligible_rows"), bool)
        or not isinstance(identity.get("eligible_rows"), int)
        or not 0 <= identity["eligible_rows"] <= identity["rows"]
    ):
        raise StrictDiscoveryMigrationError(
            "portfolio lacks a replayable predecessor snapshot identity"
        )
    return dict(identity)


def _verify_old_snapshot_copy(
    snapshot_path: Path,
    offsets_path: Path,
    *,
    run_root: Path,
    identity: Mapping[str, Any],
) -> tuple[dict[str, Any], dict[str, Any]]:
    old_snapshot_path = _confined_regular_path(
        snapshot_path,
        run_root=run_root,
        label="recovered predecessor snapshot",
    )
    old_offsets_path = _confined_regular_path(
        offsets_path,
        run_root=run_root,
        label="recovered predecessor offsets",
    )
    snapshot = _stable_file_identity(
        old_snapshot_path,
        run_root=run_root,
        label="recovered predecessor snapshot",
    )
    offsets = _stable_file_identity(
        old_offsets_path,
        run_root=run_root,
        label="recovered predecessor offsets",
    )
    if (
        snapshot["sha256"] != identity.get("snapshot_sha256")
        or offsets["sha256"] != identity.get("offsets_sha256")
        or offsets["bytes"] != (int(identity["rows"]) + 1) * 8
    ):
        raise StrictDiscoveryMigrationError(
            "recovered predecessor snapshot does not match the portfolio identity"
        )
    return snapshot, offsets


_LEDGER_EXTENSION_MUTABLE_FIELDS = frozenset({
    "ack_chain",
    "committed_digests",
    "completed_pages",
    "cursor",
    "deferred_pages",
    "last_ack_sha256",
    "last_acknowledged_at",
    "last_acknowledged_page_sha256",
    "pending",
    "progress_sha256",
})


def _ledger_extension_static_sha256(ledger: Mapping[str, Any]) -> str:
    return _sha256({
        key: value
        for key, value in ledger.items()
        if key not in _LEDGER_EXTENSION_MUTABLE_FIELDS
    })


def _ledger_deferred_prefix_sha256(
    deferred: Iterable[Mapping[str, Any]],
) -> str:
    return _sha256([dict(item) for item in deferred])


def create_successor_migration(
    *,
    paths: Any,
    portfolio_manifest: Path | str,
    new_snapshot_manifest: Path | str,
    identity_rebase_certificate: Path | str,
) -> dict[str, Any]:
    """Create a successor only from a trusted package and COMMITTED live baseline."""

    from . import strict_discovery_cli as cli

    if load_successor_lineage(paths, allow_incomplete=True) is not None:
        raise StrictDiscoveryMigrationError(
            "strict discovery already has an immutable successor lineage"
        )

    portfolio, ranked_path, bound = cli.load_portfolio_manifest(
        portfolio_manifest,
        paths=paths,
    )
    portfolio_path = Path(bound["portfolio_manifest_path"])
    portfolio_replay, portfolio_identity = _read_regular_json(
        portfolio_path,
        run_root=paths.run_root,
        label="strict discovery portfolio",
    )
    if (
        portfolio_replay != portfolio
        or portfolio_identity["sha256"]
        != bound["portfolio_manifest_file_sha256"]
    ):
        raise StrictDiscoveryMigrationError(
            "portfolio changed while migration evidence was captured"
        )
    if not _lexists(paths.progress):
        raise StrictDiscoveryMigrationError("predecessor strict progress is absent")
    progress_raw, progress_identity = _read_regular_json(
        paths.progress,
        run_root=paths.run_root,
        label="predecessor strict progress",
    )
    try:
        progress = cli.validate_progress(progress_raw)
    except (TypeError, ValueError) as exc:
        raise StrictDiscoveryMigrationError(
            "predecessor strict progress is invalid"
        ) from exc
    if progress.get("source") != bound:
        raise StrictDiscoveryMigrationError(
            "predecessor progress does not bind the supplied portfolio"
        )
    if (
        progress.get("status") != "RUNNING"
        or progress.get("wins")
        or any(
            isinstance(batch, Mapping)
            and batch.get("disposition") == "PROVEN"
            for batch in progress.get("batches", [])
        )
    ):
        raise StrictDiscoveryMigrationError(
            "only an idle nonterminal strict discovery can have a successor"
        )
    old_source = portfolio.get("source")
    if not isinstance(old_source, Mapping):
        raise StrictDiscoveryMigrationError("portfolio source provenance is absent")
    old_identity = _validate_old_snapshot_identity(old_source)
    ledger_path = _confined_regular_path(
        str(old_source.get("ledger_path")),
        run_root=paths.run_root,
        label="successor Stage 2 ledger",
    )
    prefix = _completed_prefix_evidence(
        progress,
        portfolio,
        paths=paths,
        ranked_input_path=ranked_path,
    )
    ranked_identity = prefix["ranked_input"]
    ranked = portfolio.get("ranked_input")
    if (
        not isinstance(ranked, Mapping)
        or ranked_identity["sha256"] != ranked.get("sha256")
        or ranked_identity["bytes"] != ranked.get("bytes")
        or ranked.get("rows") != len(portfolio.get("items", []))
    ):
        raise StrictDiscoveryMigrationError(
            "portfolio ranked input changed before migration"
        )
    successor_snapshot = _validate_snapshot_manifest(
        Path(new_snapshot_manifest),
        run_root=paths.run_root,
        label="successor",
        require_manifest_stat=False,
    )
    rebase = _validate_identity_rebase(
        Path(identity_rebase_certificate),
        run_root=paths.run_root,
        live_ledger_path=ledger_path,
        portfolio=portfolio,
        ranked_input=ranked,
        old_identity=old_identity,
        old_identity_sha256=str(old_source["snapshot_identity_sha256"]),
        new_snapshot=successor_snapshot,
        require_live_install_exact=True,
    )
    equivalence = {
        "method": REBASE_EQUIVALENCE_METHOD,
        "identity_rebase": rebase,
    }
    expected_manifest = ledger_path.with_name(
        f"{ledger_path.name}.ranked-snapshot.manifest.json"
    ).resolve()
    if Path(successor_snapshot["manifest"]["path"]) != expected_manifest:
        raise StrictDiscoveryMigrationError(
            "successor manifest is not the live Stage 2 ledger manifest"
        )
    live_ledger, live_ledger_identity = _validated_live_ledger(
        ledger_path,
        run_root=paths.run_root,
        expected_binding_sha256=str(successor_snapshot["binding_sha256"]),
        expected_snapshot_identity_sha256=str(
            successor_snapshot["snapshot_identity_sha256"]
        ),
        expected_snapshot_rows=int(successor_snapshot["snapshot_rows"]),
        expected_eligible_rows=int(successor_snapshot["eligible_rows"]),
    )
    pending = live_ledger.get("pending")
    pending_page_sha256 = (
        pending.get("page_sha256") if isinstance(pending, Mapping) else None
    )
    install_live = equivalence["identity_rebase"]["install"]["live"]
    if (
        install_live.get("ledger_file_sha256")
        != live_ledger_identity["sha256"]
        or install_live.get("progress_sha256")
        != live_ledger.get("progress_sha256")
        or install_live.get("last_ack_sha256")
        != live_ledger.get("last_ack_sha256")
        or install_live.get("pending_page_sha256")
        != pending_page_sha256
    ):
        raise StrictDiscoveryMigrationError(
            "live Stage 2 ledger changed after COMMITTED install validation"
        )
    foreground_owned = set(live_ledger.get("committed_digests", []))
    if isinstance(pending, Mapping):
        pending_page = (
            pending.get("page")
            if isinstance(pending.get("page"), Mapping)
            else pending
        )
        foreground_owned.update(
            str(value) for value in pending_page.get("selected_digests", [])
        )
    predecessor_audited = {
        str(digest)
        for artifact in prefix.get("artifact_identities", [])
        if isinstance(artifact, Mapping)
        for digest in artifact.get("audited_digests", [])
    }
    if predecessor_audited.intersection(foreground_owned):
        raise StrictDiscoveryMigrationError(
            "COMMITTED successor ownership overlaps the predecessor strict prefix"
        )
    old_manifest_file_sha256 = old_source.get("manifest_file_sha256")
    old_manifest_sha256 = old_source.get("manifest_sha256")
    if not _is_sha256(old_manifest_file_sha256) or not _is_sha256(
        old_manifest_sha256
    ):
        raise StrictDiscoveryMigrationError(
            "portfolio predecessor manifest anchors are invalid"
        )
    certificate = {
        "schema_version": SUCCESSOR_SCHEMA_VERSION,
        "gate": SUCCESSOR_GATE,
        "publication_certificate": False,
        "pipeline_promotion": False,
        "predecessor": {
            "portfolio": {
                "path": str(portfolio_path),
                "file_sha256": portfolio_identity["sha256"],
                "portfolio_sha256": portfolio["portfolio_sha256"],
            },
            "ranked_input": {
                **ranked_identity,
                "rows": ranked["rows"],
                "payload_kind": ranked["payload_kind"],
            },
            "stage2_source": {
                "ledger_path": str(ledger_path),
                "ledger_generation": old_source.get("ledger_generation"),
                "ledger_cursor": old_source.get("ledger_cursor"),
                "manifest_path": str(old_source.get("manifest_path")),
                "manifest_file_sha256": old_manifest_file_sha256,
                "manifest_sha256": old_manifest_sha256,
                "snapshot_identity": old_identity,
                "snapshot_identity_sha256": old_source[
                    "snapshot_identity_sha256"
                ],
            },
            "progress": {
                **progress_identity,
                "progress_sha256": progress["progress_sha256"],
                "status": progress["status"],
                "next_row": progress["next_row"],
                "completed_batches": len(progress["batches"]),
                "config_sha256": progress.get("config_sha256"),
            },
            "completed_prefix": prefix,
        },
        "successor": {
            "stage2_source": {
                **successor_snapshot,
                "ledger_path": str(ledger_path),
                "ledger_file": live_ledger_identity,
                "ledger_generation": live_ledger["generation"],
                "ledger_cursor": live_ledger["cursor"],
                "ledger_progress_sha256": live_ledger["progress_sha256"],
                "ledger_completed_pages": live_ledger["completed_pages"],
                "ledger_last_ack_sha256": live_ledger["last_ack_sha256"],
                "ledger_pending_page_sha256": pending_page_sha256,
                "ledger_committed_count": len(live_ledger["committed_digests"]),
                "ledger_committed_sha256": _sha256(
                    live_ledger["committed_digests"]
                ),
                "ledger_static_sha256": _ledger_extension_static_sha256(
                    live_ledger
                ),
                "ledger_deferred_count": len(live_ledger["deferred_pages"]),
                "ledger_deferred_sha256": _ledger_deferred_prefix_sha256(
                    live_ledger["deferred_pages"]
                ),
            },
            "equivalence": equivalence,
        },
    }
    certificate["migration_sha256"] = _sha256(certificate)
    successor_root = paths.root / "successors" / certificate["migration_sha256"]
    _validate_successor_root_set(paths, certificate["migration_sha256"])
    certificate_path = successor_root / "migration.json"
    successor_progress_path = successor_root / "progress.json"
    _, directory_descriptor = _open_confined_directory(
        successor_root,
        run_root=paths.run_root,
        label="strict successor root",
        create=True,
    )
    os.close(directory_descriptor)
    successor_progress = dict(progress)
    successor_progress.pop("active_batch", None)
    successor_progress.update({
        "status": "RUNNING",
        "successor_migration": {
            "path": str(certificate_path),
            "migration_sha256": certificate["migration_sha256"],
            "predecessor_progress_sha256": progress["progress_sha256"],
        },
    })
    successor_progress = cli._seal_progress(successor_progress)
    cli.validate_progress(successor_progress)
    _publish_or_verify_json(
        certificate_path,
        certificate,
        run_root=paths.run_root,
        label="strict successor migration",
    )
    _publish_or_verify_json(
        successor_progress_path,
        successor_progress,
        run_root=paths.run_root,
        label="strict successor progress",
    )
    lineage = {
        "schema_version": LINEAGE_SCHEMA_VERSION,
        "gate": LINEAGE_GATE,
        "migration_sha256": certificate["migration_sha256"],
        "certificate": str(certificate_path),
        "progress": str(successor_progress_path),
        "predecessor_progress_sha256": progress["progress_sha256"],
        "portfolio_manifest": str(portfolio_path),
        "portfolio_manifest_file_sha256": bound[
            "portfolio_manifest_file_sha256"
        ],
    }
    lineage["lineage_sha256"] = _sha256(lineage)
    _write_new_json(
        successor_lineage_path(paths),
        lineage,
        run_root=paths.run_root,
        label="strict successor lineage",
    )
    return {
        "status": "SUCCESSOR_READY",
        "migration_sha256": certificate["migration_sha256"],
        "certificate": str(certificate_path.resolve()),
        "successor_root": str(successor_root.resolve()),
        "successor_progress": str(successor_progress_path.resolve()),
        "next_row": successor_progress["next_row"],
        "completed_batches": len(successor_progress["batches"]),
        "equivalence_method": equivalence["method"],
    }


def _check_bound_file(
    identity: Mapping[str, Any],
    *,
    run_root: Path,
    label: str,
) -> Path:
    raw_path = Path(str(identity.get("path")))
    path, descriptor = _open_confined_regular(
        raw_path, run_root=run_root, label=label
    )
    try:
        metadata = os.fstat(descriptor)
    finally:
        os.close(descriptor)
    observed = {
        "device": int(metadata.st_dev),
        "inode": int(metadata.st_ino),
        "bytes": int(metadata.st_size),
        "mtime_ns": int(metadata.st_mtime_ns),
        "ctime_ns": int(metadata.st_ctime_ns),
    }
    if (
        str(path) != identity.get("path")
        or any(observed[name] != identity.get(name) for name in observed)
    ):
        raise StrictDiscoveryMigrationError(f"{label} identity changed")
    return path


def load_successor_migration(
    migration_path: Path | str,
    *,
    paths: Any,
    portfolio_manifest: Path | str,
    verify_large_files: bool = True,
) -> dict[str, Any]:
    """Validate a successor certificate without mutating predecessor evidence."""

    from . import strict_discovery_cli as cli

    path = _confined_regular_path(
        migration_path,
        run_root=paths.run_root,
        label="strict successor migration",
    )
    certificate, _ = _read_regular_json(
        path,
        run_root=paths.run_root,
        label="strict successor migration",
    )
    unsigned = dict(certificate)
    seal = unsigned.pop("migration_sha256", None)
    predecessor = certificate.get("predecessor")
    successor = certificate.get("successor")
    if (
        certificate.get("schema_version") != SUCCESSOR_SCHEMA_VERSION
        or certificate.get("gate") != SUCCESSOR_GATE
        or certificate.get("publication_certificate") is not False
        or certificate.get("pipeline_promotion") is not False
        or not _is_sha256(seal)
        or seal != _sha256(unsigned)
        or not isinstance(predecessor, Mapping)
        or not isinstance(successor, Mapping)
        or path.name != "migration.json"
        or path.parent.name != seal
        or path.parent.parent.name != "successors"
        or path.parent.parent.parent != paths.root
    ):
        raise StrictDiscoveryMigrationError(
            "strict successor migration seal/schema/path is invalid"
        )
    lineage = load_successor_lineage(paths, required=True)
    assert lineage is not None
    if (
        lineage.get("certificate") != str(path)
        or lineage.get("migration_sha256") != seal
    ):
        raise StrictDiscoveryMigrationError(
            "requested migration is not the active immutable successor lineage"
        )
    portfolio, ranked_path, bound = cli.load_portfolio_manifest(
        portfolio_manifest,
        paths=paths,
    )
    portfolio_path = Path(bound["portfolio_manifest_path"])
    portfolio_replay, portfolio_identity = _read_regular_json(
        portfolio_path,
        run_root=paths.run_root,
        label="strict discovery portfolio",
    )
    if (
        portfolio_replay != portfolio
        or portfolio_identity["sha256"]
        != bound["portfolio_manifest_file_sha256"]
    ):
        raise StrictDiscoveryMigrationError(
            "portfolio changed while successor evidence was loaded"
        )
    if (
        lineage.get("portfolio_manifest") != bound["portfolio_manifest_path"]
        or lineage.get("portfolio_manifest_file_sha256")
        != bound["portfolio_manifest_file_sha256"]
    ):
        raise StrictDiscoveryMigrationError(
            "successor lineage portfolio binding changed"
        )
    old_portfolio = predecessor.get("portfolio")
    old_ranked = predecessor.get("ranked_input")
    old_progress = predecessor.get("progress")
    old_stage2 = predecessor.get("stage2_source")
    completed_prefix = predecessor.get("completed_prefix")
    successor_stage2 = successor.get("stage2_source")
    equivalence = successor.get("equivalence")
    if any(
        not isinstance(value, Mapping)
        for value in (
            old_portfolio,
            old_ranked,
            old_progress,
            old_stage2,
            completed_prefix,
            successor_stage2,
            equivalence,
        )
    ):
        raise StrictDiscoveryMigrationError("successor migration evidence is incomplete")
    assert isinstance(old_portfolio, Mapping)
    assert isinstance(old_ranked, Mapping)
    assert isinstance(old_progress, Mapping)
    assert isinstance(old_stage2, Mapping)
    assert isinstance(completed_prefix, Mapping)
    assert isinstance(successor_stage2, Mapping)
    assert isinstance(equivalence, Mapping)
    if not _lexists(paths.progress):
        raise StrictDiscoveryMigrationError("predecessor strict progress disappeared")
    current_progress_raw, current_progress_identity = _read_regular_json(
        paths.progress,
        run_root=paths.run_root,
        label="predecessor strict progress",
    )
    try:
        current_progress = cli.validate_progress(current_progress_raw)
    except (TypeError, ValueError) as exc:
        raise StrictDiscoveryMigrationError("predecessor strict progress is invalid") from exc
    portfolio_source = portfolio.get("source")
    if not isinstance(portfolio_source, Mapping):
        raise StrictDiscoveryMigrationError("portfolio source provenance disappeared")
    source_fields = (
        "ledger_path",
        "ledger_generation",
        "ledger_cursor",
        "manifest_path",
        "manifest_file_sha256",
        "manifest_sha256",
        "snapshot_identity",
        "snapshot_identity_sha256",
    )
    if (
        old_portfolio.get("path") != bound["portfolio_manifest_path"]
        or old_portfolio.get("file_sha256")
        != bound["portfolio_manifest_file_sha256"]
        or old_portfolio.get("portfolio_sha256") != portfolio.get("portfolio_sha256")
        or old_ranked.get("path") != str(ranked_path)
        or old_ranked.get("sha256") != bound["ranked_input"]["sha256"]
        or old_ranked.get("rows") != portfolio["ranked_input"].get("rows")
        or old_progress.get("sha256")
        != current_progress_identity["sha256"]
        or old_progress.get("progress_sha256")
        != current_progress.get("progress_sha256")
        or old_progress.get("next_row") != current_progress.get("next_row")
        or completed_prefix.get("next_row") != current_progress.get("next_row")
        or completed_prefix.get("completed_batches")
        != len(current_progress.get("batches", []))
        or any(old_stage2.get(name) != portfolio_source.get(name) for name in source_fields)
    ):
        raise StrictDiscoveryMigrationError(
            "predecessor evidence no longer matches the successor certificate"
        )
    expected_prefix = _completed_prefix_evidence(
        current_progress,
        portfolio,
        paths=paths,
        ranked_input_path=ranked_path,
    )
    if expected_prefix != completed_prefix:
        raise StrictDiscoveryMigrationError(
            "completed strict prefix changed after successor certification"
        )
    method = equivalence.get("method")
    if method != REBASE_EQUIVALENCE_METHOD:
        raise StrictDiscoveryMigrationError(
            "only the trusted patched scheduler migration method is accepted"
        )
    new_snapshot = _validate_snapshot_manifest(
        Path(str(successor_stage2.get("manifest", {}).get("path"))),
        run_root=paths.run_root,
        label="successor",
        require_manifest_stat=False,
    )
    for key in (
        "manifest",
        "binding_sha256",
        "identity",
        "snapshot_identity_sha256",
        "snapshot_rows",
        "eligible_rows",
        "counts",
        "chunks",
        "snapshot",
        "offsets",
    ):
        if new_snapshot[key] != successor_stage2.get(key):
            raise StrictDiscoveryMigrationError(
                "successor ranked snapshot changed after certification"
            )
    rebase = equivalence.get("identity_rebase")
    if not isinstance(rebase, Mapping):
        raise StrictDiscoveryMigrationError("identity rebase evidence is absent")
    validated_rebase = _validate_identity_rebase(
        Path(str(rebase.get("path"))),
        run_root=paths.run_root,
        live_ledger_path=Path(str(successor_stage2.get("ledger_path"))),
        portfolio=portfolio,
        ranked_input=portfolio["ranked_input"],
        old_identity=old_stage2["snapshot_identity"],
        old_identity_sha256=str(old_stage2["snapshot_identity_sha256"]),
        new_snapshot=new_snapshot,
        require_live_install_exact=False,
    )
    if validated_rebase != rebase:
        raise StrictDiscoveryMigrationError(
            "identity rebase certificate or immutable receipt changed"
        )
    successor_progress_path = path.parent / "progress.json"
    if not _lexists(successor_progress_path):
        raise StrictDiscoveryMigrationError("successor progress disappeared")
    successor_progress_raw, _ = _read_regular_json(
        successor_progress_path,
        run_root=paths.run_root,
        label="successor strict progress",
    )
    try:
        successor_progress = cli.validate_progress(successor_progress_raw)
    except (TypeError, ValueError) as exc:
        raise StrictDiscoveryMigrationError("successor strict progress is invalid") from exc
    migration_binding = successor_progress.get("successor_migration")
    if (
        lineage.get("progress") != str(successor_progress_path)
        or lineage.get("predecessor_progress_sha256")
        != old_progress.get("progress_sha256")
        or not isinstance(migration_binding, Mapping)
        or migration_binding.get("path") != str(path)
        or migration_binding.get("migration_sha256") != seal
        or migration_binding.get("predecessor_progress_sha256")
        != old_progress.get("progress_sha256")
        or successor_progress.get("source") != bound
    ):
        raise StrictDiscoveryMigrationError(
            "successor progress does not bind its immutable predecessor"
        )
    replay = _validate_successor_progress_extension(
        successor_progress,
        predecessor=current_progress,
        portfolio=portfolio,
        ranked_input_path=ranked_path,
        paths=paths,
        successor_root=path.parent,
        expected_snapshot_identity_sha256=str(
            successor_stage2["snapshot_identity_sha256"]
        ),
        expected_ledger_generation=int(successor_stage2["ledger_generation"]),
    )
    sidecar_owned = [
        str(digest)
        for artifact in replay.get("artifact_identities", [])
        if isinstance(artifact, Mapping)
        for digest in artifact.get("audited_digests", [])
    ]
    active_batch = successor_progress.get("active_batch")
    if isinstance(active_batch, Mapping):
        sidecar_owned.extend(
            str(digest) for digest in active_batch.get("selected_digests", [])
        )
    if len(sidecar_owned) != len(set(sidecar_owned)):
        raise StrictDiscoveryMigrationError(
            "successor strict ownership contains duplicate candidate digests"
        )
    current_fence = successor_live_source_validator(certificate)(
        portfolio,
        paths=paths,
        candidate_digests=sidecar_owned,
    )
    if current_fence.get("overlap") is not False:
        raise StrictDiscoveryMigrationError(
            "live foreground ownership overlaps successor strict evidence"
        )
    return certificate


def successor_sidecar_paths(paths: Any, certificate: Mapping[str, Any]) -> Any:
    """Return a SidecarPaths view that writes only successor progress/batches."""

    migration_sha256 = certificate.get("migration_sha256")
    if not _is_sha256(migration_sha256):
        raise StrictDiscoveryMigrationError("successor migration seal is invalid")
    root = paths.root / "successors" / str(migration_sha256)
    return replace(
        paths,
        root=root,
        progress=root / "progress.json",
        batches=root / "batches",
    )


def prepare_successor_batch_directory(
    paths: Any,
    batch_index: int | None = None,
) -> Path:
    """Create/validate successor batch paths through no-follow dirfds.

    The strict worker is the sole writer below a validated successor root.  A
    pre-existing symlink or non-directory at either level is rejected before
    the audit backend can run.
    """

    root = Path(paths.root)
    if root.parent.name != "successors" or not _is_sha256(root.name):
        raise StrictDiscoveryMigrationError(
            "successor batch root is not a content-addressed lineage root"
        )
    _, descriptor = _open_confined_directory(
        root,
        run_root=paths.run_root,
        label="strict successor root",
    )
    os.close(descriptor)
    batches = root / "batches"
    _, descriptor = _open_confined_directory(
        batches,
        run_root=paths.run_root,
        label="strict successor batches",
        create=True,
    )
    os.close(descriptor)
    if batch_index is None:
        return batches
    if (
        isinstance(batch_index, bool)
        or not isinstance(batch_index, int)
        or batch_index < 0
    ):
        raise StrictDiscoveryMigrationError("successor batch index is invalid")
    batch_root = batches / f"batch-{batch_index:04d}"
    _, descriptor = _open_confined_directory(
        batch_root,
        run_root=paths.run_root,
        label=f"strict successor batch {batch_index}",
        create=True,
    )
    os.close(descriptor)
    return batch_root


def _validated_live_ledger(
    ledger_path: Path,
    *,
    run_root: Path,
    expected_binding_sha256: str,
    expected_snapshot_identity_sha256: str,
    expected_snapshot_rows: int,
    expected_eligible_rows: int,
) -> tuple[dict[str, Any], dict[str, Any]]:
    from evaluation.selection_ledger import validate_selection_ledger

    ledger, ledger_identity = _read_regular_json(
        ledger_path,
        run_root=run_root,
        label="live Stage 2 ledger",
    )
    try:
        validated = validate_selection_ledger(
            ledger,
            binding_sha256=expected_binding_sha256,
            snapshot_identity_sha256_value=expected_snapshot_identity_sha256,
            snapshot_rows=expected_snapshot_rows,
            eligible_rows=expected_eligible_rows,
        )
    except (TypeError, ValueError) as exc:
        raise StrictDiscoveryMigrationError(
            "live successor Stage 2 ledger identity/seal is invalid"
        ) from exc
    return validated, ledger_identity


def successor_live_source_validator(
    certificate: Mapping[str, Any],
) -> Any:
    """Build the per-batch live-source fence for a validated successor."""

    successor = certificate.get("successor")
    if not isinstance(successor, Mapping) or not isinstance(
        successor.get("stage2_source"), Mapping
    ):
        raise StrictDiscoveryMigrationError("successor Stage 2 source is absent")
    certified_source = dict(successor["stage2_source"])
    baseline_generation = certified_source.get("ledger_generation")
    baseline_cursor = certified_source.get("ledger_cursor")
    baseline_progress = certified_source.get("ledger_progress_sha256")
    baseline_pages = certified_source.get("ledger_completed_pages")
    baseline_last_ack = certified_source.get("ledger_last_ack_sha256")
    baseline_pending_page = certified_source.get(
        "ledger_pending_page_sha256"
    )
    baseline_committed_count = certified_source.get("ledger_committed_count")
    baseline_committed_sha256 = certified_source.get("ledger_committed_sha256")
    baseline_static_sha256 = certified_source.get("ledger_static_sha256")
    baseline_deferred_count = certified_source.get("ledger_deferred_count")
    baseline_deferred_sha256 = certified_source.get("ledger_deferred_sha256")

    def validate(
        _manifest: Mapping[str, Any],
        *,
        paths: Any,
        candidate_digests: Iterable[str],
    ) -> dict[str, Any]:
        manifest = certified_source.get("manifest")
        if not isinstance(manifest, Mapping):
            raise StrictDiscoveryMigrationError(
                "certified successor manifest identity is absent"
            )
        manifest_path = _confined_regular_path(
            str(manifest.get("path")),
            run_root=paths.run_root,
            label="live successor snapshot manifest",
        )
        observed_manifest, manifest_file = _read_regular_json(
            manifest_path,
            run_root=paths.run_root,
            label="live successor snapshot manifest",
        )
        unsigned = dict(observed_manifest)
        observed_seal = unsigned.pop("manifest_sha256", None)
        if (
            manifest_file["sha256"] != manifest.get("file_sha256")
            or observed_seal != manifest.get("manifest_sha256")
            or observed_seal != _sha256(unsigned)
        ):
            raise StrictDiscoveryMigrationError(
                "ranked snapshot manifest changed after successor migration"
            )
        for key, label in (("snapshot", "live successor snapshot"), ("offsets", "live successor offsets")):
            identity = certified_source.get(key)
            if not isinstance(identity, Mapping):
                raise StrictDiscoveryMigrationError(
                    f"certified {label} identity is absent"
                )
            _check_bound_file(
                identity, run_root=paths.run_root, label=label
            )
        ledger_path = _confined_regular_path(
            str(certified_source.get("ledger_path")),
            run_root=paths.run_root,
            label="live successor Stage 2 ledger",
        )
        validated, ledger_identity = _validated_live_ledger(
            ledger_path,
            run_root=paths.run_root,
            expected_binding_sha256=str(certified_source["binding_sha256"]),
            expected_snapshot_identity_sha256=str(
                certified_source["snapshot_identity_sha256"]
            ),
            expected_snapshot_rows=int(certified_source["snapshot_rows"]),
            expected_eligible_rows=int(certified_source["eligible_rows"]),
        )
        completed_pages = validated.get("completed_pages")
        committed = validated.get("committed_digests")
        ack_chain = validated.get("ack_chain")
        prefix_ack = (
            validated.get("genesis_sha256")
            if baseline_pages == 0
            else (
                ack_chain[int(baseline_pages) - 1].get("ack_sha256")
                if isinstance(ack_chain, list)
                and isinstance(baseline_pages, int)
                and not isinstance(baseline_pages, bool)
                and len(ack_chain) >= baseline_pages
                and isinstance(ack_chain[baseline_pages - 1], Mapping)
                else None
            )
        )
        committed_prefix = (
            committed[: int(baseline_committed_count)]
            if isinstance(committed, list)
            and isinstance(baseline_committed_count, int)
            and not isinstance(baseline_committed_count, bool)
            and len(committed) >= baseline_committed_count
            else None
        )
        first_new_page = (
            ack_chain[baseline_pages].get("page_sha256")
            if isinstance(ack_chain, list)
            and isinstance(baseline_pages, int)
            and not isinstance(baseline_pages, bool)
            and completed_pages > baseline_pages
            and len(ack_chain) > baseline_pages
            and isinstance(ack_chain[baseline_pages], Mapping)
            else None
        )
        deferred = validated.get("deferred_pages")
        deferred_prefix = (
            deferred[:baseline_deferred_count]
            if isinstance(deferred, list)
            and isinstance(baseline_deferred_count, int)
            and not isinstance(baseline_deferred_count, bool)
            and baseline_deferred_count >= 0
            and len(deferred) >= baseline_deferred_count
            else None
        )
        latest_ack_page = (
            ack_chain[-1].get("page_sha256")
            if isinstance(ack_chain, list)
            and ack_chain
            and isinstance(ack_chain[-1], Mapping)
            else None
        )
        acknowledged_at = validated.get("last_acknowledged_at")
        ack_metadata_valid = bool(
            (
                completed_pages == 0
                and latest_ack_page is None
                and validated.get("last_acknowledged_page_sha256") is None
                and acknowledged_at is None
            )
            or (
                isinstance(completed_pages, int)
                and not isinstance(completed_pages, bool)
                and completed_pages > 0
                and _is_sha256(latest_ack_page)
                and validated.get("last_acknowledged_page_sha256")
                == latest_ack_page
                and isinstance(acknowledged_at, str)
                and bool(acknowledged_at)
            )
        )
        if (
            not ack_metadata_valid
            or isinstance(baseline_generation, bool)
            or not isinstance(baseline_generation, int)
            or isinstance(baseline_cursor, bool)
            or not isinstance(baseline_cursor, int)
            or baseline_cursor < 0
            or not _is_sha256(baseline_progress)
            or not _is_sha256(baseline_last_ack)
            or not _is_sha256(baseline_pending_page)
            or not _is_sha256(baseline_committed_sha256)
            or not _is_sha256(baseline_static_sha256)
            or not _is_sha256(baseline_deferred_sha256)
            or validated.get("generation") != baseline_generation
            or isinstance(validated.get("cursor"), bool)
            or not isinstance(validated.get("cursor"), int)
            or validated["cursor"] < baseline_cursor
            or isinstance(completed_pages, bool)
            or not isinstance(completed_pages, int)
            or not isinstance(baseline_pages, int)
            or isinstance(baseline_pages, bool)
            or completed_pages < baseline_pages
            or prefix_ack != baseline_last_ack
            or not isinstance(committed_prefix, list)
            or _sha256(committed_prefix) != baseline_committed_sha256
            or _ledger_extension_static_sha256(validated)
            != baseline_static_sha256
            or not isinstance(deferred_prefix, list)
            or _ledger_deferred_prefix_sha256(deferred_prefix)
            != baseline_deferred_sha256
            or (
                completed_pages == baseline_pages
                and validated.get("progress_sha256") != baseline_progress
            )
            or (
                completed_pages > baseline_pages
                and baseline_pending_page is not None
                and first_new_page != baseline_pending_page
            )
        ):
            raise StrictDiscoveryMigrationError(
                "live Stage 2 source no longer extends the certified successor"
            )
        blocked = {str(value) for value in validated.get("committed_digests", [])}
        pending = validated.get("pending")
        if isinstance(pending, Mapping):
            page = (
                pending.get("page")
                if isinstance(pending.get("page"), Mapping)
                else pending
            )
            blocked.update(str(value) for value in page.get("selected_digests", []))
        requested = {str(value) for value in candidate_digests}
        overlap = sorted(requested.intersection(blocked))
        return {
            "successor_migration_sha256": certificate["migration_sha256"],
            "snapshot_identity_sha256": certified_source[
                "snapshot_identity_sha256"
            ],
            "ledger_file_sha256": ledger_identity["sha256"],
            "ledger_progress_sha256": validated.get("progress_sha256"),
            "ledger_last_ack_sha256": validated.get("last_ack_sha256"),
            "ledger_cursor": validated.get("cursor"),
            "ledger_generation": validated.get("generation"),
            "pending_page_sha256": (
                pending.get("page_sha256") if isinstance(pending, Mapping) else None
            ),
            "checked_candidates": len(requested),
            "overlap": bool(overlap),
            "blocked_digests": overlap,
            "check_scope": (
                "certified-successor pre-launch; sidecar never mutates foreground ownership"
            ),
        }

    return validate


__all__ = [
    "IDENTITY_REBASE_GATE",
    "IDENTITY_REBASE_SCHEMA_VERSION",
    "REBASE_EQUIVALENCE_METHOD",
    "SUCCESSOR_GATE",
    "SUCCESSOR_SCHEMA_VERSION",
    "StrictDiscoveryMigrationError",
    "create_successor_migration",
    "load_successor_migration",
    "prepare_successor_batch_directory",
    "successor_live_source_validator",
    "successor_sidecar_paths",
]
