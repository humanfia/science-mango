"""Batched, fail-closed cache adapter for the Stage 2 structural screen.

The authoritative structural implementation deliberately persists one v1 JSON
file per result.  That is a useful interchange/recovery format, but hundreds of
thousands of file and directory fsyncs dominate a large Stage 2 replay.  This
module leaves :mod:`evaluation.structural_dedup` untouched and temporarily
adapts its validated read/write hooks to immutable, content-addressed JSONL
shards.  A self-hashed manifest is committed only after every shard is durable.

The adapter accepts evidence in this order:

* an already committed and fully validated pack;
* the ordinary Stage 2 v1 entry at the exact requested key;
* a Stage 1 v1 annotation whose only input difference is removing two true
  ``reported_n/k_matches`` checks; or
* an exact ordered Stage 1 pair alias whose replay validates for the Stage 2
  pair dimensions.

It never treats a canonical digest alone as pair evidence.  Stage 1 roots are
derived only from explicit ``rounds/round-NNN/candidate-batch.jsonl`` inputs.
"""

from __future__ import annotations

import copy
import fcntl
import hashlib
import json
import os
import re
import stat
import tempfile
import threading
from collections import OrderedDict
from contextlib import contextmanager
from dataclasses import dataclass
from pathlib import Path
from typing import Any, Iterable, Iterator, Mapping, Sequence

from evaluation import structural_dedup as _structural

PACK_SCHEMA_VERSION = 1
PACK_KIND = "qcode-stage2-structural-pack-v1"
PACK_DIRECTORY = "stage2-structural-pack-v1"
PACK_MANIFEST = "manifest.json"
PACK_CHUNK_ROWS = 1024
_ROUND_DIRECTORY = re.compile(r"round-[0-9]+")
_SHA256 = re.compile(r"[0-9a-f]{64}")
_PATCH_LOCK = threading.RLock()


class Stage2StructuralPackError(RuntimeError):
    """A committed Stage 2 structural pack failed validation."""


def _canonical_bytes(value: Any) -> bytes:
    try:
        return json.dumps(
            value,
            ensure_ascii=False,
            allow_nan=False,
            sort_keys=True,
            separators=(",", ":"),
        ).encode("utf-8")
    except (TypeError, ValueError) as exc:
        raise Stage2StructuralPackError(
            "Stage 2 structural pack contains non-canonical JSON"
        ) from exc


def _sha256_bytes(value: bytes) -> str:
    return hashlib.sha256(value).hexdigest()


def _sha256_json(value: Any) -> str:
    return _sha256_bytes(_canonical_bytes(value))


def _is_sha256(value: Any) -> bool:
    return isinstance(value, str) and _SHA256.fullmatch(value) is not None


def _reject_symlink_components(path: Path, *, role: str) -> None:
    """Reject symlinks in every existing component of one absolute path."""

    absolute = path.absolute()
    for component in reversed((absolute, *absolute.parents)):
        try:
            metadata = component.lstat()
        except FileNotFoundError:
            continue
        if stat.S_ISLNK(metadata.st_mode):
            raise Stage2StructuralPackError(
                f"{role} path contains a symlink: {component}"
            )


def _read_regular_file(path: Path, *, role: str) -> bytes:
    """Read one file without following it or an ancestor symlink."""

    _reject_symlink_components(path, role=role)
    try:
        metadata = path.lstat()
    except FileNotFoundError:
        raise
    if stat.S_ISLNK(metadata.st_mode):
        raise Stage2StructuralPackError(f"{role} may not be a symlink: {path}")
    if not stat.S_ISREG(metadata.st_mode):
        raise Stage2StructuralPackError(f"{role} is not a regular file: {path}")
    flags = os.O_RDONLY | getattr(os, "O_NOFOLLOW", 0)
    try:
        descriptor = os.open(path, flags)
    except OSError as exc:
        raise Stage2StructuralPackError(f"cannot open {role}: {path}") from exc
    try:
        opened = os.fstat(descriptor)
        if (
            not stat.S_ISREG(opened.st_mode)
            or opened.st_dev != metadata.st_dev
            or opened.st_ino != metadata.st_ino
        ):
            raise Stage2StructuralPackError(f"{role} changed while opening: {path}")
        chunks: list[bytes] = []
        while True:
            chunk = os.read(descriptor, 1024 * 1024)
            if not chunk:
                break
            chunks.append(chunk)
        return b"".join(chunks)
    finally:
        os.close(descriptor)


def _validate_directory(path: Path, *, role: str, create: bool = False) -> None:
    _reject_symlink_components(path, role=role)
    if path.is_symlink():
        raise Stage2StructuralPackError(f"{role} may not be a symlink: {path}")
    if create:
        path.mkdir(parents=True, exist_ok=True)
        _reject_symlink_components(path, role=role)
    if path.exists() and not path.is_dir():
        raise Stage2StructuralPackError(f"{role} is not a directory: {path}")


def _fsync_directory(path: Path) -> None:
    descriptor = os.open(path, os.O_RDONLY | getattr(os, "O_DIRECTORY", 0))
    try:
        os.fsync(descriptor)
    finally:
        os.close(descriptor)


def _atomic_write(path: Path, payload: bytes) -> None:
    _validate_directory(path.parent, role="pack output directory", create=True)
    descriptor, temporary_name = tempfile.mkstemp(
        prefix=f".{path.name}.tmp-", dir=path.parent
    )
    temporary = Path(temporary_name)
    try:
        with os.fdopen(descriptor, "wb") as stream:
            stream.write(payload)
            stream.flush()
            os.fsync(stream.fileno())
        os.replace(temporary, path)
        _fsync_directory(path.parent)
    finally:
        try:
            temporary.unlink()
        except FileNotFoundError:
            pass


def _write_immutable(path: Path, payload: bytes) -> None:
    """Install one hash-named shard, accepting an identical prior file."""

    _validate_directory(path.parent, role="pack shard directory", create=True)
    if path.exists() or path.is_symlink():
        observed = _read_regular_file(path, role="pack shard")
        if observed != payload:
            raise Stage2StructuralPackError(
                f"content-addressed pack shard has conflicting bytes: {path}"
            )
        return
    descriptor, temporary_name = tempfile.mkstemp(
        prefix=f".{path.name}.tmp-", dir=path.parent
    )
    temporary = Path(temporary_name)
    try:
        with os.fdopen(descriptor, "wb") as stream:
            stream.write(payload)
            stream.flush()
            os.fsync(stream.fileno())
        # The content hash makes an existing destination equivalent.  Replace
        # is atomic and does not expose a partial shard.
        os.replace(temporary, path)
        _fsync_directory(path.parent)
    finally:
        try:
            temporary.unlink()
        except FileNotFoundError:
            pass


def _entry_seal(entry: Mapping[str, Any]) -> str:
    unsigned = dict(entry)
    unsigned.pop("seal_sha256", None)
    return _sha256_json(unsigned)


def _validate_annotation_entry(entry: Any) -> None:
    expected = {
        "schema_version",
        "input",
        "input_sha256",
        "runtime_sha256",
        "status",
        "annotation",
        "failure",
        "attempt_count",
        "seal_sha256",
    }
    if not isinstance(entry, dict) or set(entry) != expected:
        raise Stage2StructuralPackError("packed annotation v1 schema is invalid")
    if (
        entry["schema_version"] != _structural.STRUCTURAL_SCREEN_CACHE_SCHEMA_VERSION
        or not _is_sha256(entry["input_sha256"])
        or entry["input_sha256"] != _sha256_json(entry["input"])
        or not _is_sha256(entry["runtime_sha256"])
        or entry["seal_sha256"] != _entry_seal(entry)
        or isinstance(entry["attempt_count"], bool)
        or not isinstance(entry["attempt_count"], int)
        or entry["attempt_count"] < 1
    ):
        raise Stage2StructuralPackError("packed annotation v1 integrity check failed")
    if entry["status"] == "complete":
        if entry["failure"] is not None:
            raise Stage2StructuralPackError(
                "complete packed annotation carries a failure"
            )
        try:
            _structural._validate_annotation_payload(entry["annotation"])
        except Exception as exc:
            raise Stage2StructuralPackError(
                "packed annotation payload failed authoritative validation"
            ) from exc
    elif entry["status"] == "unresolved":
        if (
            entry["annotation"] is not None
            or not isinstance(entry["failure"], dict)
            or entry["failure"].get("retryable") is not True
        ):
            raise Stage2StructuralPackError(
                "packed unresolved annotation is not retryable"
            )
    else:
        raise Stage2StructuralPackError("packed annotation status is invalid")


def _validate_pair_entry(entry: Any) -> None:
    expected = {
        "schema_version",
        "input",
        "input_sha256",
        "runtime_sha256",
        "status",
        "replay",
        "failure",
        "attempt_count",
        "seal_sha256",
    }
    if not isinstance(entry, dict) or set(entry) != expected:
        raise Stage2StructuralPackError("packed pair v1 schema is invalid")
    if (
        entry["schema_version"] != _structural.STRUCTURAL_PAIR_CACHE_SCHEMA_VERSION
        or not _is_sha256(entry["input_sha256"])
        or entry["input_sha256"] != _sha256_json(entry["input"])
        or not _is_sha256(entry["runtime_sha256"])
        or entry["seal_sha256"] != _entry_seal(entry)
        or isinstance(entry["attempt_count"], bool)
        or not isinstance(entry["attempt_count"], int)
        or entry["attempt_count"] < 1
    ):
        raise Stage2StructuralPackError("packed pair v1 integrity check failed")
    if entry["status"] == "complete":
        if entry["failure"] is not None:
            raise Stage2StructuralPackError("complete packed pair carries a failure")
        try:
            _structural._validate_pair_replay_payload(
                entry["replay"], pair_input=entry["input"]
            )
        except Exception as exc:
            raise Stage2StructuralPackError(
                "packed pair replay failed authoritative validation"
            ) from exc
    elif entry["status"] == "unresolved":
        if (
            entry["replay"] is not None
            or not isinstance(entry["failure"], dict)
            or entry["failure"].get("retryable") is not True
        ):
            raise Stage2StructuralPackError("packed unresolved pair is not retryable")
    else:
        raise Stage2StructuralPackError("packed pair status is invalid")


def _validate_record(record: Any) -> None:
    if not isinstance(record, dict) or set(record) != {
        "kind",
        "key",
        "entry",
        "origin",
    }:
        raise Stage2StructuralPackError("pack record schema is invalid")
    if record["kind"] not in {"annotation", "pair"}:
        raise Stage2StructuralPackError("pack record kind is invalid")
    if not _is_sha256(record["key"]):
        raise Stage2StructuralPackError("pack record key is invalid")
    if not isinstance(record["origin"], dict):
        raise Stage2StructuralPackError("pack record provenance is invalid")
    if record["kind"] == "annotation":
        _validate_annotation_entry(record["entry"])
    else:
        _validate_pair_entry(record["entry"])
    if record["entry"]["input_sha256"] != record["key"]:
        raise Stage2StructuralPackError("pack record key does not bind its entry")


def _manifest_seal(manifest: Mapping[str, Any]) -> str:
    unsigned = dict(manifest)
    unsigned.pop("manifest_sha256", None)
    return _sha256_json(unsigned)


@contextmanager
def _exclusive_pack_lock(cache_dir: Path) -> Iterator[None]:
    """Serialize manifest generations across Stage 2 CLI processes."""

    cache_dir = Path(cache_dir)
    _validate_directory(cache_dir, role="Stage 2 structural cache", create=True)
    pack_dir = cache_dir / PACK_DIRECTORY
    _validate_directory(pack_dir, role="Stage 2 pack", create=True)
    lock_path = pack_dir / ".pack.lock"
    _reject_symlink_components(lock_path, role="Stage 2 pack lock")
    flags = os.O_RDWR | os.O_CREAT | getattr(os, "O_NOFOLLOW", 0)
    try:
        descriptor = os.open(lock_path, flags, 0o600)
    except OSError as exc:
        raise Stage2StructuralPackError(
            f"cannot open Stage 2 pack lock: {lock_path}"
        ) from exc
    try:
        if not stat.S_ISREG(os.fstat(descriptor).st_mode):
            raise Stage2StructuralPackError(
                f"Stage 2 pack lock is not a regular file: {lock_path}"
            )
        fcntl.flock(descriptor, fcntl.LOCK_EX)
        yield
    finally:
        try:
            fcntl.flock(descriptor, fcntl.LOCK_UN)
        finally:
            os.close(descriptor)


def _file_binding(path: Path) -> dict[str, Any]:
    payload = _read_regular_file(path, role="Stage 2 input")
    return {
        "path": str(path.absolute()),
        "size": len(payload),
        "sha256": _sha256_bytes(payload),
    }


def discover_stage1_cache_roots(paths: Iterable[Path]) -> tuple[Path, ...]:
    """Discover Stage 1 roots from exact candidate-batch round paths only."""

    roots: dict[str, Path] = {}
    for raw_path in paths:
        path = Path(raw_path).absolute()
        round_dir = path.parent
        rounds_dir = round_dir.parent
        run_root = rounds_dir.parent
        if (
            path.name != "candidate-batch.jsonl"
            or _ROUND_DIRECTORY.fullmatch(round_dir.name) is None
            or rounds_dir.name != "rounds"
        ):
            continue
        cache_root = run_root / "structural-screen-cache-v1"
        if not cache_root.exists() and not cache_root.is_symlink():
            continue
        _validate_directory(cache_root, role="Stage 1 structural cache")
        roots[str(cache_root)] = cache_root
    return tuple(roots[name] for name in sorted(roots))


def make_stage1_annotation_aliases(
    rows: Sequence[dict[str, Any]],
    reported: Sequence[tuple[Any, Any]],
) -> dict[str, tuple[dict[str, Any], ...]]:
    """Map Stage 2 absent-report inputs to exact Stage 1 report aliases."""

    aliases: dict[str, dict[str, dict[str, Any]]] = {}
    for row, (reported_n, reported_k) in zip(rows, reported, strict=True):
        if type(reported_n) is not int or type(reported_k) is not int:
            continue
        target = _structural._normalized_screen_input(row)
        if target.get("reported_n") != {"present": False, "value": None} or target.get(
            "reported_k"
        ) != {"present": False, "value": None}:
            continue
        alias = copy.deepcopy(target)
        alias["reported_n"] = {"present": True, "value": reported_n}
        alias["reported_k"] = {"present": True, "value": reported_k}
        target_sha256 = _sha256_json(target)
        aliases.setdefault(target_sha256, {})[_sha256_json(alias)] = alias
    return {
        key: tuple(by_alias[name] for name in sorted(by_alias))
        for key, by_alias in aliases.items()
    }


@dataclass(frozen=True)
class _RecordLocation:
    path: Path
    offset: int
    length: int


class _PackAdapter:
    def __init__(
        self,
        *,
        cache_dir: Path,
        runtime_sha256: str,
        input_paths: Sequence[Path],
        stage1_aliases: Mapping[str, Sequence[dict[str, Any]]],
        enable_stage1_import: bool,
        chunk_rows: int,
    ) -> None:
        if not _is_sha256(runtime_sha256):
            raise Stage2StructuralPackError("structural runtime fingerprint is invalid")
        if (
            isinstance(chunk_rows, bool)
            or not isinstance(chunk_rows, int)
            or chunk_rows < 1
        ):
            raise ValueError("chunk_rows must be a positive integer")
        self.cache_dir = Path(cache_dir)
        _validate_directory(
            self.cache_dir, role="Stage 2 structural cache", create=True
        )
        self.pack_dir = self.cache_dir / PACK_DIRECTORY
        _validate_directory(self.pack_dir, role="Stage 2 pack", create=True)
        self.chunks_dir = self.pack_dir / "shards"
        if self.chunks_dir.exists() or self.chunks_dir.is_symlink():
            _validate_directory(self.chunks_dir, role="Stage 2 pack shards")
        self.manifest_path = self.pack_dir / PACK_MANIFEST
        if self.manifest_path.is_symlink():
            raise Stage2StructuralPackError(
                f"pack manifest may not be a symlink: {self.manifest_path}"
            )
        self.runtime_sha256 = runtime_sha256
        self.adapter_source_sha256 = hashlib.sha256(
            Path(__file__).resolve().read_bytes()
        ).hexdigest()
        self.input_paths = tuple(Path(path).absolute() for path in input_paths)
        # Stage 1 v1 entries are individually sealed, but their directory is
        # not yet authenticated as a Stage 2 controller input.  Keep the
        # verified derivation bridge explicit and off in production.
        self.stage1_roots = (
            discover_stage1_cache_roots(self.input_paths)
            if enable_stage1_import
            else ()
        )
        self.stage1_aliases = {
            key: tuple(copy.deepcopy(list(values)))
            for key, values in stage1_aliases.items()
        }
        self.source_binding = {
            "inputs": [_file_binding(path) for path in self.input_paths],
            "stage1_cache_roots": [str(path) for path in self.stage1_roots],
        }
        self.source_binding_sha256 = _sha256_json(self.source_binding)
        self.chunk_rows = chunk_rows
        self.index: dict[tuple[str, str], _RecordLocation] = {}
        self.pending: list[dict[str, Any]] = []
        self.pending_latest: dict[tuple[str, str], dict[str, Any]] = {}
        self.active_chunks: list[dict[str, Any]] = []
        self.new_chunks: list[dict[str, Any]] = []
        self._shard_cache: OrderedDict[Path, bytes] = OrderedDict()
        self._shard_integrity: dict[Path, tuple[str, int]] = {}
        self.valid_manifest = False
        self.stats = {
            "pack_hits": 0,
            "stage2_v1_imports": 0,
            "stage1_annotation_derivations": 0,
            "stage1_pair_derivations": 0,
            "computed_writes": 0,
            "stale_pack": False,
        }
        self._load_manifest()

        self.original_read_annotation = _structural._read_cache_entry
        self.original_write_annotation = _structural._write_cache_entry
        self.original_read_pair = _structural._read_pair_cache_entry
        self.original_write_pair = _structural._write_pair_cache_entry

    def _load_manifest(self) -> None:
        if not self.manifest_path.exists():
            return
        try:
            manifest = json.loads(
                _read_regular_file(self.manifest_path, role="Stage 2 pack manifest")
            )
        except (UnicodeDecodeError, json.JSONDecodeError) as exc:
            raise Stage2StructuralPackError(
                "cannot decode Stage 2 pack manifest"
            ) from exc
        expected = {
            "schema_version",
            "kind",
            "runtime_sha256",
            "adapter_source_sha256",
            "source_binding",
            "source_binding_sha256",
            "chunks",
            "record_count",
            "statistics",
            "manifest_sha256",
        }
        if not isinstance(manifest, dict) or set(manifest) != expected:
            raise Stage2StructuralPackError("Stage 2 pack manifest schema is invalid")
        if (
            manifest["schema_version"] != PACK_SCHEMA_VERSION
            or manifest["kind"] != PACK_KIND
            or not _is_sha256(manifest["runtime_sha256"])
            or not _is_sha256(manifest["adapter_source_sha256"])
            or manifest["source_binding_sha256"]
            != _sha256_json(manifest["source_binding"])
            or manifest["manifest_sha256"] != _manifest_seal(manifest)
            or not isinstance(manifest["chunks"], list)
            or isinstance(manifest["record_count"], bool)
            or not isinstance(manifest["record_count"], int)
            or manifest["record_count"] < 0
            or not isinstance(manifest["statistics"], dict)
        ):
            raise Stage2StructuralPackError(
                "Stage 2 pack manifest integrity check failed"
            )
        # A clean manifest from another runtime or immutable input set is
        # stale evidence.  Ignore it before touching its shards; current-bound
        # manifest or shard corruption remains a hard failure.
        if (
            manifest["runtime_sha256"] != self.runtime_sha256
            or manifest["adapter_source_sha256"] != self.adapter_source_sha256
            or manifest["source_binding_sha256"] != self.source_binding_sha256
            or manifest["source_binding"] != self.source_binding
        ):
            self.stats["stale_pack"] = True
            return

        count = 0
        seen_names: set[str] = set()
        loaded_index: dict[tuple[str, str], _RecordLocation] = {}
        loaded_integrity: dict[Path, tuple[str, int]] = {}
        for descriptor in manifest["chunks"]:
            if not isinstance(descriptor, dict) or set(descriptor) != {
                "name",
                "sha256",
                "bytes",
                "rows",
            }:
                raise Stage2StructuralPackError("pack chunk descriptor is invalid")
            name = descriptor["name"]
            digest = descriptor["sha256"]
            if (
                not isinstance(name, str)
                or not _is_sha256(digest)
                or name != f"{digest}.jsonl"
                or name in seen_names
                or isinstance(descriptor["bytes"], bool)
                or not isinstance(descriptor["bytes"], int)
                or descriptor["bytes"] < 1
                or isinstance(descriptor["rows"], bool)
                or not isinstance(descriptor["rows"], int)
                or descriptor["rows"] < 1
            ):
                raise Stage2StructuralPackError(
                    "pack chunk descriptor integrity check failed"
                )
            seen_names.add(name)
            path = self.chunks_dir / name
            payload = _read_regular_file(path, role="Stage 2 pack shard")
            if len(payload) != descriptor["bytes"] or _sha256_bytes(payload) != digest:
                raise Stage2StructuralPackError(
                    f"Stage 2 pack shard hash mismatch: {path}"
                )
            loaded_integrity[path] = (digest, descriptor["bytes"])
            offset = 0
            rows = 0
            for line in payload.splitlines(keepends=True):
                if not line.endswith(b"\n") or line == b"\n":
                    raise Stage2StructuralPackError(
                        f"Stage 2 pack shard framing is invalid: {path}"
                    )
                try:
                    record = json.loads(line)
                except (UnicodeDecodeError, json.JSONDecodeError) as exc:
                    raise Stage2StructuralPackError(
                        f"cannot decode Stage 2 pack shard: {path}"
                    ) from exc
                _validate_record(record)
                loaded_index[(record["kind"], record["key"])] = _RecordLocation(
                    path, offset, len(line)
                )
                offset += len(line)
                rows += 1
            if rows != descriptor["rows"] or offset != len(payload):
                raise Stage2StructuralPackError(
                    f"Stage 2 pack shard row count mismatch: {path}"
                )
            count += rows
        if count != manifest["record_count"]:
            raise Stage2StructuralPackError(
                "Stage 2 pack manifest record count mismatch"
            )

        self.index = loaded_index
        self._shard_integrity = loaded_integrity
        self.active_chunks = [dict(item) for item in manifest["chunks"]]
        self.valid_manifest = True

    def _record_at(self, location: _RecordLocation) -> dict[str, Any]:
        payload = self._shard_cache.get(location.path)
        if payload is None:
            expected = self._shard_integrity.get(location.path)
            if expected is None:
                raise Stage2StructuralPackError(
                    f"pack index has no shard integrity binding: {location.path}"
                )
            payload = _read_regular_file(location.path, role="Stage 2 pack shard")
            digest, expected_bytes = expected
            if len(payload) != expected_bytes or _sha256_bytes(payload) != digest:
                raise Stage2StructuralPackError(
                    f"Stage 2 pack shard changed after manifest load: {location.path}"
                )
            self._shard_cache[location.path] = payload
            self._shard_cache.move_to_end(location.path)
            while len(self._shard_cache) > 8:
                self._shard_cache.popitem(last=False)
        line = payload[location.offset : location.offset + location.length]
        try:
            record = json.loads(line)
        except (UnicodeDecodeError, json.JSONDecodeError) as exc:
            raise Stage2StructuralPackError(
                f"cannot decode indexed Stage 2 pack record: {location.path}"
            ) from exc
        _validate_record(record)
        return record

    def _lookup(self, kind: str, key: str) -> dict[str, Any] | None:
        pending = self.pending_latest.get((kind, key))
        if pending is not None:
            return copy.deepcopy(pending["entry"])
        location = self.index.get((kind, key))
        if location is None:
            return None
        record = self._record_at(location)
        if record["kind"] != kind or record["key"] != key:
            raise Stage2StructuralPackError("pack index resolved the wrong record")
        self.stats["pack_hits"] += 1
        return copy.deepcopy(record["entry"])

    def _capture(
        self,
        kind: str,
        entry: dict[str, Any],
        origin: dict[str, Any],
    ) -> None:
        validator = (
            _validate_annotation_entry if kind == "annotation" else _validate_pair_entry
        )
        validator(entry)
        record = {
            "kind": kind,
            "key": entry["input_sha256"],
            "entry": copy.deepcopy(entry),
            "origin": copy.deepcopy(origin),
        }
        _validate_record(record)
        self.pending.append(record)
        self.pending_latest[(kind, entry["input_sha256"])] = record
        if len(self.pending) >= self.chunk_rows:
            self._flush_pending()

    def _publish_manifest(self) -> None:
        """Publish the ordered durable shard prefix atomically."""

        if not self.active_chunks:
            return
        manifest = {
            "schema_version": PACK_SCHEMA_VERSION,
            "kind": PACK_KIND,
            "runtime_sha256": self.runtime_sha256,
            "adapter_source_sha256": self.adapter_source_sha256,
            "source_binding": self.source_binding,
            "source_binding_sha256": self.source_binding_sha256,
            "chunks": self.active_chunks,
            "record_count": sum(item["rows"] for item in self.active_chunks),
            "statistics": copy.deepcopy(self.stats),
            "manifest_sha256": "",
        }
        manifest["manifest_sha256"] = _manifest_seal(manifest)
        _atomic_write(self.manifest_path, _canonical_bytes(manifest) + b"\n")
        self.valid_manifest = True

    def _flush_pending(self) -> None:
        if not self.pending:
            return
        lines = [_canonical_bytes(record) + b"\n" for record in self.pending]
        payload = b"".join(lines)
        digest = _sha256_bytes(payload)
        descriptor = {
            "name": f"{digest}.jsonl",
            "sha256": digest,
            "bytes": len(payload),
            "rows": len(lines),
        }
        path = self.chunks_dir / descriptor["name"]
        _write_immutable(path, payload)
        self._shard_integrity[path] = (digest, len(payload))
        offset = 0
        for record, line in zip(self.pending, lines, strict=True):
            self.index[(record["kind"], record["key"])] = _RecordLocation(
                path, offset, len(line)
            )
            offset += len(line)
        if descriptor not in self.active_chunks:
            self.active_chunks.append(descriptor)
            self.new_chunks.append(descriptor)
        self.pending.clear()
        self.pending_latest.clear()
        # Each full shard becomes restart-visible immediately.  A signal can
        # lose only the final partial in-memory batch.
        self._publish_manifest()

    def _stage1_annotation(
        self, screen_input: dict[str, Any], key: str
    ) -> dict[str, Any] | None:
        derived: dict[str, Any] | None = None
        for alias in self.stage1_aliases.get(key, ()):
            alias_sha256 = _sha256_json(alias)
            for root in self.stage1_roots:
                source_path = root / alias_sha256[:2] / f"{alias_sha256}.json"
                source = self.original_read_annotation(
                    source_path,
                    screen_input=alias,
                    input_sha256=alias_sha256,
                    runtime_sha256=self.runtime_sha256,
                )
                if source is None or source["status"] != "complete":
                    continue
                annotation = copy.deepcopy(source["annotation"])
                static = annotation.get("static_eligibility")
                checks = static.get("checks") if isinstance(static, dict) else None
                reported_n = alias["reported_n"]["value"]
                reported_k = alias["reported_k"]["value"]
                if (
                    not isinstance(checks, dict)
                    or checks.get("reported_n_matches") is not True
                    or checks.get("reported_k_matches") is not True
                    or static.get("n") != reported_n
                    or static.get("k") != reported_k
                ):
                    continue
                checks.pop("reported_n_matches")
                checks.pop("reported_k_matches")
                try:
                    _structural._validate_annotation_payload(annotation)
                except Exception as exc:
                    raise Stage2StructuralPackError(
                        "derived Stage 1 annotation failed absent-report validation"
                    ) from exc
                target = {
                    **source,
                    "input": copy.deepcopy(screen_input),
                    "input_sha256": key,
                    "annotation": annotation,
                    "seal_sha256": "",
                }
                target["seal_sha256"] = _entry_seal(target)
                _validate_annotation_entry(target)
                if derived is not None and derived != target:
                    raise Stage2StructuralPackError(
                        "validated Stage 1 aliases disagree on one annotation"
                    )
                derived = target
                provenance = {
                    "kind": "stage1_v1_report_checks_removed",
                    "cache_root": str(root),
                    "source_input_sha256": alias_sha256,
                }
        return None if derived is None else (derived, provenance)

    def read_annotation(
        self,
        path: Path,
        *,
        screen_input: dict[str, Any],
        input_sha256: str,
        runtime_sha256: str,
    ) -> dict[str, Any] | None:
        if runtime_sha256 != self.runtime_sha256:
            return self.original_read_annotation(
                path,
                screen_input=screen_input,
                input_sha256=input_sha256,
                runtime_sha256=runtime_sha256,
            )
        packed = self._lookup("annotation", input_sha256)
        if packed is not None:
            if (
                packed["input"] != screen_input
                or packed["runtime_sha256"] != runtime_sha256
            ):
                raise Stage2StructuralPackError(
                    "packed annotation does not match the requested input/runtime"
                )
            return packed
        entry = self.original_read_annotation(
            path,
            screen_input=screen_input,
            input_sha256=input_sha256,
            runtime_sha256=runtime_sha256,
        )
        if entry is not None:
            self.stats["stage2_v1_imports"] += 1
            self._capture("annotation", entry, {"kind": "stage2_v1_import"})
            return entry
        derived_result = self._stage1_annotation(screen_input, input_sha256)
        if derived_result is None:
            return None
        derived, provenance = derived_result
        self.stats["stage1_annotation_derivations"] += 1
        self._capture("annotation", derived, provenance)
        return derived

    def write_annotation(self, path: Path, **kwargs: Any) -> None:
        entry = {
            "schema_version": _structural.STRUCTURAL_SCREEN_CACHE_SCHEMA_VERSION,
            "input": copy.deepcopy(kwargs["screen_input"]),
            "input_sha256": kwargs["input_sha256"],
            "runtime_sha256": kwargs["runtime_sha256"],
            "status": kwargs["status"],
            "annotation": copy.deepcopy(kwargs["annotation"]),
            "failure": copy.deepcopy(kwargs["failure"]),
            "attempt_count": kwargs["attempt_count"],
            "seal_sha256": "",
        }
        entry["seal_sha256"] = _entry_seal(entry)
        self.stats["computed_writes"] += 1
        self._capture("annotation", entry, {"kind": "stage2_computed"})

    def _pair_aliases(self, pair_input: dict[str, Any]) -> Iterator[dict[str, Any]]:
        candidate_key = _sha256_json(pair_input["candidate"])
        representative_key = _sha256_json(pair_input["representative"])
        for candidate in self.stage1_aliases.get(candidate_key, ()):
            for representative in self.stage1_aliases.get(representative_key, ()):
                alias = copy.deepcopy(pair_input)
                alias["candidate"] = copy.deepcopy(candidate)
                alias["representative"] = copy.deepcopy(representative)
                yield alias

    def _stage1_pair(self, pair_input: dict[str, Any], key: str) -> Any:
        derived: dict[str, Any] | None = None
        provenance: dict[str, Any] | None = None
        for alias in self._pair_aliases(pair_input):
            alias_sha256 = _sha256_json(alias)
            for root in self.stage1_roots:
                source_path = (
                    root
                    / "within-pool-isomorphism-v1"
                    / alias_sha256[:2]
                    / f"{alias_sha256}.json"
                )
                _reject_symlink_components(source_path, role="Stage 1 pair cache entry")
                source = self.original_read_pair(
                    source_path,
                    pair_input=alias,
                    input_sha256=alias_sha256,
                    runtime_sha256=self.runtime_sha256,
                )
                if source is None or source["status"] != "complete":
                    continue
                try:
                    _structural._validate_pair_replay_payload(
                        source["replay"], pair_input=pair_input
                    )
                except Exception as exc:
                    raise Stage2StructuralPackError(
                        "Stage 1 pair replay failed Stage 2 dimension validation"
                    ) from exc
                target = {
                    **source,
                    "input": copy.deepcopy(pair_input),
                    "input_sha256": key,
                    "seal_sha256": "",
                }
                target["seal_sha256"] = _entry_seal(target)
                _validate_pair_entry(target)
                if derived is not None and derived != target:
                    raise Stage2StructuralPackError(
                        "validated Stage 1 aliases disagree on one pair replay"
                    )
                derived = target
                provenance = {
                    "kind": "stage1_v1_exact_ordered_pair_alias",
                    "cache_root": str(root),
                    "source_input_sha256": alias_sha256,
                }
        return None if derived is None else (derived, provenance)

    def read_pair(
        self,
        path: Path,
        *,
        pair_input: dict[str, Any],
        input_sha256: str,
        runtime_sha256: str,
    ) -> dict[str, Any] | None:
        if runtime_sha256 != self.runtime_sha256:
            return self.original_read_pair(
                path,
                pair_input=pair_input,
                input_sha256=input_sha256,
                runtime_sha256=runtime_sha256,
            )
        packed = self._lookup("pair", input_sha256)
        if packed is not None:
            if (
                packed["input"] != pair_input
                or packed["runtime_sha256"] != runtime_sha256
            ):
                raise Stage2StructuralPackError(
                    "packed pair does not match the requested input/runtime"
                )
            return packed
        entry = self.original_read_pair(
            path,
            pair_input=pair_input,
            input_sha256=input_sha256,
            runtime_sha256=runtime_sha256,
        )
        if entry is not None:
            self.stats["stage2_v1_imports"] += 1
            self._capture("pair", entry, {"kind": "stage2_v1_import"})
            return entry
        derived_result = self._stage1_pair(pair_input, input_sha256)
        if derived_result is None:
            return None
        derived, provenance = derived_result
        self.stats["stage1_pair_derivations"] += 1
        self._capture("pair", derived, provenance)
        return derived

    def write_pair(self, path: Path, **kwargs: Any) -> None:
        entry = {
            "schema_version": _structural.STRUCTURAL_PAIR_CACHE_SCHEMA_VERSION,
            "input": copy.deepcopy(kwargs["pair_input"]),
            "input_sha256": kwargs["input_sha256"],
            "runtime_sha256": kwargs["runtime_sha256"],
            "status": kwargs["status"],
            "replay": copy.deepcopy(kwargs["replay"]),
            "failure": copy.deepcopy(kwargs["failure"]),
            "attempt_count": kwargs["attempt_count"],
            "seal_sha256": "",
        }
        entry["seal_sha256"] = _entry_seal(entry)
        self.stats["computed_writes"] += 1
        self._capture("pair", entry, {"kind": "stage2_computed"})

    def commit(self) -> None:
        # _flush_pending publishes manifest-last.  If the context is
        # interrupted, previously full shards already remain committed.
        self._flush_pending()


@contextmanager
def packed_structural_cache(
    *,
    cache_dir: Path,
    runtime_sha256: str,
    input_paths: Sequence[Path],
    stage1_aliases: Mapping[str, Sequence[dict[str, Any]]],
    enable_stage1_import: bool = False,
    chunk_rows: int = PACK_CHUNK_ROWS,
) -> Iterator[Mapping[str, Any]]:
    """Adapt the existing structural screen to a batched durable cache."""

    with _PATCH_LOCK, _exclusive_pack_lock(cache_dir):
        adapter = _PackAdapter(
            cache_dir=cache_dir,
            runtime_sha256=runtime_sha256,
            input_paths=input_paths,
            stage1_aliases=stage1_aliases,
            enable_stage1_import=enable_stage1_import,
            chunk_rows=chunk_rows,
        )
        _structural._read_cache_entry = adapter.read_annotation
        _structural._write_cache_entry = adapter.write_annotation
        _structural._read_pair_cache_entry = adapter.read_pair
        _structural._write_pair_cache_entry = adapter.write_pair
        try:
            yield adapter.stats
        except BaseException:
            # Unmanifested partial shards are ignored; every earlier full
            # shard was already committed by _flush_pending.
            raise
        else:
            adapter.commit()
        finally:
            _structural._read_cache_entry = adapter.original_read_annotation
            _structural._write_cache_entry = adapter.original_write_annotation
            _structural._read_pair_cache_entry = adapter.original_read_pair
            _structural._write_pair_cache_entry = adapter.original_write_pair
