#!/usr/bin/env python3
"""TEST_ONLY exact-resume controller for one CaDiCaL process under DMTCP.

This is deliberately isolated from the production proof runner.  It is a
fault-injection harness for checking whether DMTCP 4.2.0 can preserve a live
CaDiCaL search and its ordinary, append-only DRAT file across a process
restart.  Nothing emitted here is a production distance certificate.

The durable layout is generation based.  Every mutating operation first
publishes an immutable, canonical, self-hashed claim.  A claim without its
matching commit poisons the root; it is never guessed or repaired.  Each
generation gets a fresh checkpoint directory, and a checkpoint is consumed
at most once.  An OS lock serializes commands while the immutable claims stop
double resume after the lock is released.

The proof is intentionally an ordinary file.  DMTCP's ``--ckpt-open-files``
and ``DMTCP_SKIP_TRUNCATE_FILE_AT_RESTART`` mechanisms are forbidden.  The
default DMTCP file plugin must reopen the proof, truncate an injected stale
suffix to the checkpointed size, and seek to the saved offset.  A final DRAT
check from the original CNF is still mandatory before any scientific use.
"""

from __future__ import annotations

import argparse
import contextlib
import datetime as _datetime
import fcntl
import hashlib
import json
import os
import re
import signal
import stat
import struct
import subprocess
import sys
import time
import uuid
from pathlib import Path
from typing import Any, Iterable, Iterator, Mapping, Sequence


SCHEMA_VERSION = 1
AUTHORITY = "TEST_ONLY"
CONTROLLER = "cadical-dmtcp-exact-resume-v1"
DMTCP_VERSION = "4.2.0"
DMTCP_REFERENCE_COMMIT = "f8009ce7b4ad211311ca2f72a929b975e4aa1155"
GENERATION_RE = re.compile(r"^[0-9]{6}$")
SHA256_RE = re.compile(r"^[0-9a-f]{64}$")
PORT_RE = re.compile(r"^[0-9]{1,5}\n?$")
WORKER_LIST_RE = re.compile(
    r"^(?P<index>[0-9]+), (?P<program>[^\[\],]+)\[(?P<virtual_pid>[0-9]+):"
    r"(?P<real_pid>[0-9]+)\]@(?P<host>[^,]+), (?P<unique_pid>[^,]+), (?P<state>[^,]+), (?P<barrier>.*)$"
)
MAX_JSON_BYTES = 16 << 20
HASH_CHUNK_BYTES = 8 << 20
READY_TIMEOUT_S = 30.0
CONTROL_TIMEOUT_S = 600.0
POLL_S = 0.10
DMTCP_IMAGE_MAGIC = b"DMTCP_CHECKPOINT_IMAGE_v4.0\n"

REQUIRED_DMTCP_BINS = (
    "dmtcp_launch",
    "dmtcp_command",
    "dmtcp_restart",
    "dmtcp_coordinator",
    "mtcp_restart",
)
UNSAFE_DMTCP_ENV = (
    "DMTCP_CKPT_OPEN_FILES",
    "DMTCP_SKIP_TRUNCATE_FILE_AT_RESTART",
    "DMTCP_ALLOW_OVERWRITE_WITH_CKPTED_FILES",
)
FORBIDDEN_DMTCP_TOKENS = (
    "--ckpt-open-files",
    "--checkpoint-open-files",
    "--allow-file-overwrite",
)
STALE_FLAG = "--test-only-allow-stale-tail"


class ResumeControllerError(RuntimeError):
    """A fail-closed controller or evidence error."""


def _utc_now() -> str:
    return _datetime.datetime.now(_datetime.timezone.utc).isoformat().replace(
        "+00:00", "Z"
    )


def canonical_bytes(value: Any) -> bytes:
    try:
        return json.dumps(
            value,
            sort_keys=True,
            separators=(",", ":"),
            ensure_ascii=True,
            allow_nan=False,
        ).encode("ascii")
    except (TypeError, ValueError, UnicodeEncodeError) as exc:
        raise ResumeControllerError(f"not canonical JSON: {exc}") from exc


def seal_manifest(kind: str, fields: Mapping[str, Any]) -> dict[str, Any]:
    if "self_sha256" in fields:
        raise ResumeControllerError("caller supplied reserved self_sha256")
    doc: dict[str, Any] = {
        "authority": AUTHORITY,
        "controller": CONTROLLER,
        "created_utc": _utc_now(),
        "kind": kind,
        "schema_version": SCHEMA_VERSION,
        **dict(fields),
    }
    doc["self_sha256"] = hashlib.sha256(canonical_bytes(doc)).hexdigest()
    return doc


def selfhash_valid(doc: Mapping[str, Any]) -> bool:
    digest = doc.get("self_sha256")
    if not isinstance(digest, str) or not SHA256_RE.fullmatch(digest):
        return False
    unsigned = dict(doc)
    del unsigned["self_sha256"]
    return hashlib.sha256(canonical_bytes(unsigned)).hexdigest() == digest


def _no_duplicate_object(pairs: list[tuple[str, Any]]) -> dict[str, Any]:
    result: dict[str, Any] = {}
    for key, value in pairs:
        if key in result:
            raise ResumeControllerError(f"duplicate JSON key: {key}")
        result[key] = value
    return result


def _reject_constant(value: str) -> Any:
    raise ResumeControllerError(f"non-finite JSON constant: {value}")


def decode_manifest(payload: bytes, *, expected_kind: str | None = None) -> dict[str, Any]:
    if len(payload) > MAX_JSON_BYTES:
        raise ResumeControllerError("manifest exceeds size cap")
    try:
        doc = json.loads(
            payload.decode("ascii"),
            object_pairs_hook=_no_duplicate_object,
            parse_constant=_reject_constant,
        )
    except (UnicodeDecodeError, json.JSONDecodeError) as exc:
        raise ResumeControllerError(f"invalid manifest JSON: {exc}") from exc
    if not isinstance(doc, dict):
        raise ResumeControllerError("manifest top level is not an object")
    if payload != canonical_bytes(doc) + b"\n":
        raise ResumeControllerError("manifest is not canonical newline JSON")
    if doc.get("authority") != AUTHORITY:
        raise ResumeControllerError("manifest authority is not TEST_ONLY")
    if doc.get("controller") != CONTROLLER:
        raise ResumeControllerError("manifest controller mismatch")
    if doc.get("schema_version") != SCHEMA_VERSION:
        raise ResumeControllerError("manifest schema mismatch")
    if expected_kind is not None and doc.get("kind") != expected_kind:
        raise ResumeControllerError(
            f"manifest kind mismatch: expected {expected_kind!r}"
        )
    if not selfhash_valid(doc):
        raise ResumeControllerError("manifest self hash mismatch")
    return doc


def _ensure_plain_directory(path: Path) -> None:
    try:
        info = path.lstat()
    except FileNotFoundError as exc:
        raise ResumeControllerError(f"missing directory: {path}") from exc
    if stat.S_ISLNK(info.st_mode) or not stat.S_ISDIR(info.st_mode):
        raise ResumeControllerError(f"not a plain directory: {path}")


def _fsync_dir(path: Path) -> None:
    fd = os.open(path, os.O_RDONLY | os.O_DIRECTORY | os.O_CLOEXEC)
    try:
        os.fsync(fd)
    finally:
        os.close(fd)


def _atomic_publish(path: Path, payload: bytes, *, mode: int = 0o600) -> None:
    _ensure_plain_directory(path.parent)
    temp = path.parent / f".{path.name}.private-{uuid.uuid4().hex}"
    flags = os.O_WRONLY | os.O_CREAT | os.O_EXCL | os.O_CLOEXEC | os.O_NOFOLLOW
    fd = os.open(temp, flags, mode)
    linked = False
    try:
        view = memoryview(payload)
        while view:
            count = os.write(fd, view)
            if count <= 0:
                raise ResumeControllerError("short manifest write")
            view = view[count:]
        os.fsync(fd)
        os.close(fd)
        fd = -1
        os.link(temp, path, follow_symlinks=False)
        linked = True
        _fsync_dir(path.parent)
    except FileExistsError:
        raise ResumeControllerError(f"immutable path already exists: {path}")
    finally:
        if fd >= 0:
            os.close(fd)
        try:
            temp.unlink()
        except FileNotFoundError:
            pass
        if linked:
            _fsync_dir(path.parent)


def write_manifest(path: Path, kind: str, fields: Mapping[str, Any]) -> dict[str, Any]:
    doc = seal_manifest(kind, fields)
    _atomic_publish(path, canonical_bytes(doc) + b"\n")
    return doc


def read_manifest(path: Path, *, expected_kind: str | None = None) -> dict[str, Any]:
    fd = os.open(path, os.O_RDONLY | os.O_CLOEXEC | os.O_NOFOLLOW)
    try:
        info = os.fstat(fd)
        if not stat.S_ISREG(info.st_mode):
            raise ResumeControllerError(f"manifest is not regular: {path}")
        if info.st_size > MAX_JSON_BYTES:
            raise ResumeControllerError(f"manifest is too large: {path}")
        payload = b""
        while len(payload) <= MAX_JSON_BYTES:
            chunk = os.read(fd, min(1 << 20, MAX_JSON_BYTES + 1 - len(payload)))
            if not chunk:
                break
            payload += chunk
    finally:
        os.close(fd)
    return decode_manifest(payload, expected_kind=expected_kind)


def _sha256_fd(fd: int, *, limit: int | None = None) -> tuple[str, int]:
    os.lseek(fd, 0, os.SEEK_SET)
    digest = hashlib.sha256()
    total = 0
    while limit is None or total < limit:
        want = HASH_CHUNK_BYTES if limit is None else min(HASH_CHUNK_BYTES, limit - total)
        if want == 0:
            break
        chunk = os.read(fd, want)
        if not chunk:
            break
        digest.update(chunk)
        total += len(chunk)
    return digest.hexdigest(), total


def stable_file_record(path: Path, *, relative_to: Path | None = None) -> dict[str, Any]:
    canonical = path.resolve(strict=True)
    fd = os.open(canonical, os.O_RDONLY | os.O_CLOEXEC | os.O_NOFOLLOW)
    try:
        before = os.fstat(fd)
        if not stat.S_ISREG(before.st_mode):
            raise ResumeControllerError(f"not a regular file: {canonical}")
        digest, size = _sha256_fd(fd)
        after = os.fstat(fd)
    finally:
        os.close(fd)
    identity_before = (
        before.st_dev,
        before.st_ino,
        before.st_size,
        before.st_mtime_ns,
        before.st_ctime_ns,
    )
    identity_after = (
        after.st_dev,
        after.st_ino,
        after.st_size,
        after.st_mtime_ns,
        after.st_ctime_ns,
    )
    if identity_before != identity_after or size != before.st_size:
        raise ResumeControllerError(f"file changed while hashing: {canonical}")
    if relative_to is None:
        rendered_path = str(canonical)
        path_kind = "absolute"
    else:
        root = relative_to.resolve(strict=True)
        try:
            rendered_path = str(canonical.relative_to(root))
        except ValueError as exc:
            raise ResumeControllerError(f"file escapes root: {canonical}") from exc
        path_kind = "root_relative"
    return {
        "bytes": size,
        "mode": stat.S_IMODE(before.st_mode),
        "path": rendered_path,
        "path_kind": path_kind,
        "sha256": digest,
    }


def _record_path(record: Mapping[str, Any], *, root: Path | None = None) -> Path:
    path_value = record.get("path")
    path_kind = record.get("path_kind")
    if not isinstance(path_value, str) or not path_value:
        raise ResumeControllerError("bad file-record path")
    if path_kind == "absolute":
        path = Path(path_value)
        if not path.is_absolute():
            raise ResumeControllerError("absolute file record is relative")
        return path
    if path_kind == "root_relative":
        if root is None:
            raise ResumeControllerError("root required for relative file record")
        relative = Path(path_value)
        if relative.is_absolute() or ".." in relative.parts:
            raise ResumeControllerError("unsafe relative file record")
        return root / relative
    raise ResumeControllerError("unknown file-record path kind")


def verify_file_record(record: Mapping[str, Any], *, root: Path | None = None) -> Path:
    expected_keys = {"bytes", "mode", "path", "path_kind", "sha256"}
    if set(record) != expected_keys:
        raise ResumeControllerError("file-record key set mismatch")
    if type(record.get("bytes")) is not int or record["bytes"] < 0:
        raise ResumeControllerError("bad file-record size")
    if type(record.get("mode")) is not int:
        raise ResumeControllerError("bad file-record mode")
    if not isinstance(record.get("sha256"), str) or not SHA256_RE.fullmatch(
        record["sha256"]
    ):
        raise ResumeControllerError("bad file-record hash")
    path = _record_path(record, root=root)
    actual = stable_file_record(path, relative_to=root if record["path_kind"] == "root_relative" else None)
    if actual != dict(record):
        raise ResumeControllerError(f"file binding mismatch: {path}")
    return path.resolve(strict=True)


def _hash_prefix(path: Path, size: int, *, allow_append: bool = False) -> str:
    if type(size) is not int or size < 0:
        raise ResumeControllerError("invalid prefix size")
    fd = os.open(path, os.O_RDONLY | os.O_CLOEXEC | os.O_NOFOLLOW)
    try:
        before = os.fstat(fd)
        if not stat.S_ISREG(before.st_mode) or before.st_size < size:
            raise ResumeControllerError("proof is shorter than checkpoint prefix")
        digest, read_size = _sha256_fd(fd, limit=size)
        after = os.fstat(fd)
    finally:
        os.close(fd)
    if read_size != size:
        raise ResumeControllerError("short read while hashing proof prefix")
    if allow_append:
        if (
            before.st_dev != after.st_dev
            or before.st_ino != after.st_ino
            or after.st_size < before.st_size
            or after.st_size < size
        ):
            raise ResumeControllerError(
                "proof identity changed or shrank while hashing live prefix"
            )
    elif (
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
        raise ResumeControllerError("proof changed while hashing prefix")
    return digest


def _elf_interpreter(path: Path) -> str | None:
    """Return PT_INTERP using only stdlib, or None for non/dynamic-free ELF."""
    with path.open("rb") as handle:
        ident = handle.read(16)
        if len(ident) < 16 or ident[:4] != b"\x7fELF":
            return None
        elf_class, endian_tag = ident[4], ident[5]
        if endian_tag == 1:
            endian = "<"
        elif endian_tag == 2:
            endian = ">"
        else:
            raise ResumeControllerError("unsupported ELF endianness")
        if elf_class == 2:
            header_format = endian + "HHIQQQIHHHHHH"
            ph_format = endian + "IIQQQQQQ"
            phoff_index, phentsize_index, phnum_index = 4, 8, 9
            offset_index, filesz_index = 2, 5
        elif elf_class == 1:
            header_format = endian + "HHIIIIIHHHHHH"
            ph_format = endian + "IIIIIIII"
            phoff_index, phentsize_index, phnum_index = 4, 8, 9
            offset_index, filesz_index = 1, 4
        else:
            raise ResumeControllerError("unsupported ELF class")
        header_size = struct.calcsize(header_format)
        rest = handle.read(header_size)
        if len(rest) != header_size:
            raise ResumeControllerError("truncated ELF header")
        header = struct.unpack(header_format, rest)
        phoff = int(header[phoff_index])
        phentsize = int(header[phentsize_index])
        phnum = int(header[phnum_index])
        expected_ph_size = struct.calcsize(ph_format)
        if phentsize < expected_ph_size or phnum > 65535:
            raise ResumeControllerError("invalid ELF program header table")
        for index in range(phnum):
            handle.seek(phoff + index * phentsize)
            raw = handle.read(expected_ph_size)
            if len(raw) != expected_ph_size:
                raise ResumeControllerError("truncated ELF program header")
            program = struct.unpack(ph_format, raw)
            if program[0] != 3:  # PT_INTERP
                continue
            offset = int(program[offset_index])
            size = int(program[filesz_index])
            if size <= 1 or size > 4096:
                raise ResumeControllerError("invalid ELF interpreter size")
            handle.seek(offset)
            value = handle.read(size)
            if len(value) != size or not value.endswith(b"\x00"):
                raise ResumeControllerError("invalid ELF interpreter payload")
            try:
                return value[:-1].decode("ascii")
            except UnicodeDecodeError as exc:
                raise ResumeControllerError("non-ASCII ELF interpreter") from exc
    return None


def _check_unsafe_environment(environ: Mapping[str, str] | None = None) -> None:
    source = os.environ if environ is None else environ
    present = [name for name in UNSAFE_DMTCP_ENV if name in source]
    if present:
        raise ResumeControllerError(
            "unsafe DMTCP environment variable is present: " + ", ".join(present)
        )


def _clean_dmtcp_environment() -> dict[str, str]:
    _check_unsafe_environment()
    env = {key: value for key, value in os.environ.items() if not key.startswith("DMTCP_")}
    env["DMTCP_GZIP"] = "0"
    env["DMTCP_QUIET"] = "1"
    return env


def _assert_safe_dmtcp_argv(argv: Sequence[str]) -> None:
    bad = [token for token in argv if token in FORBIDDEN_DMTCP_TOKENS]
    if bad:
        raise ResumeControllerError(f"forbidden DMTCP option: {bad[0]}")


def _run_version(binary: Path) -> str:
    result = subprocess.run(
        [str(binary), "--version"],
        stdin=subprocess.DEVNULL,
        stdout=subprocess.PIPE,
        stderr=subprocess.PIPE,
        timeout=10,
        check=False,
        env=_clean_dmtcp_environment(),
    )
    # DMTCP 4.2.0's command client prints a valid version and exits 1;
    # launch/restart exit 0. Bind the output as well as this exact quirk.
    if result.returncode not in {0, 1} or result.stderr:
        raise ResumeControllerError(f"failed to query DMTCP version: {binary}")
    try:
        first = result.stdout.decode("utf-8", "strict").splitlines()[0]
    except (UnicodeDecodeError, IndexError) as exc:
        raise ResumeControllerError(f"invalid DMTCP version output: {binary}") from exc
    if not first.endswith(f"(DMTCP) {DMTCP_VERSION}"):
        raise ResumeControllerError(f"DMTCP is not pinned v{DMTCP_VERSION}: {first}")
    return first


def build_dmtcp_binding(prefix: Path) -> dict[str, Any]:
    prefix = prefix.resolve(strict=True)
    _ensure_plain_directory(prefix)
    binaries: list[dict[str, Any]] = []
    versions: dict[str, str] = {}
    for name in REQUIRED_DMTCP_BINS:
        path = prefix / "bin" / name
        record = stable_file_record(path)
        if not (path.stat().st_mode & stat.S_IXUSR):
            raise ResumeControllerError(f"DMTCP binary is not executable: {path}")
        binaries.append(record)
        if name in {"dmtcp_launch", "dmtcp_command", "dmtcp_restart"}:
            versions[name] = _run_version(path)
    library_root = prefix / "lib" / "dmtcp"
    _ensure_plain_directory(library_root)
    library_paths = sorted(
        path for path in library_root.rglob("*") if path.is_file() and not path.is_symlink()
    )
    if not library_paths:
        raise ResumeControllerError("DMTCP library directory is empty")
    libraries = [stable_file_record(path) for path in library_paths]
    return {
        "binaries": binaries,
        "libraries": libraries,
        "prefix": str(prefix),
        "reference_commit": DMTCP_REFERENCE_COMMIT,
        "version": DMTCP_VERSION,
        "version_outputs": versions,
    }


def _verify_dmtcp_binding(binding: Mapping[str, Any]) -> dict[str, Path]:
    if binding.get("version") != DMTCP_VERSION:
        raise ResumeControllerError("DMTCP version binding mismatch")
    if binding.get("reference_commit") != DMTCP_REFERENCE_COMMIT:
        raise ResumeControllerError("DMTCP reference commit mismatch")
    prefix_value = binding.get("prefix")
    if not isinstance(prefix_value, str) or not Path(prefix_value).is_absolute():
        raise ResumeControllerError("invalid DMTCP prefix binding")
    prefix = Path(prefix_value).resolve(strict=True)
    binaries_value = binding.get("binaries")
    libraries_value = binding.get("libraries")
    if not isinstance(binaries_value, list) or not isinstance(libraries_value, list):
        raise ResumeControllerError("invalid DMTCP file bindings")
    resolved: dict[str, Path] = {}
    for record in binaries_value:
        if not isinstance(record, dict):
            raise ResumeControllerError("invalid DMTCP binary record")
        path = verify_file_record(record)
        try:
            relative = path.relative_to(prefix / "bin")
        except ValueError as exc:
            raise ResumeControllerError("DMTCP binary escapes prefix") from exc
        if len(relative.parts) != 1 or relative.name not in REQUIRED_DMTCP_BINS:
            raise ResumeControllerError("unexpected DMTCP binary binding")
        if relative.name in resolved:
            raise ResumeControllerError("duplicate DMTCP binary binding")
        resolved[relative.name] = path
    if set(resolved) != set(REQUIRED_DMTCP_BINS):
        raise ResumeControllerError("incomplete DMTCP binary binding")
    seen_libraries: set[Path] = set()
    for record in libraries_value:
        if not isinstance(record, dict):
            raise ResumeControllerError("invalid DMTCP library record")
        path = verify_file_record(record)
        try:
            path.relative_to(prefix / "lib" / "dmtcp")
        except ValueError as exc:
            raise ResumeControllerError("DMTCP library escapes prefix") from exc
        if path in seen_libraries:
            raise ResumeControllerError("duplicate DMTCP library binding")
        seen_libraries.add(path)
    if not seen_libraries:
        raise ResumeControllerError("empty DMTCP library binding")
    return resolved


def _validate_solver_args(values: Sequence[str]) -> list[str]:
    result: list[str] = []
    for value in values:
        if not isinstance(value, str) or not value or "\x00" in value:
            raise ResumeControllerError("invalid solver argument")
        if value in FORBIDDEN_DMTCP_TOKENS:
            raise ResumeControllerError("DMTCP option supplied as solver argument")
        result.append(value)
    return result


def _config_path(root: Path) -> Path:
    return root / "00-init.commit.json"


def _proof_path(root: Path, config: Mapping[str, Any]) -> Path:
    relative = config.get("proof_relative_path")
    if not isinstance(relative, str):
        raise ResumeControllerError("missing proof relative path")
    path = Path(relative)
    if path.is_absolute() or path.parts != ("proof.drat",):
        raise ResumeControllerError("unsafe proof path binding")
    return root / path


def initialize(
    root: Path,
    *,
    cnf: Path,
    solver: Path,
    dmtcp_prefix: Path,
    solver_args: Sequence[str],
    runtime_libs: Sequence[Path],
    runtime_libs_complete: bool,
) -> dict[str, Any]:
    _check_unsafe_environment()
    root = root.absolute()
    try:
        root.mkdir(mode=0o700, parents=False, exist_ok=False)
    except FileExistsError as exc:
        raise ResumeControllerError(f"root already exists: {root}") from exc
    _fsync_dir(root.parent)
    try:
        (root / "generations").mkdir(mode=0o700)
        _atomic_publish(root / ".controller.lock", b"", mode=0o600)
        cnf_record = stable_file_record(cnf)
        solver_path = solver.resolve(strict=True)
        solver_record = stable_file_record(solver_path)
        if not (solver_path.stat().st_mode & stat.S_IXUSR):
            raise ResumeControllerError("solver is not executable")
        interpreter = _elf_interpreter(solver_path)
        declared_paths = [path.resolve(strict=True) for path in runtime_libs]
        if interpreter is not None:
            if not runtime_libs_complete:
                raise ResumeControllerError(
                    "dynamic ELF solver requires --runtime-libs-complete"
                )
            declared_paths.append(Path(interpreter).resolve(strict=True))
        unique_runtime = sorted(set(declared_paths), key=str)
        runtime_records = [stable_file_record(path) for path in unique_runtime]
        dmtcp = build_dmtcp_binding(dmtcp_prefix)
        fields = {
            "cnf": cnf_record,
            "controller_source": stable_file_record(Path(__file__)),
            "dmtcp": dmtcp,
            "dmtcp_file_policy": {
                "allow_file_overwrite": False,
                "checkpoint_open_files": False,
                "ordinary_proof_file": True,
                "skip_truncate_at_restart": False,
            },
            "proof_relative_path": "proof.drat",
            "root": str(root.resolve(strict=True)),
            "runtime_libraries": runtime_records,
            "runtime_libraries_complete_attestation": bool(runtime_libs_complete),
            "solver": solver_record,
            "solver_args": _validate_solver_args(solver_args),
            "solver_elf_interpreter": interpreter,
        }
        return write_manifest(_config_path(root), "init.commit", fields)
    except BaseException:
        # The newly created root is deliberately retained as failed evidence.
        raise


def _load_and_verify_config(root: Path) -> tuple[dict[str, Any], dict[str, Path]]:
    _check_unsafe_environment()
    root = root.resolve(strict=True)
    _ensure_plain_directory(root)
    config = read_manifest(_config_path(root), expected_kind="init.commit")
    if config.get("root") != str(root):
        raise ResumeControllerError("root binding mismatch")
    policy = config.get("dmtcp_file_policy")
    if policy != {
        "allow_file_overwrite": False,
        "checkpoint_open_files": False,
        "ordinary_proof_file": True,
        "skip_truncate_at_restart": False,
    }:
        raise ResumeControllerError("unsafe or unknown DMTCP file policy")
    for name in ("cnf", "solver", "controller_source"):
        record = config.get(name)
        if not isinstance(record, dict):
            raise ResumeControllerError(f"missing {name} binding")
        verify_file_record(record)
    runtime = config.get("runtime_libraries")
    if not isinstance(runtime, list):
        raise ResumeControllerError("invalid runtime library binding")
    for record in runtime:
        if not isinstance(record, dict):
            raise ResumeControllerError("invalid runtime library record")
        verify_file_record(record)
    interpreter = config.get("solver_elf_interpreter")
    if interpreter is not None and config.get("runtime_libraries_complete_attestation") is not True:
        raise ResumeControllerError("dynamic runtime completeness was not attested")
    solver_args = config.get("solver_args")
    if not isinstance(solver_args, list):
        raise ResumeControllerError("invalid solver arguments binding")
    _validate_solver_args(solver_args)
    dmtcp = config.get("dmtcp")
    if not isinstance(dmtcp, dict):
        raise ResumeControllerError("missing DMTCP binding")
    binaries = _verify_dmtcp_binding(dmtcp)
    return config, binaries


@contextlib.contextmanager
def controller_lock(root: Path, *, exclusive: bool = True) -> Iterator[None]:
    fd = os.open(root / ".controller.lock", os.O_RDWR | os.O_CLOEXEC | os.O_NOFOLLOW)
    try:
        info = os.fstat(fd)
        if not stat.S_ISREG(info.st_mode):
            raise ResumeControllerError("controller lock is not regular")
        fcntl.flock(fd, fcntl.LOCK_EX if exclusive else fcntl.LOCK_SH)
        yield
    finally:
        fcntl.flock(fd, fcntl.LOCK_UN)
        os.close(fd)


def _generation_dir(root: Path, generation: int) -> Path:
    if type(generation) is not int or generation < 0 or generation > 999999:
        raise ResumeControllerError("generation out of range")
    return root / "generations" / f"{generation:06d}"


def _generation_numbers(root: Path) -> list[int]:
    parent = root / "generations"
    _ensure_plain_directory(parent)
    numbers: list[int] = []
    for entry in parent.iterdir():
        if entry.name.startswith("."):
            continue
        if not GENERATION_RE.fullmatch(entry.name):
            raise ResumeControllerError(f"unexpected generation entry: {entry.name}")
        _ensure_plain_directory(entry)
        numbers.append(int(entry.name))
    numbers.sort()
    if numbers != list(range(len(numbers))):
        raise ResumeControllerError("generation sequence is not contiguous from zero")
    return numbers


def _create_generation(root: Path, generation: int) -> Path:
    path = _generation_dir(root, generation)
    path.mkdir(mode=0o700, exist_ok=False)
    for name in ("images", "tmp"):
        (path / name).mkdir(mode=0o700)
    _fsync_dir(path)
    _fsync_dir(path.parent)
    return path


def _proc_start_ticks(pid: int, *, allow_zombie: bool = False) -> int:
    try:
        payload = Path(f"/proc/{pid}/stat").read_text(encoding="ascii")
    except (FileNotFoundError, ProcessLookupError) as exc:
        raise ResumeControllerError(f"process is not alive: {pid}") from exc
    closing = payload.rfind(")")
    if closing < 0:
        raise ResumeControllerError("malformed /proc stat")
    fields = payload[closing + 2 :].split()
    if len(fields) <= 19:
        raise ResumeControllerError("short /proc stat")
    if fields[0] == "Z" and not allow_zombie:
        raise ResumeControllerError(f"process is a zombie: {pid}")
    try:
        return int(fields[19])
    except ValueError as exc:
        raise ResumeControllerError("bad process start time") from exc


def _pid_identity(pid: int, start_ticks: int) -> bool:
    try:
        return _proc_start_ticks(pid) == start_ticks
    except ResumeControllerError:
        return False


def _read_port(path: Path) -> int:
    fd = os.open(path, os.O_RDONLY | os.O_CLOEXEC | os.O_NOFOLLOW)
    try:
        info = os.fstat(fd)
        if not stat.S_ISREG(info.st_mode) or info.st_size > 8:
            raise ResumeControllerError("invalid DMTCP port file")
        payload = os.read(fd, 16)
    finally:
        os.close(fd)
    if not PORT_RE.fullmatch(payload.decode("ascii", "strict")):
        raise ResumeControllerError("invalid DMTCP port payload")
    port = int(payload)
    if not 1 <= port <= 65535:
        raise ResumeControllerError("DMTCP port out of range")
    return port


def _parse_status(stdout: bytes) -> tuple[int, bool]:
    try:
        lines = stdout.decode("utf-8", "strict").splitlines()
    except UnicodeDecodeError as exc:
        raise ResumeControllerError("non-UTF8 DMTCP status") from exc
    peers = [line for line in lines if line.startswith("  NUM_PEERS=")]
    running = [line for line in lines if line.startswith("  RUNNING=")]
    if len(peers) != 1 or len(running) != 1:
        raise ResumeControllerError("ambiguous DMTCP status")
    try:
        peer_count = int(peers[0].split("=", 1)[1])
    except ValueError as exc:
        raise ResumeControllerError("invalid DMTCP peer count") from exc
    running_value = running[0].split("=", 1)[1]
    if running_value not in {"yes", "no"}:
        raise ResumeControllerError("invalid DMTCP running state")
    return peer_count, running_value == "yes"


def _query_status(command: Path, port: int, *, timeout: float = 5.0) -> tuple[int, bool]:
    argv = [str(command), "--coord-host", "127.0.0.1", "--coord-port", str(port), "--status"]
    _assert_safe_dmtcp_argv(argv)
    result = subprocess.run(
        argv,
        stdin=subprocess.DEVNULL,
        stdout=subprocess.PIPE,
        stderr=subprocess.PIPE,
        timeout=timeout,
        check=False,
        env=_clean_dmtcp_environment(),
    )
    if result.returncode != 0 or result.stderr:
        raise ResumeControllerError("DMTCP coordinator status failed")
    return _parse_status(result.stdout)


def _parse_client_list(
    stdout: bytes, *, expected_host: str, expected_port: int
) -> dict[str, Any]:
    try:
        lines = stdout.decode("utf-8", "strict").splitlines()
    except UnicodeDecodeError as exc:
        raise ResumeControllerError("non-UTF8 DMTCP client list") from exc
    while lines and not lines[-1]:
        lines.pop()
    expected_prefix = [
        "Coordinator:",
        f"  Host: {expected_host}",
        f"  Port: {expected_port}",
        "Client List:",
        "#, PROG[virtPID:realPID]@HOST, DMTCP-UNIQUEPID, STATE, BARRIER",
    ]
    if lines[:5] != expected_prefix:
        raise ResumeControllerError("DMTCP client-list framing changed")
    if len(lines) != 6:
        raise ResumeControllerError(
            f"expected exactly one DMTCP client, found {max(0, len(lines) - 5)}"
        )
    match = WORKER_LIST_RE.fullmatch(lines[5])
    if match is None:
        raise ResumeControllerError("unrecognized DMTCP client-list row")
    worker: dict[str, Any] = {
        "barrier": match.group("barrier"),
        "client_index": int(match.group("index")),
        "host": match.group("host"),
        "program": match.group("program"),
        "real_pid": int(match.group("real_pid")),
        "state": match.group("state"),
        "unique_pid": match.group("unique_pid"),
        "virtual_pid": int(match.group("virtual_pid")),
    }
    if (
        worker["client_index"] != 1
        or worker["virtual_pid"] <= 0
        or worker["real_pid"] <= 0
        or worker["state"] != "WorkerState::RUNNING"
        or worker["barrier"] != ""
        or not worker["host"]
        or not worker["unique_pid"]
    ):
        raise ResumeControllerError("DMTCP client is not one live running peer")
    return worker


def _query_client_identity(
    command: Path,
    port: int,
    *,
    expected_program: str,
    expected_executable: Path,
    timeout: float = 5.0,
) -> dict[str, Any]:
    argv = [
        str(command),
        "--coord-host",
        "127.0.0.1",
        "--coord-port",
        str(port),
        "--list",
    ]
    _assert_safe_dmtcp_argv(argv)
    result = subprocess.run(
        argv,
        stdin=subprocess.DEVNULL,
        stdout=subprocess.PIPE,
        stderr=subprocess.PIPE,
        timeout=timeout,
        check=False,
        env=_clean_dmtcp_environment(),
    )
    if result.returncode != 0 or result.stderr:
        raise ResumeControllerError("DMTCP coordinator client-list failed")
    worker = _parse_client_list(
        result.stdout, expected_host="127.0.0.1", expected_port=port
    )
    real_pid = worker["real_pid"]
    start_ticks = _proc_start_ticks(real_pid)
    try:
        observed_executable = Path(os.readlink(f"/proc/{real_pid}/exe")).resolve(
            strict=True
        )
    except OSError as exc:
        raise ResumeControllerError(
            "could not bind restored process executable"
        ) from exc
    if _proc_start_ticks(real_pid) != start_ticks:
        raise ResumeControllerError("restored process identity changed during binding")
    expected_executable = expected_executable.resolve(strict=True)
    if worker["program"] != expected_program:
        raise ResumeControllerError(
            "DMTCP program name does not match solver binding"
        )
    if observed_executable != expected_executable:
        raise ResumeControllerError(
            "restored process executable does not match solver binding"
        )
    worker["executable"] = str(observed_executable)
    worker["proc_start_ticks"] = start_ticks
    return worker


def _wait_resume_ready(
    command: Path,
    port_file: Path,
    bootstrap_pid: int,
    *,
    expected_program: str,
    expected_executable: Path,
) -> tuple[int, dict[str, Any], int | None]:
    """Wait for the restored peer; dmtcp_restart's bootstrap may exit normally."""
    deadline = time.monotonic() + READY_TIMEOUT_S
    last_error = "restored DMTCP peer did not become ready"
    bootstrap_exit_code: int | None = None
    while time.monotonic() < deadline:
        if bootstrap_exit_code is None:
            try:
                waited, wait_status = os.waitpid(bootstrap_pid, os.WNOHANG)
            except ChildProcessError:
                waited = 0
            if waited == bootstrap_pid:
                bootstrap_exit_code = os.waitstatus_to_exitcode(wait_status)
                if bootstrap_exit_code != 0:
                    raise ResumeControllerError(
                        f"dmtcp_restart bootstrap exited {bootstrap_exit_code}"
                    )
        try:
            port = _read_port(port_file)
            peers, running = _query_status(command, port)
            if peers != 1 or not running:
                last_error = (
                    f"unexpected restored status peers={peers} running={running}"
                )
            else:
                worker = _query_client_identity(
                    command,
                    port,
                    expected_program=expected_program,
                    expected_executable=expected_executable,
                )
                peers_after, running_after = _query_status(command, port)
                confirmed_worker = _query_client_identity(
                    command,
                    port,
                    expected_program=expected_program,
                    expected_executable=expected_executable,
                )
                if (
                    peers_after == 1
                    and running_after
                    and confirmed_worker == worker
                ):
                    return port, worker, bootstrap_exit_code
                last_error = "restored DMTCP identity changed during confirmation"
        except (FileNotFoundError, ResumeControllerError) as exc:
            last_error = str(exc)
        time.sleep(POLL_S)
    raise ResumeControllerError(last_error)


def _quit_coordinator_if_present(command: Path, port_file: Path) -> None:
    """Best-effort fail-closed cleanup for a poisoned resume generation."""
    try:
        port = _read_port(port_file)
    except (OSError, UnicodeError, ResumeControllerError):
        return
    argv = [
        str(command),
        "--coord-host",
        "127.0.0.1",
        "--coord-port",
        str(port),
        "--quit",
    ]
    _assert_safe_dmtcp_argv(argv)
    with contextlib.suppress(OSError, subprocess.SubprocessError):
        subprocess.run(
            argv,
            stdin=subprocess.DEVNULL,
            stdout=subprocess.PIPE,
            stderr=subprocess.PIPE,
            timeout=10,
            check=False,
            env=_clean_dmtcp_environment(),
        )


def _wait_ready(command: Path, port_file: Path, pid: int, start_ticks: int) -> int:
    deadline = time.monotonic() + READY_TIMEOUT_S
    last_error = "coordinator did not become ready"
    while time.monotonic() < deadline:
        if not _pid_identity(pid, start_ticks):
            raise ResumeControllerError("DMTCP-controlled process exited during startup")
        try:
            port = _read_port(port_file)
            peers, running = _query_status(command, port)
            if peers == 1 and running:
                return port
            last_error = f"unexpected single-process status peers={peers} running={running}"
        except (FileNotFoundError, ResumeControllerError) as exc:
            last_error = str(exc)
        time.sleep(POLL_S)
    raise ResumeControllerError(last_error)


def _solver_command(root: Path, config: Mapping[str, Any]) -> list[str]:
    solver = _record_path(config["solver"])
    cnf = _record_path(config["cnf"])
    args = _validate_solver_args(config["solver_args"])
    return [str(solver), *args, str(cnf), str(_proof_path(root, config))]


def _launch_argv(
    generation_dir: Path, binaries: Mapping[str, Path], solver_command: Sequence[str]
) -> list[str]:
    argv = [
        str(binaries["dmtcp_launch"]),
        "--new-coordinator",
        "--port-file",
        str(generation_dir / "coordinator.port"),
        "--interval",
        "0",
        "--no-gzip",
        "--ckptdir",
        str(generation_dir / "images"),
        "--tmpdir",
        str(generation_dir / "tmp"),
        "--coord-logfile",
        str(generation_dir / "coordinator.log"),
        *solver_command,
    ]
    _assert_safe_dmtcp_argv(argv)
    return argv


def _restart_argv(
    generation_dir: Path, binaries: Mapping[str, Path], images: Sequence[Path]
) -> list[str]:
    if len(images) != 1:
        raise ResumeControllerError("single-process controller requires exactly one image")
    argv = [
        str(binaries["dmtcp_restart"]),
        "--new-coordinator",
        "--port-file",
        str(generation_dir / "coordinator.port"),
        "--interval",
        "0",
        "--ckptdir",
        str(generation_dir / "images"),
        "--tmpdir",
        str(generation_dir / "tmp"),
        "--coord-logfile",
        str(generation_dir / "coordinator.log"),
        str(images[0]),
    ]
    _assert_safe_dmtcp_argv(argv)
    return argv


def _open_new_log(path: Path) -> int:
    return os.open(
        path,
        os.O_WRONLY | os.O_CREAT | os.O_EXCL | os.O_CLOEXEC | os.O_NOFOLLOW,
        0o600,
    )


def _spawn_detached(argv: Sequence[str], *, cwd: Path, stdout_path: Path, stderr_path: Path) -> tuple[int, int]:
    stdout_fd = _open_new_log(stdout_path)
    stderr_fd = _open_new_log(stderr_path)
    try:
        process = subprocess.Popen(
            list(argv),
            cwd=cwd,
            env=_clean_dmtcp_environment(),
            stdin=subprocess.DEVNULL,
            stdout=stdout_fd,
            stderr=stderr_fd,
            close_fds=True,
            start_new_session=True,
        )
    finally:
        os.close(stdout_fd)
        os.close(stderr_fd)
    try:
        start_ticks = _proc_start_ticks(process.pid)
    except BaseException:
        with contextlib.suppress(ProcessLookupError):
            os.killpg(process.pid, signal.SIGKILL)
        raise
    return process.pid, start_ticks


def _kill_spawned_group(pid: int, start_ticks: int) -> None:
    """Fail closed after a post-spawn validation error."""
    try:
        if _proc_start_ticks(pid, allow_zombie=True) != start_ticks:
            return
    except ResumeControllerError:
        return
    with contextlib.suppress(ProcessLookupError):
        os.killpg(pid, signal.SIGKILL)
    deadline = time.monotonic() + READY_TIMEOUT_S
    while time.monotonic() < deadline:
        try:
            waited, _ = os.waitpid(pid, os.WNOHANG)
        except ChildProcessError:
            waited = 0
        if waited == pid or not _pid_identity(pid, start_ticks):
            return
        time.sleep(POLL_S)
    raise ResumeControllerError("failed to reap DMTCP computation after startup error")


def _active_commit(generation_dir: Path, generation: int) -> dict[str, Any]:
    candidates = []
    for name, kind in (("start.commit.json", "start.commit"), ("resume.commit.json", "resume.commit")):
        path = generation_dir / name
        if path.exists():
            candidates.append(read_manifest(path, expected_kind=kind))
    if len(candidates) != 1:
        raise ResumeControllerError("generation has missing or ambiguous active commit")
    doc = candidates[0]
    if doc.get("generation") != generation:
        raise ResumeControllerError("active commit generation mismatch")
    return doc


def _claim_without_commit(generation_dir: Path) -> str | None:
    pairs = (
        ("start.claim.json", "start.commit.json"),
        ("resume.claim.json", "resume.commit.json"),
        ("checkpoint.claim.json", "checkpoint.commit.json"),
    )
    for claim, commit in pairs:
        if (generation_dir / claim).exists() and not (generation_dir / commit).exists():
            return claim
    return None


def start(root: Path) -> dict[str, Any]:
    root = root.resolve(strict=True)
    with controller_lock(root):
        config, binaries = _load_and_verify_config(root)
        if _generation_numbers(root):
            raise ResumeControllerError("start is allowed only before generation zero exists")
        proof = _proof_path(root, config)
        proof_fd = os.open(
            proof,
            os.O_WRONLY | os.O_CREAT | os.O_EXCL | os.O_CLOEXEC | os.O_NOFOLLOW,
            0o600,
        )
        os.fsync(proof_fd)
        os.close(proof_fd)
        generation = 0
        generation_dir = _create_generation(root, generation)
        claim = write_manifest(
            generation_dir / "start.claim.json",
            "start.claim",
            {
                "generation": generation,
                "init_manifest_sha256": config["self_sha256"],
            },
        )
        argv = _launch_argv(generation_dir, binaries, _solver_command(root, config))
        pid, start_ticks = _spawn_detached(
            argv,
            cwd=root,
            stdout_path=root / "solver.stdout",
            stderr_path=root / "solver.stderr",
        )
        try:
            port = _wait_ready(binaries["dmtcp_command"], generation_dir / "coordinator.port", pid, start_ticks)
            commit = write_manifest(
                generation_dir / "start.commit.json",
                "start.commit",
                {
                    "argv_sha256": hashlib.sha256(canonical_bytes(list(argv))).hexdigest(),
                    "claim_sha256": claim["self_sha256"],
                    "generation": generation,
                    "pid": pid,
                    "proc_start_ticks": start_ticks,
                    "single_process_peer_count": 1,
                    "coordinator_port": port,
                },
            )
        except BaseException:
            _kill_spawned_group(pid, start_ticks)
            raise
        return commit


def _kc_semantics(returncode: int, stdout: bytes, stderr: bytes) -> bool:
    """Accept DMTCP 4.2.0's observed rc=2 success only with exact wording.

    ``-kc`` can return 2 after successfully checkpointing and killing because
    its follow-up coordinator request sees no running computation.  Filesystem
    and process evidence is checked separately by ``checkpoint_stop``.
    """
    if returncode not in {0, 2}:
        return False
    try:
        out_lines = [line for line in stdout.decode("utf-8", "strict").splitlines() if line]
        err_lines = [line for line in stderr.decode("utf-8", "strict").splitlines() if line]
    except UnicodeDecodeError:
        return False
    phrase = "Computation was checkpointed and killed."
    if returncode == 2:
        return out_lines == [phrase] and not err_lines
    return phrase in out_lines and not err_lines


def _wait_pid_gone(pid: int, start_ticks: int, *, timeout: float = 30.0) -> None:
    deadline = time.monotonic() + timeout
    while time.monotonic() < deadline:
        if not _pid_identity(pid, start_ticks):
            return
        time.sleep(POLL_S)
    raise ResumeControllerError("controlled process survived checkpoint-stop")


def _checkpoint_images(generation_dir: Path, root: Path) -> list[dict[str, Any]]:
    images_dir = generation_dir / "images"
    candidates = sorted(images_dir.glob("ckpt_*.dmtcp"))
    if len(candidates) != 1:
        raise ResumeControllerError(
            f"single-process checkpoint requires exactly one image, found {len(candidates)}"
        )
    records: list[dict[str, Any]] = []
    for image in candidates:
        fd = os.open(image, os.O_RDONLY | os.O_CLOEXEC | os.O_NOFOLLOW)
        try:
            if os.read(fd, len(DMTCP_IMAGE_MAGIC)) != DMTCP_IMAGE_MAGIC:
                raise ResumeControllerError("checkpoint image has wrong uncompressed magic")
        finally:
            os.close(fd)
        records.append(stable_file_record(image, relative_to=root))
    return records


def _publish_command_capture(generation_dir: Path, prefix: str, payload: bytes) -> dict[str, Any]:
    path = generation_dir / prefix
    _atomic_publish(path, payload)
    return stable_file_record(path, relative_to=generation_dir.parent.parent)


def checkpoint_stop(root: Path) -> dict[str, Any]:
    root = root.resolve(strict=True)
    with controller_lock(root):
        config, binaries = _load_and_verify_config(root)
        numbers = _generation_numbers(root)
        if not numbers:
            raise ResumeControllerError("no started generation")
        generation = numbers[-1]
        generation_dir = _generation_dir(root, generation)
        poison = _claim_without_commit(generation_dir)
        if poison is not None:
            raise ResumeControllerError(f"generation is poisoned by {poison}")
        if (generation_dir / "checkpoint.commit.json").exists():
            raise ResumeControllerError("generation is already checkpointed")
        active = _active_commit(generation_dir, generation)
        pid = active.get("pid")
        start_ticks = active.get("proc_start_ticks")
        port = active.get("coordinator_port")
        if type(pid) is not int or type(start_ticks) is not int or type(port) is not int:
            raise ResumeControllerError("invalid active process identity")
        if not _pid_identity(pid, start_ticks):
            raise ResumeControllerError("active process identity is not alive")
        peers, running = _query_status(binaries["dmtcp_command"], port)
        if peers != 1 or not running:
            raise ResumeControllerError("not one running DMTCP peer")
        claim = write_manifest(
            generation_dir / "checkpoint.claim.json",
            "checkpoint.claim",
            {
                "active_manifest_sha256": active["self_sha256"],
                "generation": generation,
                "method": "dmtcp_command --kcheckpoint",
            },
        )
        argv = [
            str(binaries["dmtcp_command"]),
            "--coord-host",
            "127.0.0.1",
            "--coord-port",
            str(port),
            "--kcheckpoint",
        ]
        _assert_safe_dmtcp_argv(argv)
        result = subprocess.run(
            argv,
            stdin=subprocess.DEVNULL,
            stdout=subprocess.PIPE,
            stderr=subprocess.PIPE,
            timeout=CONTROL_TIMEOUT_S,
            check=False,
            env=_clean_dmtcp_environment(),
        )
        stdout_record = _publish_command_capture(
            generation_dir, "checkpoint.command.stdout", result.stdout
        )
        stderr_record = _publish_command_capture(
            generation_dir, "checkpoint.command.stderr", result.stderr
        )
        if not _kc_semantics(result.returncode, result.stdout, result.stderr):
            raise ResumeControllerError(
                f"checkpoint-stop command semantics rejected (rc={result.returncode})"
            )
        _wait_pid_gone(pid, start_ticks)
        images = _checkpoint_images(generation_dir, root)
        proof_record = stable_file_record(_proof_path(root, config), relative_to=root)
        commit = write_manifest(
            generation_dir / "checkpoint.commit.json",
            "checkpoint.commit",
            {
                "claim_sha256": claim["self_sha256"],
                "command_returncode": result.returncode,
                "command_stderr": stderr_record,
                "command_stdout": stdout_record,
                "generation": generation,
                "images": images,
                "proof_prefix": proof_record,
                "single_writer_stopped": True,
            },
        )
        return commit


def _read_optional_injection(generation_dir: Path) -> dict[str, Any] | None:
    path = generation_dir / "stale-tail.commit.json"
    if not path.exists():
        return None
    return read_manifest(path, expected_kind="stale-tail.commit")


def _checkpoint_commit(generation_dir: Path, generation: int) -> dict[str, Any]:
    doc = read_manifest(
        generation_dir / "checkpoint.commit.json", expected_kind="checkpoint.commit"
    )
    if doc.get("generation") != generation or doc.get("single_writer_stopped") is not True:
        raise ResumeControllerError("invalid checkpoint commit")
    return doc


def _verify_checkpoint_images(root: Path, checkpoint: Mapping[str, Any]) -> list[Path]:
    images = checkpoint.get("images")
    if not isinstance(images, list) or len(images) != 1:
        raise ResumeControllerError("invalid single-process image manifest")
    paths: list[Path] = []
    for record in images:
        if not isinstance(record, dict):
            raise ResumeControllerError("invalid checkpoint image record")
        path = verify_file_record(record, root=root)
        fd = os.open(path, os.O_RDONLY | os.O_CLOEXEC | os.O_NOFOLLOW)
        try:
            if os.read(fd, len(DMTCP_IMAGE_MAGIC)) != DMTCP_IMAGE_MAGIC:
                raise ResumeControllerError("checkpoint image magic changed")
        finally:
            os.close(fd)
        paths.append(path)
    return paths


def _validate_proof_before_resume(
    root: Path,
    checkpoint: Mapping[str, Any],
    injection: Mapping[str, Any] | None,
) -> dict[str, Any]:
    prefix = checkpoint.get("proof_prefix")
    if not isinstance(prefix, dict):
        raise ResumeControllerError("checkpoint has no proof prefix binding")
    proof = _record_path(prefix, root=root)
    expected_size = prefix.get("bytes")
    expected_hash = prefix.get("sha256")
    if type(expected_size) is not int or not isinstance(expected_hash, str):
        raise ResumeControllerError("invalid proof prefix binding")
    if _hash_prefix(proof, expected_size) != expected_hash:
        raise ResumeControllerError("proof prefix hash mismatch")
    current = stable_file_record(proof, relative_to=root)
    if injection is None:
        if current != prefix:
            raise ResumeControllerError("uncommitted proof suffix or mutation")
        return {
            "injected_stale_tail": False,
            "prefix_bytes": expected_size,
            "prefix_sha256": expected_hash,
        }
    if injection.get("checkpoint_manifest_sha256") != checkpoint.get("self_sha256"):
        raise ResumeControllerError("stale-tail commit targets another checkpoint")
    after = injection.get("proof_after_injection")
    if not isinstance(after, dict) or current != after:
        raise ResumeControllerError("stale-tail proof binding mismatch")
    offset = injection.get("stale_offset")
    marker_hex = injection.get("stale_payload_hex")
    if type(offset) is not int or offset != expected_size or not isinstance(marker_hex, str):
        raise ResumeControllerError("invalid stale-tail metadata")
    try:
        marker = bytes.fromhex(marker_hex)
    except ValueError as exc:
        raise ResumeControllerError("invalid stale-tail encoding") from exc
    if not marker or current["bytes"] != expected_size + len(marker):
        raise ResumeControllerError("invalid stale-tail extent")
    fd = os.open(proof, os.O_RDONLY | os.O_CLOEXEC | os.O_NOFOLLOW)
    try:
        os.lseek(fd, offset, os.SEEK_SET)
        observed = os.read(fd, len(marker))
    finally:
        os.close(fd)
    if observed != marker:
        raise ResumeControllerError("stale-tail marker mismatch")
    return {
        "injected_stale_tail": True,
        "prefix_bytes": expected_size,
        "prefix_sha256": expected_hash,
        "stale_payload_hex": marker.hex(),
        "stale_offset": offset,
    }


def inject_stale_tail(root: Path, *, explicit_test_flag: bool) -> dict[str, Any]:
    if not explicit_test_flag:
        raise ResumeControllerError(f"stale-tail injection requires {STALE_FLAG}")
    root = root.resolve(strict=True)
    with controller_lock(root):
        config, _ = _load_and_verify_config(root)
        numbers = _generation_numbers(root)
        if not numbers:
            raise ResumeControllerError("no checkpointed generation")
        generation = numbers[-1]
        generation_dir = _generation_dir(root, generation)
        if _claim_without_commit(generation_dir) is not None:
            raise ResumeControllerError("generation is poisoned")
        checkpoint = _checkpoint_commit(generation_dir, generation)
        if _read_optional_injection(generation_dir) is not None:
            raise ResumeControllerError("stale tail was already injected")
        if _generation_dir(root, generation + 1).exists():
            raise ResumeControllerError("checkpoint was already consumed")
        _verify_checkpoint_images(root, checkpoint)
        _validate_proof_before_resume(root, checkpoint, None)
        marker = (
            f"\nDMTCP_TEST_ONLY_STALE_TAIL_V1:g={generation}:"
            f"ckpt={checkpoint['self_sha256']}\n"
        ).encode("ascii")
        proof = _proof_path(root, config)
        offset = proof.stat().st_size
        fd = os.open(proof, os.O_WRONLY | os.O_APPEND | os.O_CLOEXEC | os.O_NOFOLLOW)
        try:
            count = os.write(fd, marker)
            if count != len(marker):
                raise ResumeControllerError("short stale-tail injection write")
            os.fsync(fd)
        finally:
            os.close(fd)
        after = stable_file_record(proof, relative_to=root)
        return write_manifest(
            generation_dir / "stale-tail.commit.json",
            "stale-tail.commit",
            {
                "checkpoint_manifest_sha256": checkpoint["self_sha256"],
                "generation": generation,
                "proof_after_injection": after,
                "stale_offset": offset,
                "stale_payload_hex": marker.hex(),
                "test_flag": STALE_FLAG,
            },
        )


def _assert_stale_marker_removed(proof: Path, resume_preflight: Mapping[str, Any]) -> None:
    if resume_preflight.get("injected_stale_tail") is not True:
        return
    offset = resume_preflight.get("stale_offset")
    marker_hex = resume_preflight.get("stale_payload_hex")
    if type(offset) is not int or not isinstance(marker_hex, str):
        raise ResumeControllerError("missing stale marker preflight")
    marker = bytes.fromhex(marker_hex)
    fd = os.open(proof, os.O_RDONLY | os.O_CLOEXEC | os.O_NOFOLLOW)
    try:
        info = os.fstat(fd)
        if info.st_size <= offset:
            return
        os.lseek(fd, offset, os.SEEK_SET)
        observed = os.read(fd, len(marker))
    finally:
        os.close(fd)
    if observed == marker:
        raise ResumeControllerError("DMTCP failed to truncate the committed stale proof tail")


def resume(root: Path) -> dict[str, Any]:
    root = root.resolve(strict=True)
    with controller_lock(root):
        config, binaries = _load_and_verify_config(root)
        numbers = _generation_numbers(root)
        if not numbers:
            raise ResumeControllerError("no generation to resume")
        source_generation = numbers[-1]
        source_dir = _generation_dir(root, source_generation)
        poison = _claim_without_commit(source_dir)
        if poison is not None:
            raise ResumeControllerError(f"source generation is poisoned by {poison}")
        checkpoint = _checkpoint_commit(source_dir, source_generation)
        injection = _read_optional_injection(source_dir)
        images = _verify_checkpoint_images(root, checkpoint)
        proof_preflight = _validate_proof_before_resume(root, checkpoint, injection)
        generation = source_generation + 1
        generation_dir = _create_generation(root, generation)
        claim = write_manifest(
            generation_dir / "resume.claim.json",
            "resume.claim",
            {
                "generation": generation,
                "proof_preflight": proof_preflight,
                "source_checkpoint_manifest_sha256": checkpoint["self_sha256"],
                "source_generation": source_generation,
            },
        )
        argv = _restart_argv(generation_dir, binaries, images)
        bootstrap_pid, bootstrap_start_ticks = _spawn_detached(
            argv,
            cwd=root,
            stdout_path=generation_dir / "restart.stdout",
            stderr_path=generation_dir / "restart.stderr",
        )
        restored_worker: dict[str, Any] | None = None
        try:
            solver_path = _record_path(config["solver"])
            port, restored_worker, bootstrap_exit_code = _wait_resume_ready(
                binaries["dmtcp_command"],
                generation_dir / "coordinator.port",
                bootstrap_pid,
                expected_program=solver_path.name,
                expected_executable=binaries["mtcp_restart"],
            )
            proof = _proof_path(root, config)
            if (
                _hash_prefix(
                    proof,
                    proof_preflight["prefix_bytes"],
                    allow_append=True,
                )
                != proof_preflight["prefix_sha256"]
            ):
                raise ResumeControllerError("proof prefix changed during restart")
            _assert_stale_marker_removed(proof, proof_preflight)
            commit = write_manifest(
                generation_dir / "resume.commit.json",
                "resume.commit",
                {
                    "argv_sha256": hashlib.sha256(canonical_bytes(list(argv))).hexdigest(),
                    "bootstrap_exit_code_at_commit": bootstrap_exit_code,
                    "bootstrap_pid": bootstrap_pid,
                    "bootstrap_proc_start_ticks": bootstrap_start_ticks,
                    "claim_sha256": claim["self_sha256"],
                    "coordinator_port": port,
                    "dmtcp_worker": restored_worker,
                    "generation": generation,
                    "pid": restored_worker["real_pid"],
                    "proc_start_ticks": restored_worker["proc_start_ticks"],
                    "proof_prefix_revalidated": True,
                    "single_process_peer_count": 1,
                    "source_checkpoint_manifest_sha256": checkpoint["self_sha256"],
                    "source_generation": source_generation,
                    "stale_tail_absent_after_restart": proof_preflight["injected_stale_tail"],
                },
            )
        except BaseException:
            _quit_coordinator_if_present(
                binaries["dmtcp_command"],
                generation_dir / "coordinator.port",
            )
            if restored_worker is not None:
                restored_pid = restored_worker["real_pid"]
                restored_ticks = restored_worker["proc_start_ticks"]
                with contextlib.suppress(ResumeControllerError):
                    _wait_pid_gone(
                        restored_pid,
                        restored_ticks,
                        timeout=READY_TIMEOUT_S,
                    )
                if _pid_identity(restored_pid, restored_ticks):
                    with contextlib.suppress(ProcessLookupError):
                        os.kill(restored_pid, signal.SIGKILL)
            with contextlib.suppress(ResumeControllerError):
                _kill_spawned_group(bootstrap_pid, bootstrap_start_ticks)
            raise
        return commit


def _generation_summary(root: Path, generation: int, *, verify_hashes: bool) -> dict[str, Any]:
    path = _generation_dir(root, generation)
    poison = _claim_without_commit(path)
    summary: dict[str, Any] = {"generation": generation, "poison_claim": poison}
    active: dict[str, Any] | None = None
    try:
        active = _active_commit(path, generation)
    except ResumeControllerError as exc:
        summary["active_error"] = str(exc)
    if active is not None:
        pid, ticks = active.get("pid"), active.get("proc_start_ticks")
        summary["active_kind"] = active["kind"]
        summary["pid_identity_alive"] = (
            type(pid) is int and type(ticks) is int and _pid_identity(pid, ticks)
        )
        summary["active_manifest_sha256"] = active["self_sha256"]
    checkpoint_path = path / "checkpoint.commit.json"
    if checkpoint_path.exists():
        try:
            checkpoint = _checkpoint_commit(path, generation)
            summary["checkpoint_manifest_sha256"] = checkpoint["self_sha256"]
            summary["checkpointed"] = True
            if verify_hashes:
                _verify_checkpoint_images(root, checkpoint)
                injection = _read_optional_injection(path)
                # Only the latest unconsumed checkpoint still owns the proof.
                if generation == _generation_numbers(root)[-1]:
                    _validate_proof_before_resume(root, checkpoint, injection)
                summary["checkpoint_hashes_valid"] = True
        except ResumeControllerError as exc:
            summary["checkpoint_error"] = str(exc)
    else:
        summary["checkpointed"] = False
    injection_path = path / "stale-tail.commit.json"
    summary["stale_tail_injected"] = injection_path.exists()
    return summary


def inspect(root: Path, *, verify_hashes: bool) -> dict[str, Any]:
    root = root.resolve(strict=True)
    with controller_lock(root, exclusive=False):
        config, binaries = _load_and_verify_config(root)
        numbers = _generation_numbers(root)
        generations = [
            _generation_summary(root, number, verify_hashes=verify_hashes)
            for number in numbers
        ]
        if not numbers:
            state = "INITIALIZED"
        elif any(item.get("poison_claim") or item.get("active_error") or item.get("checkpoint_error") for item in generations):
            state = "POISONED"
        elif generations[-1].get("checkpointed"):
            state = "CHECKPOINTED"
        elif generations[-1].get("pid_identity_alive"):
            state = "RUNNING"
        else:
            state = "INACTIVE_UNCHECKPOINTED"
        return {
            "authority": AUTHORITY,
            "config_manifest_sha256": config["self_sha256"],
            "dmtcp_command_sha256": stable_file_record(binaries["dmtcp_command"])["sha256"],
            "generations": generations,
            "hash_verification_requested": verify_hashes,
            "root": str(root),
            "state": state,
        }


def _emit(value: Mapping[str, Any]) -> None:
    sys.stdout.buffer.write(canonical_bytes(dict(value)) + b"\n")


def build_parser() -> argparse.ArgumentParser:
    parser = argparse.ArgumentParser(description=__doc__)
    sub = parser.add_subparsers(dest="command", required=True)

    init_parser = sub.add_parser("init", help="create a new TEST_ONLY root")
    init_parser.add_argument("--root", type=Path, required=True)
    init_parser.add_argument("--cnf", type=Path, required=True)
    init_parser.add_argument("--solver", type=Path, required=True)
    init_parser.add_argument("--dmtcp-prefix", type=Path, required=True)
    init_parser.add_argument("--solver-arg", action="append", default=[])
    init_parser.add_argument("--runtime-lib", type=Path, action="append", default=[])
    init_parser.add_argument("--runtime-libs-complete", action="store_true")

    for name in ("start", "checkpoint-stop", "resume", "status", "inspect"):
        command_parser = sub.add_parser(name)
        command_parser.add_argument("--root", type=Path, required=True)
    inject_parser = sub.add_parser("inject-stale-tail")
    inject_parser.add_argument("--root", type=Path, required=True)
    inject_parser.add_argument(STALE_FLAG, action="store_true")
    return parser


def main(argv: Sequence[str] | None = None) -> int:
    args = build_parser().parse_args(argv)
    try:
        if args.command == "init":
            result = initialize(
                args.root,
                cnf=args.cnf,
                solver=args.solver,
                dmtcp_prefix=args.dmtcp_prefix,
                solver_args=args.solver_arg,
                runtime_libs=args.runtime_lib,
                runtime_libs_complete=args.runtime_libs_complete,
            )
        elif args.command == "start":
            result = start(args.root)
        elif args.command == "checkpoint-stop":
            result = checkpoint_stop(args.root)
        elif args.command == "inject-stale-tail":
            result = inject_stale_tail(
                args.root,
                explicit_test_flag=getattr(args, "test_only_allow_stale_tail"),
            )
        elif args.command == "resume":
            result = resume(args.root)
        elif args.command == "status":
            result = inspect(args.root, verify_hashes=False)
        elif args.command == "inspect":
            result = inspect(args.root, verify_hashes=True)
        else:  # pragma: no cover - argparse makes this unreachable.
            raise ResumeControllerError("unknown command")
        _emit(result)
        return 0
    except (OSError, ResumeControllerError, subprocess.SubprocessError) as exc:
        print(f"ERROR: {exc}", file=sys.stderr)
        return 2


if __name__ == "__main__":
    raise SystemExit(main())
