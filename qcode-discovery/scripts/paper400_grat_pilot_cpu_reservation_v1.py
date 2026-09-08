#!/usr/bin/env python3
"""Transactional CPU reservations for the non-authoritative GRAT pilot.

The helper owns no solver, proof, terminal, aggregate, cleanup, systemd, or
process-control authority.  It only:

* audits four or eight CPUs while holding all three Paper400 lease locks;
* creates one private ``paper400-grat-pilot-v1-*`` bundle containing the
  immutable reservation consumed by ``paper400_grat_parallel_pilot_v1.py``;
* places the same reservation row in every production lease catalogue; and
* marks those rows RELEASED after an immutable, self-hashed pilot RESULT is
  bound to the bundle and no pilot child remains alive.

Catalogue publication is atomic per file.  A crash between catalogues leaves
an intentionally visible partial transaction.  Re-running ``reserve`` or
``release`` with the same output root can only complete that exact sealed
transaction; it can never substitute CPUs, a bundle, or a reservation hash.
No command deletes experiment or pilot data.
"""

from __future__ import annotations

import argparse
import contextlib
import ctypes
import dataclasses
import errno
import fcntl
import hashlib
import json
import math
import os
import pwd
import re
import stat
import sys
import time
import uuid
from collections.abc import Iterator, Mapping, Sequence
from pathlib import Path
from typing import Any


SCHEMA_VERSION = 1
GATE = "paper400-grat-pilot-cpu-reservation-transaction-v1"
AUDIT_KIND = GATE + "-audit"
RESERVE_KIND = GATE + "-reserve"
RELEASE_KIND = GATE + "-release"

PILOT_GATE = "paper400-grat-parallel-pilot-v1"
PILOT_PLAN_KIND = "paper400-grat-parallel-pilot-plan-v1"
PILOT_RESULT_KIND = "paper400-grat-parallel-pilot-result-v1"
PILOT_ABORT_KIND = "paper400-grat-pilot-recovery-abort-v1"
PILOT_FINAL_STATUSES = frozenset((
    "GRATCHK_ACCEPTED_PILOT_ONLY", "FAILED_CLOSED", "RECOVERED_ABORTED",
))
TRUSTED_PILOT_WRAPPER_SHA256 = (
    "583eac56a3af73e25897d507f28fefe676742d7439a7cc6069cb11f7dd29987b"
)
TRUSTED_TOOLCHAIN_MANIFEST_SHA256 = (
    "f53178ab4f5372c213411f2acb344133a91995b6e6000674792a20e7ffdfe057"
)
TRUSTED_PILOT_TOOL_SHA256S = {
    "gratgen": "9c945d7d4b983f3c6c2f40d73b8dd425f7c722edd48f45244f7c6c138ee6fbdb",
    "gratchk": "fc4cf9f93d8b834cf14aa4dee566c39d85e128c86e6cbdeac3c184b0c5d078c1",
}
PILOT_PLAN_FIELDS = {
    "schema_version", "kind", "gate", "created_utc", "label", "mode",
    "authoritative", "terminal_publication", "aggregate_publication",
    "cleanup_authority", "output_root", "inputs", "proof_quiescence",
    "proof_format", "threads", "cpus", "cpu_scheduler_authority", "resources",
    "stage_timeout_seconds", "toolchain", "toolchain_trust", "pipeline",
    "wrapper_source", "wrapper_source_fd_pinned_for_context_lifetime",
    "wrapper_source_initial_full_hash_verified",
    "manifest_sha256",
}
PILOT_FAILURE_RESULT_FIELDS = {
    "schema_version", "kind", "gate", "completed_utc", "status", "authoritative",
    "terminal_publication", "aggregate_publication", "cleanup_authority",
    "eligible_for_terminal_publication", "plan_sha256", "wrapper_source",
    "wrapper_source_final_full_reverify", "failure", "manifest_sha256",
}
PILOT_ACCEPTED_RESULT_FIELDS = {
    "schema_version", "kind", "gate", "completed_utc", "status", "authoritative",
    "terminal_publication", "aggregate_publication", "cleanup_authority",
    "eligible_for_terminal_publication", "artifacts_staged_only", "plan_sha256",
    "wrapper_source", "wrapper_source_final_full_reverify",
    "inputs", "scheduler_boundary_snapshots", "catalog_locks_held_across_stage",
    "toolchain", "cgroup_after_stages", "stages", "staged_artifacts",
    "manifest_sha256",
}
PILOT_ABORT_FIELDS = {
    "schema_version", "kind", "gate", "completed_at", "status",
    "authoritative", "terminal_publication", "aggregate_publication",
    "cleanup_authority", "eligible_for_terminal_publication", "plan_sha256",
    "reservation_sha256", "wrapper_source", "recovery", "record_sha256",
}
PILOT_WRAPPER_SOURCE_FIELDS = {
    "role", "requested_path", "realpath", "device", "inode", "bytes", "sha256",
    "mode", "uid", "gid", "links", "mtime_ns", "ctime_ns",
}
PILOT_SOURCE_REVERIFY_SUCCESS_FIELDS = {"checked_utc", "full_hash", "passed"}
PILOT_SOURCE_REVERIFY_FAILURE_FIELDS = {
    "checked_utc", "full_hash", "passed", "error",
}
PILOT_SOURCE_REVERIFY_ERROR_FIELDS = {"type", "message"}
PILOT_FILE_RECORD_FIELDS = PILOT_WRAPPER_SOURCE_FIELDS
PILOT_STAGE_FIELDS = {
    "stage", "exit_code", "elapsed_wall_seconds", "required_success_line",
    "status_stream", "observed_parallel_threads", "stdout", "stderr",
    "runtime", "process_identity", "process_policy",
}
PILOT_PROCESS_IDENTITY_FIELDS = {
    "pid", "proc_start_ticks", "argv", "observed_affinity",
    "observed_before_wait",
}
MAX_PILOT_WRAPPER_SOURCE_BYTES = 8 << 20
PILOT_WRAPPER_SOURCE_PATH = Path(__file__).resolve().with_name(
    "paper400_grat_parallel_pilot_v1.py"
)

RUN_ROOT = Path("/home/jing/paper400-runs")
CATALOGS = (
    RUN_ROOT / ".paper400-recursive-split-v1/cpu-leases.json",
    RUN_ROOT
    / ".paper400-recursive-certified-slot-handoffs-v1/borrow-control/cpu-leases.json",
    RUN_ROOT
    / ".paper400-recursive-nested-certified-slot-handoffs-v2/cpu-leases.json",
)
CATALOG_KIND = "paper400-dic5-recursive-cpu-lease-catalog-v1"
RESERVATION_KIND = "paper400-dic5-recursive-cpu-reservation-v1"

PILOT_ROOT_RE = re.compile(
    r"^paper400-grat-pilot-v1-[A-Za-z0-9][A-Za-z0-9._-]{0,95}$"
)
SHA256_RE = re.compile(r"^[0-9a-f]{64}$")
MAX_JSON_BYTES = 16 << 20
MAX_PROC_TEXT_BYTES = 1 << 20
MAX_PROC_ENTRIES = 1_000_000
MAX_DISCOVERY_ENTRIES = 16_384
MAX_CPU_ID = 1_048_575
RENAME_NOREPLACE = 1

CATALOG_FIELDS = {
    "schema_version", "kind", "leases", "updated_at", "catalog_sha256",
}
LEASE_FIELDS = {
    "cpu", "bundle", "reservation_sha256", "state", "created_at", "released_at",
}
RESERVATION_FIELDS = {
    "schema_version", "kind", "bundle", "cpus", "observations",
    "kernel_hardware_exclusive", "scheduler_lease_only", "created_at",
    "reservation_sha256",
}
OBSERVATION_FIELDS = {
    "cpu", "pinned_running_processes", "broad_affinity_running_process_count",
    "kernel_hardware_exclusive", "lease_scope",
}
RELEASE_RECORD_FIELDS = {
    "schema_version", "kind", "completed_at", "released_at", "bundle", "cpus",
    "reservation_sha256", "plan_sha256", "result_sha256", "result_status",
    "catalog_sha256s", "all_three_catalogs_released", "pilot_children_alive",
    "removed_data", "process_control_authority", "terminal_publication",
    "aggregate_publication", "cleanup_authority", "scientific_claim",
    "record_sha256",
}


class ReservationError(RuntimeError):
    """An invariant needed for a safe scheduler reservation did not hold."""


@dataclasses.dataclass(frozen=True)
class ReservationConfig:
    run_root: Path
    catalogs: tuple[Path, ...]
    output_root: Path
    threads: int
    requested_cpus: tuple[int, ...] | None = None
    proc_root: Path = Path("/proc")


@dataclasses.dataclass(frozen=True)
class ProcessScan:
    processes: tuple[dict[str, Any], ...]
    races: tuple[dict[str, Any], ...]


def _canonical(value: Any) -> bytes:
    try:
        return json.dumps(
            value,
            sort_keys=True,
            separators=(",", ":"),
            ensure_ascii=True,
            allow_nan=False,
        ).encode("ascii")
    except (TypeError, ValueError, UnicodeEncodeError) as exc:
        raise ReservationError(f"value is not canonical JSON: {exc}") from exc


def _seal(value: Mapping[str, Any], field: str = "record_sha256") -> dict[str, Any]:
    if type(value) is not dict or field in value:
        raise ReservationError("cannot seal malformed or already sealed record")
    result = dict(value)
    result[field] = hashlib.sha256(_canonical(result)).hexdigest()
    return result


def _selfhash_valid(value: Any, field: str) -> bool:
    if type(value) is not dict:
        return False
    digest = value.get(field)
    if type(digest) is not str or SHA256_RE.fullmatch(digest) is None:
        return False
    unsigned = dict(value)
    unsigned.pop(field)
    return hashlib.sha256(_canonical(unsigned)).hexdigest() == digest


def _finite(value: Any) -> bool:
    if type(value) not in {int, float}:
        return False
    try:
        return math.isfinite(float(value))
    except OverflowError:
        return False


def _valid_cpu(value: Any) -> bool:
    return type(value) is int and 0 <= value <= MAX_CPU_ID


def _absolute_normal(path: Path, role: str) -> Path:
    value = Path(path)
    if not value.is_absolute() or str(value) != os.path.abspath(str(value)):
        raise ReservationError(f"{role} must be an absolute normalized path")
    return value


def _is_within(path: Path, root: Path) -> bool:
    text = str(path)
    return text == str(root) or text.startswith(str(root) + os.sep)


def _safe_directory(path: Path, role: str, *, mode: int | None = None) -> Path:
    candidate = _absolute_normal(path, role)
    try:
        edge = candidate.lstat()
        resolved = candidate.resolve(strict=True)
    except (OSError, RuntimeError) as exc:
        raise ReservationError(f"cannot resolve {role}: {candidate}") from exc
    if (
        resolved != candidate
        or stat.S_ISLNK(edge.st_mode)
        or not stat.S_ISDIR(edge.st_mode)
        or edge.st_uid != os.geteuid()
        or (mode is not None and stat.S_IMODE(edge.st_mode) != mode)
    ):
        raise ReservationError(f"unsafe {role}: {candidate}")
    return candidate


def _reject_duplicate_keys(pairs: list[tuple[str, Any]]) -> dict[str, Any]:
    result: dict[str, Any] = {}
    for key, value in pairs:
        if key in result:
            raise ReservationError(f"duplicate JSON key: {key}")
        result[key] = value
    return result


def _read_json(path: Path, role: str, *, required_mode: int | None = None) -> dict[str, Any]:
    candidate = _absolute_normal(path, role)
    flags = os.O_RDONLY | os.O_CLOEXEC
    if hasattr(os, "O_NOFOLLOW"):
        flags |= os.O_NOFOLLOW
    try:
        before_path = candidate.lstat()
        fd = os.open(candidate, flags)
    except OSError as exc:
        raise ReservationError(f"cannot open {role}: {candidate}") from exc
    try:
        before = os.fstat(fd)
        if (
            not stat.S_ISREG(before.st_mode)
            or stat.S_ISLNK(before_path.st_mode)
            or before.st_uid != os.geteuid()
            or before.st_nlink != 1
            or before.st_size > MAX_JSON_BYTES
            or (before.st_dev, before.st_ino) != (before_path.st_dev, before_path.st_ino)
            or (
                required_mode is not None
                and stat.S_IMODE(before.st_mode) != required_mode
            )
        ):
            raise ReservationError(f"unsafe {role}: {candidate}")
        payload = bytearray()
        while len(payload) <= MAX_JSON_BYTES:
            chunk = os.read(fd, min(64 << 10, MAX_JSON_BYTES + 1 - len(payload)))
            if not chunk:
                break
            payload.extend(chunk)
        after = os.fstat(fd)
        after_path = candidate.lstat()
        if (
            len(payload) > MAX_JSON_BYTES
            or (
                before.st_dev, before.st_ino, before.st_mode, before.st_uid,
                before.st_gid, before.st_nlink, before.st_size, before.st_mtime_ns,
                before.st_ctime_ns,
            ) != (
                after.st_dev, after.st_ino, after.st_mode, after.st_uid,
                after.st_gid, after.st_nlink, after.st_size, after.st_mtime_ns,
                after.st_ctime_ns,
            )
            or (
                after.st_dev, after.st_ino, after.st_mode, after.st_uid,
                after.st_gid, after.st_nlink, after.st_size, after.st_mtime_ns,
                after.st_ctime_ns,
            ) != (
                after_path.st_dev, after_path.st_ino, after_path.st_mode,
                after_path.st_uid, after_path.st_gid, after_path.st_nlink,
                after_path.st_size, after_path.st_mtime_ns, after_path.st_ctime_ns,
            )
        ):
            raise ReservationError(f"{role} changed while being read")
        try:
            value = json.loads(
                bytes(payload).decode("ascii"), object_pairs_hook=_reject_duplicate_keys,
            )
        except (UnicodeDecodeError, json.JSONDecodeError) as exc:
            raise ReservationError(f"cannot decode {role}: {candidate}") from exc
        if type(value) is not dict:
            raise ReservationError(f"{role} must contain one JSON object")
        return value
    finally:
        os.close(fd)


def _fsync_directory(path: Path) -> None:
    descriptor = os.open(path, os.O_RDONLY | os.O_DIRECTORY | os.O_CLOEXEC)
    try:
        os.fsync(descriptor)
    finally:
        os.close(descriptor)


def _rename_noreplace(source: Path, target: Path, role: str) -> None:
    """Atomically publish a prepared filesystem object without overwriting."""

    libc = ctypes.CDLL(None, use_errno=True)
    renameat2 = getattr(libc, "renameat2", None)
    if renameat2 is None:
        raise ReservationError("renameat2(RENAME_NOREPLACE) is required")
    renameat2.argtypes = [
        ctypes.c_int, ctypes.c_char_p, ctypes.c_int, ctypes.c_char_p, ctypes.c_uint,
    ]
    renameat2.restype = ctypes.c_int
    result = renameat2(
        -100,
        os.fsencode(source),
        -100,
        os.fsencode(target),
        RENAME_NOREPLACE,
    )
    if result != 0:
        problem = ctypes.get_errno()
        if problem == errno.EEXIST:
            raise ReservationError(f"refusing to overwrite existing {role}")
        raise ReservationError(
            f"cannot atomically publish {role}: {os.strerror(problem)}"
        )


def _write_exclusive(path: Path, value: Mapping[str, Any], *, mode: int = 0o400) -> None:
    payload = _canonical(value)
    temporary = path.with_name(
        f".{path.name}.{GATE}.{os.getpid()}.{uuid.uuid4().hex}.tmp"
    )
    flags = os.O_WRONLY | os.O_CREAT | os.O_EXCL | os.O_CLOEXEC
    if hasattr(os, "O_NOFOLLOW"):
        flags |= os.O_NOFOLLOW
    descriptor = os.open(temporary, flags, mode)
    try:
        os.fchmod(descriptor, mode)
        offset = 0
        while offset < len(payload):
            written = os.write(descriptor, payload[offset:])
            if written <= 0:
                raise ReservationError("short immutable record write")
            offset += written
        os.fsync(descriptor)
    except BaseException:
        os.close(descriptor)
        with contextlib.suppress(OSError):
            temporary.unlink()
        raise
    else:
        os.close(descriptor)
    try:
        _rename_noreplace(temporary, path, f"immutable file {path.name}")
        _fsync_directory(path.parent)
    except BaseException:
        with contextlib.suppress(OSError):
            temporary.unlink()
        raise


def _atomic_catalog_write(
    path: Path,
    value: Mapping[str, Any],
    *,
    expected_catalog_sha256: str,
) -> None:
    """Atomically replace one locked catalog; never expose a partial JSON file."""

    payload = _canonical(value) + b"\n"
    temporary = path.with_name(f".{path.name}.{GATE}.{os.getpid()}.{uuid.uuid4().hex}.tmp")
    flags = os.O_WRONLY | os.O_CREAT | os.O_EXCL | os.O_CLOEXEC
    if hasattr(os, "O_NOFOLLOW"):
        flags |= os.O_NOFOLLOW
    descriptor = os.open(temporary, flags, 0o600)
    try:
        os.fchmod(descriptor, 0o600)
        offset = 0
        while offset < len(payload):
            written = os.write(descriptor, payload[offset:])
            if written <= 0:
                raise ReservationError("short catalog write")
            offset += written
        os.fsync(descriptor)
    except BaseException:
        os.close(descriptor)
        with contextlib.suppress(OSError):
            temporary.unlink()
        raise
    else:
        os.close(descriptor)
    try:
        current = _read_json(path, "locked CPU lease catalog", required_mode=0o600)
        if (
            current.get("catalog_sha256") != expected_catalog_sha256
            or not _selfhash_valid(current, "catalog_sha256")
        ):
            raise ReservationError("CPU lease catalog changed before atomic publication")
        os.replace(temporary, path)
        _fsync_directory(path.parent)
    except BaseException:
        with contextlib.suppress(OSError):
            temporary.unlink()
        raise


def _load_catalog(path: Path, run_root: Path) -> dict[str, Any]:
    value = _read_json(path, "Paper400 CPU lease catalog", required_mode=0o600)
    if (
        set(value) != CATALOG_FIELDS
        or value.get("schema_version") != SCHEMA_VERSION
        or value.get("kind") != CATALOG_KIND
        or type(value.get("leases")) is not list
        or not _finite(value.get("updated_at"))
        or not _selfhash_valid(value, "catalog_sha256")
    ):
        raise ReservationError(f"malformed CPU lease catalog: {path}")
    active: set[int] = set()
    for row in value["leases"]:
        if (
            type(row) is not dict
            or set(row) != LEASE_FIELDS
            or not _valid_cpu(row.get("cpu"))
            or type(row.get("bundle")) is not str
            or SHA256_RE.fullmatch(str(row.get("reservation_sha256", ""))) is None
            or row.get("state") not in {"RESERVED", "RELEASED"}
            or not _finite(row.get("created_at"))
            or (
                row.get("state") == "RESERVED"
                and row.get("released_at") is not None
            )
            or (
                row.get("state") == "RELEASED"
                and not _finite(row.get("released_at"))
            )
        ):
            raise ReservationError(f"malformed CPU lease row: {path}")
        try:
            bundle = _absolute_normal(Path(row["bundle"]), "lease bundle")
        except ReservationError as exc:
            raise ReservationError(f"lease bundle is malformed: {path}") from exc
        if not _is_within(bundle, run_root):
            raise ReservationError(f"lease bundle leaves Paper400 run root: {path}")
        if row["state"] == "RESERVED":
            if row["cpu"] in active:
                raise ReservationError(f"duplicate active CPU in catalog: {path}")
            active.add(row["cpu"])
    return value


def _discover_catalogs(run_root: Path) -> tuple[Path, ...]:
    discovered: set[Path] = set()
    examined = 0
    try:
        first_level = sorted(run_root.iterdir(), key=lambda item: item.name)
    except OSError as exc:
        raise ReservationError("cannot inventory Paper400 lease catalogs") from exc
    for first in first_level:
        examined += 1
        if examined > MAX_DISCOVERY_ENTRIES:
            raise ReservationError("lease catalog discovery exceeded its bound")
        try:
            info = first.lstat()
        except OSError as exc:
            raise ReservationError("lease catalog inventory changed") from exc
        if stat.S_ISLNK(info.st_mode) or not stat.S_ISDIR(info.st_mode):
            continue
        candidate = first / "cpu-leases.json"
        if candidate.exists() or candidate.is_symlink():
            discovered.add(candidate)
        try:
            second_level = sorted(first.iterdir(), key=lambda item: item.name)
        except OSError as exc:
            raise ReservationError("lease catalog inventory changed") from exc
        for second in second_level:
            examined += 1
            if examined > MAX_DISCOVERY_ENTRIES:
                raise ReservationError("lease catalog discovery exceeded its bound")
            try:
                info = second.lstat()
            except OSError as exc:
                raise ReservationError("lease catalog inventory changed") from exc
            if stat.S_ISLNK(info.st_mode) or not stat.S_ISDIR(info.st_mode):
                continue
            candidate = second / "cpu-leases.json"
            if candidate.exists() or candidate.is_symlink():
                discovered.add(candidate)
    return tuple(sorted(discovered, key=str))


def _open_catalog_lock(catalog: Path) -> int:
    path = catalog.with_name("cpu-leases.lock")
    flags = os.O_RDWR | os.O_CLOEXEC
    if hasattr(os, "O_NOFOLLOW"):
        flags |= os.O_NOFOLLOW
    try:
        descriptor = os.open(path, flags)
    except OSError as exc:
        raise ReservationError(f"cannot open scheduler lock: {path}") from exc
    try:
        info = os.fstat(descriptor)
        edge = path.lstat()
        if (
            not stat.S_ISREG(info.st_mode)
            or info.st_uid != os.geteuid()
            or info.st_nlink != 1
            or stat.S_IMODE(info.st_mode) != 0o600
            or (info.st_dev, info.st_ino) != (edge.st_dev, edge.st_ino)
        ):
            raise ReservationError(f"unsafe scheduler lock: {path}")
        try:
            fcntl.flock(descriptor, fcntl.LOCK_EX | fcntl.LOCK_NB)
        except BlockingIOError as exc:
            raise ReservationError(f"scheduler lock is busy: {path}") from exc
        return descriptor
    except BaseException:
        os.close(descriptor)
        raise


@contextlib.contextmanager
def _catalog_locks(config: ReservationConfig) -> Iterator[None]:
    descriptors: list[int] = []
    try:
        ordered = sorted(
            config.catalogs,
            key=lambda path: str(path.with_name("cpu-leases.lock")),
        )
        for catalog in ordered:
            descriptors.append(_open_catalog_lock(catalog))
        if _discover_catalogs(config.run_root) != tuple(sorted(config.catalogs, key=str)):
            raise ReservationError("catalog inventory changed under scheduler locks")
        yield
        if _discover_catalogs(config.run_root) != tuple(sorted(config.catalogs, key=str)):
            raise ReservationError("catalog inventory changed before scheduler unlock")
    finally:
        for descriptor in reversed(descriptors):
            with contextlib.suppress(OSError):
                fcntl.flock(descriptor, fcntl.LOCK_UN)
            with contextlib.suppress(OSError):
                os.close(descriptor)


def _parse_proc_stat(payload: str, pid: int) -> tuple[str, str, int]:
    prefix = f"{pid} ("
    close = payload.rfind(") ")
    if not payload.startswith(prefix) or close < len(prefix):
        raise ReservationError(f"malformed /proc/{pid}/stat")
    fields = payload[close + 2 :].split()
    if len(fields) < 20:
        raise ReservationError(f"short /proc/{pid}/stat")
    try:
        start_ticks = int(fields[19])
    except ValueError as exc:
        raise ReservationError(f"malformed /proc/{pid}/stat start time") from exc
    return payload[len(prefix):close], fields[0], start_ticks


def _read_proc(path: Path, cap: int = MAX_PROC_TEXT_BYTES) -> bytes:
    flags = os.O_RDONLY | os.O_CLOEXEC
    if hasattr(os, "O_NOFOLLOW"):
        flags |= os.O_NOFOLLOW
    descriptor = os.open(path, flags)
    try:
        payload = bytearray()
        while len(payload) <= cap:
            chunk = os.read(descriptor, min(64 << 10, cap + 1 - len(payload)))
            if not chunk:
                break
            payload.extend(chunk)
        if len(payload) > cap:
            raise ReservationError(f"oversized proc record: {path}")
        return bytes(payload)
    finally:
        os.close(descriptor)


def _decode_argv(payload: bytes) -> tuple[str, ...]:
    if not payload:
        return ()
    if not payload.endswith(b"\0"):
        raise ReservationError("unterminated live process argv")
    return tuple(
        item.decode("utf-8", "surrogateescape") for item in payload[:-1].split(b"\0")
    )


def _compute_kind(comm: str, argv: Sequence[str]) -> str | None:
    markers = {os.path.basename(item).lower() for item in argv}
    for index, item in enumerate(argv):
        if item == "--argv0" and index + 1 < len(argv):
            markers.add(os.path.basename(argv[index + 1]).lower())
        elif item.startswith("--argv0="):
            markers.add(os.path.basename(item.split("=", 1)[1]).lower())
    comm_value = comm.lower()
    if comm_value == "cadical" or "cadical" in markers:
        return "cadical"
    if (
        comm_value in {"final-drat-replay", "final-drat-repl", "drat-trim"}
        or markers & {"final-drat-replay", "drat-trim"}
    ):
        return "drat"
    if (
        comm_value in {"final-lrat-replay", "final-lrat-repl", "lrat-check"}
        or markers & {"final-lrat-replay", "lrat-check"}
    ):
        return "lrat"
    if comm_value in {"gratgen", "gratchk"} or markers & {"gratgen", "gratchk"}:
        return "grat"
    return None


def _known_benign_inaccessible_cwd(
    comm: str, argv: Sequence[str], cgroup: str,
) -> bool:
    """Recognize only reviewed persistent session helpers."""

    uid = os.geteuid()
    sd_pam = (
        comm == "(sd-pam)"
        and tuple(argv) == ("(sd-pam)",)
        and cgroup
        == f"0::/user.slice/user-{uid}.slice/user@{uid}.service/init.scope\n"
    )
    if sd_pam:
        return True
    try:
        username = pwd.getpwuid(uid).pw_name
    except (KeyError, OSError):
        return False
    sshd_argv = tuple(argv)
    return (
        comm == "sshd"
        and len(sshd_argv) >= 2
        and sshd_argv[0] == f"sshd: {username}@notty"
        and all(item == "" for item in sshd_argv[1:])
        and re.fullmatch(
            rf"0::/user\.slice/user-{uid}\.slice/session-[0-9]+\.scope\n",
            cgroup,
        )
        is not None
    )


def _path_text_within(value: str, root: Path) -> bool:
    return value == str(root) or value.startswith(str(root) + os.sep)


def _scan_processes(config: ReservationConfig) -> ProcessScan:
    """Return an identity-stable same-UID process snapshot.

    Only short procfs reads occur.  Candidate Paper400 compute races are
    retained as blockers instead of being silently treated as free CPUs.
    """

    try:
        entries = sorted(
            (entry for entry in config.proc_root.iterdir() if entry.name.isdecimal()),
            key=lambda entry: int(entry.name),
        )
    except OSError as exc:
        raise ReservationError("cannot enumerate procfs") from exc
    if len(entries) > MAX_PROC_ENTRIES:
        raise ReservationError("procfs entry bound exceeded")
    records: list[dict[str, Any]] = []
    races: list[dict[str, Any]] = []
    for entry in entries:
        pid = int(entry.name)
        candidate_seen = False
        benign_cwd_unavailable = False
        try:
            if entry.stat().st_uid != os.geteuid():
                continue
            first_raw = _read_proc(entry / "stat").decode("ascii")
            comm, state, start_ticks = _parse_proc_stat(first_raw, pid)
            if state in {"Z", "X", "x"}:
                continue
            candidate_seen = _compute_kind(comm, ()) is not None
            argv_raw = _read_proc(entry / "cmdline")
            argv = _decode_argv(argv_raw)
            kind = _compute_kind(comm, argv)
            argv_paper400 = any(
                _path_text_within(item, config.run_root) for item in argv
            )
            candidate_seen = candidate_seen or kind is not None or argv_paper400
            cgroup_raw = _read_proc(entry / "cgroup")
            cgroup = cgroup_raw.decode("utf-8", "surrogateescape")
            paper400_without_cwd = (
                "paper400" in cgroup.lower()
                or argv_paper400
            )
            # A compute-looking process may be Paper400-bound only through cwd;
            # likewise an existing Paper400 cgroup/argv binding must not lose
            # evidence merely because procfs denies cwd inspection.
            candidate_seen = kind is not None or paper400_without_cwd
            try:
                cwd = os.readlink(entry / "cwd")
            except (FileNotFoundError, ProcessLookupError):
                cwd = ""
            except PermissionError as exc:
                if (
                    exc.errno != errno.EACCES
                    or candidate_seen
                    or not _known_benign_inaccessible_cwd(comm, argv, cgroup)
                ):
                    raise ReservationError(
                        f"cannot inspect cwd of candidate same-UID PID {pid}"
                    ) from exc
                # This exact reviewed helper may be skipped only after its
                # comm/argv/cgroup, PID identity, affinity, and denial state
                # are all proven stable below.
                cwd = ""
                benign_cwd_unavailable = True
            cwd_paper400 = _path_text_within(cwd, config.run_root)
            candidate_seen = candidate_seen or cwd_paper400
            affinity_first = sorted(os.sched_getaffinity(pid))
            second_raw = _read_proc(entry / "stat").decode("ascii")
            second_comm, second_state, second_ticks = _parse_proc_stat(second_raw, pid)
            if comm != second_comm or start_ticks != second_ticks:
                races.append({"pid": pid, "reason": "identity_or_affinity_changed"})
                continue
            candidate_seen = (
                candidate_seen or _compute_kind(second_comm, ()) is not None
            )
            second_argv_raw = _read_proc(entry / "cmdline")
            second_argv = _decode_argv(second_argv_raw)
            second_kind = _compute_kind(second_comm, second_argv)
            second_argv_paper400 = any(
                _path_text_within(item, config.run_root)
                for item in second_argv
            )
            candidate_seen = (
                candidate_seen
                or second_kind is not None
                or second_argv_paper400
            )
            second_cgroup_raw = _read_proc(entry / "cgroup")
            second_cgroup = second_cgroup_raw.decode("utf-8", "surrogateescape")
            second_paper400_without_cwd = (
                "paper400" in second_cgroup.lower()
                or second_argv_paper400
            )
            candidate_seen = (
                candidate_seen
                or second_kind is not None
                or second_paper400_without_cwd
            )
            affinity_second = sorted(os.sched_getaffinity(pid))
            if (
                argv_raw != second_argv_raw
                or cgroup_raw != second_cgroup_raw
                or affinity_first != affinity_second
            ):
                if candidate_seen or benign_cwd_unavailable:
                    races.append({"pid": pid, "reason": "identity_or_affinity_changed"})
                continue
            if second_state in {"Z", "X", "x"}:
                if candidate_seen or benign_cwd_unavailable:
                    races.append({"pid": pid, "reason": "became_terminal"})
                continue
            if not affinity_first:
                raise ReservationError(f"PID {pid} has empty scheduler affinity")
            if benign_cwd_unavailable:
                try:
                    os.readlink(entry / "cwd")
                except PermissionError as exc:
                    if exc.errno != errno.EACCES:
                        raise ReservationError(
                            f"cannot recheck benign cwd denial for same-UID PID {pid}"
                        ) from exc
                    # The exact reviewed session-helper signature and its
                    # inaccessible cwd were stable across the observation.
                    continue
                except (FileNotFoundError, ProcessLookupError):
                    races.append({"pid": pid, "reason": "disappeared_during_scan"})
                    continue
                except OSError as exc:
                    raise ReservationError(
                        f"cannot recheck benign cwd denial for same-UID PID {pid}"
                    ) from exc
                races.append({"pid": pid, "reason": "cwd_access_changed"})
                continue
            try:
                second_cwd = os.readlink(entry / "cwd")
            except (FileNotFoundError, ProcessLookupError):
                if candidate_seen:
                    races.append({"pid": pid, "reason": "disappeared_during_scan"})
                continue
            except PermissionError:
                # A formerly readable cwd becoming opaque can hide a move into
                # the Paper400 tree, even for a process with no compute marker.
                races.append({"pid": pid, "reason": "cwd_access_changed"})
                continue
            except OSError as exc:
                raise ReservationError(
                    f"cannot recheck cwd identity for same-UID PID {pid}"
                ) from exc
            if second_cwd != cwd:
                races.append({"pid": pid, "reason": "cwd_identity_changed"})
                continue
            paper400_bound = paper400_without_cwd or cwd_paper400
            records.append({
                "pid": pid,
                "start_ticks": start_ticks,
                "state": second_state,
                "comm": comm,
                "argv": list(argv),
                "cmdline_sha256": hashlib.sha256(argv_raw).hexdigest(),
                "cgroup_sha256": hashlib.sha256(cgroup_raw).hexdigest(),
                "cgroup": cgroup,
                "cwd": cwd,
                "compute_kind": kind,
                "paper400_bound": paper400_bound,
                "affinity": affinity_first,
                "affinity_class": "exact" if len(affinity_first) == 1 else "broad",
            })
        except BaseException as exc:
            transient = isinstance(exc, (FileNotFoundError, ProcessLookupError)) or (
                isinstance(exc, OSError) and exc.errno in {errno.ENOENT, errno.ESRCH}
            )
            if transient:
                if candidate_seen or benign_cwd_unavailable:
                    races.append({"pid": pid, "reason": "disappeared_during_scan"})
                continue
            if isinstance(exc, PermissionError):
                raise ReservationError(
                    f"cannot prove same-UID PID {pid} is unrelated to the pilot"
                ) from exc
            raise
    records.sort(key=lambda row: (row["pid"], row["start_ticks"]))
    races.sort(key=lambda row: (row["pid"], row["reason"]))
    return ProcessScan(tuple(records), tuple(races))


def _compute_conflicts(scan: ProcessScan, cpus: set[int]) -> list[dict[str, Any]]:
    conflicts = []
    for row in scan.processes:
        if row.get("compute_kind") is None or row.get("paper400_bound") is not True:
            continue
        overlap = sorted(cpus.intersection(row["affinity"]))
        if overlap:
            conflicts.append({
                "pid": row["pid"],
                "start_ticks": row["start_ticks"],
                "state": row["state"],
                "compute_kind": row["compute_kind"],
                "affinity_class": row["affinity_class"],
                "affinity": row["affinity"],
                "overlap": overlap,
                "cmdline_sha256": row["cmdline_sha256"],
                "cgroup_sha256": row["cgroup_sha256"],
            })
    return conflicts


def _validate_config(config: ReservationConfig) -> ReservationConfig:
    run_root = _safe_directory(config.run_root, "Paper400 run root", mode=0o700)
    output_root = _absolute_normal(config.output_root, "pilot output root")
    if output_root.parent != run_root or PILOT_ROOT_RE.fullmatch(output_root.name) is None:
        raise ReservationError(
            "output root must be a direct paper400-grat-pilot-v1-* child of run root"
        )
    if config.threads not in {4, 8}:
        raise ReservationError("GRAT reservation must contain exactly 4 or 8 CPUs")
    catalogs = tuple(sorted(
        (_absolute_normal(path, "CPU lease catalog") for path in config.catalogs),
        key=str,
    ))
    if len(catalogs) != 3 or len(set(catalogs)) != 3:
        raise ReservationError("exactly three distinct production catalogs are required")
    if any(not _is_within(path, run_root) for path in catalogs):
        raise ReservationError("CPU lease catalog leaves Paper400 run root")
    if _discover_catalogs(run_root) != catalogs:
        raise ReservationError("configured catalogs differ from bounded production discovery")
    requested = config.requested_cpus
    if requested is not None:
        if (
            len(requested) != config.threads
            or len(set(requested)) != len(requested)
            or any(not _valid_cpu(cpu) for cpu in requested)
        ):
            raise ReservationError("requested CPUs do not match the 4/8-thread reservation")
        requested = tuple(sorted(requested))
    proc_root = _absolute_normal(config.proc_root, "proc root")
    return ReservationConfig(run_root, catalogs, output_root, config.threads, requested, proc_root)


def _catalog_state(catalogs: Sequence[Mapping[str, Any]]) -> tuple[set[int], set[int]]:
    ever_listed: set[int] = set()
    active: set[int] = set()
    for catalog in catalogs:
        for row in catalog["leases"]:
            ever_listed.add(row["cpu"])
            if row["state"] == "RESERVED":
                active.add(row["cpu"])
    return ever_listed, active


def _audit_locked(config: ReservationConfig) -> dict[str, Any]:
    if os.path.lexists(config.output_root):
        raise ReservationError("pilot output root already exists; audit is new-root only")
    catalogs = [_load_catalog(path, config.run_root) for path in config.catalogs]
    ever_listed, active = _catalog_state(catalogs)
    try:
        allowed = sorted(os.sched_getaffinity(0))
    except OSError as exc:
        raise ReservationError("cannot inspect controller scheduler affinity") from exc
    if not allowed or any(not _valid_cpu(cpu) for cpu in allowed):
        raise ReservationError("controller scheduler affinity is malformed")
    scan = _scan_processes(config)
    compute_cpus = {
        cpu
        for row in scan.processes
        if row.get("compute_kind") is not None and row.get("paper400_bound") is True
        for cpu in row["affinity"]
    }
    eligible = [
        cpu for cpu in allowed if cpu not in ever_listed and cpu not in compute_cpus
    ]
    selected = list(config.requested_cpus) if config.requested_cpus is not None else (
        eligible[: config.threads]
    )
    blockers: list[str] = []
    if len(selected) != config.threads:
        blockers.append("fewer than the requested 4/8 CPUs are eligible")
    requested_ineligible = sorted(set(selected).difference(eligible))
    if requested_ineligible:
        blockers.append("requested CPUs are historically listed, active, or compute-conflicted")
    conflicts = _compute_conflicts(scan, set(selected))
    if conflicts:
        blockers.append("selected CPUs intersect live exact/broad Paper400 compute")
    if scan.races:
        blockers.append("Paper400 process identity changed during the admission scan")
    return _seal({
        "schema_version": SCHEMA_VERSION,
        "kind": AUDIT_KIND,
        "observed_at": time.time(),
        "run_root": str(config.run_root),
        "output_root": str(config.output_root),
        "threads": config.threads,
        "allowed_cpus": allowed,
        "ever_listed_cpus": sorted(ever_listed),
        "active_cpus": sorted(active),
        "compute_occupied_cpus": sorted(compute_cpus),
        "eligible_cpus": eligible,
        "selected_cpus": selected,
        "catalog_sha256s": {
            str(path): value["catalog_sha256"]
            for path, value in zip(config.catalogs, catalogs)
        },
        "live_compute_conflicts": conflicts,
        "process_scan_races": list(scan.races),
        "blockers": blockers,
        "go": not blockers,
        "scheduler_lease_only": True,
        "kernel_hardware_exclusive": False,
        "scientific_claim": False,
    })


def audit(config: ReservationConfig) -> dict[str, Any]:
    config = _validate_config(config)
    with _catalog_locks(config):
        return _audit_locked(config)


def _reservation(output_root: Path, cpus: Sequence[int], created_at: float) -> dict[str, Any]:
    observations = [
        {
            "cpu": cpu,
            "pinned_running_processes": [],
            "broad_affinity_running_process_count": 0,
            "kernel_hardware_exclusive": False,
            "lease_scope": GATE,
        }
        for cpu in cpus
    ]
    return _seal({
        "schema_version": SCHEMA_VERSION,
        "kind": RESERVATION_KIND,
        "bundle": str(output_root),
        "cpus": list(cpus),
        "observations": observations,
        "kernel_hardware_exclusive": False,
        "scheduler_lease_only": True,
        "created_at": created_at,
    }, "reservation_sha256")


def _load_reservation(config: ReservationConfig) -> dict[str, Any]:
    value = _read_json(
        config.output_root / "cpu-reservation.json",
        "GRAT pilot CPU reservation",
        required_mode=0o400,
    )
    observations = value.get("observations")
    cpus = value.get("cpus")
    if (
        set(value) != RESERVATION_FIELDS
        or value.get("schema_version") != SCHEMA_VERSION
        or value.get("kind") != RESERVATION_KIND
        or value.get("bundle") != str(config.output_root)
        or type(cpus) is not list
        or cpus != sorted(cpus)
        or len(cpus) != config.threads
        or len(set(cpus)) != len(cpus)
        or any(not _valid_cpu(cpu) for cpu in cpus)
        or (
            config.requested_cpus is not None
            and cpus != list(config.requested_cpus)
        )
        or type(observations) is not list
        or len(observations) != len(cpus)
        or [item.get("cpu") if type(item) is dict else None for item in observations] != cpus
        or any(
            type(item) is not dict
            or set(item) != OBSERVATION_FIELDS
            or item.get("pinned_running_processes") != []
            or item.get("broad_affinity_running_process_count") != 0
            or item.get("kernel_hardware_exclusive") is not False
            or item.get("lease_scope") != GATE
            for item in observations
        )
        or value.get("kernel_hardware_exclusive") is not False
        or value.get("scheduler_lease_only") is not True
        or not _finite(value.get("created_at"))
        or not _selfhash_valid(value, "reservation_sha256")
    ):
        raise ReservationError("GRAT pilot CPU reservation is malformed or cross-bound")
    return value


def _create_reservation_root(config: ReservationConfig, cpus: Sequence[int]) -> dict[str, Any]:
    staging = config.run_root / (
        f".{GATE}.{os.getpid()}.{uuid.uuid4().hex}.tmp"
    )
    os.mkdir(staging, 0o700)
    os.chmod(staging, 0o700, follow_symlinks=False)
    value = _reservation(config.output_root, cpus, time.time())
    try:
        _write_exclusive(staging / "cpu-reservation.json", value, mode=0o400)
        _fsync_directory(staging)
        _rename_noreplace(staging, config.output_root, "pilot root")
        _fsync_directory(config.run_root)
    except BaseException:
        # Only the helper's unpublished staging object is eligible for this
        # cleanup.  The target bundle and every experiment artifact remain
        # untouched; a process crash merely leaves the staging object visible.
        with contextlib.suppress(OSError):
            (staging / "cpu-reservation.json").unlink()
        with contextlib.suppress(OSError):
            staging.rmdir()
        raise
    return value


def _validate_recovery_root(config: ReservationConfig) -> dict[str, Any]:
    root = _safe_directory(config.output_root, "existing pilot output root", mode=0o700)
    try:
        entries = sorted(item.name for item in root.iterdir())
    except OSError as exc:
        raise ReservationError("cannot inventory existing pilot output root") from exc
    if entries != ["cpu-reservation.json"]:
        raise ReservationError("reserve recovery requires a pristine reservation-only root")
    return _load_reservation(config)


def _matching_rows(
    catalog: Mapping[str, Any], reservation: Mapping[str, Any], cpu: int,
) -> list[dict[str, Any]]:
    return [row for row in catalog["leases"] if row["cpu"] == cpu]


def _assert_reserve_replayable(
    catalogs: Sequence[Mapping[str, Any]], reservation: Mapping[str, Any],
) -> None:
    expected = (reservation["bundle"], reservation["reservation_sha256"])
    expected_cpus = set(reservation["cpus"])
    for catalog in catalogs:
        related = [
            row for row in catalog["leases"]
            if row["bundle"] == reservation["bundle"]
            or row["reservation_sha256"] == reservation["reservation_sha256"]
        ]
        if any(
            row["cpu"] not in expected_cpus
            or (row["bundle"], row["reservation_sha256"]) != expected
            for row in related
        ):
            raise ReservationError("reservation identity is reused by a foreign catalog row")
        for cpu in reservation["cpus"]:
            rows = _matching_rows(catalog, reservation, cpu)
            if len(rows) > 1:
                raise ReservationError("reserved CPU has multiple historical catalog rows")
            if rows and (
                (rows[0]["bundle"], rows[0]["reservation_sha256"]) != expected
                or rows[0]["state"] != "RESERVED"
                or rows[0]["created_at"] != reservation["created_at"]
                or rows[0]["released_at"] is not None
            ):
                raise ReservationError("reserved CPU has a foreign or non-active catalog row")


def _append_missing_rows(
    config: ReservationConfig,
    catalogs: list[dict[str, Any]],
    reservation: Mapping[str, Any],
) -> None:
    for path, catalog in zip(config.catalogs, catalogs):
        present = {
            cpu
            for cpu in reservation["cpus"]
            if _matching_rows(catalog, reservation, cpu)
        }
        if present == set(reservation["cpus"]):
            continue
        unsigned = dict(catalog)
        unsigned.pop("catalog_sha256")
        unsigned["updated_at"] = time.time()
        unsigned["leases"] = [*catalog["leases"], *[
            {
                "cpu": cpu,
                "bundle": reservation["bundle"],
                "reservation_sha256": reservation["reservation_sha256"],
                "state": "RESERVED",
                "created_at": reservation["created_at"],
                "released_at": None,
            }
            for cpu in reservation["cpus"]
            if cpu not in present
        ]]
        replacement = _seal(unsigned, "catalog_sha256")
        _atomic_catalog_write(
            path,
            replacement,
            expected_catalog_sha256=catalog["catalog_sha256"],
        )
        catalogs[list(config.catalogs).index(path)] = replacement


def reserve(config: ReservationConfig) -> dict[str, Any]:
    config = _validate_config(config)
    with _catalog_locks(config):
        recovery = os.path.lexists(config.output_root)
        if recovery:
            reservation = _validate_recovery_root(config)
            catalogs = [_load_catalog(path, config.run_root) for path in config.catalogs]
            _assert_reserve_replayable(catalogs, reservation)
        else:
            admission = _audit_locked(config)
            if not admission["go"]:
                raise ReservationError(
                    "GRAT pilot CPU admission is NO-GO: " + "; ".join(admission["blockers"])
                )
            reservation = _create_reservation_root(config, admission["selected_cpus"])
            catalogs = [_load_catalog(path, config.run_root) for path in config.catalogs]
            _assert_reserve_replayable(catalogs, reservation)

        first_scan = _scan_processes(config)
        conflicts = _compute_conflicts(first_scan, set(reservation["cpus"]))
        if conflicts or first_scan.races:
            raise ReservationError(
                "live/racing Paper400 compute appeared before reservation commit"
            )
        _append_missing_rows(config, catalogs, reservation)

        verified = [_load_catalog(path, config.run_root) for path in config.catalogs]
        _assert_reserve_replayable(verified, reservation)
        expected = (reservation["bundle"], reservation["reservation_sha256"])
        for catalog in verified:
            for cpu in reservation["cpus"]:
                rows = _matching_rows(catalog, reservation, cpu)
                if len(rows) != 1 or (
                    rows[0]["bundle"], rows[0]["reservation_sha256"]
                ) != expected:
                    raise ReservationError("reservation is not complete in every catalog")
        final_scan = _scan_processes(config)
        final_conflicts = _compute_conflicts(final_scan, set(reservation["cpus"]))
        if final_conflicts or final_scan.races:
            raise ReservationError(
                "live/racing Paper400 compute appeared after persistent reservation"
            )
        return _seal({
            "schema_version": SCHEMA_VERSION,
            "kind": RESERVE_KIND,
            "completed_at": time.time(),
            "bundle": reservation["bundle"],
            "cpus": reservation["cpus"],
            "reservation_sha256": reservation["reservation_sha256"],
            "catalog_sha256s": {
                str(path): value["catalog_sha256"]
                for path, value in zip(config.catalogs, verified)
            },
            "recovery_replay": recovery,
            "all_three_catalogs_exact": True,
            "scheduler_lease_only": True,
            "kernel_hardware_exclusive": False,
            "process_control_authority": False,
            "scientific_claim": False,
        })


def _valid_absolute_normal_text(value: Any) -> bool:
    return (
        type(value) is str
        and bool(value)
        and "\x00" not in value
        and Path(value).is_absolute()
        and value == os.path.abspath(value)
    )


def _valid_file_record(value: Any, *, role: str | None = None) -> bool:
    if type(value) is not dict or set(value) != PILOT_FILE_RECORD_FIELDS:
        return False
    integer_bounds = {
        "device": 0, "inode": 1, "bytes": 0, "mode": 0, "uid": 0,
        "gid": 0, "links": 1, "mtime_ns": 0, "ctime_ns": 0,
    }
    if any(
        type(value.get(field)) is not int or value[field] < minimum
        for field, minimum in integer_bounds.items()
    ):
        return False
    return (
        (role is None or value.get("role") == role)
        and type(value.get("role")) is str
        and bool(value["role"])
        and _valid_absolute_normal_text(value.get("requested_path"))
        and _valid_absolute_normal_text(value.get("realpath"))
        and type(value.get("sha256")) is str
        and SHA256_RE.fullmatch(value["sha256"]) is not None
        and value["mode"] <= 0o7777
    )


def _file_record_matches_disk(
    value: Mapping[str, Any], *, root: Path, allow_empty: bool,
) -> bool:
    if not _valid_file_record(value):
        return False
    path = Path(value["realpath"])
    if not _is_within(path, root) or value["requested_path"] != value["realpath"]:
        return False
    flags = os.O_RDONLY | os.O_CLOEXEC | getattr(os, "O_NOFOLLOW", 0)
    try:
        descriptor = os.open(path, flags)
    except OSError:
        return False
    try:
        before = os.fstat(descriptor)
        if (
            not stat.S_ISREG(before.st_mode)
            or int(before.st_dev) != value["device"]
            or int(before.st_ino) != value["inode"]
            or int(before.st_size) != value["bytes"]
            or int(before.st_uid) != value["uid"]
            or int(before.st_gid) != value["gid"]
            or int(before.st_nlink) != value["links"]
            or stat.S_IMODE(before.st_mode) != value["mode"]
            or int(before.st_mtime_ns) != value["mtime_ns"]
            or int(before.st_ctime_ns) != value["ctime_ns"]
            or (not allow_empty and before.st_size == 0)
        ):
            return False
        digest = hashlib.sha256()
        while True:
            chunk = os.read(descriptor, 8 << 20)
            if not chunk:
                break
            digest.update(chunk)
        after = os.fstat(descriptor)
        return (
            digest.hexdigest() == value["sha256"]
            and (before.st_dev, before.st_ino, before.st_size, before.st_mtime_ns,
                 before.st_ctime_ns)
            == (after.st_dev, after.st_ino, after.st_size, after.st_mtime_ns,
                after.st_ctime_ns)
        )
    finally:
        os.close(descriptor)


def _valid_pilot_wrapper_source(value: Any) -> bool:
    """Validate the wrapper's sealed path/content/stat identity without reopening it."""

    if not _valid_file_record(value, role="pilot wrapper source"):
        return False
    return (
        value["bytes"] > 0
        and value["requested_path"] == str(PILOT_WRAPPER_SOURCE_PATH)
        and value["realpath"] == str(PILOT_WRAPPER_SOURCE_PATH)
        and value["bytes"] <= MAX_PILOT_WRAPPER_SOURCE_BYTES
        and value["sha256"] == TRUSTED_PILOT_WRAPPER_SHA256
        and value["mode"] <= 0o7777
        and (value["mode"] & stat.S_IXUSR) == 0
        and value["uid"] == os.geteuid()
        and value["links"] == 1
    )


def _valid_pilot_source_reverification(value: Any, *, accepted: bool) -> bool:
    if type(value) is not dict or type(value.get("passed")) is not bool:
        return False
    passed = value["passed"]
    expected_fields = (
        PILOT_SOURCE_REVERIFY_SUCCESS_FIELDS
        if passed
        else PILOT_SOURCE_REVERIFY_FAILURE_FIELDS
    )
    if (
        set(value) != expected_fields
        or type(value.get("checked_utc")) is not str
        or not value["checked_utc"]
        or value.get("full_hash") is not True
        or (accepted and passed is not True)
    ):
        return False
    if passed:
        return True
    error = value.get("error")
    return (
        type(error) is dict
        and set(error) == PILOT_SOURCE_REVERIFY_ERROR_FIELDS
        and type(error.get("type")) is str
        and bool(error["type"])
        and type(error.get("message")) is str
        and bool(error["message"])
    )


def _valid_plan_evidence(
    plan: Mapping[str, Any], config: ReservationConfig,
    reservation: Mapping[str, Any],
) -> bool:
    inputs = plan.get("inputs")
    pipeline = plan.get("pipeline")
    trust = plan.get("toolchain_trust")
    toolchain = plan.get("toolchain")
    if (
        type(inputs) is not dict
        or set(inputs) != {"cnf", "drat"}
        or not _valid_file_record(inputs.get("cnf"), role="input CNF")
        or not _valid_file_record(inputs.get("drat"), role="input DRAT proof")
        or type(plan.get("proof_quiescence")) is not dict
        or plan.get("proof_format") not in {"ascii", "binary"}
        or type(plan.get("resources")) is not dict
        or plan["resources"].get("passed") is not True
        or type(pipeline) is not list
        or len(pipeline) != 2
        or [item.get("stage") if type(item) is dict else None for item in pipeline]
        != ["gratgen", "gratchk"]
        or type(trust) is not dict
        or trust.get("observed_lock_sha256") != TRUSTED_TOOLCHAIN_MANIFEST_SHA256
        or trust.get("compiled_binary_sha256") != TRUSTED_PILOT_TOOL_SHA256S
        or trust.get("compiled_runtime_policy") is not True
        or trust.get("run_enabled") is not True
        or type(toolchain) is not dict
        or set(toolchain) != {"lock", "tools"}
        or not _valid_file_record(toolchain.get("lock"), role="toolchain lock")
        or toolchain["lock"].get("sha256") != TRUSTED_TOOLCHAIN_MANIFEST_SHA256
        or type(toolchain.get("tools")) is not dict
        or set(toolchain["tools"]) != {"gratgen", "gratchk"}
    ):
        return False
    gratgen_argv = pipeline[0].get("argv")
    gratchk_argv = pipeline[1].get("argv")
    if (
        type(gratgen_argv) is not list
        or len(gratgen_argv) < 3
        or gratgen_argv[-2:] != ["-j", str(config.threads)]
        or (("-b" in gratgen_argv) != (plan["proof_format"] == "binary"))
        or type(gratchk_argv) is not list
        or gratchk_argv[:2] != ["gratchk", "unsat"]
    ):
        return False
    for name in ("gratgen", "gratchk"):
        value = toolchain["tools"][name]
        if (
            type(value) is not dict
            or set(value) != {"name", "binary", "runtime_kind", "runtime_libraries"}
            or value.get("name") != name
            or not _valid_file_record(value.get("binary"), role=f"{name} binary")
            or value["binary"].get("sha256") != TRUSTED_PILOT_TOOL_SHA256S[name]
            or value.get("runtime_kind") not in {"static", "dynamic"}
            or type(value.get("runtime_libraries")) is not list
        ):
            return False
    return True


def _valid_runtime_evidence(value: Any, *, tool: str) -> bool:
    if (
        type(value) is not dict
        or set(value) != {
            "kind", "tool", "runtime_kind", "binary_memfd", "runtime_objects",
            "loader_options", "system_loader_cache_bypassed",
        }
        or value.get("kind") != "paper400-grat-private-runtime-v1"
        or value.get("tool") != tool
        or value.get("runtime_kind") != "dynamic"
        or value.get("loader_options") != ["--inhibit-cache", "--library-path", "--argv0"]
        or value.get("system_loader_cache_bypassed") is not True
        or type(value.get("runtime_objects")) is not list
    ):
        return False
    binary = value.get("binary_memfd")
    return (
        type(binary) is dict
        and set(binary) == {"name", "bytes", "sha256", "mode", "seals"}
        and binary.get("sha256") == TRUSTED_PILOT_TOOL_SHA256S[tool]
        and type(binary.get("bytes")) is int and binary["bytes"] > 0
        and binary.get("seals") == 15
    )


def _valid_stage_evidence(
    value: Any, *, stage: str, threads: int, cpus: Sequence[int], root: Path,
) -> bool:
    if (
        type(value) is not dict
        or set(value) != {
            "stage", "exit_code", "elapsed_wall_seconds", "required_success_line",
            "status_stream", "observed_parallel_threads", "stdout", "stderr",
            "runtime", "process_identity", "process_policy",
        }
        or value.get("stage") != stage
        or value.get("exit_code") != 0
        or not _finite(value.get("elapsed_wall_seconds"))
        or float(value["elapsed_wall_seconds"]) < 0
        or not _valid_runtime_evidence(value.get("runtime"), tool=stage)
    ):
        return False
    expected_status = "s VERIFIED" if stage == "gratgen" else "s VERIFIED UNSAT"
    if (
        value.get("required_success_line") != expected_status
        or value.get("status_stream") != ("stderr" if stage == "gratgen" else "stdout")
        or value.get("observed_parallel_threads") != (threads if stage == "gratgen" else None)
    ):
        return False
    process = value.get("process_identity")
    policy = value.get("process_policy")
    if (
        type(process) is not dict
        or set(process) != {
            "pid", "proc_start_ticks", "argv", "observed_affinity",
            "observed_before_wait",
        }
        or type(process.get("pid")) is not int or process["pid"] <= 0
        or type(process.get("proc_start_ticks")) is not int
        or process["proc_start_ticks"] <= 0
        or type(process.get("argv")) is not list
        or not process["argv"]
        or any(type(item) is not str for item in process["argv"])
        or process.get("observed_affinity") != list(cpus)
        or process.get("observed_before_wait") is not True
        or type(policy) is not dict
        or policy.get("exact_affinity") != list(cpus)
    ):
        return False
    if stage == "gratgen":
        argv = process["argv"]
        if "-j" not in argv or argv[argv.index("-j") + 1:] != [str(threads)]:
            return False
    for stream, allow_empty in (("stdout", stage == "gratgen"), ("stderr", stage == "gratchk")):
        record = value.get(stream)
        if not _valid_file_record(record, role=f"{stage} {stream}"):
            return False
        if not _file_record_matches_disk(record, root=root, allow_empty=allow_empty):
            return False
    return True


def _load_bound_plan(
    config: ReservationConfig, reservation: Mapping[str, Any],
) -> dict[str, Any]:
    plan = _read_json(
        config.output_root / "PLAN.json", "immutable GRAT pilot PLAN", required_mode=0o400,
    )
    scheduler = plan.get("cpu_scheduler_authority")
    admission = scheduler.get("admission") if type(scheduler) is dict else None
    if (
        set(plan) != PILOT_PLAN_FIELDS
        or plan.get("schema_version") != SCHEMA_VERSION
        or plan.get("kind") != PILOT_PLAN_KIND
        or plan.get("gate") != PILOT_GATE
        or plan.get("mode") != "NON_PRODUCTION_PILOT"
        or plan.get("authoritative") is not False
        or plan.get("terminal_publication") is not False
        or plan.get("aggregate_publication") is not False
        or plan.get("cleanup_authority") is not False
        or plan.get("output_root") != str(config.output_root)
        or plan.get("threads") != config.threads
        or plan.get("cpus") != reservation["cpus"]
        or not _valid_pilot_wrapper_source(plan.get("wrapper_source"))
        or not _valid_plan_evidence(plan, config, reservation)
        or plan.get("wrapper_source_fd_pinned_for_context_lifetime") is not True
        or plan.get("wrapper_source_initial_full_hash_verified") is not True
        or not _selfhash_valid(plan, "manifest_sha256")
        or type(scheduler) is not dict
        or set(scheduler) != {
            "admission", "catalog_locks_released_before_expensive_work",
            "run_requires_short_locked_revalidation_at_each_boundary",
        }
        or scheduler.get("catalog_locks_released_before_expensive_work") is not True
        or scheduler.get("run_requires_short_locked_revalidation_at_each_boundary") is not True
        or type(admission) is not dict
        or admission.get("run_root") != str(config.run_root)
        or admission.get("bundle") != reservation["bundle"]
        or admission.get("reservation_sha256") != reservation["reservation_sha256"]
        or admission.get("cpus") != reservation["cpus"]
        or admission.get("scheduler_lease_only") is not True
        or admission.get("catalog_mutation_by_pilot") is not False
    ):
        raise ReservationError("pilot PLAN is not exactly bound to the CPU reservation")
    return plan


def _load_final_pilot_chain(
    config: ReservationConfig, reservation: Mapping[str, Any],
) -> tuple[dict[str, Any], dict[str, Any]]:
    plan = _load_bound_plan(config, reservation)
    result = _read_json(
        config.output_root / "RESULT.json", "immutable GRAT pilot RESULT", required_mode=0o400,
    )
    expected_result_fields = (
        PILOT_FAILURE_RESULT_FIELDS
        if result.get("status") == "FAILED_CLOSED"
        else PILOT_ACCEPTED_RESULT_FIELDS
    )
    if (
        set(result) != expected_result_fields
        or result.get("schema_version") != SCHEMA_VERSION
        or result.get("kind") != PILOT_RESULT_KIND
        or result.get("gate") != PILOT_GATE
        or result.get("status") not in {
            "GRATCHK_ACCEPTED_PILOT_ONLY", "FAILED_CLOSED",
        }
        or result.get("authoritative") is not False
        or result.get("terminal_publication") is not False
        or result.get("aggregate_publication") is not False
        or result.get("cleanup_authority") is not False
        or result.get("eligible_for_terminal_publication") is not False
        or result.get("plan_sha256") != plan["manifest_sha256"]
        or result.get("wrapper_source") != plan["wrapper_source"]
        or not _valid_pilot_source_reverification(
            result.get("wrapper_source_final_full_reverify"),
            accepted=result.get("status") == "GRATCHK_ACCEPTED_PILOT_ONLY",
        )
        or type(result.get("completed_utc")) is not str
        or not result["completed_utc"]
        or not _selfhash_valid(result, "manifest_sha256")
        or (
            result.get("status") == "FAILED_CLOSED"
            and type(result.get("failure")) is not dict
        )
        or (
            result.get("status") == "GRATCHK_ACCEPTED_PILOT_ONLY"
            and (
                result.get("artifacts_staged_only") is not True
                or result.get("catalog_locks_held_across_stage") is not False
            )
        )
    ):
        raise ReservationError("pilot RESULT is not an accepted/failed-closed finalized result")
    if result.get("status") == "GRATCHK_ACCEPTED_PILOT_ONLY":
        stages = result.get("stages")
        artifacts = result.get("staged_artifacts")
        if (
            result.get("inputs") != plan.get("inputs")
            or result.get("toolchain") != plan.get("toolchain")
            or type(stages) is not list
            or len(stages) != 2
            or not _valid_stage_evidence(
                stages[0], stage="gratgen", threads=config.threads,
                cpus=reservation["cpus"], root=config.output_root,
            )
            or not _valid_stage_evidence(
                stages[1], stage="gratchk", threads=config.threads,
                cpus=reservation["cpus"], root=config.output_root,
            )
            or type(artifacts) is not dict
            or set(artifacts) != {"gratl", "gratp"}
            or not _valid_file_record(artifacts.get("gratl"), role="staged GRAT lemmas")
            or not _valid_file_record(artifacts.get("gratp"), role="staged GRAT proof")
            or not _file_record_matches_disk(
                artifacts["gratl"], root=config.output_root, allow_empty=True,
            )
            or not _file_record_matches_disk(
                artifacts["gratp"], root=config.output_root, allow_empty=False,
            )
        ):
            raise ReservationError("accepted pilot RESULT evidence is incomplete or changed")
    return plan, result


def _load_recovery_abort(
    config: ReservationConfig, reservation: Mapping[str, Any],
) -> tuple[dict[str, Any], dict[str, Any]]:
    plan = _load_bound_plan(config, reservation)
    value = _read_json(
        config.output_root / "RECOVERY-ABORT.json",
        "immutable GRAT pilot recovery abort",
        required_mode=0o400,
    )
    recovery = value.get("recovery")
    if (
        set(value) != PILOT_ABORT_FIELDS
        or value.get("schema_version") != SCHEMA_VERSION
        or value.get("kind") != PILOT_ABORT_KIND
        or value.get("gate") != GATE
        or value.get("status") != "RECOVERED_ABORTED"
        or value.get("authoritative") is not False
        or value.get("terminal_publication") is not False
        or value.get("aggregate_publication") is not False
        or value.get("cleanup_authority") is not False
        or value.get("eligible_for_terminal_publication") is not False
        or value.get("plan_sha256") != plan["manifest_sha256"]
        or value.get("reservation_sha256") != reservation["reservation_sha256"]
        or value.get("wrapper_source") != plan["wrapper_source"]
        or not _finite(value.get("completed_at"))
        or type(recovery) is not dict
        or set(recovery) != {
            "reason", "first_scan_sha256", "locked_scan_sha256",
            "pilot_children_alive",
        }
        or recovery.get("reason") != "PILOT_CONTROLLER_DISAPPEARED_WITHOUT_RESULT"
        or recovery.get("pilot_children_alive") is not False
        or any(
            type(recovery.get(field)) is not str
            or SHA256_RE.fullmatch(recovery[field]) is None
            for field in ("first_scan_sha256", "locked_scan_sha256")
        )
        or not _selfhash_valid(value, "record_sha256")
    ):
        raise ReservationError("pilot recovery ABORT is malformed or cross-bound")
    return plan, value


def _load_final_or_abort(
    config: ReservationConfig, reservation: Mapping[str, Any],
) -> tuple[dict[str, Any], dict[str, Any], str]:
    result_exists = os.path.lexists(config.output_root / "RESULT.json")
    abort_exists = os.path.lexists(config.output_root / "RECOVERY-ABORT.json")
    if result_exists == abort_exists:
        raise ReservationError("exactly one final RESULT or recovery ABORT is required")
    if result_exists:
        plan, result = _load_final_pilot_chain(config, reservation)
        return plan, result, result["manifest_sha256"]
    plan, abort = _load_recovery_abort(config, reservation)
    return plan, abort, abort["record_sha256"]


def _pilot_children(
    config: ReservationConfig, reservation: Mapping[str, Any], scan: ProcessScan,
) -> list[dict[str, Any]]:
    children: list[dict[str, Any]] = []
    reserved = set(reservation["cpus"])
    for row in scan.processes:
        if row["pid"] == os.getpid():
            continue
        root_bound = (
            _path_text_within(row.get("cwd", ""), config.output_root)
            or any(_path_text_within(item, config.output_root) for item in row.get("argv", []))
            or config.output_root.name.lower() in row.get("cgroup", "").lower()
        )
        compute_overlap = (
            row.get("compute_kind") is not None
            and row.get("paper400_bound") is True
            and bool(reserved.intersection(row.get("affinity", [])))
        )
        if root_bound or compute_overlap:
            children.append({
                "pid": row["pid"],
                "start_ticks": row["start_ticks"],
                "state": row["state"],
                "root_bound": root_bound,
                "reserved_cpu_compute_overlap": compute_overlap,
                "compute_kind": row.get("compute_kind"),
                "affinity_class": row.get("affinity_class"),
                "affinity": row.get("affinity"),
            })
    return children


def _exact_transaction_rows(
    catalogs: Sequence[Mapping[str, Any]], reservation: Mapping[str, Any],
) -> list[list[dict[str, Any]]]:
    expected_cpus = set(reservation["cpus"])
    result: list[list[dict[str, Any]]] = []
    for catalog in catalogs:
        matches = [
            row for row in catalog["leases"]
            if row["bundle"] == reservation["bundle"]
            or row["reservation_sha256"] == reservation["reservation_sha256"]
            or row["cpu"] in expected_cpus
        ]
        if (
            len(matches) != len(expected_cpus)
            or {row["cpu"] for row in matches} != expected_cpus
            or any(
                row["bundle"] != reservation["bundle"]
                or row["reservation_sha256"] != reservation["reservation_sha256"]
                or row["created_at"] != reservation["created_at"]
                for row in matches
            )
        ):
            raise ReservationError("catalog does not contain the exact pilot transaction")
        result.append(matches)
    return result


def _load_release_record(config: ReservationConfig) -> dict[str, Any] | None:
    path = config.output_root / "CPU-LEASE-RELEASE.json"
    if not os.path.lexists(path):
        return None
    value = _read_json(path, "immutable CPU lease release", required_mode=0o400)
    cpus = value.get("cpus")
    if (
        set(value) != RELEASE_RECORD_FIELDS
        or value.get("schema_version") != SCHEMA_VERSION
        or value.get("kind") != RELEASE_KIND
        or value.get("bundle") != str(config.output_root)
        or type(cpus) is not list
        or cpus != sorted(cpus)
        or len(cpus) != config.threads
        or len(set(cpus)) != len(cpus)
        or any(not _valid_cpu(cpu) for cpu in cpus)
        or not _finite(value.get("completed_at"))
        or not _finite(value.get("released_at"))
        or SHA256_RE.fullmatch(str(value.get("reservation_sha256", ""))) is None
        or SHA256_RE.fullmatch(str(value.get("plan_sha256", ""))) is None
        or SHA256_RE.fullmatch(str(value.get("result_sha256", ""))) is None
        or value.get("result_status") not in PILOT_FINAL_STATUSES
        or type(value.get("catalog_sha256s")) is not dict
        or value.get("all_three_catalogs_released") is not True
        or value.get("pilot_children_alive") is not False
        or value.get("removed_data") is not False
        or value.get("process_control_authority") is not False
        or value.get("terminal_publication") is not False
        or value.get("aggregate_publication") is not False
        or value.get("cleanup_authority") is not False
        or value.get("scientific_claim") is not False
        or not _selfhash_valid(value, "record_sha256")
    ):
        raise ReservationError("existing CPU lease release record is malformed")
    return value


def _scan_sha256(scan: ProcessScan) -> str:
    return hashlib.sha256(_canonical({
        "processes": list(scan.processes), "races": list(scan.races),
    })).hexdigest()


def recover_abort(config: ReservationConfig) -> dict[str, Any]:
    """Seal a missing-RESULT controller crash, then release only its CPU rows."""

    config = _validate_config(config)
    _safe_directory(config.output_root, "pilot output root", mode=0o700)
    reservation = _load_reservation(config)
    plan = _load_bound_plan(config, reservation)
    if os.path.lexists(config.output_root / "RESULT.json"):
        raise ReservationError("recovery ABORT is forbidden after RESULT publication")
    existing_path = config.output_root / "RECOVERY-ABORT.json"
    if not os.path.lexists(existing_path):
        first = _scan_processes(config)
        if _pilot_children(config, reservation, first) or first.races:
            raise ReservationError("cannot recover while a pilot child may be alive")
        with _catalog_locks(config):
            locked = _scan_processes(config)
            if _pilot_children(config, reservation, locked) or locked.races:
                raise ReservationError("pilot child state changed before recovery ABORT")
            catalogs = [_load_catalog(path, config.run_root) for path in config.catalogs]
            _exact_transaction_rows(catalogs, reservation)
            abort = _seal({
                "schema_version": SCHEMA_VERSION,
                "kind": PILOT_ABORT_KIND,
                "gate": GATE,
                "completed_at": time.time(),
                "status": "RECOVERED_ABORTED",
                "authoritative": False,
                "terminal_publication": False,
                "aggregate_publication": False,
                "cleanup_authority": False,
                "eligible_for_terminal_publication": False,
                "plan_sha256": plan["manifest_sha256"],
                "reservation_sha256": reservation["reservation_sha256"],
                "wrapper_source": plan["wrapper_source"],
                "recovery": {
                    "reason": "PILOT_CONTROLLER_DISAPPEARED_WITHOUT_RESULT",
                    "first_scan_sha256": _scan_sha256(first),
                    "locked_scan_sha256": _scan_sha256(locked),
                    "pilot_children_alive": False,
                },
            })
            _write_exclusive(existing_path, abort, mode=0o400)
    _load_recovery_abort(config, reservation)
    return release(config)


def release(config: ReservationConfig) -> dict[str, Any]:
    config = _validate_config(config)
    _safe_directory(config.output_root, "pilot output root", mode=0o700)
    reservation = _load_reservation(config)
    plan, result, final_sha256 = _load_final_or_abort(config, reservation)
    scan = _scan_processes(config)
    children = _pilot_children(config, reservation, scan)
    if children or scan.races:
        raise ReservationError(
            "cannot release while a pilot child/conflicting compute may be alive"
        )

    with _catalog_locks(config):
        # Recheck after acquiring scheduler authority.  No process is signalled;
        # a new/racing child leaves the reservation active and visible.
        locked_scan = _scan_processes(config)
        locked_children = _pilot_children(config, reservation, locked_scan)
        if locked_children or locked_scan.races:
            raise ReservationError("pilot child state changed before catalog release")
        catalogs = [_load_catalog(path, config.run_root) for path in config.catalogs]
        matching = _exact_transaction_rows(catalogs, reservation)
        states = {row["state"] for rows in matching for row in rows}
        if not states.issubset({"RESERVED", "RELEASED"}):
            raise ReservationError("pilot transaction has an invalid release state")
        prior_times = {
            float(row["released_at"])
            for rows in matching for row in rows if row["state"] == "RELEASED"
        }
        if len(prior_times) > 1:
            raise ReservationError("partial release contains inconsistent timestamps")
        released_at = next(iter(prior_times)) if prior_times else time.time()
        for index, (path, catalog, rows) in enumerate(zip(config.catalogs, catalogs, matching)):
            if all(row["state"] == "RELEASED" for row in rows):
                if any(float(row["released_at"]) != released_at for row in rows):
                    raise ReservationError("catalog release timestamp is inconsistent")
                continue
            if any(row["state"] != "RESERVED" for row in rows):
                raise ReservationError("catalog has a mixed partial CPU release")
            identities = {
                (row["cpu"], row["bundle"], row["reservation_sha256"])
                for row in rows
            }
            unsigned = dict(catalog)
            unsigned.pop("catalog_sha256")
            unsigned["updated_at"] = released_at
            unsigned["leases"] = [
                ({**row, "state": "RELEASED", "released_at": released_at}
                 if (row["cpu"], row["bundle"], row["reservation_sha256"]) in identities
                 else row)
                for row in catalog["leases"]
            ]
            replacement = _seal(unsigned, "catalog_sha256")
            _atomic_catalog_write(
                path,
                replacement,
                expected_catalog_sha256=catalog["catalog_sha256"],
            )
            catalogs[index] = replacement

        final_catalogs = [_load_catalog(path, config.run_root) for path in config.catalogs]
        final_rows = _exact_transaction_rows(final_catalogs, reservation)
        if any(
            row["state"] != "RELEASED" or float(row["released_at"]) != released_at
            for rows in final_rows for row in rows
        ):
            raise ReservationError("release did not commit identically in every catalog")

        record = _seal({
            "schema_version": SCHEMA_VERSION,
            "kind": RELEASE_KIND,
            "completed_at": time.time(),
            "released_at": released_at,
            "bundle": str(config.output_root),
            "cpus": reservation["cpus"],
            "reservation_sha256": reservation["reservation_sha256"],
            "plan_sha256": plan["manifest_sha256"],
            "result_sha256": final_sha256,
            "result_status": result["status"],
            "catalog_sha256s": {
                str(path): value["catalog_sha256"]
                for path, value in zip(config.catalogs, final_catalogs)
            },
            "all_three_catalogs_released": True,
            "pilot_children_alive": False,
            "removed_data": False,
            "process_control_authority": False,
            "terminal_publication": False,
            "aggregate_publication": False,
            "cleanup_authority": False,
            "scientific_claim": False,
        })
        existing = _load_release_record(config)
        if existing is not None:
            if (
                existing.get("reservation_sha256") != reservation["reservation_sha256"]
                or existing.get("cpus") != reservation["cpus"]
                or existing.get("released_at") != released_at
                or existing.get("result_sha256") != final_sha256
                or existing.get("all_three_catalogs_released") is not True
            ):
                raise ReservationError("existing release record does not match catalog state")
            return existing
        _write_exclusive(config.output_root / "CPU-LEASE-RELEASE.json", record, mode=0o400)
        return record


def _parse_cpus(value: str) -> tuple[int, ...]:
    if re.fullmatch(r"[0-9]+(?:,[0-9]+)*", value) is None:
        raise argparse.ArgumentTypeError("CPUs must be comma-separated non-negative integers")
    cpus = tuple(int(item) for item in value.split(","))
    if len(set(cpus)) != len(cpus):
        raise argparse.ArgumentTypeError("CPU list contains duplicates")
    return cpus


def _cli_config(args: argparse.Namespace, *, release_mode: bool = False) -> ReservationConfig:
    if release_mode:
        # The immutable reservation determines this value; loading it safely is
        # intentionally deferred until after normal path/catalog validation.
        raw = _read_json(
            args.output_root / "cpu-reservation.json",
            "GRAT pilot CPU reservation",
            required_mode=0o400,
        )
        cpus = raw.get("cpus")
        if type(cpus) is not list or len(cpus) not in {4, 8}:
            raise ReservationError("cannot derive release thread count from reservation")
        threads = len(cpus)
    else:
        threads = args.threads
    return ReservationConfig(
        run_root=RUN_ROOT,
        catalogs=CATALOGS,
        output_root=args.output_root,
        threads=threads,
        requested_cpus=getattr(args, "cpus", None),
    )


def _parser() -> argparse.ArgumentParser:
    parser = argparse.ArgumentParser(description=__doc__, allow_abbrev=False)
    commands = parser.add_subparsers(dest="command", required=True)
    for name in ("audit", "reserve"):
        child = commands.add_parser(name)
        child.add_argument("--output-root", type=Path, required=True)
        child.add_argument("--threads", type=int, choices=(4, 8), required=True)
        child.add_argument("--cpus", type=_parse_cpus)
    for name in ("release", "recover-abort"):
        release_parser = commands.add_parser(name)
        release_parser.add_argument("--output-root", type=Path, required=True)
    return parser


def main(argv: Sequence[str] | None = None) -> int:
    args = _parser().parse_args(argv)
    try:
        if args.command == "audit":
            result = audit(_cli_config(args))
        elif args.command == "reserve":
            result = reserve(_cli_config(args))
        elif args.command == "release":
            result = release(_cli_config(args, release_mode=True))
        else:
            result = recover_abort(_cli_config(args, release_mode=True))
    except (ReservationError, OSError, ValueError, TypeError) as exc:
        print(f"{GATE}: FAIL-CLOSED: {exc}", file=sys.stderr)
        return 2
    sys.stdout.buffer.write(_canonical(result) + b"\n")
    return 0 if result.get("go", True) else 3
if __name__ == "__main__":
    raise SystemExit(main())
