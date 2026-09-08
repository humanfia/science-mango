#!/usr/bin/env python3
"""Isolated native-LRAT execution pilot for future Paper400 leaves.

This module is deliberately *not* a production Paper400 authority.  It can
execute a previously sealed :mod:`paper400_native_lrat_future_v1` PLAN_ONLY
record, but only in a dedicated ``paper400-native-lrat-pilot-v1-*`` root and
only while an external reservation owns every requested CPU in all three
Paper400 scheduler catalogues.

The launcher creates every proof with O_EXCL, forks every generation-zero
solver behind a pre-exec pipe gate, records PID/start-tick/CPU/proof-inode
receipts, seals the complete all-start barrier, replays the three-catalogue
lease authority, and only then releases all solvers.  CaDiCaL's logical argv
is exactly ``cadical --lrat --no-binary CNF_FD PROOF_FD``.  Pinned ELF objects
are transported through a sealed loader/runtime closure.

An UNSAT proof is checked twice by two distinct, gated ``lrat-check``
processes.  The resulting handoff is intentionally not a certificate: it has
no ``certificate_sha256``, no terminal claim, and no queue/aggregate/cleanup
mutation authority.  An optional recursive-queue binding lets a later,
independently reviewed authority replay the exact frontier identity.

No command creates or releases scheduler reservations, modifies a recursive
queue, invokes systemd, resumes a checkpoint, signals an unrelated process,
publishes a terminal/aggregate, or deletes experiment data.
"""

from __future__ import annotations

import argparse
import contextlib
import ctypes
import errno
import fcntl
import hashlib
import json
import math
import os
import re
import resource
import selectors
import signal
import stat
import struct
import sys
import time
import uuid
from dataclasses import dataclass
from pathlib import Path
from typing import Any, Callable, Iterator, Mapping, Sequence

try:
    from scripts import paper400_native_lrat_future_v1 as native
    from scripts import paper400_native_lrat_lease_owner_v1 as lease_owner
    from scripts import paper400_native_lrat_resource_gate_v1 as resource_gate
    from investigations import paper400_dic5_recursive_split_v1 as recursive
except ModuleNotFoundError:  # Direct execution from qcode-discovery/scripts.
    sys.path.insert(0, str(Path(__file__).resolve().parent.parent))
    from scripts import paper400_native_lrat_future_v1 as native
    from scripts import paper400_native_lrat_lease_owner_v1 as lease_owner
    from scripts import paper400_native_lrat_resource_gate_v1 as resource_gate
    from investigations import paper400_dic5_recursive_split_v1 as recursive


SCHEMA_VERSION = 1
GATE = "paper400-native-lrat-launcher-v1"
AUDIT_KIND = GATE + "-audit"
RUN_KIND = GATE + "-run"
FAILURE_KIND = GATE + "-failure"
LEASE_BINDING_KIND = GATE + "-three-catalog-lease-binding"
CATALOG_SNAPSHOT_KIND = GATE + "-three-catalog-snapshot"
RECURSIVE_BINDING_KIND = GATE + "-recursive-leaf-binding"
CHECK_RESULT_KIND = GATE + "-lrat-check-result"
HANDOFF_KIND = GATE + "-certification-handoff"

RUNS = Path("/home/jing/paper400-runs")
DEFAULT_CATALOGS = tuple(sorted((
    RUNS / ".paper400-recursive-split-v1/cpu-leases.json",
    RUNS / ".paper400-recursive-certified-slot-handoffs-v1/borrow-control/cpu-leases.json",
    RUNS / ".paper400-recursive-nested-certified-slot-handoffs-v2/cpu-leases.json",
), key=str))
CATALOG_KIND = lease_owner.CATALOG_KIND
RESERVATION_KIND = lease_owner.RESERVATION_KIND
RESERVATION_LEASE_SCOPE = lease_owner.LEASE_SCOPE

MAX_JSON_BYTES = 64 << 20
MAX_LOG_BYTES = 16 << 20
DEFAULT_PROOF_CAP_BYTES = 1 << 40
DEFAULT_SOLVER_TIMEOUT_SECONDS = 7 * 24 * 60 * 60
DEFAULT_CHECKER_TIMEOUT_SECONDS = native.LRAT_CHECKER_TIMEOUT_SECONDS
DEFAULT_LEASE_RECHECK_SECONDS = 30.0
DEFAULT_DISK_RESERVE_BYTES = 128 << 30
DEFAULT_HOST_MEMORY_RESERVE_BYTES = 64 << 30
DEFAULT_CGROUP_MEMORY_RESERVE_BYTES = 32 << 30
DEFAULT_HOST_PSI_SOME_AVG10 = 20.0
DEFAULT_HOST_PSI_FULL_AVG10 = 5.0
DEFAULT_CGROUP_PSI_SOME_AVG10 = 20.0
DEFAULT_CGROUP_PSI_FULL_AVG10 = 5.0
PROC_ROOT = Path("/proc")
CGROUP_MOUNT = Path("/sys/fs/cgroup")
READY_TIMEOUT_MAX_SECONDS = 600
TERM_GRACE_SECONDS = 2.0
READ_CHUNK_BYTES = 1 << 20
HASH_CHUNK_BYTES = 8 << 20
SHA256_RE = re.compile(r"[0-9a-f]{64}\Z")
EXEC_LEAF_ID_RE = re.compile(r"[A-Za-z0-9][A-Za-z0-9_.:-]{0,127}\Z")
FORBIDDEN_COMPONENT_RE = re.compile(
    r"(?:^|[._-])(dmtcp|checkpoint|resume)(?:$|[._-])", re.IGNORECASE,
)

SOLVER_CNF_FD = native.SOLVER_CNF_FD
SOLVER_PROOF_FD = native.SOLVER_PROOF_FD
CHECKER_CNF_FD = native.CHECKER_CNF_FD
CHECKER_PROOF_FD = native.CHECKER_PROOF_FD
READY_FD = 206
GATE_FD = 207
RUNTIME_LOADER_FD = 220
RUNTIME_TOOL_FD = 221
RUNTIME_DIRECTORY_FD = 222
RUNTIME_DSO_FD_BASE = 230

F_ADD_SEALS = getattr(fcntl, "F_ADD_SEALS", 1033)
F_GET_SEALS = getattr(fcntl, "F_GET_SEALS", 1034)
F_SEAL_SEAL = getattr(fcntl, "F_SEAL_SEAL", 0x0001)
F_SEAL_SHRINK = getattr(fcntl, "F_SEAL_SHRINK", 0x0002)
F_SEAL_GROW = getattr(fcntl, "F_SEAL_GROW", 0x0004)
F_SEAL_WRITE = getattr(fcntl, "F_SEAL_WRITE", 0x0008)
ALL_MEMFD_SEALS = F_SEAL_WRITE | F_SEAL_GROW | F_SEAL_SHRINK | F_SEAL_SEAL
DT_FLAGS_1 = 0x6FFFFFFB
DF_1_NODEFLIB = 0x00000800

PR_SET_PDEATHSIG = 1
_PRCTL = ctypes.CDLL(None, use_errno=True).prctl

# Frozen Ubuntu 22.04 ELF closure already used by the Paper400 standalone
# proof runner.  linux-vdso is an explicit host-kernel trust boundary.
ELF_OBJECT_SPECS = (
    (
        "ld-linux-x86-64.so.2",
        Path("/usr/lib/x86_64-linux-gnu/ld-linux-x86-64.so.2"),
        240_936,
        "8d06f393f4a93bcf9b81145a259524d66a95522a646bf8d7e05b6ffdf2e63dcc",
    ),
    (
        "libstdc++.so.6",
        Path("/usr/lib/x86_64-linux-gnu/libstdc++.so.6.0.30"),
        2_260_296,
        "ff0825e113603c3866680d5d52216bc6d8eedf3a59f52a0aef67ff01994db128",
    ),
    (
        "libm.so.6",
        Path("/usr/lib/x86_64-linux-gnu/libm.so.6"),
        940_560,
        "df621c68dbfed7e843434ef2faedb9f4d4b0543ad161e9a55eaf4d4ce2443176",
    ),
    (
        "libgcc_s.so.1",
        Path("/usr/lib/x86_64-linux-gnu/libgcc_s.so.1"),
        125_488,
        "fc9d43b2f6c20e53b009238f767c5b949d202389e20de9e202ea684b4ba3729a",
    ),
    (
        "libc.so.6",
        Path("/usr/lib/x86_64-linux-gnu/libc.so.6"),
        2_220_400,
        "e01b1ce7be2987f3b8560e26d0df2623f9dd5cec17be923ae28a785bc0d32d50",
    ),
)

_TEST_ONLY_NONCE = object()


class NativeLratLaunchError(RuntimeError):
    """The isolated execution or certification boundary failed closed."""


@dataclass(frozen=True)
class ExecutionConfig:
    output_root: Path
    lease_catalogs: tuple[Path, ...]
    reservation_sha256: str
    solver_timeout_seconds: int = DEFAULT_SOLVER_TIMEOUT_SECONDS
    checker_timeout_seconds: int = DEFAULT_CHECKER_TIMEOUT_SECONDS
    proof_cap_bytes: int = DEFAULT_PROOF_CAP_BYTES
    stdout_cap_bytes: int = MAX_LOG_BYTES
    stderr_cap_bytes: int = MAX_LOG_BYTES
    lease_recheck_seconds: float = DEFAULT_LEASE_RECHECK_SECONDS
    disk_reserve_bytes: int = DEFAULT_DISK_RESERVE_BYTES
    sealed_elf_runtime: bool = True
    proc_root: Path = PROC_ROOT
    cgroup_mount: Path = CGROUP_MOUNT
    min_host_available_bytes: int = DEFAULT_HOST_MEMORY_RESERVE_BYTES
    min_cgroup_available_bytes: int = DEFAULT_CGROUP_MEMORY_RESERVE_BYTES
    max_host_psi_some_avg10: float = DEFAULT_HOST_PSI_SOME_AVG10
    max_host_psi_full_avg10: float = DEFAULT_HOST_PSI_FULL_AVG10
    max_cgroup_psi_some_avg10: float = DEFAULT_CGROUP_PSI_SOME_AVG10
    max_cgroup_psi_full_avg10: float = DEFAULT_CGROUP_PSI_FULL_AVG10


@dataclass
class _Runtime:
    parent_fd: int
    directory_fd: int
    loader_fd: int
    solver_fd: int
    checker_fd: int
    dso_fds: tuple[int, ...]
    directory_name: str
    preload_sonames: tuple[str, ...]
    record: dict[str, Any]


@dataclass
class _Child:
    leaf_id: str
    role: str
    cpu: int
    pid: int
    ready_fd: int
    gate_fd: int
    stdout_fd: int
    stderr_fd: int
    logical_argv: list[str]
    transport_argv: list[str]
    proc_start_ticks: int | None = None
    exit_code: int | None = None
    reaped: bool = False
    stdout: bytes = b""
    stderr: bytes = b""


def _canonical(value: Any) -> bytes:
    try:
        return json.dumps(
            value, sort_keys=True, separators=(",", ":"), ensure_ascii=True,
            allow_nan=False,
        ).encode("ascii")
    except (TypeError, ValueError, UnicodeEncodeError) as exc:
        raise NativeLratLaunchError(f"non-canonical value: {exc}") from exc


def _digest(value: Any) -> str:
    return hashlib.sha256(_canonical(value)).hexdigest()


def _seal(value: Mapping[str, Any], field: str = "record_sha256") -> dict[str, Any]:
    if field in value:
        raise NativeLratLaunchError(f"record already contains {field}")
    result = dict(value)
    result[field] = _digest(result)
    return result


def _selfhash(value: Any, field: str) -> bool:
    if type(value) is not dict or type(value.get(field)) is not str:
        return False
    if SHA256_RE.fullmatch(value[field]) is None:
        return False
    unsigned = dict(value)
    expected = unsigned.pop(field)
    return _digest(unsigned) == expected


def _require_sha256(value: Any, role: str) -> str:
    if type(value) is not str or SHA256_RE.fullmatch(value) is None:
        raise NativeLratLaunchError(f"invalid {role}")
    return value


def _normalized_absolute(path: Path, role: str, *, must_exist: bool) -> Path:
    target = Path(path)
    if not target.is_absolute() or str(target) != os.path.abspath(str(target)):
        raise NativeLratLaunchError(f"{role} is not a normalized absolute path")
    try:
        resolved = target.resolve(strict=must_exist)
    except (OSError, RuntimeError) as exc:
        raise NativeLratLaunchError(f"cannot resolve {role}") from exc
    if resolved != target:
        raise NativeLratLaunchError(f"{role} is aliased or non-canonical")
    return target


def _safe_directory(path: Path, role: str, *, mode: int = 0o700) -> Path:
    target = _normalized_absolute(path, role, must_exist=True)
    info = target.lstat()
    if (
        stat.S_ISLNK(info.st_mode)
        or not stat.S_ISDIR(info.st_mode)
        or info.st_uid != os.geteuid()
        or stat.S_IMODE(info.st_mode) != mode
    ):
        raise NativeLratLaunchError(f"unsafe {role}: {target}")
    return target


def _read_exact_fd(fd: int, cap: int) -> bytes:
    chunks: list[bytes] = []
    total = 0
    offset = 0
    while True:
        chunk = os.pread(fd, min(READ_CHUNK_BYTES, cap + 1 - total), offset)
        if not chunk:
            break
        chunks.append(chunk)
        total += len(chunk)
        offset += len(chunk)
        if total > cap:
            raise NativeLratLaunchError("file exceeds configured byte cap")
    return b"".join(chunks)


def _open_regular(
    path: Path, role: str, *, cap: int, executable: bool | None = None,
    allow_root_owner: bool = False,
) -> int:
    target = _normalized_absolute(path, role, must_exist=True)
    flags = os.O_RDONLY | os.O_CLOEXEC
    if hasattr(os, "O_NOFOLLOW"):
        flags |= os.O_NOFOLLOW
    try:
        fd = os.open(target, flags)
    except OSError as exc:
        raise NativeLratLaunchError(f"cannot open {role}") from exc
    try:
        info = os.fstat(fd)
        edge = target.lstat()
        if (
            not stat.S_ISREG(info.st_mode)
            or info.st_uid not in ({os.geteuid(), 0} if allow_root_owner else {os.geteuid()})
            or info.st_nlink != 1
            or info.st_size < 0
            or info.st_size > cap
            or (info.st_dev, info.st_ino) != (edge.st_dev, edge.st_ino)
            or (executable is True and not (info.st_mode & stat.S_IXUSR))
            or (executable is False and bool(info.st_mode & stat.S_IXUSR))
        ):
            raise NativeLratLaunchError(f"unsafe {role}: {target}")
        return fd
    except BaseException:
        os.close(fd)
        raise


def _stable_hash_fd(fd: int, *, cap: int) -> tuple[str, int, os.stat_result]:
    before = os.fstat(fd)
    digest = hashlib.sha256()
    total = 0
    offset = 0
    while True:
        chunk = os.pread(fd, HASH_CHUNK_BYTES, offset)
        if not chunk:
            break
        total += len(chunk)
        offset += len(chunk)
        if total > cap:
            raise NativeLratLaunchError("file exceeds hash cap")
        digest.update(chunk)
    after = os.fstat(fd)
    identity = lambda value: (
        value.st_dev, value.st_ino, value.st_mode, value.st_uid,
        value.st_nlink, value.st_size, value.st_mtime_ns, value.st_ctime_ns,
    )
    if identity(before) != identity(after) or total != before.st_size:
        raise NativeLratLaunchError("file changed while hashing")
    return digest.hexdigest(), total, after


def _file_record(path: Path, role: str, *, cap: int) -> dict[str, Any]:
    fd = _open_regular(path, role, cap=cap, executable=False)
    try:
        digest, size, info = _stable_hash_fd(fd, cap=cap)
    finally:
        os.close(fd)
    return {
        "role": role,
        "path": str(path),
        "file_sha256": digest,
        "bytes": size,
        "device": int(info.st_dev),
        "inode": int(info.st_ino),
        "mode": stat.S_IMODE(info.st_mode),
        "uid": int(info.st_uid),
        "links": int(info.st_nlink),
        "mtime_ns": int(info.st_mtime_ns),
        "ctime_ns": int(info.st_ctime_ns),
    }


def _assert_record_fd(fd: int, path: Path, record: Mapping[str, Any]) -> None:
    info = os.fstat(fd)
    edge = path.lstat()
    actual = {
        "bytes": int(info.st_size), "device": int(info.st_dev),
        "inode": int(info.st_ino), "mode": stat.S_IMODE(info.st_mode),
        "uid": int(info.st_uid), "links": int(info.st_nlink),
        "mtime_ns": int(info.st_mtime_ns), "ctime_ns": int(info.st_ctime_ns),
    }
    if any(actual.get(key) != record.get(key) for key in actual):
        raise NativeLratLaunchError("bound file identity changed")
    if (edge.st_dev, edge.st_ino) != (info.st_dev, info.st_ino):
        raise NativeLratLaunchError("bound file pathname changed")


def _assert_inode_fd_path(fd: int, path: Path, binding: Mapping[str, Any]) -> None:
    info = os.fstat(fd)
    edge = path.lstat()
    expected = (
        binding["device"], binding["inode"], binding["mode"],
        binding["uid"], binding["links"],
    )
    for observed in (info, edge):
        actual = (
            int(observed.st_dev), int(observed.st_ino),
            stat.S_IMODE(observed.st_mode), int(observed.st_uid),
            int(observed.st_nlink),
        )
        if actual != expected:
            raise NativeLratLaunchError("exclusive proof inode/path binding changed")


def _load_json(path: Path, role: str, *, cap: int = MAX_JSON_BYTES) -> dict[str, Any]:
    fd = _open_regular(path, role, cap=cap, executable=False)
    try:
        before = os.fstat(fd)
        payload = _read_exact_fd(fd, cap)
        after = os.fstat(fd)
    finally:
        os.close(fd)
    if (before.st_dev, before.st_ino, before.st_size) != (
        after.st_dev, after.st_ino, after.st_size,
    ):
        raise NativeLratLaunchError(f"{role} changed while reading")
    try:
        value = json.loads(payload.decode("ascii"))
    except (UnicodeDecodeError, json.JSONDecodeError) as exc:
        raise NativeLratLaunchError(f"invalid {role} JSON") from exc
    if type(value) is not dict or payload not in {_canonical(value), _canonical(value) + b"\n"}:
        raise NativeLratLaunchError(f"{role} is not a canonical JSON object")
    return value


def _publish_json(path: Path, value: Mapping[str, Any]) -> None:
    native.publish_record(path, value)


def _publish_bytes(path: Path, payload: bytes) -> dict[str, Any]:
    target = _normalized_absolute(path, "log output", must_exist=False)
    _safe_directory(target.parent, "log output parent")
    flags = os.O_WRONLY | os.O_CREAT | os.O_EXCL | os.O_CLOEXEC
    if hasattr(os, "O_NOFOLLOW"):
        flags |= os.O_NOFOLLOW
    fd = os.open(target, flags, 0o600)
    try:
        view = memoryview(payload)
        while view:
            written = os.write(fd, view)
            if written <= 0:
                raise NativeLratLaunchError("short log write")
            view = view[written:]
        os.fsync(fd)
    finally:
        os.close(fd)
    directory_fd = os.open(target.parent, os.O_RDONLY | os.O_DIRECTORY | os.O_CLOEXEC)
    try:
        os.fsync(directory_fd)
    finally:
        os.close(directory_fd)
    return {"path": str(target), "bytes": len(payload),
            "sha256": hashlib.sha256(payload).hexdigest()}


def _clean_environment() -> dict[str, str]:
    return {
        "PATH": "/usr/bin:/bin", "LC_ALL": "C", "LANG": "C", "TZ": "UTC",
        "OMP_NUM_THREADS": "1", "OPENBLAS_NUM_THREADS": "1",
        "MKL_NUM_THREADS": "1", "NUMEXPR_NUM_THREADS": "1",
    }


def _validate_config(config: ExecutionConfig, *, test_mode: bool) -> ExecutionConfig:
    root = _safe_directory(config.output_root, "pilot output root")
    if not test_mode:
        if root.parent != RUNS or not root.name.startswith("paper400-native-lrat-pilot-v1-"):
            raise NativeLratLaunchError("CLI execution is restricted to a versioned pilot root")
        if config.sealed_elf_runtime is not True:
            raise NativeLratLaunchError("CLI execution requires the sealed ELF runtime")
    catalogs = tuple(sorted((
        _normalized_absolute(path, "CPU lease catalog", must_exist=True)
        for path in config.lease_catalogs
    ), key=str))
    if len(catalogs) != 3 or len(set(catalogs)) != 3:
        raise NativeLratLaunchError("exactly three distinct lease catalogues are required")
    if not test_mode and catalogs != DEFAULT_CATALOGS:
        raise NativeLratLaunchError("CLI execution requires the three pinned catalogues")
    proc_root = _normalized_absolute(config.proc_root, "procfs root", must_exist=True)
    cgroup_mount = _normalized_absolute(
        config.cgroup_mount, "cgroup-v2 mount", must_exist=True,
    )
    if not test_mode and (proc_root != PROC_ROOT or cgroup_mount != CGROUP_MOUNT):
        raise NativeLratLaunchError("CLI execution requires pinned procfs/cgroup roots")
    _require_sha256(config.reservation_sha256, "reservation SHA-256")
    for value, role in (
        (config.solver_timeout_seconds, "solver timeout"),
        (config.checker_timeout_seconds, "checker timeout"),
        (config.proof_cap_bytes, "proof cap"),
        (config.stdout_cap_bytes, "stdout cap"),
        (config.stderr_cap_bytes, "stderr cap"),
        (config.disk_reserve_bytes, "disk reserve"),
    ):
        if type(value) is not int or value <= 0:
            raise NativeLratLaunchError(f"invalid {role}")
    if (
        type(config.lease_recheck_seconds) not in {int, float}
        or isinstance(config.lease_recheck_seconds, bool)
        or not math.isfinite(float(config.lease_recheck_seconds))
        or not 0.05 <= float(config.lease_recheck_seconds) <= 3600.0
    ):
        raise NativeLratLaunchError("invalid lease recheck interval")
    try:
        resource_config = resource_gate._validate_config(resource_gate.ResourceGateConfig(
            proc_root=proc_root, cgroup_mount=cgroup_mount,
            min_host_available_bytes=config.min_host_available_bytes,
            min_cgroup_available_bytes=config.min_cgroup_available_bytes,
            max_host_psi_some_avg10=config.max_host_psi_some_avg10,
            max_host_psi_full_avg10=config.max_host_psi_full_avg10,
            max_cgroup_psi_some_avg10=config.max_cgroup_psi_some_avg10,
            max_cgroup_psi_full_avg10=config.max_cgroup_psi_full_avg10,
        ))
    except resource_gate.ResourceGateError as exc:
        raise NativeLratLaunchError(str(exc)) from exc
    if not test_mode and (
        resource_config.min_host_available_bytes != DEFAULT_HOST_MEMORY_RESERVE_BYTES
        or resource_config.min_cgroup_available_bytes != DEFAULT_CGROUP_MEMORY_RESERVE_BYTES
        or resource_config.max_host_psi_some_avg10 != DEFAULT_HOST_PSI_SOME_AVG10
        or resource_config.max_host_psi_full_avg10 != DEFAULT_HOST_PSI_FULL_AVG10
        or resource_config.max_cgroup_psi_some_avg10 != DEFAULT_CGROUP_PSI_SOME_AVG10
        or resource_config.max_cgroup_psi_full_avg10 != DEFAULT_CGROUP_PSI_FULL_AVG10
    ):
        raise NativeLratLaunchError("CLI execution requires pinned resource thresholds")
    return ExecutionConfig(
        output_root=root,
        lease_catalogs=catalogs,
        reservation_sha256=config.reservation_sha256,
        solver_timeout_seconds=config.solver_timeout_seconds,
        checker_timeout_seconds=config.checker_timeout_seconds,
        proof_cap_bytes=config.proof_cap_bytes,
        stdout_cap_bytes=config.stdout_cap_bytes,
        stderr_cap_bytes=config.stderr_cap_bytes,
        lease_recheck_seconds=float(config.lease_recheck_seconds),
        disk_reserve_bytes=config.disk_reserve_bytes,
        sealed_elf_runtime=config.sealed_elf_runtime,
        proc_root=resource_config.proc_root,
        cgroup_mount=resource_config.cgroup_mount,
        min_host_available_bytes=resource_config.min_host_available_bytes,
        min_cgroup_available_bytes=resource_config.min_cgroup_available_bytes,
        max_host_psi_some_avg10=resource_config.max_host_psi_some_avg10,
        max_host_psi_full_avg10=resource_config.max_host_psi_full_avg10,
        max_cgroup_psi_some_avg10=resource_config.max_cgroup_psi_some_avg10,
        max_cgroup_psi_full_avg10=resource_config.max_cgroup_psi_full_avg10,
    )


def _lease_contract_payload(
    *, cpu: int, bundle: Path, reservation_sha256: str,
    catalogs: Sequence[Path],
) -> dict[str, Any]:
    if type(cpu) is not int or cpu < 0:
        raise NativeLratLaunchError("invalid lease CPU")
    root = _normalized_absolute(bundle, "lease bundle", must_exist=True)
    paths = sorted(
        str(_normalized_absolute(path, "lease catalog", must_exist=True))
        for path in catalogs
    )
    if len(paths) != 3 or len(set(paths)) != 3:
        raise NativeLratLaunchError("lease contract requires three distinct catalogues")
    reservation = _require_sha256(reservation_sha256, "reservation SHA-256")
    return {
        "kind": LEASE_BINDING_KIND,
        "bundle": str(root),
        "reservation_sha256": reservation,
        "catalogs": paths,
        "cpu": cpu,
        "generation": 0,
    }


def derive_plan_cpu_lease(
    *, cpu: int, bundle: Path, reservation_sha256: str,
    catalogs: Sequence[Path],
) -> dict[str, Any]:
    """Derive the PLAN_ONLY lease fields from one three-catalog reservation."""

    payload = _lease_contract_payload(
        cpu=cpu, bundle=bundle, reservation_sha256=reservation_sha256,
        catalogs=catalogs,
    )
    token = hashlib.sha256(
        b"paper400-native-lrat-lease-token-v1\0" + _canonical(payload)
    ).hexdigest()
    return {
        "kind": native.CPU_LEASE_KIND,
        "lease_id": f"native-lrat-v1-cpu{cpu}-{reservation_sha256[:16]}",
        "lease_token_sha256": token,
        "catalog_record_sha256": _digest(payload),
        "cpu": cpu,
        "generation": 0,
        "exclusive": True,
        "state": "RESERVED",
    }


@contextlib.contextmanager
def _catalog_locks(catalogs: Sequence[Path]) -> Iterator[None]:
    descriptors: list[int] = []
    deadline = time.monotonic() + 5.0
    try:
        while True:
            busy = False
            for catalog in sorted(catalogs, key=str):
                lock = catalog.with_name("cpu-leases.lock")
                fd = _open_regular(lock, "CPU lease catalog lock", cap=1 << 20)
                info = os.fstat(fd)
                if stat.S_IMODE(info.st_mode) != 0o600:
                    os.close(fd)
                    raise NativeLratLaunchError("CPU lease catalog lock must be mode 0600")
                try:
                    fcntl.flock(fd, fcntl.LOCK_EX | fcntl.LOCK_NB)
                except BlockingIOError:
                    os.close(fd)
                    busy = True
                    break
                descriptors.append(fd)
            if not busy:
                break
            for fd in reversed(descriptors):
                with contextlib.suppress(OSError):
                    fcntl.flock(fd, fcntl.LOCK_UN)
                with contextlib.suppress(OSError):
                    os.close(fd)
            descriptors.clear()
            if time.monotonic() >= deadline:
                raise NativeLratLaunchError("CPU lease catalog locks remained busy for 5 seconds")
            time.sleep(0.01)
        yield
    finally:
        for fd in reversed(descriptors):
            with contextlib.suppress(OSError):
                fcntl.flock(fd, fcntl.LOCK_UN)
            with contextlib.suppress(OSError):
                os.close(fd)


def _validate_catalog(path: Path) -> tuple[dict[str, Any], dict[str, Any]]:
    fd = _open_regular(path, "CPU lease catalog", cap=MAX_JSON_BYTES, executable=False)
    try:
        info = os.fstat(fd)
        if stat.S_IMODE(info.st_mode) != 0o600:
            raise NativeLratLaunchError("CPU lease catalog must be mode 0600")
        payload = _read_exact_fd(fd, MAX_JSON_BYTES)
        after = os.fstat(fd)
        if (
            info.st_dev, info.st_ino, info.st_mode, info.st_uid, info.st_nlink,
            info.st_size, info.st_mtime_ns, info.st_ctime_ns,
        ) != (
            after.st_dev, after.st_ino, after.st_mode, after.st_uid, after.st_nlink,
            after.st_size, after.st_mtime_ns, after.st_ctime_ns,
        ):
            raise NativeLratLaunchError("CPU lease catalog changed while reading")
        digest = hashlib.sha256(payload).hexdigest()
    finally:
        os.close(fd)
    try:
        value = json.loads(payload.decode("ascii"))
    except (UnicodeDecodeError, json.JSONDecodeError) as exc:
        raise NativeLratLaunchError("CPU lease catalog JSON is invalid") from exc
    if (
        type(value) is not dict
        or payload not in {_canonical(value), _canonical(value) + b"\n"}
        or set(value) != {"schema_version", "kind", "leases", "updated_at", "catalog_sha256"}
        or value.get("schema_version") != 1
        or value.get("kind") != CATALOG_KIND
        or not _selfhash(value, "catalog_sha256")
        or type(value.get("leases")) is not list
        or type(value.get("updated_at")) not in {int, float}
        or not math.isfinite(float(value["updated_at"]))
    ):
        raise NativeLratLaunchError("CPU lease catalog schema/self-hash mismatch")
    active: set[int] = set()
    for entry in value["leases"]:
        if (
            type(entry) is not dict
            or set(entry) != {"cpu", "bundle", "reservation_sha256", "state", "created_at", "released_at"}
            or type(entry.get("cpu")) is not int
            or entry["cpu"] < 0
            or type(entry.get("bundle")) is not str
            or type(entry.get("reservation_sha256")) is not str
            or SHA256_RE.fullmatch(entry["reservation_sha256"]) is None
            or entry.get("state") not in {"RESERVED", "RELEASED"}
            or type(entry.get("created_at")) not in {int, float}
            or not math.isfinite(float(entry["created_at"]))
            or (
                entry.get("released_at") is not None
                and (
                    type(entry["released_at"]) not in {int, float}
                    or not math.isfinite(float(entry["released_at"]))
                )
            )
        ):
            raise NativeLratLaunchError("CPU lease catalog contains a malformed entry")
        if entry["state"] == "RESERVED":
            if entry["cpu"] in active:
                raise NativeLratLaunchError("CPU lease catalog duplicates an active CPU")
            active.add(entry["cpu"])
    return value, {
        "path": str(path), "payload_sha256": digest,
        "catalog_sha256": value["catalog_sha256"], "bytes": len(payload),
        "device": int(info.st_dev), "inode": int(info.st_ino),
        "mode": stat.S_IMODE(info.st_mode), "uid": int(info.st_uid),
    }


def _validate_reservation(config: ExecutionConfig, cpus: Sequence[int]) -> tuple[dict[str, Any], dict[str, Any]]:
    path = config.output_root / "cpu-reservation.json"
    fd = _open_regular(path, "external CPU reservation", cap=MAX_JSON_BYTES, executable=False)
    try:
        info = os.fstat(fd)
        if stat.S_IMODE(info.st_mode) != 0o400:
            raise NativeLratLaunchError("CPU reservation must be immutable mode 0400")
        payload = _read_exact_fd(fd, MAX_JSON_BYTES)
        after = os.fstat(fd)
        if (
            info.st_dev, info.st_ino, info.st_mode, info.st_uid, info.st_nlink,
            info.st_size, info.st_mtime_ns, info.st_ctime_ns,
        ) != (
            after.st_dev, after.st_ino, after.st_mode, after.st_uid, after.st_nlink,
            after.st_size, after.st_mtime_ns, after.st_ctime_ns,
        ):
            raise NativeLratLaunchError("CPU reservation changed while reading")
    finally:
        os.close(fd)
    try:
        value = json.loads(payload.decode("ascii"))
    except (UnicodeDecodeError, json.JSONDecodeError) as exc:
        raise NativeLratLaunchError("CPU reservation JSON is invalid") from exc
    if (
        type(value) is not dict
        or payload not in {_canonical(value), _canonical(value) + b"\n"}
        or set(value) != {
            "schema_version", "kind", "bundle", "cpus", "observations",
            "kernel_hardware_exclusive", "scheduler_lease_only", "created_at",
            "reservation_sha256",
        }
        or value.get("schema_version") != 1
        or value.get("kind") != RESERVATION_KIND
        or value.get("bundle") != str(config.output_root)
        or value.get("cpus") != sorted(cpus)
        or type(value.get("observations")) is not list
        or value.get("kernel_hardware_exclusive") is not False
        or value.get("scheduler_lease_only") is not True
        or type(value.get("created_at")) not in {int, float}
        or not math.isfinite(float(value["created_at"]))
        or value.get("reservation_sha256") != config.reservation_sha256
        or not _selfhash(value, "reservation_sha256")
    ):
        raise NativeLratLaunchError("external CPU reservation is malformed or cross-bound")
    observed_cpus: list[int] = []
    for observation in value["observations"]:
        if (
            type(observation) is not dict
            or set(observation) != {
                "cpu", "pinned_running_processes",
                "broad_affinity_running_process_count",
                "kernel_hardware_exclusive", "lease_scope",
            }
            or type(observation.get("cpu")) is not int
            or type(observation.get("pinned_running_processes")) is not list
            or type(observation.get("broad_affinity_running_process_count")) is not int
            or observation["broad_affinity_running_process_count"] < 0
            or observation.get("kernel_hardware_exclusive") is not False
            or observation.get("lease_scope") != RESERVATION_LEASE_SCOPE
        ):
            raise NativeLratLaunchError("CPU reservation observation is malformed")
        for process in observation["pinned_running_processes"]:
            if (
                type(process) is not dict
                or set(process) != {"command", "pid", "state"}
                or type(process.get("command")) is not str
                or type(process.get("pid")) is not int
                or process["pid"] <= 0
                or type(process.get("state")) is not str
                or not process["state"]
            ):
                raise NativeLratLaunchError("CPU reservation process observation is malformed")
        if (
            observation["pinned_running_processes"]
            or observation["broad_affinity_running_process_count"] != 0
        ):
            raise NativeLratLaunchError(
                "CPU reservation contains a nonempty conflict observation"
            )
        observed_cpus.append(observation["cpu"])
    if sorted(observed_cpus) != sorted(cpus) or len(set(observed_cpus)) != len(cpus):
        raise NativeLratLaunchError("CPU reservation observations do not cover each CPU once")
    return value, {
        "path": str(path), "sha256": hashlib.sha256(payload).hexdigest(),
        "bytes": len(payload), "device": int(info.st_dev), "inode": int(info.st_ino),
        "mode": stat.S_IMODE(info.st_mode), "uid": int(info.st_uid),
    }


def _validate_lease_state(
    config: ExecutionConfig, reservation: Mapping[str, Any], cpus: Sequence[int],
) -> tuple[dict[str, Any], dict[str, Any]]:
    path = config.output_root / lease_owner.STATE_FILE
    fd = _open_regular(path, "native-LRAT lease state", cap=MAX_JSON_BYTES, executable=False)
    try:
        info = os.fstat(fd)
        if stat.S_IMODE(info.st_mode) != 0o600:
            raise NativeLratLaunchError("native-LRAT lease state must be mode 0600")
        payload = _read_exact_fd(fd, MAX_JSON_BYTES)
        after = os.fstat(fd)
        if (
            info.st_dev, info.st_ino, info.st_mode, info.st_uid,
            info.st_size, info.st_mtime_ns, info.st_ctime_ns,
        ) != (
            after.st_dev, after.st_ino, after.st_mode, after.st_uid,
            after.st_size, after.st_mtime_ns, after.st_ctime_ns,
        ):
            raise NativeLratLaunchError("native-LRAT lease state changed while reading")
    finally:
        os.close(fd)
    try:
        value = json.loads(payload.decode("ascii"))
    except (UnicodeDecodeError, json.JSONDecodeError) as exc:
        raise NativeLratLaunchError("native-LRAT lease state is invalid JSON") from exc
    if (
        type(value) is not dict
        or payload not in {_canonical(value), _canonical(value) + b"\n"}
        or set(value) != {
            "schema_version", "kind", "bundle", "reservation_sha256", "cpus",
            "state", "epoch", "acquired_at", "renewed_at", "expires_at",
            "release_requested_at", "released_at", "process_control_authority",
            "proof_or_certificate_authority", "cleanup_authority", "record_sha256",
        }
        or value.get("schema_version") != 1
        or value.get("kind") != lease_owner.STATE_KIND
        or value.get("bundle") != str(config.output_root)
        or value.get("reservation_sha256") != reservation["reservation_sha256"]
        or value.get("cpus") != sorted(cpus)
        or value.get("state") != "ACTIVE"
        or type(value.get("epoch")) is not int or value["epoch"] < 1
        or type(value.get("expires_at")) not in {int, float}
        or not math.isfinite(float(value["expires_at"]))
        or float(value["expires_at"]) <= time.time() + config.lease_recheck_seconds
        or value.get("release_requested_at") is not None
        or value.get("released_at") is not None
        or value.get("process_control_authority") is not False
        or value.get("proof_or_certificate_authority") is not False
        or value.get("cleanup_authority") is not False
        or not _selfhash(value, "record_sha256")
    ):
        raise NativeLratLaunchError("native-LRAT lease state is inactive, expired, or malformed")
    return value, {
        "path": str(path), "sha256": hashlib.sha256(payload).hexdigest(),
        "record_sha256": value["record_sha256"], "epoch": value["epoch"],
        "expires_at": value["expires_at"], "device": int(info.st_dev),
        "inode": int(info.st_ino), "mode": stat.S_IMODE(info.st_mode),
    }


def _catalog_snapshot(
    config: ExecutionConfig, participants: Sequence[Mapping[str, Any]],
) -> dict[str, Any]:
    cpus = sorted(item["cpu_lease"]["cpu"] for item in participants)
    if cpus != sorted(set(cpus)):
        raise NativeLratLaunchError("plan reuses a CPU")
    with _catalog_locks(config.lease_catalogs):
        reservation, reservation_record = _validate_reservation(config, cpus)
        _lease_state, lease_state_record = _validate_lease_state(
            config, reservation, cpus,
        )
        catalog_values: list[tuple[Path, dict[str, Any], dict[str, Any]]] = []
        for path in config.lease_catalogs:
            value, record = _validate_catalog(path)
            catalog_values.append((path, value, record))
        expected_owner = (str(config.output_root), config.reservation_sha256)
        for participant in participants:
            cpu = participant["cpu_lease"]["cpu"]
            expected_lease = derive_plan_cpu_lease(
                cpu=cpu, bundle=config.output_root,
                reservation_sha256=config.reservation_sha256,
                catalogs=sorted(config.lease_catalogs, key=str),
            )
            if participant["cpu_lease"] != expected_lease:
                raise NativeLratLaunchError(
                    f"leaf {participant['leaf_id']} PLAN_ONLY lease is not cross-bound "
                    "to the three-catalog reservation"
                )
            for path, catalog, _record in catalog_values:
                owners = [
                    entry for entry in catalog["leases"]
                    if entry["state"] == "RESERVED" and entry["cpu"] == cpu
                ]
                if len(owners) != 1:
                    raise NativeLratLaunchError(
                        f"CPU {cpu} lacks exactly one active owner in {path}"
                    )
                owner = owners[0]
                if (owner["bundle"], owner["reservation_sha256"]) != expected_owner:
                    raise NativeLratLaunchError(f"CPU {cpu} has a mismatched scheduler owner")
        snapshot = {
            "schema_version": 1, "kind": CATALOG_SNAPSHOT_KIND,
            "observed_at": time.time(), "bundle": str(config.output_root),
            "reservation_sha256": reservation["reservation_sha256"],
            "reservation": reservation_record,
            "lease_state": lease_state_record, "cpus": cpus,
            "catalogs": [record for _path, _value, record in catalog_values],
            "each_cpu_has_one_identical_owner_in_every_catalog": True,
            "catalog_locks_held_only_during_snapshot": True,
            "catalog_mutation": False,
        }
        return _seal(snapshot, "authority_sha256")


def _resource_config(config: ExecutionConfig) -> resource_gate.ResourceGateConfig:
    return resource_gate.ResourceGateConfig(
        proc_root=config.proc_root,
        cgroup_mount=config.cgroup_mount,
        min_host_available_bytes=config.min_host_available_bytes,
        min_cgroup_available_bytes=config.min_cgroup_available_bytes,
        max_host_psi_some_avg10=config.max_host_psi_some_avg10,
        max_host_psi_full_avg10=config.max_host_psi_full_avg10,
        max_cgroup_psi_some_avg10=config.max_cgroup_psi_some_avg10,
        max_cgroup_psi_full_avg10=config.max_cgroup_psi_full_avg10,
    )


def _owned_process_map(children: Sequence[_Child]) -> dict[int, int]:
    return {
        child.pid: child.proc_start_ticks
        for child in children
        if not child.reaped and child.proc_start_ticks is not None
    }


def _resource_snapshot(
    config: ExecutionConfig, participants: Sequence[Mapping[str, Any]], *,
    children: Sequence[_Child] = (),
    baseline: Mapping[str, Any] | None = None,
) -> dict[str, Any]:
    cpus = sorted(item["cpu_lease"]["cpu"] for item in participants)
    try:
        return resource_gate.snapshot(
            _resource_config(config), cpus,
            owned_processes=_owned_process_map(children),
            baseline=baseline,
        )
    except resource_gate.ResourceGateError as exc:
        raise NativeLratLaunchError(str(exc)) from exc


def _guarded_catalog_snapshot(
    config: ExecutionConfig, participants: Sequence[Mapping[str, Any]], *,
    children: Sequence[_Child] = (),
    baseline: Mapping[str, Any] | None = None,
) -> tuple[dict[str, Any], dict[str, Any]]:
    """Bracket the short catalog lock with lock-free live resource gates."""

    before = _resource_snapshot(
        config, participants, children=children, baseline=baseline,
    )
    initial = before if baseline is None else dict(baseline)
    catalog = _catalog_snapshot(config, participants)
    after = _resource_snapshot(
        config, participants, children=children, baseline=initial,
    )
    payload = dict(catalog)
    payload.pop("authority_sha256")
    payload.update({
        "resource_gate_before": before,
        "resource_gate_after": after,
        "resource_gate_brackets_catalog_lock": True,
    })
    return _seal(payload, "authority_sha256"), initial


def _check_initial_root_shape(
    plan: Mapping[str, Any], config: ExecutionConfig,
) -> None:
    allowed_root = {"cpu-reservation.json", lease_owner.STATE_FILE, "leaves"}
    entries = {item.name for item in config.output_root.iterdir()}
    if entries != allowed_root:
        raise NativeLratLaunchError(
            "fresh pilot root must contain only reservation, lease state, and leaves/"
        )
    leaves_root = _safe_directory(config.output_root / "leaves", "pilot leaves root")
    expected_leaf_ids = {item["leaf_id"] for item in plan["participants"]}
    if any(EXEC_LEAF_ID_RE.fullmatch(leaf_id) is None for leaf_id in expected_leaf_ids):
        raise NativeLratLaunchError("leaf id is not execution-path safe")
    actual_leaf_ids = {item.name for item in leaves_root.iterdir()}
    if actual_leaf_ids != expected_leaf_ids:
        raise NativeLratLaunchError("pilot leaf directory membership mismatch")
    for participant in plan["participants"]:
        leaf_id = participant["leaf_id"]
        leaf_root = _safe_directory(leaves_root / leaf_id, "pilot leaf root")
        if any(leaf_root.iterdir()):
            raise NativeLratLaunchError("fresh pilot leaf root is not empty")
        expected_proof = leaf_root / "proof.lrat"
        if participant["proof_output"]["path"] != str(expected_proof):
            raise NativeLratLaunchError("proof output escapes the exact pilot leaf root")
        cnf = Path(participant["cnf"]["path"])
        if any(FORBIDDEN_COMPONENT_RE.search(part) for part in cnf.parts):
            raise NativeLratLaunchError("checkpoint/DMTCP/resume CNF source is forbidden")
    available = os.statvfs(config.output_root)
    free_bytes = int(available.f_bavail) * int(available.f_frsize)
    required = config.proof_cap_bytes * len(plan["participants"]) + config.disk_reserve_bytes
    if free_bytes < required:
        raise NativeLratLaunchError("insufficient disk headroom for all proof caps")


def _validate_plan_for_execution(
    plan: Mapping[str, Any], config: ExecutionConfig, *,
    pins: native.ToolchainPins, planner_path: Path,
) -> dict[str, Any]:
    verified = native.verify_plan(
        plan, pins=pins, planner_path=planner_path, require_prelaunch=True,
    )
    if (
        verified.get("authority") != "PLAN_ONLY"
        or verified.get("production_deployed") is not False
        or verified.get("request", {}).get("generation") != 0
        or verified.get("request", {}).get("fresh_leaf_generation") is not True
        or verified.get("request", {}).get("resume") is not False
        or verified.get("request", {}).get("checkpoint_source") is not None
        or verified.get("request", {}).get("existing_proof_path") is not None
        or verified.get("request", {}).get("existing_proof_format") is not None
        or verified.get("deployment_gate", {}).get("production_eligible") is not False
    ):
        raise NativeLratLaunchError("plan is not a fresh, non-production generation-zero plan")
    if not 1 <= len(verified.get("participants", [])) <= native.MAX_PARTICIPANTS:
        raise NativeLratLaunchError("invalid participant count")
    if config.checker_timeout_seconds > pins.lrat_checker_timeout_seconds:
        raise NativeLratLaunchError("checker timeout exceeds the trusted checker policy")
    if config.proof_cap_bytes > pins.lrat_checker_max_proof_bytes:
        raise NativeLratLaunchError("proof cap exceeds the trusted checker policy")
    for participant in verified["participants"]:
        argv = participant["solver_invocation"]["argv"]
        exact = [
            participant["solver_invocation"]["argv"][0],
            "--lrat", "--no-binary",
            f"/proc/self/fd/{SOLVER_CNF_FD}",
            f"/proc/self/fd/{SOLVER_PROOF_FD}",
        ]
        if argv != exact:
            raise NativeLratLaunchError("CaDiCaL logical argv is not exact native ASCII LRAT")
        if participant.get("generation") != 0:
            raise NativeLratLaunchError("participant is not generation zero")
    _check_initial_root_shape(verified, config)
    return verified


def _source_binding(path: Path) -> dict[str, Any]:
    return _file_record(path, "native-lrat-launcher-source-v1", cap=16 << 20)


def _copy_to_sealed_memfd(
    path: Path, *, expected_sha256: str, expected_bytes: int | None,
    allow_root_owner: bool = False, executable: bool | None = True,
    enforce_nodeflib: bool = False,
) -> tuple[int, dict[str, Any]]:
    source = _open_regular(
        path, "pinned executable", cap=64 << 20, executable=executable,
        allow_root_owner=allow_root_owner,
    )
    if not hasattr(os, "memfd_create"):
        os.close(source)
        raise NativeLratLaunchError("sealed memfd execution is unavailable")
    target = os.memfd_create(
        f"paper400-native-lrat-{path.name}",
        getattr(os, "MFD_CLOEXEC", 0) | getattr(os, "MFD_ALLOW_SEALING", 0),
    )
    try:
        before = os.fstat(source)
        chunks: list[bytes] = []
        digest = hashlib.sha256()
        total = 0
        while True:
            chunk = os.read(source, READ_CHUNK_BYTES)
            if not chunk:
                break
            digest.update(chunk)
            chunks.append(chunk)
            total += len(chunk)
        after = os.fstat(source)
        identity = lambda value: (
            value.st_dev, value.st_ino, value.st_size,
            value.st_mtime_ns, value.st_ctime_ns,
        )
        if identity(before) != identity(after):
            raise NativeLratLaunchError("executable changed while sealing")
        actual = digest.hexdigest()
        if actual != expected_sha256 or (expected_bytes is not None and total != expected_bytes):
            raise NativeLratLaunchError("pinned executable hash/size mismatch")
        payload = b"".join(chunks)
        if enforce_nodeflib:
            derived, nodeflib_patch = _derive_nodeflib_elf(payload, path.name)
        else:
            derived, nodeflib_patch = payload, None
        view = memoryview(derived)
        while view:
            written = os.write(target, view)
            if written <= 0:
                raise NativeLratLaunchError("short memfd write")
            view = view[written:]
        os.fchmod(target, 0o500)
        fcntl.fcntl(target, F_ADD_SEALS, ALL_MEMFD_SEALS)
        if fcntl.fcntl(target, F_GET_SEALS) != ALL_MEMFD_SEALS:
            raise NativeLratLaunchError("executable memfd seal mismatch")
        os.lseek(target, 0, os.SEEK_SET)
        return target, {
            "source_path": str(path), "source_sha256": actual,
            "sha256": hashlib.sha256(derived).hexdigest(), "bytes": len(derived),
            "nodeflib_derivation": enforce_nodeflib,
            "nodeflib_patch_witness": nodeflib_patch,
            "mode": 0o500, "sealed_memfd": True,
            "seals": ["WRITE", "GROW", "SHRINK", "SEAL"],
        }
    except BaseException:
        os.close(target)
        raise
    finally:
        os.close(source)


def _derive_nodeflib_elf(payload: bytes, role: str) -> tuple[bytes, dict[str, Any]]:
    """Deterministically add DF_1_NODEFLIB before sealing a pinned ELF."""

    if (
        len(payload) < 64 or payload[:4] != b"\x7fELF"
        or payload[4] != 2 or payload[5] != 1 or payload[6] != 1
    ):
        raise NativeLratLaunchError(f"{role} is not derivable ELF64")
    try:
        header = struct.unpack_from("<HHIQQQIHHHHHH", payload, 16)
    except struct.error as exc:
        raise NativeLratLaunchError(f"{role} has a truncated ELF header") from exc
    program_offset = header[4]
    program_entry_size = header[8]
    program_count = header[9]
    if (
        program_entry_size != 56 or not 1 <= program_count <= 4096
        or program_offset + program_entry_size * program_count > len(payload)
    ):
        raise NativeLratLaunchError(f"{role} has an invalid ELF program table")
    dynamic: tuple[int, int] | None = None
    for index in range(program_count):
        offset = program_offset + index * program_entry_size
        segment = struct.unpack_from("<IIQQQQQQ", payload, offset)
        if segment[0] == 2:
            if dynamic is not None:
                raise NativeLratLaunchError(f"{role} has multiple PT_DYNAMIC segments")
            dynamic = (segment[2], segment[5])
    if dynamic is None or dynamic[1] % 16 or sum(dynamic) > len(payload):
        raise NativeLratLaunchError(f"{role} has no bounded PT_DYNAMIC segment")
    result = bytearray(payload)
    first_null_offset: int | None = None
    flags_offset: int | None = None
    flags_value = 0
    for offset in range(dynamic[0], dynamic[0] + dynamic[1], 16):
        tag, value = struct.unpack_from("<qQ", result, offset)
        if first_null_offset is not None:
            break
        if tag == DT_FLAGS_1:
            if flags_offset is not None:
                raise NativeLratLaunchError(f"{role} repeats DT_FLAGS_1")
            flags_offset, flags_value = offset, value
        elif tag == 0:
            if value != 0:
                raise NativeLratLaunchError(f"{role} has a nonzero DT_NULL value")
            first_null_offset = offset
    if flags_offset is not None:
        patch_offset = flags_offset
        old_tag, old_value = DT_FLAGS_1, flags_value
        new_value = flags_value | DF_1_NODEFLIB
        struct.pack_into("<qQ", result, flags_offset, DT_FLAGS_1, new_value)
    else:
        if first_null_offset is None or first_null_offset + 32 > dynamic[0] + dynamic[1]:
            raise NativeLratLaunchError(f"{role} lacks a spare DT_NULL slot for NODEFLIB")
        next_tag, next_value = struct.unpack_from("<qQ", result, first_null_offset + 16)
        if (next_tag, next_value) != (0, 0):
            raise NativeLratLaunchError(
                f"{role} lacks adjacent zero DT_NULL slots for NODEFLIB"
            )
        patch_offset = first_null_offset
        old_tag, old_value = 0, 0
        new_value = DF_1_NODEFLIB
        struct.pack_into("<qQ", result, first_null_offset, DT_FLAGS_1, new_value)
    derived = bytes(result)
    differences = [
        {"offset": index, "old": before, "new": after}
        for index, (before, after) in enumerate(zip(payload, derived, strict=True))
        if before != after
    ]
    if not differences:
        raise NativeLratLaunchError(f"{role} NODEFLIB derivation made no byte change")
    return derived, {
        "dynamic_entry_offset": patch_offset,
        "old_tag": old_tag, "old_value": old_value,
        "new_tag": DT_FLAGS_1, "new_value": new_value,
        "byte_differences": differences,
    }


def _elf_dynamic_contract(fd: int, role: str) -> dict[str, Any]:
    """Parse the ELF64 dynamic table without trusting a host-side helper."""

    payload = _read_exact_fd(fd, 64 << 20)
    if (
        len(payload) < 64 or payload[:4] != b"\x7fELF"
        or payload[4] != 2 or payload[5] != 1 or payload[6] != 1
    ):
        raise NativeLratLaunchError(f"{role} is not little-endian ELF64")
    try:
        header = struct.unpack_from("<HHIQQQIHHHHHH", payload, 16)
    except struct.error as exc:
        raise NativeLratLaunchError(f"{role} has a truncated ELF header") from exc
    (
        elf_type, machine, version, _entry, program_offset, _section_offset,
        _flags, header_size, program_entry_size, program_count,
        _section_entry_size, _section_count, _section_name_index,
    ) = header
    if (
        elf_type not in {2, 3} or machine != 62 or version != 1
        or header_size != 64 or program_entry_size != 56
        or not 1 <= program_count <= 4096
        or program_offset + program_entry_size * program_count > len(payload)
    ):
        raise NativeLratLaunchError(f"{role} ELF header is outside the pinned ABI")
    loads: list[tuple[int, int, int]] = []
    dynamic: tuple[int, int] | None = None
    for index in range(program_count):
        offset = program_offset + index * program_entry_size
        try:
            (
                segment_type, _segment_flags, file_offset, virtual_address,
                _physical_address, file_size, _memory_size, _alignment,
            ) = struct.unpack_from("<IIQQQQQQ", payload, offset)
        except struct.error as exc:
            raise NativeLratLaunchError(f"{role} has a truncated program table") from exc
        if file_offset + file_size > len(payload):
            raise NativeLratLaunchError(f"{role} ELF segment escapes the file")
        if segment_type == 1:
            loads.append((virtual_address, file_offset, file_size))
        elif segment_type == 2:
            if dynamic is not None:
                raise NativeLratLaunchError(f"{role} has multiple PT_DYNAMIC segments")
            dynamic = (file_offset, file_size)
    if dynamic is None or not loads:
        raise NativeLratLaunchError(f"{role} lacks a dynamic loading contract")
    dynamic_offset, dynamic_size = dynamic
    if dynamic_size % 16:
        raise NativeLratLaunchError(f"{role} dynamic table is misaligned")
    needed_offsets: list[int] = []
    string_address: int | None = None
    string_size: int | None = None
    soname_offset: int | None = None
    forbidden_tags = {15, 29, 0x6FFFFEFB, 0x6FFFFEFC, 0x7FFFFFFD, 0x7FFFFFFF}
    forbidden_seen: list[int] = []
    flags_1: int | None = None
    terminated = False
    for offset in range(dynamic_offset, dynamic_offset + dynamic_size, 16):
        tag, value = struct.unpack_from("<qQ", payload, offset)
        if tag == 0:
            terminated = True
            break
        if tag == 1:
            needed_offsets.append(value)
        elif tag == 5:
            string_address = value
        elif tag == 10:
            string_size = value
        elif tag == 14:
            soname_offset = value
        elif tag == DT_FLAGS_1:
            if flags_1 is not None:
                raise NativeLratLaunchError(f"{role} repeats DT_FLAGS_1")
            flags_1 = value
        elif tag in forbidden_tags:
            forbidden_seen.append(tag)
    if (
        not terminated or string_address is None or string_size is None
        or string_size <= 0 or forbidden_seen
    ):
        raise NativeLratLaunchError(
            f"{role} has an incomplete or redirectable dynamic loading contract"
        )
    string_file_offset: int | None = None
    for virtual_address, file_offset, file_size in loads:
        if (
            virtual_address <= string_address
            and string_address + string_size <= virtual_address + file_size
        ):
            string_file_offset = file_offset + string_address - virtual_address
            break
    if (
        string_file_offset is None
        or string_file_offset + string_size > len(payload)
    ):
        raise NativeLratLaunchError(f"{role} dynamic string table is unmapped")
    string_table = payload[string_file_offset:string_file_offset + string_size]

    def dynamic_string(offset: int, field: str) -> str:
        if offset < 0 or offset >= len(string_table):
            raise NativeLratLaunchError(f"{role} {field} offset is invalid")
        end = string_table.find(b"\0", offset)
        if end < 0:
            raise NativeLratLaunchError(f"{role} {field} is unterminated")
        try:
            value = string_table[offset:end].decode("ascii")
        except UnicodeDecodeError as exc:
            raise NativeLratLaunchError(f"{role} {field} is not ASCII") from exc
        if not value or "/" in value:
            raise NativeLratLaunchError(f"{role} {field} is not a bare SONAME")
        return value

    needed = [dynamic_string(offset, "DT_NEEDED") for offset in needed_offsets]
    if len(needed) != len(set(needed)):
        raise NativeLratLaunchError(f"{role} repeats a DT_NEEDED entry")
    soname = (
        None if soname_offset is None
        else dynamic_string(soname_offset, "DT_SONAME")
    )
    return {
        "elf_class": "ELF64", "endianness": "little", "machine": "x86_64",
        "needed": needed, "soname": soname,
        "forbidden_dynamic_redirect_tags_absent": True,
        "dt_flags_1": flags_1 or 0,
        "nodeflib": bool((flags_1 or 0) & DF_1_NODEFLIB),
    }


def _dead_empty_directory(fd: int) -> bool:
    if os.fstat(fd).st_nlink != 0:
        return False
    try:
        return os.listdir(fd) == []
    except FileNotFoundError as exc:
        return exc.errno == errno.ENOENT


def _stage_runtime(config: ExecutionConfig, pins: native.ToolchainPins) -> _Runtime:
    if Path("/etc/ld.so.preload").exists() or Path("/etc/ld.so.preload").is_symlink():
        raise NativeLratLaunchError("/etc/ld.so.preload must remain absent")
    parent = _safe_directory(config.output_root, "runtime parent")
    parent_fd = os.open(parent, os.O_RDONLY | os.O_DIRECTORY | os.O_CLOEXEC)
    directory_fd = loader_fd = solver_fd = checker_fd = -1
    dso_fds: list[int] = []
    name = f".native-lrat-elf-v1-{os.getpid()}-{uuid.uuid4().hex}"
    directory_unlinked = False
    try:
        os.mkdir(name, 0o700, dir_fd=parent_fd)
        directory_fd = os.open(
            name, os.O_RDONLY | os.O_DIRECTORY | os.O_CLOEXEC | os.O_NOFOLLOW,
            dir_fd=parent_fd,
        )
        loader_name, loader_path, loader_bytes, loader_sha = ELF_OBJECT_SPECS[0]
        loader_fd, loader_record = _copy_to_sealed_memfd(
            loader_path, expected_sha256=loader_sha,
            expected_bytes=loader_bytes, allow_root_owner=True,
            executable=None, enforce_nodeflib=False,
        )
        loader_record.update({
            "soname": loader_name,
            "runtime_fd": RUNTIME_LOADER_FD,
            "dynamic": _elf_dynamic_contract(loader_fd, loader_name),
        })
        records: list[dict[str, Any]] = []
        for index, (soname, source_path, expected_bytes, expected_sha) in enumerate(
            ELF_OBJECT_SPECS[1:]
        ):
            descriptor, object_record = _copy_to_sealed_memfd(
                source_path, expected_sha256=expected_sha,
                expected_bytes=expected_bytes, allow_root_owner=True,
                executable=None, enforce_nodeflib=True,
            )
            dso_fds.append(descriptor)
            runtime_fd = RUNTIME_DSO_FD_BASE + index
            target = f"/proc/self/fd/{runtime_fd}"
            records.append({
                "soname": soname, **object_record,
                "runtime_fd": runtime_fd, "preload_path": target,
                "dynamic": _elf_dynamic_contract(descriptor, soname),
            })
        available_sonames = {loader_name, *(item["soname"] for item in records)}
        if available_sonames != {item[0] for item in ELF_OBJECT_SPECS}:
            raise NativeLratLaunchError("private runtime SONAME membership mismatch")
        for item in (loader_record, *records):
            if item["dynamic"]["soname"] != item["soname"]:
                raise NativeLratLaunchError("pinned DSO DT_SONAME mismatch")
            if not set(item["dynamic"]["needed"]).issubset(available_sonames):
                raise NativeLratLaunchError("pinned DSO dependency closure is incomplete")
            if item is not loader_record and item["dynamic"]["nodeflib"] is not True:
                raise NativeLratLaunchError("pinned DSO NODEFLIB derivation failed")
        if loader_record["dynamic"]["needed"] or loader_record["dynamic"]["nodeflib"]:
            raise NativeLratLaunchError("loader bootstrap contract is not dependency-free")
        solver_fd, solver_record = _copy_to_sealed_memfd(
            pins.solver_path, expected_sha256=pins.solver_sha256,
            expected_bytes=None, enforce_nodeflib=True,
        )
        checker_fd, checker_record = _copy_to_sealed_memfd(
            pins.lrat_checker_path, expected_sha256=pins.lrat_checker_sha256,
            expected_bytes=None, enforce_nodeflib=True,
        )
        solver_record["dynamic"] = _elf_dynamic_contract(solver_fd, "solver")
        checker_record["dynamic"] = _elf_dynamic_contract(checker_fd, "checker")
        for role, tool_record in (("solver", solver_record), ("checker", checker_record)):
            if not set(tool_record["dynamic"]["needed"]).issubset(available_sonames):
                raise NativeLratLaunchError(f"{role} dependency closure is incomplete")
            if tool_record["dynamic"]["nodeflib"] is not True:
                raise NativeLratLaunchError(f"{role} NODEFLIB derivation failed")
        # No path-addressable DSO is ever created.  The loader receives every
        # non-loader member of the closed DT_NEEDED graph through --preload
        # using its sealed memfd.  Its nominal --library-path is an empty,
        # already-unlinked directory, so another same-UID process cannot add
        # or replace a lookup candidate between verification and exec.
        os.fchmod(directory_fd, 0o500)
        os.fsync(directory_fd)
        os.rmdir(name, dir_fd=parent_fd)
        os.fsync(parent_fd)
        directory_unlinked = True
        directory_info = os.fstat(directory_fd)
        if not _dead_empty_directory(directory_fd):
            raise NativeLratLaunchError("private loader fallback directory is not empty/unlinked")
        record = _seal({
            "schema_version": 1,
            "kind": "paper400-native-lrat-sealed-elf-runtime-v2",
            "system_preload_absent": True,
            "loader": loader_record,
            "solver": solver_record,
            "checker": checker_record,
            "directory": {
                "device": int(directory_info.st_dev),
                "inode": int(directory_info.st_ino),
                "mode": stat.S_IMODE(directory_info.st_mode),
                "uid": int(directory_info.st_uid),
                "link_count": int(directory_info.st_nlink),
                "unlinked_before_fork": True,
            },
            "objects": records,
            "preload_paths": [item["preload_path"] for item in records],
            "role_preload_paths": {
                "solver": [item["preload_path"] for item in records],
                "checker": [records[-1]["preload_path"]],
            },
            "loader_options": [
                "--inhibit-cache", "--library-path", "--preload", "--argv0",
            ],
            "directory_membership_exact": True,
            "dso_payloads_are_sealed_memfds": True,
            "recursive_dt_needed_closure_complete": True,
            "dynamic_redirect_tags_absent": True,
            "every_dependency_bearing_elf_has_df_1_nodeflib": True,
            "loader_has_no_dt_needed": True,
            "all_startup_dependencies_preloaded_by_sealed_memfd": True,
            "startup_base_namespace_dt_needed_path_fallback_excluded": True,
            "same_uid_symlink_directory_is_a_declared_trust_boundary": False,
            "runtime_contains_symlinks": False,
            "runtime_dlopen_path_fallback_excluded": False,
            "root_ptrace_and_host_etc_are_trusted_boundaries": True,
            "production_eligible": False,
            "host_kernel_vdso_trusted_boundary": True,
        })
        return _Runtime(
            parent_fd=parent_fd, directory_fd=directory_fd,
            loader_fd=loader_fd, solver_fd=solver_fd, checker_fd=checker_fd,
            dso_fds=tuple(dso_fds),
            directory_name=name,
            preload_sonames=tuple(item["soname"] for item in records),
            record=record,
        )
    except BaseException:
        for fd in (checker_fd, solver_fd, loader_fd, *dso_fds):
            if fd >= 0:
                with contextlib.suppress(OSError):
                    os.close(fd)
        if directory_fd >= 0:
            with contextlib.suppress(OSError):
                os.close(directory_fd)
        if not directory_unlinked:
            with contextlib.suppress(OSError):
                os.rmdir(name, dir_fd=parent_fd)
        os.close(parent_fd)
        raise


def _verify_runtime(runtime: _Runtime) -> None:
    if Path("/etc/ld.so.preload").exists() or Path("/etc/ld.so.preload").is_symlink():
        raise NativeLratLaunchError("loader preload state changed")
    info = os.fstat(runtime.directory_fd)
    expected = runtime.record["directory"]
    if expected != {
        "device": int(info.st_dev), "inode": int(info.st_ino),
        "mode": stat.S_IMODE(info.st_mode), "uid": int(info.st_uid),
        "link_count": int(info.st_nlink), "unlinked_before_fork": True,
    }:
        raise NativeLratLaunchError("private ELF runtime directory changed")
    by_name = {item["soname"]: item for item in runtime.record["objects"]}
    if (
        not _dead_empty_directory(runtime.directory_fd)
        or set(by_name) != set(runtime.preload_sonames)
        or len(runtime.dso_fds) != len(runtime.preload_sonames)
    ):
        raise NativeLratLaunchError("private ELF runtime membership changed")
    try:
        os.stat(runtime.directory_name, dir_fd=runtime.parent_fd, follow_symlinks=False)
    except FileNotFoundError:
        pass
    else:
        raise NativeLratLaunchError("private ELF runtime pathname reappeared")
    for name, fd in zip(runtime.preload_sonames, runtime.dso_fds, strict=True):
        expected_item = by_name[name]
        if (
            expected_item["preload_path"]
            != f"/proc/self/fd/{expected_item['runtime_fd']}"
            or fcntl.fcntl(fd, F_GET_SEALS) != ALL_MEMFD_SEALS
        ):
            raise NativeLratLaunchError("private sealed-DSO runtime object changed")
    for fd, role in (
        (runtime.loader_fd, "loader"),
        (runtime.solver_fd, "solver"),
        (runtime.checker_fd, "checker"),
    ):
        if fcntl.fcntl(fd, F_GET_SEALS) != ALL_MEMFD_SEALS:
            raise NativeLratLaunchError(f"sealed {role} memfd changed")


def _destroy_runtime(runtime: _Runtime) -> None:
    failure: BaseException | None = None
    try:
        _verify_runtime(runtime)
    except BaseException as exc:  # Preserve cleanup while reporting failure.
        failure = exc
    for fd in (
        runtime.checker_fd, runtime.solver_fd, runtime.loader_fd,
        *runtime.dso_fds,
    ):
        with contextlib.suppress(OSError):
            os.close(fd)
    try:
        os.close(runtime.directory_fd)
        os.fsync(runtime.parent_fd)
    except BaseException as exc:
        if failure is None:
            failure = exc
    finally:
        with contextlib.suppress(OSError):
            os.close(runtime.parent_fd)
    if failure is not None:
        raise NativeLratLaunchError("private ELF runtime validation/cleanup failed") from failure


def _proc_identity(
    pid: int, *, allow_zombie: bool = False,
) -> tuple[int, str, int, int]:
    try:
        payload = Path(f"/proc/{pid}/stat").read_text(encoding="ascii")
        close = payload.rfind(")")
        fields = payload[close + 2:].split() if close > 0 else []
        if len(fields) <= 19 or (fields[0] == "Z" and not allow_zombie):
            raise ValueError("dead or malformed process")
        state = fields[0]
        process_group = int(fields[2])
        session = int(fields[3])
        ticks = int(fields[19])
    except (OSError, UnicodeDecodeError, ValueError) as exc:
        raise NativeLratLaunchError(f"cannot observe live process identity {pid}") from exc
    if ticks <= 0 or process_group <= 0 or session <= 0:
        raise NativeLratLaunchError("invalid process start tick")
    return ticks, state, process_group, session


def _proc_start_ticks(pid: int, *, allow_zombie: bool = False) -> int:
    return _proc_identity(pid, allow_zombie=allow_zombie)[0]


def _assert_live_identity(pid: int, start_ticks: int, cpu: int) -> None:
    ticks, _state, process_group, session = _proc_identity(pid)
    if ticks != start_ticks:
        raise NativeLratLaunchError("process identity changed")
    if process_group != pid or session != pid:
        raise NativeLratLaunchError("process lost its exclusive session/process group")
    try:
        affinity = sorted(os.sched_getaffinity(pid))
    except OSError as exc:
        raise NativeLratLaunchError("cannot replay process CPU affinity") from exc
    if affinity != [cpu]:
        raise NativeLratLaunchError("process does not have its exact singleton CPU")


def _set_pdeathsig(expected_parent: int) -> None:
    ctypes.set_errno(0)
    if _PRCTL(PR_SET_PDEATHSIG, signal.SIGKILL, 0, 0, 0) != 0:
        raise OSError(ctypes.get_errno() or errno.EPERM, "PR_SET_PDEATHSIG failed")
    if os.getppid() != expected_parent:
        os.kill(os.getpid(), signal.SIGKILL)


def _close_all_except(keep: set[int]) -> None:
    try:
        descriptors = [int(name) for name in os.listdir("/proc/self/fd") if name.isdecimal()]
    except OSError:
        soft, _hard = resource.getrlimit(resource.RLIMIT_NOFILE)
        descriptors = list(range(3, min(int(soft), 65_536)))
    for fd in descriptors:
        if fd > 2 and fd not in keep:
            with contextlib.suppress(OSError):
                os.close(fd)


def _transport_argv(logical_argv: Sequence[str], *, tool: str, sealed: bool) -> list[str]:
    if not sealed:
        return list(logical_argv)
    if tool not in {"solver", "checker"}:
        raise NativeLratLaunchError("unknown sealed tool role")
    preload_indices = range(len(ELF_OBJECT_SPECS) - 1) if tool == "solver" else (3,)
    preload = ":".join(
        f"/proc/self/fd/{RUNTIME_DSO_FD_BASE + index}"
        for index in preload_indices
    )
    return [
        f"/proc/self/fd/{RUNTIME_LOADER_FD}",
        "--inhibit-cache", "--library-path", f"/proc/self/fd/{RUNTIME_DIRECTORY_FD}",
        "--preload", preload,
        "--argv0", logical_argv[0], f"/proc/self/fd/{RUNTIME_TOOL_FD}",
        *logical_argv[1:],
    ]


def _child_exec(
    *, parent_pid: int, cpu: int, cnf_fd: int, proof_fd: int,
    ready_write: int, gate_read: int, stdout_write: int, stderr_write: int,
    logical_argv: Sequence[str], runtime: _Runtime | None, tool: str,
    proof_cap: int,
) -> None:
    error_fd = ready_write
    try:
        os.setsid()
        _set_pdeathsig(parent_pid)
        os.sched_setaffinity(0, {cpu})
        resource.setrlimit(resource.RLIMIT_CORE, (0, 0))
        resource.setrlimit(resource.RLIMIT_FSIZE, (proof_cap, proof_cap))
        os.umask(0o077)
        devnull = os.open("/dev/null", os.O_RDONLY | os.O_CLOEXEC)
        cnf_target = SOLVER_CNF_FD if tool == "solver" else CHECKER_CNF_FD
        proof_target = SOLVER_PROOF_FD if tool == "solver" else CHECKER_PROOF_FD
        sources = {
            0: devnull, 1: stdout_write, 2: stderr_write,
            cnf_target: cnf_fd, proof_target: proof_fd,
            READY_FD: ready_write, GATE_FD: gate_read,
        }
        if runtime is not None:
            sources.update({
                RUNTIME_LOADER_FD: runtime.loader_fd,
                RUNTIME_TOOL_FD: (
                    runtime.solver_fd if tool == "solver" else runtime.checker_fd
                ),
                RUNTIME_DIRECTORY_FD: runtime.directory_fd,
            })
            sources.update({
                RUNTIME_DSO_FD_BASE + index: descriptor
                for index, descriptor in enumerate(runtime.dso_fds)
            })
        # With a 224-leaf all-start barrier, ordinary parent descriptors can
        # occupy any of the fixed 201..222 protocol slots.  A direct sequence
        # of dup2 calls could therefore destroy a source needed by a later
        # mapping.  Clone every source above the protocol range first; only
        # those collision-free clones are ever mapped to fixed targets.
        clone_floor = max(sources) + 1
        clones = {
            target: fcntl.fcntl(source, fcntl.F_DUPFD_CLOEXEC, clone_floor)
            for target, source in sources.items()
        }
        error_fd = clones[READY_FD]
        for target, source in clones.items():
            os.dup2(source, target)
        error_fd = READY_FD
        keep = {
            0, 1, 2, READY_FD, GATE_FD,
            cnf_target, proof_target,
        }
        if runtime is not None:
            keep.update({RUNTIME_LOADER_FD, RUNTIME_TOOL_FD, RUNTIME_DIRECTORY_FD})
            keep.update(
                RUNTIME_DSO_FD_BASE + index
                for index in range(len(runtime.dso_fds))
            )
        _close_all_except(keep)
        for fd in keep:
            if fd not in {READY_FD, GATE_FD}:
                os.set_inheritable(fd, True)
        os.set_inheritable(READY_FD, False)
        os.set_inheritable(GATE_FD, False)
        os.write(READY_FD, b"R\n")
        gate = os.read(GATE_FD, 1)
        if gate != b"G":
            os._exit(125)
        transport = _transport_argv(logical_argv, tool=tool, sealed=runtime is not None)
        executable = transport[0] if runtime is not None else logical_argv[0]
        os.execve(executable, transport, _clean_environment())
    except BaseException as exc:
        message = ("E:" + type(exc).__name__ + ":" + str(exc))[:1900].encode(
            "utf-8", "replace",
        ) + b"\n"
        with contextlib.suppress(OSError):
            os.write(error_fd, message)
        os._exit(127)


def _reap_unregistered_child(pid: int, descriptors: Sequence[int]) -> None:
    """Close a failed post-fork transport and reap its direct child.

    Until ``_Child`` has been constructed and appended to the caller's owner
    registry, the numeric PID is protected from reuse by the unreaped direct
    child relationship. Closing every parent endpoint makes the pre-exec gate
    fail closed; SIGKILL is a bounded last resort.
    """

    for fd in descriptors:
        with contextlib.suppress(OSError):
            os.close(fd)
    deadline = time.monotonic() + TERM_GRACE_SECONDS
    while time.monotonic() < deadline:
        try:
            waited, _status = os.waitpid(pid, os.WNOHANG)
        except ChildProcessError:
            return
        if waited == pid:
            return
        time.sleep(0.02)
    try:
        os.kill(pid, signal.SIGKILL)
    except ProcessLookupError:
        pass
    except PermissionError as exc:
        raise NativeLratLaunchError(
            "cannot terminate unregistered direct child"
        ) from exc
    try:
        waited, _status = os.waitpid(pid, 0)
    except ChildProcessError:
        return
    if waited != pid:
        raise NativeLratLaunchError("reaped an unexpected unregistered child")


def _fork_gated_child(
    *, leaf_id: str, role: str, cpu: int, cnf_fd: int, proof_fd: int,
    logical_argv: Sequence[str], runtime: _Runtime | None, proof_cap: int,
    owner_registry: list[_Child],
) -> _Child:
    ready_r, ready_w = os.pipe2(os.O_CLOEXEC)
    gate_r, gate_w = os.pipe2(os.O_CLOEXEC)
    out_r, out_w = os.pipe2(os.O_CLOEXEC)
    err_r, err_w = os.pipe2(os.O_CLOEXEC)
    parent = os.getpid()
    try:
        pid = os.fork()
    except BaseException:
        for fd in (ready_r, ready_w, gate_r, gate_w, out_r, out_w, err_r, err_w):
            os.close(fd)
        raise
    if pid == 0:
        for fd in (ready_r, gate_w, out_r, err_r):
            os.close(fd)
        _child_exec(
            parent_pid=parent, cpu=cpu, cnf_fd=cnf_fd, proof_fd=proof_fd,
            ready_write=ready_w, gate_read=gate_r,
            stdout_write=out_w, stderr_write=err_w,
            logical_argv=logical_argv, runtime=runtime, tool=role,
            proof_cap=proof_cap,
        )
        os._exit(127)
    for fd in (ready_w, gate_r, out_w, err_w):
        with contextlib.suppress(OSError):
            os.close(fd)
    child: _Child | None = None
    registered = False
    try:
        child = _Child(
            leaf_id=leaf_id, role=role, cpu=cpu, pid=pid,
            ready_fd=ready_r, gate_fd=gate_w,
            stdout_fd=out_r, stderr_fd=err_r,
            logical_argv=list(logical_argv),
            transport_argv=_transport_argv(
                logical_argv, tool=role, sealed=runtime is not None,
            ),
        )
        owner_registry.append(child)
        registered = True
        os.set_blocking(ready_r, False)
        os.set_blocking(out_r, False)
        os.set_blocking(err_r, False)
        return child
    except BaseException:
        if registered and child is not None:
            _terminate_owned([child])
        else:
            _reap_unregistered_child(pid, (gate_w, ready_r, out_r, err_r))
        raise


def _wait_gated_ready(children: Sequence[_Child], timeout_seconds: int) -> None:
    selector = selectors.DefaultSelector()
    buffers = {child.pid: bytearray() for child in children}
    pending = {child.pid: child for child in children}
    deadline = time.monotonic() + min(timeout_seconds, READY_TIMEOUT_MAX_SECONDS)
    try:
        for child in children:
            selector.register(child.ready_fd, selectors.EVENT_READ, child)
        while pending:
            remaining = deadline - time.monotonic()
            if remaining <= 0:
                raise NativeLratLaunchError("pre-exec gate readiness timed out")
            for key, _mask in selector.select(min(remaining, 0.1)):
                child = key.data
                try:
                    chunk = os.read(child.ready_fd, 2048)
                except BlockingIOError:
                    continue
                if chunk:
                    buffers[child.pid].extend(chunk)
                    if len(buffers[child.pid]) > 2048:
                        raise NativeLratLaunchError("pre-exec child error exceeded cap")
                    if buffers[child.pid].startswith(b"R\n"):
                        selector.unregister(child.ready_fd)
                        os.close(child.ready_fd)
                        child.ready_fd = -1
                        child.proc_start_ticks = _proc_start_ticks(child.pid)
                        _assert_live_identity(child.pid, child.proc_start_ticks, child.cpu)
                        pending.pop(child.pid)
                    elif b"\n" in buffers[child.pid]:
                        raise NativeLratLaunchError(
                            "pre-exec child failed: "
                            + bytes(buffers[child.pid]).decode("utf-8", "replace").strip()
                        )
                else:
                    raise NativeLratLaunchError("pre-exec child exited before readiness")
            for child in list(pending.values()):
                waited, status_value = os.waitpid(child.pid, os.WNOHANG)
                if waited:
                    child.exit_code = os.waitstatus_to_exitcode(status_value)
                    child.reaped = True
                    raise NativeLratLaunchError("pre-exec child terminated before barrier")
    finally:
        selector.close()


def _release_gates(children: Sequence[_Child]) -> None:
    for child in children:
        if child.proc_start_ticks is None:
            raise NativeLratLaunchError("cannot release an unobserved child")
        _assert_live_identity(child.pid, child.proc_start_ticks, child.cpu)
    for child in children:
        try:
            if os.write(child.gate_fd, b"G") != 1:
                raise NativeLratLaunchError("short pre-exec gate release")
        finally:
            os.close(child.gate_fd)
            child.gate_fd = -1


def _owned_identity_live(child: _Child) -> bool:
    if child.reaped:
        return False
    if child.proc_start_ticks is None:
        try:
            return _proc_start_ticks(child.pid) > 0
        except NativeLratLaunchError:
            return False
    try:
        ticks, _state, process_group, session = _proc_identity(
            child.pid, allow_zombie=True,
        )
        return (
            ticks == child.proc_start_ticks
            and process_group == child.pid
            and session == child.pid
        )
    except NativeLratLaunchError:
        return False


def _observe_child_exit(child: _Child) -> bool:
    if child.reaped or child.exit_code is not None:
        return True
    try:
        result = os.waitid(
            os.P_PID, child.pid, os.WEXITED | os.WNOHANG | os.WNOWAIT,
        )
    except ChildProcessError:
        # An unexpected external reaper destroys the numeric-PGID ownership
        # gate.  Mark the child unavailable and, crucially, never signal that
        # bare number.
        child.reaped = True
        child.exit_code = 127
        return True
    if result is None:
        return False
    if result.si_code == os.CLD_EXITED:
        child.exit_code = int(result.si_status)
    elif result.si_code in {os.CLD_KILLED, os.CLD_DUMPED}:
        child.exit_code = -int(result.si_status)
    else:
        raise NativeLratLaunchError("unexpected direct-child wait status")
    return True


def _reap_observed_child(child: _Child) -> None:
    if child.reaped:
        return
    if child.exit_code is None and not _observe_child_exit(child):
        raise NativeLratLaunchError("cannot reap a running direct child")
    try:
        waited, status_value = os.waitpid(child.pid, 0)
    except ChildProcessError:
        child.reaped = True
        if child.exit_code is None:
            child.exit_code = 127
        return
    if waited != child.pid:
        raise NativeLratLaunchError("reaped an unexpected direct child")
    actual = os.waitstatus_to_exitcode(status_value)
    if child.exit_code is not None and actual != child.exit_code:
        raise NativeLratLaunchError("waitid/waitpid exit status mismatch")
    child.exit_code = actual
    child.reaped = True


def _owned_group_descendants(child: _Child) -> list[tuple[int, int]]:
    if child.reaped or child.proc_start_ticks is None:
        raise NativeLratLaunchError("process-group ownership gate is unavailable")
    ticks, _state, process_group, session = _proc_identity(
        child.pid, allow_zombie=True,
    )
    if (
        ticks != child.proc_start_ticks
        or process_group != child.pid
        or session != child.pid
    ):
        raise NativeLratLaunchError("process-group leader identity changed")
    members: list[tuple[int, int]] = []
    try:
        entries = list(os.scandir("/proc"))
    except OSError as exc:
        raise NativeLratLaunchError("cannot enumerate owned process group") from exc
    for entry in entries:
        if not entry.name.isdecimal():
            continue
        pid = int(entry.name)
        if pid == child.pid:
            continue
        try:
            member_ticks, _member_state, member_group, member_session = _proc_identity(
                pid, allow_zombie=True,
            )
        except NativeLratLaunchError:
            continue
        if member_group == child.pid and member_session == child.pid:
            members.append((pid, member_ticks))
    return sorted(members)


def _signal_owned_group(child: _Child, sig: int) -> bool:
    # Keeping the direct leader unreaped makes its PID/PGID unavailable for
    # reuse.  The start-tick + session replay below therefore remains a valid
    # ownership gate across the subsequent killpg syscall.
    if not _owned_identity_live(child) or child.proc_start_ticks is None:
        return False
    try:
        os.killpg(child.pid, sig)
    except ProcessLookupError:
        return False
    except PermissionError as exc:
        raise NativeLratLaunchError("cannot signal owned process group") from exc
    return True


def _finish_terminated_child(child: _Child) -> bool:
    if child.reaped:
        return True
    if not _observe_child_exit(child):
        return False
    if child.proc_start_ticks is not None and _owned_group_descendants(child):
        return False
    _reap_observed_child(child)
    return True


def _terminate_owned(children: Sequence[_Child]) -> None:
    for child in children:
        if child.gate_fd >= 0:
            with contextlib.suppress(OSError):
                os.close(child.gate_fd)
            child.gate_fd = -1
    for child in children:
        # A readiness receipt is written only after setsid().  Never signal a
        # numeric PGID after its direct leader has been reaped.
        if child.proc_start_ticks is not None and not child.reaped:
            _signal_owned_group(child, signal.SIGTERM)
        elif _owned_identity_live(child):
            with contextlib.suppress(ProcessLookupError, PermissionError):
                os.kill(child.pid, signal.SIGTERM)
    deadline = time.monotonic() + TERM_GRACE_SECONDS
    while time.monotonic() < deadline:
        finished = [_finish_terminated_child(child) for child in children]
        if all(finished):
            break
        time.sleep(0.02)
    for child in children:
        if child.reaped:
            continue
        if child.proc_start_ticks is not None:
            _signal_owned_group(child, signal.SIGKILL)
        elif _owned_identity_live(child):
            with contextlib.suppress(ProcessLookupError, PermissionError):
                os.kill(child.pid, signal.SIGKILL)
    kill_deadline = time.monotonic() + TERM_GRACE_SECONDS
    while time.monotonic() < kill_deadline:
        finished = [_finish_terminated_child(child) for child in children]
        if all(finished):
            break
        time.sleep(0.02)
    for child in children:
        for name in ("ready_fd", "stdout_fd", "stderr_fd"):
            fd = getattr(child, name)
            if fd >= 0:
                with contextlib.suppress(OSError):
                    os.close(fd)
                setattr(child, name, -1)
    unreaped = [child.pid for child in children if not child.reaped]
    if unreaped:
        raise NativeLratLaunchError(
            "owned direct children were not all reaped after SIGKILL: "
            + ",".join(str(pid) for pid in unreaped)
        )


def _monitor_children(
    children: Sequence[_Child], *, timeout_seconds: int,
    stdout_cap: int, stderr_cap: int,
    lease_recheck_seconds: float,
    replay_authority: Callable[[], dict[str, Any]],
) -> tuple[list[dict[str, Any]], list[dict[str, Any]]]:
    selector = selectors.DefaultSelector()
    streams: dict[tuple[int, str], bytearray] = {}
    eof: set[tuple[int, str]] = set()
    deadline = time.monotonic() + timeout_seconds
    next_recheck = time.monotonic() + lease_recheck_seconds
    snapshots: list[dict[str, Any]] = []
    try:
        for child in children:
            for role, fd in (("stdout", child.stdout_fd), ("stderr", child.stderr_fd)):
                streams[(child.pid, role)] = bytearray()
                selector.register(fd, selectors.EVENT_READ, (child, role))
        while True:
            now = time.monotonic()
            if now >= deadline:
                raise NativeLratLaunchError("child stage timed out")
            if now >= next_recheck:
                snapshots.append(replay_authority())
                next_recheck = now + lease_recheck_seconds
            for key, _mask in selector.select(min(0.1, deadline - now)):
                child, role = key.data
                try:
                    chunk = os.read(key.fd, READ_CHUNK_BYTES)
                except BlockingIOError:
                    continue
                stream_key = (child.pid, role)
                if chunk:
                    streams[stream_key].extend(chunk)
                    cap = stdout_cap if role == "stdout" else stderr_cap
                    if len(streams[stream_key]) > cap:
                        raise NativeLratLaunchError(f"child {role} exceeded cap")
                else:
                    selector.unregister(key.fd)
                    os.close(key.fd)
                    if role == "stdout":
                        child.stdout_fd = -1
                    else:
                        child.stderr_fd = -1
                    eof.add(stream_key)
            for child in children:
                _observe_child_exit(child)
            all_exited = all(child.exit_code is not None for child in children)
            all_eof = len(eof) == 2 * len(children)
            if all_exited and all_eof:
                for child in children:
                    descendants = _owned_group_descendants(child)
                    if descendants:
                        raise NativeLratLaunchError(
                            "child process group retained owned descendants"
                        )
                for child in children:
                    _reap_observed_child(child)
                break
        snapshots.append(replay_authority())
        results: list[dict[str, Any]] = []
        for child in children:
            child.stdout = bytes(streams[(child.pid, "stdout")])
            child.stderr = bytes(streams[(child.pid, "stderr")])
            if not child.reaped:
                raise NativeLratLaunchError("direct child was not safely reaped")
            results.append(_seal({
                "schema_version": 1,
                "kind": GATE + "-bounded-process-result",
                "leaf_id": child.leaf_id, "role": child.role,
                "pid": child.pid, "proc_start_ticks": child.proc_start_ticks,
                "cpu": child.cpu, "generation": 0,
                "logical_argv": child.logical_argv,
                "logical_argv_sha256": _digest(child.logical_argv),
                "transport_argv": child.transport_argv,
                "transport_argv_sha256": _digest(child.transport_argv),
                "stdin": "DEVNULL",
                "exit_code": child.exit_code,
                "stdout": {"bytes": len(child.stdout),
                           "sha256": hashlib.sha256(child.stdout).hexdigest()},
                "stderr": {"bytes": len(child.stderr),
                           "sha256": hashlib.sha256(child.stderr).hexdigest()},
                "direct_child_reaped": True,
                "process_group_empty": True,
            }))
        return results, snapshots
    except BaseException:
        _terminate_owned(children)
        raise
    finally:
        selector.close()


def build_recursive_binding(
    plan: Mapping[str, Any], *, queue_path: Path, item_id: str,
    pins: native.ToolchainPins = native.DEFAULT_PINS,
    planner_path: Path = Path(native.__file__).resolve(),
) -> dict[str, Any]:
    """Read-only bind one claimed recursive item to one native-LRAT leaf."""

    verified = native.verify_plan(plan, pins=pins, planner_path=planner_path)
    queue_target = _normalized_absolute(queue_path, "recursive queue", must_exist=True)
    queue = recursive.load_split_queue(queue_target)
    items = [item for item in queue["items"] if item.get("item_id") == item_id]
    if len(items) != 1:
        raise NativeLratLaunchError("recursive queue item is missing or duplicated")
    item = items[0]
    participants = [
        participant for participant in verified["participants"]
        if participant["leaf_id"] == item.get("leaf_id")
    ]
    if len(participants) != 1:
        raise NativeLratLaunchError("recursive item is not a plan participant")
    participant = participants[0]
    claim = item.get("claim")
    if (
        item.get("state") != "CLAIMED" or type(claim) is not dict
        or item.get("cpu_ids") != [participant["cpu_lease"]["cpu"]]
        or item.get("cpu_slots") != 1
        or item.get("child_dimacs_sha256") != participant["cnf"]["sha256"]
        or item.get("child_dimacs_bytes") != participant["cnf"]["bytes"]
        or item.get("child_num_variables") != participant["cnf"]["dimacs_variables"]
        or item.get("child_num_clauses") != participant["cnf"]["dimacs_clauses"]
    ):
        raise NativeLratLaunchError("recursive item/claim/CNF/CPU binding mismatch")
    token = claim.get("token")
    if type(token) is not str or re.fullmatch(r"[0-9a-f]{64}", token) is None:
        raise NativeLratLaunchError("recursive claim token is malformed")
    return _seal({
        "schema_version": 1, "kind": RECURSIVE_BINDING_KIND,
        "plan_sha256": verified["plan_sha256"],
        "leaf_id": participant["leaf_id"],
        "queue_path": str(queue_target), "queue_id": queue["queue_id"],
        "observed_queue_sha256": queue["queue_sha256"],
        "item_id": item["item_id"], "observed_item_sha256": item["item_sha256"],
        "parent_id": item["parent_id"],
        "parent_manifest_sha256": item["parent_manifest_sha256"],
        "split_manifest_sha256": item["split_manifest_sha256"],
        "leaf_sha256": item["leaf_sha256"],
        "child_cnf_sha256": item["child_cnf_sha256"],
        "child_dimacs_sha256": item["child_dimacs_sha256"],
        "child_num_variables": item["child_num_variables"],
        "child_num_clauses": item["child_num_clauses"],
        "child_dimacs_bytes": item["child_dimacs_bytes"],
        "cpu": participant["cpu_lease"]["cpu"],
        "claim_worker_id": claim["worker_id"],
        "claim_token_sha256": hashlib.sha256(token.encode("ascii")).hexdigest(),
        "claim_lease_expires_at": claim["lease_expires_at"],
        "queue_mutation": False, "scientific_claim": False,
    }, "binding_sha256")


def _replay_recursive_binding(
    plan: Mapping[str, Any], binding: Mapping[str, Any],
) -> dict[str, Any]:
    if not _selfhash(binding, "binding_sha256") or binding.get("kind") != RECURSIVE_BINDING_KIND:
        raise NativeLratLaunchError("recursive binding seal/kind is invalid")
    if binding.get("plan_sha256") != plan["plan_sha256"]:
        raise NativeLratLaunchError("recursive binding belongs to another plan")
    queue = recursive.load_split_queue(Path(binding["queue_path"]))
    items = [item for item in queue["items"] if item.get("item_id") == binding.get("item_id")]
    if len(items) != 1:
        raise NativeLratLaunchError("recursive binding item disappeared")
    item = items[0]
    claim = item.get("claim")
    immutable_pairs = (
        ("leaf_id", "leaf_id"), ("parent_id", "parent_id"),
        ("parent_manifest_sha256", "parent_manifest_sha256"),
        ("split_manifest_sha256", "split_manifest_sha256"),
        ("leaf_sha256", "leaf_sha256"),
        ("child_cnf_sha256", "child_cnf_sha256"),
        ("child_dimacs_sha256", "child_dimacs_sha256"),
        ("child_num_variables", "child_num_variables"),
        ("child_num_clauses", "child_num_clauses"),
        ("child_dimacs_bytes", "child_dimacs_bytes"),
    )
    if (
        queue.get("queue_id") != binding.get("queue_id")
        or any(item.get(item_key) != binding.get(bind_key)
               for item_key, bind_key in immutable_pairs)
        or item.get("state") != "CLAIMED"
        or type(claim) is not dict
        or item.get("cpu_ids") != [binding.get("cpu")]
        or claim.get("worker_id") != binding.get("claim_worker_id")
        or hashlib.sha256(str(claim.get("token", "")).encode("ascii")).hexdigest()
        != binding.get("claim_token_sha256")
        or time.time() >= float(claim.get("lease_expires_at", 0))
    ):
        raise NativeLratLaunchError("recursive queue claim/binding is no longer live")
    return _seal({
        "schema_version": 1, "kind": GATE + "-recursive-binding-replay",
        "binding_sha256": binding["binding_sha256"],
        "queue_sha256": queue["queue_sha256"],
        "item_sha256": item["item_sha256"],
        "claim_lease_expires_at": claim["lease_expires_at"],
        "claim_live": True, "queue_mutation": False,
    })


def _create_proof_anchor(participant: Mapping[str, Any], cap: int) -> int:
    path = Path(participant["proof_output"]["path"])
    flags = os.O_WRONLY | os.O_CREAT | os.O_EXCL | os.O_CLOEXEC
    if hasattr(os, "O_NOFOLLOW"):
        flags |= os.O_NOFOLLOW
    try:
        fd = os.open(path, flags, 0o600)
    except FileExistsError as exc:
        raise NativeLratLaunchError("proof output appeared before O_EXCL creation") from exc
    info = os.fstat(fd)
    if (
        not stat.S_ISREG(info.st_mode) or info.st_uid != os.geteuid()
        or info.st_nlink != 1 or info.st_size != 0
        or stat.S_IMODE(info.st_mode) != 0o600
    ):
        os.close(fd)
        raise NativeLratLaunchError("new proof anchor metadata is unsafe")
    return fd


def _open_plan_cnf(participant: Mapping[str, Any], *, full_hash: bool = True) -> int:
    path = Path(participant["cnf"]["path"])
    fd = _open_regular(path, "planned leaf CNF", cap=native.MAX_CNF_BYTES, executable=False)
    try:
        expected = participant["cnf"]
        info = os.fstat(fd)
        if (
            int(info.st_size) != expected["bytes"]
            or int(info.st_dev) != expected["device"]
            or int(info.st_ino) != expected["inode"]
            or stat.S_IMODE(info.st_mode) != expected["mode"]
            or int(info.st_uid) != expected["uid"]
            or int(info.st_nlink) != expected["links"]
            or int(info.st_mtime_ns) != expected["mtime_ns"]
            or int(info.st_ctime_ns) != expected["ctime_ns"]
        ):
            raise NativeLratLaunchError("planned CNF binding changed")
        if full_hash:
            digest, size, hashed_info = _stable_hash_fd(fd, cap=native.MAX_CNF_BYTES)
            if (
                digest != expected["sha256"] or size != expected["bytes"]
                or (hashed_info.st_dev, hashed_info.st_ino) != (info.st_dev, info.st_ino)
            ):
                raise NativeLratLaunchError("planned CNF content hash changed")
        return fd
    except BaseException:
        os.close(fd)
        raise


def _start_observation(
    plan: Mapping[str, Any], participant: Mapping[str, Any], child: _Child,
    proof_fd: int,
) -> dict[str, Any]:
    if child.proc_start_ticks is None:
        raise NativeLratLaunchError("child process identity was not observed")
    proof_path = Path(participant["proof_output"]["path"])
    binding, _prefix = native._bind_file(
        proof_path, role="exclusive-native-lrat-output", cap=0, executable=False,
    )
    _assert_record_fd(proof_fd, proof_path, binding)
    lease = participant["cpu_lease"]
    return {
        "schema_version": 1, "kind": native.PREEXEC_OBSERVATION_KIND,
        "plan_sha256": plan["plan_sha256"], "leaf_id": participant["leaf_id"],
        "generation": 0, "pid": child.pid,
        "proc_start_ticks": child.proc_start_ticks, "cpu": lease["cpu"],
        "lease_id": lease["lease_id"],
        "lease_token_sha256": lease["lease_token_sha256"],
        "planned_argv_sha256": participant["solver_invocation"]["argv_sha256"],
        "preexec_gate_held": True, "proof_output_binding": binding,
        "proof_fd": SOLVER_PROOF_FD, "proof_fd_o_excl_anchor_held": True,
    }


def _checker_terminal_success(stdout: bytes, stderr: bytes, returncode: int) -> bool:
    try:
        lines = stdout.decode("ascii").splitlines()
    except UnicodeDecodeError:
        return False
    terminal_words = ("VERIFIED", "INVALID", "FAILED", "ERROR")
    terminal = [
        line for line in lines
        if line.startswith("c ") and any(word in line.upper() for word in terminal_words)
    ]
    return returncode == 0 and stderr == b"" and terminal == ["c VERIFIED"]


def _run_checker_once(
    *, plan: Mapping[str, Any], participant: Mapping[str, Any],
    proof_record: Mapping[str, Any], config: ExecutionConfig,
    runtime: _Runtime | None,
    replay_authority: Callable[[Sequence[_Child]], dict[str, Any]],
    role: str,
) -> tuple[dict[str, Any], list[dict[str, Any]], dict[str, Any], dict[str, Any]]:
    # run_pilot keeps the initially hash-verified CNF descriptor anchored for
    # the entire transaction.  Each checker independently reopens the same
    # pathname/inode and checks all mutation-sensitive metadata; hashing it
    # yet again would add two redundant full CNF scans.
    cnf_fd = _open_plan_cnf(participant, full_hash=False)
    proof_path = Path(participant["proof_output"]["path"])
    proof_fd = _open_regular(proof_path, "sealed native LRAT proof", cap=config.proof_cap_bytes,
                             executable=False)
    try:
        _assert_record_fd(proof_fd, proof_path, proof_record)
        contract = participant["certification_handoff_contract"][
            "initial_lrat_check" if role == "initial-lrat-check" else "fresh_lrat_replay"
        ]
        logical = list(contract["argv"])
        checker_children: list[_Child] = []
        child = _fork_gated_child(
            leaf_id=participant["leaf_id"], role="checker",
            cpu=participant["cpu_lease"]["cpu"], cnf_fd=cnf_fd,
            proof_fd=proof_fd, logical_argv=logical, runtime=runtime,
            proof_cap=config.proof_cap_bytes, owner_registry=checker_children,
        )
        try:
            _wait_gated_ready([child], min(config.checker_timeout_seconds, 60))
            checker_replay = lambda: replay_authority([child])
            before = checker_replay()
            _assert_live_identity(child.pid, child.proc_start_ticks or 0, child.cpu)
            _release_gates([child])
            process_records, stage_snapshots = _monitor_children(
                [child], timeout_seconds=config.checker_timeout_seconds,
                stdout_cap=config.stdout_cap_bytes,
                stderr_cap=config.stderr_cap_bytes,
                lease_recheck_seconds=config.lease_recheck_seconds,
                replay_authority=checker_replay,
            )
        except BaseException:
            _terminate_owned([child])
            raise
        process = process_records[0]
        _assert_record_fd(proof_fd, proof_path, proof_record)
        success = _checker_terminal_success(child.stdout, child.stderr, child.exit_code or 0)
        semantic_hash = hashlib.sha256(b"c VERIFIED\n").hexdigest()
        if semantic_hash != contract["expected_semantic_stdout_sha256"]:
            raise NativeLratLaunchError("checker semantic marker policy changed")
        check = _seal({
            "schema_version": 1, "kind": CHECK_RESULT_KIND,
            "role": role, "leaf_id": participant["leaf_id"],
            "generation": 0, "process": process,
            "proof": dict(proof_record),
            "logical_argv_matches_plan": process["logical_argv_sha256"] == contract["argv_sha256"],
            "semantic_marker": "c VERIFIED",
            "semantic_marker_sha256": semantic_hash,
            "stderr_empty": child.stderr == b"", "verified": success,
            "terminal_publication": False,
        })
        stdout_record = _publish_bytes(
            proof_path.parent / f"{role}.stdout", child.stdout,
        )
        stderr_record = _publish_bytes(
            proof_path.parent / f"{role}.stderr", child.stderr,
        )
        if not success:
            raise NativeLratLaunchError(f"{role} did not return one exact c VERIFIED status")
        return check, [before, *stage_snapshots], stdout_record, stderr_record
    finally:
        os.close(proof_fd)
        os.close(cnf_fd)


def _normalise_recursive_bindings(
    plan: Mapping[str, Any], bindings: Sequence[Mapping[str, Any]],
) -> dict[str, dict[str, Any]]:
    result: dict[str, dict[str, Any]] = {}
    for binding in bindings:
        if (
            not _selfhash(binding, "binding_sha256")
            or binding.get("kind") != RECURSIVE_BINDING_KIND
            or binding.get("plan_sha256") != plan["plan_sha256"]
            or type(binding.get("leaf_id")) is not str
            or binding["leaf_id"] in result
        ):
            raise NativeLratLaunchError("recursive binding set is malformed or duplicated")
        result[binding["leaf_id"]] = dict(binding)
    plan_leaves = {item["leaf_id"] for item in plan["participants"]}
    if not set(result).issubset(plan_leaves):
        raise NativeLratLaunchError("recursive binding names a nonparticipant")
    for binding in result.values():
        _replay_recursive_binding(plan, binding)
    return result


def _proof_artifact_state(participant: Mapping[str, Any]) -> dict[str, Any]:
    path = Path(participant["proof_output"]["path"])
    try:
        info = path.lstat()
    except FileNotFoundError:
        return {"path": str(path), "exists": False}
    except OSError as exc:
        return {
            "path": str(path), "exists": None,
            "observation_error": f"{type(exc).__name__}:{exc}",
        }
    return {
        "path": str(path), "exists": True,
        "regular": stat.S_ISREG(info.st_mode),
        "symlink": stat.S_ISLNK(info.st_mode),
        "device": int(info.st_dev), "inode": int(info.st_ino),
        "bytes": int(info.st_size), "mode": stat.S_IMODE(info.st_mode),
        "uid": int(info.st_uid), "links": int(info.st_nlink),
        "mtime_ns": int(info.st_mtime_ns), "ctime_ns": int(info.st_ctime_ns),
    }


def audit_pilot(
    plan: Mapping[str, Any], config: ExecutionConfig, *,
    pins: native.ToolchainPins = native.DEFAULT_PINS,
    planner_path: Path = Path(native.__file__).resolve(),
    recursive_bindings: Sequence[Mapping[str, Any]] = (),
    _test_nonce: object | None = None,
) -> dict[str, Any]:
    test_mode = _test_nonce is _TEST_ONLY_NONCE
    checked_config = _validate_config(config, test_mode=test_mode)
    verified = _validate_plan_for_execution(
        plan, checked_config, pins=pins, planner_path=planner_path,
    )
    bindings = _normalise_recursive_bindings(verified, recursive_bindings)
    authority, resource_baseline = _guarded_catalog_snapshot(
        checked_config, verified["participants"],
    )
    source = _source_binding(Path(__file__).resolve())
    return _seal({
        "schema_version": 1, "kind": AUDIT_KIND, "gate": GATE,
        "observed_at": time.time(), "go": True,
        "authority": "NON_PRODUCTION_PILOT_ONLY",
        "production_eligible": False,
        "plan_sha256": verified["plan_sha256"],
        "participant_count": len(verified["participants"]),
        "cpus": sorted(item["cpu_lease"]["cpu"] for item in verified["participants"]),
        "lease_authority": authority,
        "resource_baseline_sha256": resource_baseline["record_sha256"],
        "launcher_source": source,
        "recursive_binding_leaf_ids": sorted(bindings),
        "sealed_elf_runtime_required": checked_config.sealed_elf_runtime,
        "starts_solver": False, "runs_checker": False,
        "queue_mutation": False, "terminal_publication": False,
        "aggregate_publication": False, "cleanup_or_deletion": False,
        "blockers": [
            "independent-production-review-and-signed-execution-manifest",
            "authoritative-recursive-certificate-builder-and-queue-commit-adapter",
            "crash-recovery-policy-for-abandoned-O_EXCL-native-LRAT-output",
            "independent-review-and-supervised-renewal-wiring-for-native-lease-owner",
            "signed-derived-ELF-manifest-and-runtime-dlopen-exclusion-audit",
        ],
    })


def run_pilot(
    plan: Mapping[str, Any], config: ExecutionConfig, *,
    pins: native.ToolchainPins = native.DEFAULT_PINS,
    planner_path: Path = Path(native.__file__).resolve(),
    recursive_bindings: Sequence[Mapping[str, Any]] = (),
    _test_nonce: object | None = None,
) -> dict[str, Any]:
    """Execute and twice-check an isolated group; never publish authority."""

    test_mode = _test_nonce is _TEST_ONLY_NONCE
    checked_config = _validate_config(config, test_mode=test_mode)
    verified = _validate_plan_for_execution(
        plan, checked_config, pins=pins, planner_path=planner_path,
    )
    bindings = _normalise_recursive_bindings(verified, recursive_bindings)
    participants = verified["participants"]
    initial_authority, resource_baseline = _guarded_catalog_snapshot(
        checked_config, participants,
    )
    source = _source_binding(Path(__file__).resolve())
    intent = _seal({
        "schema_version": 1, "kind": GATE + "-intent", "gate": GATE,
        "created_at": time.time(), "authority": "NON_PRODUCTION_PILOT_ONLY",
        "production_eligible": False, "plan": dict(verified),
        "plan_sha256": verified["plan_sha256"], "launcher_source": source,
        "initial_lease_authority": initial_authority,
        "resource_baseline": resource_baseline,
        "recursive_binding_sha256s": {
            key: value["binding_sha256"] for key, value in sorted(bindings.items())
        },
        "generation": 0, "resume": False, "checkpoint_source": None,
        "existing_proof_adoption": False, "queue_mutation": False,
        "terminal_publication": False, "aggregate_publication": False,
        "cleanup_or_deletion": False,
    })
    _publish_json(checked_config.output_root / "00-launch-intent.json", intent)

    runtime: _Runtime | None = None
    cnf_fds: dict[str, int] = {}
    proof_fds: dict[str, int] = {}
    children: list[_Child] = []
    completed = False
    failure: BaseException | None = None
    try:
        if checked_config.sealed_elf_runtime:
            runtime = _stage_runtime(checked_config, pins)
            _verify_runtime(runtime)
            runtime_record = runtime.record
        else:
            runtime_record = _seal({
                "schema_version": 1,
                "kind": "paper400-native-lrat-direct-exec-test-runtime-v1",
                "test_only": True,
                "production_eligible": False,
                "sealed_elf_runtime": False,
            })
        _publish_json(checked_config.output_root / "05-runtime-binding.json", runtime_record)
        for participant in participants:
            leaf_id = participant["leaf_id"]
            cnf_fds[leaf_id] = _open_plan_cnf(participant)
            proof_fds[leaf_id] = _create_proof_anchor(
                participant, checked_config.proof_cap_bytes,
            )
        for participant in participants:
            leaf_id = participant["leaf_id"]
            _fork_gated_child(
                leaf_id=leaf_id, role="solver",
                cpu=participant["cpu_lease"]["cpu"],
                cnf_fd=cnf_fds[leaf_id], proof_fd=proof_fds[leaf_id],
                logical_argv=participant["solver_invocation"]["argv"],
                runtime=runtime, proof_cap=checked_config.proof_cap_bytes,
                owner_registry=children,
            )
        _wait_gated_ready(children, verified["all_start_barrier"]["timeout_seconds"])
        observations = [
            _start_observation(
                verified, participant, child, proof_fds[participant["leaf_id"]],
            )
            for participant, child in zip(participants, children, strict=True)
        ]
        receipts = [
            native.build_start_receipt(
                verified, observation, pins=pins, planner_path=planner_path,
            )
            for observation in observations
        ]
        barrier = native.build_barrier_receipt(
            verified, receipts, pins=pins, planner_path=planner_path,
        )
        for participant, receipt in zip(participants, receipts, strict=True):
            _publish_json(
                Path(participant["proof_output"]["path"]).parent / "10-start-receipt.json",
                receipt,
            )
        _publish_json(checked_config.output_root / "20-all-start-barrier.json", barrier)
        before_release, _baseline = _guarded_catalog_snapshot(
            checked_config, participants, children=children,
            baseline=resource_baseline,
        )
        for participant, receipt, child in zip(
            participants, receipts, children, strict=True,
        ):
            _assert_live_identity(child.pid, child.proc_start_ticks or 0, child.cpu)
            _assert_record_fd(
                proof_fds[participant["leaf_id"]],
                Path(participant["proof_output"]["path"]),
                receipt["proof_output_binding"],
            )
        if runtime is not None:
            _verify_runtime(runtime)
        _release_gates(children)

        def replay(active: Sequence[_Child]) -> dict[str, Any]:
            authority, _baseline = _guarded_catalog_snapshot(
                checked_config, participants, children=active,
                baseline=resource_baseline,
            )
            return authority

        solver_replay = lambda: replay(children)
        solver_processes, solver_snapshots = _monitor_children(
            children, timeout_seconds=checked_config.solver_timeout_seconds,
            stdout_cap=checked_config.stdout_cap_bytes,
            stderr_cap=checked_config.stderr_cap_bytes,
            lease_recheck_seconds=checked_config.lease_recheck_seconds,
            replay_authority=solver_replay,
        )
        for participant, child, process in zip(participants, children, solver_processes, strict=True):
            proof_path = Path(participant["proof_output"]["path"])
            _publish_bytes(proof_path.parent / "solver.stdout", child.stdout)
            _publish_bytes(proof_path.parent / "solver.stderr", child.stderr)
            if process["exit_code"] != 20:
                raise NativeLratLaunchError(
                    f"leaf {participant['leaf_id']} solver did not return UNSAT exit 20"
                )
        # The O_EXCL descriptors are writable transport anchors.  Retain them
        # through every solver exit, then durably close *all* writers before
        # hashing or handing the proof to either read-only checker.
        for participant in participants:
            leaf_id = participant["leaf_id"]
            proof_fd = proof_fds.pop(leaf_id)
            try:
                receipt = next(
                    item for item in receipts if item["leaf_id"] == leaf_id
                )
                _assert_inode_fd_path(
                    proof_fd, Path(participant["proof_output"]["path"]),
                    receipt["proof_output_binding"],
                )
                os.fsync(proof_fd)
            finally:
                os.close(proof_fd)
        proof_records: dict[str, dict[str, Any]] = {}
        for participant, receipt in zip(participants, receipts, strict=True):
            leaf_id = participant["leaf_id"]
            record = _file_record(
                Path(participant["proof_output"]["path"]),
                "native-ascii-lrat-proof", cap=checked_config.proof_cap_bytes,
            )
            initial = receipt["proof_output_binding"]
            if any(
                record[key] != initial[key]
                for key in ("device", "inode", "mode", "uid", "links")
            ):
                raise NativeLratLaunchError(
                    "hashed proof is not the original O_EXCL inode"
                )
            proof_records[leaf_id] = record
        if any(record["bytes"] <= 0 for record in proof_records.values()):
            raise NativeLratLaunchError("UNSAT solver produced an empty native LRAT proof")
        solver_commit = _seal({
            "schema_version": 1, "kind": GATE + "-solver-group-result",
            "plan_sha256": verified["plan_sha256"], "generation": 0,
            "barrier_sha256": barrier["barrier_sha256"],
            "before_release_authority_sha256": before_release["authority_sha256"],
            "lease_snapshots": [item["authority_sha256"] for item in solver_snapshots],
            "processes": solver_processes, "proofs": proof_records,
            "all_solver_exit_codes_are_unsat_20": True,
            "terminal_publication": False,
        })
        _publish_json(checked_config.output_root / "30-solver-group-result.json", solver_commit)

        handoffs: list[dict[str, Any]] = []
        checker_identities: set[tuple[int, int]] = set()
        for participant in participants:
            leaf_id = participant["leaf_id"]
            first, first_snapshots, first_stdout, first_stderr = _run_checker_once(
                plan=verified, participant=participant,
                proof_record=proof_records[leaf_id], config=checked_config,
                runtime=runtime, replay_authority=replay,
                role="initial-lrat-check",
            )
            second, second_snapshots, second_stdout, second_stderr = _run_checker_once(
                plan=verified, participant=participant,
                proof_record=proof_records[leaf_id], config=checked_config,
                runtime=runtime, replay_authority=replay,
                role="fresh-lrat-replay",
            )
            identities = [
                (first["process"]["pid"], first["process"]["proc_start_ticks"]),
                (second["process"]["pid"], second["process"]["proc_start_ticks"]),
            ]
            if identities[0] == identities[1] or any(item in checker_identities for item in identities):
                raise NativeLratLaunchError("checker processes do not have distinct identities")
            checker_identities.update(identities)
            proof_path = Path(participant["proof_output"]["path"])
            final_fd = _open_regular(
                proof_path, "native ASCII LRAT final replay",
                cap=checked_config.proof_cap_bytes, executable=False,
            )
            try:
                _assert_record_fd(final_fd, proof_path, proof_records[leaf_id])
            finally:
                os.close(final_fd)
            # The content hash was sealed once after the writer exited.  Both
            # checkers opened that exact inode, and the second checker already
            # replayed mutation-sensitive metadata after consuming it.  Reuse
            # the sealed record instead of imposing a fourth full proof scan.
            final_proof = dict(proof_records[leaf_id])
            recursive_replay = (
                _replay_recursive_binding(verified, bindings[leaf_id])
                if leaf_id in bindings else None
            )
            adapter_candidate = {
                "leaf_id": leaf_id,
                "leaf_sha256": None if recursive_replay is None else bindings[leaf_id]["leaf_sha256"],
                "child_cnf_sha256": (
                    None if recursive_replay is None else bindings[leaf_id]["child_cnf_sha256"]
                ),
                "child_dimacs_sha256": participant["cnf"]["sha256"],
                "child_num_variables": participant["cnf"]["dimacs_variables"],
                "child_num_clauses": participant["cnf"]["dimacs_clauses"],
                "child_dimacs_bytes": participant["cnf"]["bytes"],
                "adapter_verified": True,
                "strict_proof_unsat": True,
                "fresh_proof_replay": True,
                "source_toolchain_fresh": True,
                "failures": [],
                # Fail closed if accidentally passed to recursive.certify_queue_item.
                "solver_terminal_claim": False,
                "publication_certificate": False,
            }
            handoff = _seal({
                "schema_version": 1, "kind": HANDOFF_KIND, "gate": GATE,
                "authority": "NON_AUTHORITATIVE_CERTIFICATION_ADAPTER",
                "production_eligible": False,
                "plan_sha256": verified["plan_sha256"], "leaf_id": leaf_id,
                "generation": 0, "cnf": dict(participant["cnf"]),
                "runtime_record_sha256": runtime_record["record_sha256"],
                "proof": final_proof,
                "solver_process_record_sha256": next(
                    item["record_sha256"] for item in solver_processes
                    if item["leaf_id"] == leaf_id
                ),
                "initial_lrat_check": first,
                "fresh_lrat_replay": second,
                "checker_process_identities_distinct": True,
                "checker_logs": {
                    "initial_stdout": first_stdout, "initial_stderr": first_stderr,
                    "fresh_stdout": second_stdout, "fresh_stderr": second_stderr,
                },
                "lease_authority_sha256s": [
                    item["authority_sha256"]
                    for item in [*first_snapshots, *second_snapshots]
                ],
                "recursive_binding": bindings.get(leaf_id),
                "recursive_binding_final_replay": recursive_replay,
                "adapter_candidate": adapter_candidate,
                "ready_for_external_authoritative_certifier": recursive_replay is not None,
                "is_recursive_certificate": False,
                "has_certificate_sha256": False,
                "queue_mutation": False, "terminal_publication": False,
                "aggregate_publication": False, "cleanup_or_deletion": False,
            }, "handoff_sha256")
            _publish_json(
                Path(participant["proof_output"]["path"]).parent
                / "40-certification-handoff.json",
                handoff,
            )
            handoffs.append(handoff)
        final_authority, _baseline = _guarded_catalog_snapshot(
            checked_config, participants, baseline=resource_baseline,
        )
        if runtime is not None:
            _verify_runtime(runtime)
            _destroy_runtime(runtime)
            runtime = None
        result = _seal({
            "schema_version": 1, "kind": RUN_KIND, "gate": GATE,
            "authority": "NON_PRODUCTION_PILOT_ONLY",
            "production_eligible": False, "status": "PILOT_VERIFIED",
            "plan_sha256": verified["plan_sha256"],
            "reservation_sha256": checked_config.reservation_sha256,
            "intent_sha256": intent["record_sha256"],
            "barrier_sha256": barrier["barrier_sha256"],
            "solver_group_sha256": solver_commit["record_sha256"],
            "runtime_record_sha256": runtime_record["record_sha256"],
            "handoff_sha256s": [item["handoff_sha256"] for item in handoffs],
            "all_native_lrat_proofs_checked_twice": True,
            "private_elf_runtime_cleanup_confirmed": checked_config.sealed_elf_runtime,
            "final_lease_authority_sha256": final_authority["authority_sha256"],
            "queue_mutation": False, "terminal_publication": False,
            "aggregate_publication": False, "cleanup_or_deletion": False,
            "scheduler_reservation_release": False,
            "next_authority": "independently-reviewed-recursive-certificate-adapter",
        })
        _publish_json(checked_config.output_root / "50-pilot-result.json", result)
        completed = True
        return result
    except BaseException as exc:
        failure = exc
        termination_error: str | None = None
        try:
            _terminate_owned(children)
        except BaseException as termination_exc:
            termination_error = (
                f"{type(termination_exc).__name__}:{termination_exc}"
            )[:1900]
        artifact_states = {
            participant["leaf_id"]: _proof_artifact_state(participant)
            for participant in participants
        }
        failure_record = _seal({
            "schema_version": 1, "kind": FAILURE_KIND, "gate": GATE,
            "failed_at": time.time(), "plan_sha256": verified["plan_sha256"],
            "reservation_sha256": checked_config.reservation_sha256,
            "error_type": type(exc).__name__, "error": str(exc)[:2048],
            "proof_outputs_may_be_abandoned": any(
                item.get("exists") is not False for item in artifact_states.values()
            ),
            "proof_artifacts": artifact_states,
            "owned_process_termination_error": termination_error,
            "automatic_retry": False, "queue_mutation": False,
            "terminal_publication": False, "aggregate_publication": False,
            "cleanup_or_deletion": False,
        })
        failure_path = checked_config.output_root / "99-failure.json"
        if not failure_path.exists():
            with contextlib.suppress(BaseException):
                _publish_json(failure_path, failure_record)
        raise
    finally:
        for fd in proof_fds.values():
            with contextlib.suppress(OSError):
                os.close(fd)
        for fd in cnf_fds.values():
            with contextlib.suppress(OSError):
                os.close(fd)
        if runtime is not None:
            try:
                _destroy_runtime(runtime)
            except BaseException:
                if completed:
                    raise
                if failure is None:
                    raise


def _load_bindings(paths: Sequence[Path]) -> list[dict[str, Any]]:
    return [_load_json(path.resolve(strict=True), "recursive binding") for path in paths]


def _config_from_args(args: argparse.Namespace) -> ExecutionConfig:
    return ExecutionConfig(
        output_root=args.output_root.resolve(strict=True),
        lease_catalogs=tuple(path.resolve(strict=True) for path in args.lease_catalog),
        reservation_sha256=args.reservation_sha256,
        solver_timeout_seconds=args.solver_timeout_seconds,
        checker_timeout_seconds=args.checker_timeout_seconds,
        proof_cap_bytes=args.proof_cap_bytes,
        lease_recheck_seconds=args.lease_recheck_seconds,
        disk_reserve_bytes=args.disk_reserve_bytes,
        sealed_elf_runtime=True,
    )


def _add_execution_args(parser: argparse.ArgumentParser) -> None:
    parser.add_argument("--plan", type=Path, required=True)
    parser.add_argument("--output-root", type=Path, required=True)
    parser.add_argument("--lease-catalog", type=Path, action="append", required=True)
    parser.add_argument("--reservation-sha256", required=True)
    parser.add_argument("--recursive-binding", type=Path, action="append", default=[])
    parser.add_argument("--solver-timeout-seconds", type=int,
                        default=DEFAULT_SOLVER_TIMEOUT_SECONDS)
    parser.add_argument("--checker-timeout-seconds", type=int,
                        default=DEFAULT_CHECKER_TIMEOUT_SECONDS)
    parser.add_argument("--proof-cap-bytes", type=int, default=DEFAULT_PROOF_CAP_BYTES)
    parser.add_argument("--lease-recheck-seconds", type=float,
                        default=DEFAULT_LEASE_RECHECK_SECONDS)
    parser.add_argument("--disk-reserve-bytes", type=int,
                        default=DEFAULT_DISK_RESERVE_BYTES)


def _parser() -> argparse.ArgumentParser:
    parser = argparse.ArgumentParser(description=__doc__, allow_abbrev=False)
    commands = parser.add_subparsers(dest="command", required=True)
    lease = commands.add_parser("derive-lease", help="derive one read-only PLAN lease contract")
    lease.add_argument("--output-root", type=Path, required=True)
    lease.add_argument("--lease-catalog", type=Path, action="append", required=True)
    lease.add_argument("--reservation-sha256", required=True)
    lease.add_argument("--cpu", type=int, required=True)
    audit = commands.add_parser("audit", help="read-only pilot admission audit")
    _add_execution_args(audit)
    run = commands.add_parser("run-pilot", help="execute a non-authoritative native-LRAT pilot")
    _add_execution_args(run)
    bind = commands.add_parser("bind-recursive", help="read-only bind a claimed recursive item")
    bind.add_argument("--plan", type=Path, required=True)
    bind.add_argument("--queue", type=Path, required=True)
    bind.add_argument("--item-id", required=True)
    return parser


def main(argv: Sequence[str] | None = None) -> int:
    args = _parser().parse_args(argv)
    try:
        if args.command == "derive-lease":
            result = derive_plan_cpu_lease(
                cpu=args.cpu,
                bundle=args.output_root.resolve(strict=True),
                reservation_sha256=args.reservation_sha256,
                catalogs=tuple(sorted(
                    (path.resolve(strict=True) for path in args.lease_catalog),
                    key=str,
                )),
            )
        elif args.command == "bind-recursive":
            plan = _load_json(args.plan.resolve(strict=True), "native LRAT plan")
            result = build_recursive_binding(
                plan, queue_path=args.queue.resolve(strict=True), item_id=args.item_id,
            )
        elif args.command in {"audit", "run-pilot"}:
            plan = _load_json(args.plan.resolve(strict=True), "native LRAT plan")
            config = _config_from_args(args)
            bindings = _load_bindings(args.recursive_binding)
            if args.command == "audit":
                result = audit_pilot(plan, config, recursive_bindings=bindings)
            else:
                result = run_pilot(plan, config, recursive_bindings=bindings)
        else:  # pragma: no cover - argparse owns this branch.
            raise NativeLratLaunchError("unknown command")
    except (
        NativeLratLaunchError, native.NativeLratPlanError,
        recursive.RecursiveSplitError, OSError, ValueError, TypeError,
    ) as exc:
        print(f"ERROR: {exc}", file=sys.stderr)
        return 2
    sys.stdout.buffer.write(_canonical(result) + b"\n")
    return 0 if result.get("go", True) else 3


if __name__ == "__main__":
    raise SystemExit(main())
