#!/usr/bin/env python3
"""Recoverable, native-LRAT-only scheduler lease transaction sidecar.

This helper owns only rows whose bundle points at a dedicated native-LRAT
pilot root and whose immutable reservation uses this module's namespace.  It
never signals a process, publishes a proof/certificate, or deletes data.
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
import stat
import sys
import time
import uuid
from dataclasses import dataclass
from pathlib import Path
from typing import Any, Iterator, Mapping, Sequence

try:
    from scripts import paper400_native_lrat_resource_gate_v1 as resource_gate
except ModuleNotFoundError:
    sys.path.insert(0, str(Path(__file__).resolve().parent.parent))
    from scripts import paper400_native_lrat_resource_gate_v1 as resource_gate


SCHEMA_VERSION = 1
GATE = "paper400-native-lrat-lease-owner-v1"
RESERVATION_KIND = GATE + "-reservation"
STATE_KIND = GATE + "-state"
ACQUIRE_KIND = GATE + "-acquire"
RENEW_KIND = GATE + "-renew"
RELEASE_KIND = GATE + "-release"
LEASE_SCOPE = GATE + "-scheduler-scope"
CATALOG_KIND = "paper400-dic5-recursive-cpu-lease-catalog-v1"
LAUNCHER_RUN_KIND = "paper400-native-lrat-launcher-v1-run"
LAUNCHER_FAILURE_KIND = "paper400-native-lrat-launcher-v1-failure"
RUN_ROOT = Path("/home/jing/paper400-runs")
DEFAULT_CATALOGS = tuple(sorted((
    RUN_ROOT / ".paper400-recursive-split-v1/cpu-leases.json",
    RUN_ROOT / ".paper400-recursive-certified-slot-handoffs-v1/borrow-control/cpu-leases.json",
    RUN_ROOT / ".paper400-recursive-nested-certified-slot-handoffs-v2/cpu-leases.json",
), key=str))
STATE_FILE = "NATIVE-LRAT-LEASE-STATE.json"
RELEASE_FILE = "NATIVE-LRAT-LEASE-RELEASE.json"
MAX_JSON_BYTES = 64 << 20
SHA256_LENGTH = 64
DEFAULT_TTL_SECONDS = 300.0
DEFAULT_HOST_MEMORY_RESERVE_BYTES = 64 << 30
DEFAULT_CGROUP_MEMORY_RESERVE_BYTES = 32 << 30
DEFAULT_HOST_PSI_SOME_AVG10 = 20.0
DEFAULT_HOST_PSI_FULL_AVG10 = 5.0
DEFAULT_CGROUP_PSI_SOME_AVG10 = 20.0
DEFAULT_CGROUP_PSI_FULL_AVG10 = 5.0
_TEST_ONLY_NONCE = object()
AT_FDCWD = -100
RENAME_NOREPLACE = 1
_LIBC = ctypes.CDLL(None, use_errno=True)


class NativeLeaseError(RuntimeError):
    """The dedicated native-LRAT lease transaction failed closed."""


@dataclass(frozen=True)
class LeaseConfig:
    run_root: Path
    output_root: Path
    catalogs: tuple[Path, ...]
    cpus: tuple[int, ...]
    ttl_seconds: float
    resource: resource_gate.ResourceGateConfig


def _canonical(value: Any) -> bytes:
    try:
        return json.dumps(
            value, sort_keys=True, separators=(",", ":"), ensure_ascii=True,
            allow_nan=False,
        ).encode("ascii")
    except (TypeError, ValueError, UnicodeEncodeError) as exc:
        raise NativeLeaseError(f"non-canonical lease value: {exc}") from exc


def _seal(value: Mapping[str, Any], field: str = "record_sha256") -> dict[str, Any]:
    result = dict(value)
    if field in result:
        raise NativeLeaseError("cannot reseal an already sealed lease value")
    result[field] = hashlib.sha256(_canonical(result)).hexdigest()
    return result


def _selfhash(value: Any, field: str) -> bool:
    if type(value) is not dict or type(value.get(field)) is not str:
        return False
    expected = value[field]
    if len(expected) != SHA256_LENGTH or any(c not in "0123456789abcdef" for c in expected):
        return False
    unsigned = dict(value)
    unsigned.pop(field)
    return hashlib.sha256(_canonical(unsigned)).hexdigest() == expected


def _normal_directory(path: Path, role: str) -> Path:
    if not path.is_absolute() or os.path.normpath(str(path)) != str(path):
        raise NativeLeaseError(f"{role} is not absolute and normalized")
    try:
        resolved = path.resolve(strict=True)
        info = resolved.stat()
    except OSError as exc:
        raise NativeLeaseError(f"cannot resolve {role}") from exc
    if resolved != path or not stat.S_ISDIR(info.st_mode):
        raise NativeLeaseError(f"{role} is not an exact directory")
    return resolved


def _read_json(path: Path, role: str, *, mode: int) -> dict[str, Any]:
    flags = os.O_RDONLY | os.O_CLOEXEC | getattr(os, "O_NOFOLLOW", 0)
    try:
        fd = os.open(path, flags)
    except OSError as exc:
        raise NativeLeaseError(f"cannot open {role}") from exc
    try:
        before = os.fstat(fd)
        if not stat.S_ISREG(before.st_mode) or stat.S_IMODE(before.st_mode) != mode:
            raise NativeLeaseError(f"{role} type/mode mismatch")
        chunks: list[bytes] = []
        total = 0
        while True:
            chunk = os.read(fd, min(1 << 16, MAX_JSON_BYTES + 1 - total))
            if not chunk:
                break
            total += len(chunk)
            if total > MAX_JSON_BYTES:
                raise NativeLeaseError(f"{role} exceeds size cap")
            chunks.append(chunk)
        after = os.fstat(fd)
        identity = lambda item: (
            item.st_dev, item.st_ino, item.st_mode, item.st_uid,
            item.st_size, item.st_mtime_ns, item.st_ctime_ns,
        )
        if identity(before) != identity(after):
            raise NativeLeaseError(f"{role} changed while reading")
    finally:
        os.close(fd)
    payload = b"".join(chunks)
    try:
        value = json.loads(payload.decode("ascii"))
    except (UnicodeDecodeError, json.JSONDecodeError) as exc:
        raise NativeLeaseError(f"{role} is not canonical JSON") from exc
    if type(value) is not dict or payload not in {_canonical(value), _canonical(value) + b"\n"}:
        raise NativeLeaseError(f"{role} is not canonical JSON")
    return value


def _fsync_dir(path: Path) -> None:
    fd = os.open(path, os.O_RDONLY | os.O_DIRECTORY | os.O_CLOEXEC)
    try:
        os.fsync(fd)
    finally:
        os.close(fd)


def _write_exclusive(path: Path, value: Mapping[str, Any], *, mode: int) -> None:
    flags = os.O_WRONLY | os.O_CREAT | os.O_EXCL | os.O_CLOEXEC | getattr(os, "O_NOFOLLOW", 0)
    fd = os.open(path, flags, mode)
    try:
        payload = _canonical(value) + b"\n"
        view = memoryview(payload)
        while view:
            count = os.write(fd, view)
            if count <= 0:
                raise NativeLeaseError("short lease record write")
            view = view[count:]
        os.fsync(fd)
    finally:
        os.close(fd)
    _fsync_dir(path.parent)


def _atomic_replace(path: Path, value: Mapping[str, Any], *, mode: int) -> None:
    temporary = path.with_name(f".{path.name}.{os.getpid()}.{uuid.uuid4().hex}.tmp")
    try:
        _write_exclusive(temporary, value, mode=mode)
        os.replace(temporary, path)
        _fsync_dir(path.parent)
    except BaseException:
        with contextlib.suppress(OSError):
            temporary.unlink()
        raise


def _rename_noreplace(source: Path, target: Path) -> None:
    ctypes.set_errno(0)
    result = _LIBC.renameat2(
        AT_FDCWD, os.fsencode(source), AT_FDCWD, os.fsencode(target),
        RENAME_NOREPLACE,
    )
    if result != 0:
        code = ctypes.get_errno() or errno.EIO
        raise OSError(code, os.strerror(code), str(target))


@contextlib.contextmanager
def _catalog_locks(catalogs: Sequence[Path]) -> Iterator[None]:
    descriptors: list[int] = []
    try:
        for catalog in sorted(catalogs, key=str):
            lock = catalog.with_name("cpu-leases.lock")
            fd = os.open(lock, os.O_RDWR | os.O_CLOEXEC | getattr(os, "O_NOFOLLOW", 0))
            info = os.fstat(fd)
            if not stat.S_ISREG(info.st_mode) or stat.S_IMODE(info.st_mode) != 0o600:
                os.close(fd)
                raise NativeLeaseError("catalog lock type/mode mismatch")
            fcntl.flock(fd, fcntl.LOCK_EX)
            descriptors.append(fd)
        yield
    finally:
        for fd in reversed(descriptors):
            with contextlib.suppress(OSError):
                fcntl.flock(fd, fcntl.LOCK_UN)
            with contextlib.suppress(OSError):
                os.close(fd)


def _validate_config(config: LeaseConfig, *, test_mode: bool) -> LeaseConfig:
    run_root = _normal_directory(config.run_root, "run root")
    output = config.output_root
    if not output.is_absolute() or os.path.normpath(str(output)) != str(output):
        raise NativeLeaseError("output root is not absolute and normalized")
    if output.parent != run_root:
        raise NativeLeaseError("output root is not a direct child of run root")
    if not output.name.startswith("paper400-native-lrat-pilot-v1-"):
        raise NativeLeaseError("output root is outside the native-LRAT namespace")
    catalogs = tuple(sorted(config.catalogs, key=str))
    if len(catalogs) != 3 or len(set(catalogs)) != 3:
        raise NativeLeaseError("exactly three distinct catalogs are required")
    for path in catalogs:
        if path.resolve(strict=True) != path:
            raise NativeLeaseError("catalog path is not exact")
    if not test_mode and (run_root != RUN_ROOT or catalogs != DEFAULT_CATALOGS):
        raise NativeLeaseError("CLI lease owner requires pinned production roots")
    cpus = tuple(sorted(config.cpus))
    if (
        not cpus or cpus != config.cpus or len(set(cpus)) != len(cpus)
        or any(type(cpu) is not int or cpu < 0 for cpu in cpus)
    ):
        raise NativeLeaseError("lease CPU set is invalid")
    if (
        type(config.ttl_seconds) not in {int, float}
        or not math.isfinite(float(config.ttl_seconds))
        or not 30.0 <= float(config.ttl_seconds) <= 3600.0
    ):
        raise NativeLeaseError("lease TTL is outside 30..3600 seconds")
    checked_resource = resource_gate._validate_config(config.resource)
    if not test_mode and (
        float(config.ttl_seconds) != DEFAULT_TTL_SECONDS
        or checked_resource.proc_root != Path("/proc")
        or checked_resource.cgroup_mount != Path("/sys/fs/cgroup")
        or checked_resource.min_host_available_bytes != DEFAULT_HOST_MEMORY_RESERVE_BYTES
        or checked_resource.min_cgroup_available_bytes != DEFAULT_CGROUP_MEMORY_RESERVE_BYTES
        or checked_resource.max_host_psi_some_avg10 != DEFAULT_HOST_PSI_SOME_AVG10
        or checked_resource.max_host_psi_full_avg10 != DEFAULT_HOST_PSI_FULL_AVG10
        or checked_resource.max_cgroup_psi_some_avg10 != DEFAULT_CGROUP_PSI_SOME_AVG10
        or checked_resource.max_cgroup_psi_full_avg10 != DEFAULT_CGROUP_PSI_FULL_AVG10
    ):
        raise NativeLeaseError("CLI lease owner requires pinned TTL/resource thresholds")
    return LeaseConfig(
        run_root=run_root, output_root=output, catalogs=catalogs, cpus=cpus,
        ttl_seconds=float(config.ttl_seconds), resource=checked_resource,
    )


def _load_catalog(path: Path) -> dict[str, Any]:
    value = _read_json(path, "CPU lease catalog", mode=0o600)
    if (
        set(value) != {"schema_version", "kind", "leases", "updated_at", "catalog_sha256"}
        or value.get("schema_version") != 1
        or value.get("kind") != CATALOG_KIND
        or type(value.get("leases")) is not list
        or type(value.get("updated_at")) not in {int, float}
        or not math.isfinite(float(value["updated_at"]))
        or not _selfhash(value, "catalog_sha256")
    ):
        raise NativeLeaseError("catalog schema/self-hash mismatch")
    active: set[int] = set()
    for row in value["leases"]:
        if (
            type(row) is not dict
            or set(row) != {
                "cpu", "bundle", "reservation_sha256", "state",
                "created_at", "released_at",
            }
            or type(row.get("cpu")) is not int or row["cpu"] < 0
            or type(row.get("bundle")) is not str
            or type(row.get("reservation_sha256")) is not str
            or len(row["reservation_sha256"]) != SHA256_LENGTH
            or any(c not in "0123456789abcdef" for c in row["reservation_sha256"])
            or row.get("state") not in {"RESERVED", "RELEASED"}
            or type(row.get("created_at")) not in {int, float}
            or not math.isfinite(float(row["created_at"]))
            or (
                row.get("released_at") is not None
                and (
                    type(row["released_at"]) not in {int, float}
                    or not math.isfinite(float(row["released_at"]))
                )
            )
        ):
            raise NativeLeaseError("catalog contains a malformed row")
        if row["state"] == "RESERVED":
            if row["cpu"] in active:
                raise NativeLeaseError("catalog duplicates an active CPU")
            active.add(row["cpu"])
    return value


def _write_catalog(path: Path, current: Mapping[str, Any], leases: Sequence[Mapping[str, Any]], now: float) -> dict[str, Any]:
    replacement = _seal({
        "schema_version": 1, "kind": CATALOG_KIND,
        "leases": [dict(row) for row in leases], "updated_at": now,
    }, "catalog_sha256")
    observed = _load_catalog(path)
    if observed["catalog_sha256"] != current["catalog_sha256"]:
        raise NativeLeaseError("catalog changed before compare-and-swap")
    _atomic_replace(path, replacement, mode=0o600)
    return replacement


def _matching_rows(catalog: Mapping[str, Any], reservation: Mapping[str, Any]) -> list[dict[str, Any]]:
    cpus = set(reservation["cpus"])
    return [
        row for row in catalog["leases"]
        if (row["cpu"] in cpus and row["state"] == "RESERVED")
        or row["bundle"] == reservation["bundle"]
        or row["reservation_sha256"] == reservation["reservation_sha256"]
    ]


def _assert_transaction(catalog: Mapping[str, Any], reservation: Mapping[str, Any], *, allow_missing: bool) -> None:
    rows = _matching_rows(catalog, reservation)
    expected = (reservation["bundle"], reservation["reservation_sha256"])
    if any(
        row["cpu"] not in set(reservation["cpus"])
        or (row["bundle"], row["reservation_sha256"]) != expected
        or row["created_at"] != reservation["created_at"]
        for row in rows
    ):
        raise NativeLeaseError("catalog CPU/owner identity conflicts with transaction")
    counts = {cpu: sum(row["cpu"] == cpu for row in rows) for cpu in reservation["cpus"]}
    if any(count > 1 for count in counts.values()):
        raise NativeLeaseError("catalog repeats a native lease row")
    if not allow_missing and any(count != 1 for count in counts.values()):
        raise NativeLeaseError("catalog lacks the complete native lease transaction")


def _reservation(config: LeaseConfig, now: float) -> dict[str, Any]:
    return _seal({
        "schema_version": 1,
        "kind": RESERVATION_KIND,
        "bundle": str(config.output_root),
        "cpus": list(config.cpus),
        "observations": [
            {
                "cpu": cpu,
                "pinned_running_processes": [],
                "broad_affinity_running_process_count": 0,
                "kernel_hardware_exclusive": False,
                "lease_scope": LEASE_SCOPE,
            }
            for cpu in config.cpus
        ],
        "kernel_hardware_exclusive": False,
        "scheduler_lease_only": True,
        "created_at": now,
    }, "reservation_sha256")


def _state(
    reservation: Mapping[str, Any], *, state: str, epoch: int,
    acquired_at: float, renewed_at: float, expires_at: float,
    release_requested_at: float | None = None,
    released_at: float | None = None,
) -> dict[str, Any]:
    return _seal({
        "schema_version": 1,
        "kind": STATE_KIND,
        "bundle": reservation["bundle"],
        "reservation_sha256": reservation["reservation_sha256"],
        "cpus": reservation["cpus"],
        "state": state,
        "epoch": epoch,
        "acquired_at": acquired_at,
        "renewed_at": renewed_at,
        "expires_at": expires_at,
        "release_requested_at": release_requested_at,
        "released_at": released_at,
        "process_control_authority": False,
        "proof_or_certificate_authority": False,
        "cleanup_authority": False,
    })


def _load_reservation(config: LeaseConfig) -> dict[str, Any]:
    value = _read_json(
        config.output_root / "cpu-reservation.json",
        "native-LRAT reservation", mode=0o400,
    )
    if (
        set(value) != {
            "schema_version", "kind", "bundle", "cpus", "observations",
            "kernel_hardware_exclusive", "scheduler_lease_only", "created_at",
            "reservation_sha256",
        }
        or value.get("schema_version") != 1
        or value.get("kind") != RESERVATION_KIND
        or value.get("bundle") != str(config.output_root)
        or value.get("cpus") != list(config.cpus)
        or type(value.get("created_at")) not in {int, float}
        or not math.isfinite(float(value["created_at"]))
        or value.get("kernel_hardware_exclusive") is not False
        or value.get("scheduler_lease_only") is not True
        or not _selfhash(value, "reservation_sha256")
    ):
        raise NativeLeaseError("native-LRAT reservation is malformed")
    observations = value.get("observations")
    if (
        type(observations) is not list
        or [item.get("cpu") if type(item) is dict else None for item in observations]
        != list(config.cpus)
        or any(
            type(item) is not dict
            or set(item) != {
                "cpu", "pinned_running_processes",
                "broad_affinity_running_process_count",
                "kernel_hardware_exclusive", "lease_scope",
            }
            or item.get("pinned_running_processes") != []
            or item.get("broad_affinity_running_process_count") != 0
            or item.get("kernel_hardware_exclusive") is not False
            or item.get("lease_scope") != LEASE_SCOPE
            for item in observations
        )
    ):
        raise NativeLeaseError("native-LRAT reservation observations are malformed")
    return value


def _load_state(config: LeaseConfig, reservation: Mapping[str, Any]) -> dict[str, Any]:
    value = _read_json(
        config.output_root / STATE_FILE, "native-LRAT lease state", mode=0o600,
    )
    if (
        set(value) != {
            "schema_version", "kind", "bundle", "reservation_sha256", "cpus",
            "state", "epoch", "acquired_at", "renewed_at", "expires_at",
            "release_requested_at", "released_at", "process_control_authority",
            "proof_or_certificate_authority", "cleanup_authority", "record_sha256",
        }
        or value.get("schema_version") != 1
        or value.get("kind") != STATE_KIND
        or value.get("bundle") != reservation["bundle"]
        or value.get("reservation_sha256") != reservation["reservation_sha256"]
        or value.get("cpus") != reservation["cpus"]
        or value.get("state") not in {"PENDING", "ACTIVE", "RELEASING", "RELEASED"}
        or type(value.get("epoch")) is not int or value["epoch"] < 0
        or any(
            type(value.get(field)) not in {int, float}
            or not math.isfinite(float(value[field]))
            for field in ("acquired_at", "renewed_at", "expires_at")
        )
        or value.get("process_control_authority") is not False
        or value.get("proof_or_certificate_authority") is not False
        or value.get("cleanup_authority") is not False
        or not _selfhash(value, "record_sha256")
    ):
        raise NativeLeaseError("native-LRAT lease state is malformed")
    for field in ("release_requested_at", "released_at"):
        if value[field] is not None and (
            type(value[field]) not in {int, float}
            or not math.isfinite(float(value[field]))
        ):
            raise NativeLeaseError("native-LRAT lease release timestamp is malformed")
    return value


def _resource_snapshot(
    config: LeaseConfig, *, owned: Mapping[int, int] | None = None,
    baseline: Mapping[str, Any] | None = None,
) -> dict[str, Any]:
    owned = {} if owned is None else owned
    try:
        return resource_gate.snapshot(
            config.resource, config.cpus,
            owned_processes=owned, baseline=baseline,
        )
    except resource_gate.ResourceGateError as exc:
        raise NativeLeaseError(str(exc)) from exc


def _owned_from_barrier(config: LeaseConfig) -> dict[int, int]:
    path = config.output_root / "20-all-start-barrier.json"
    if not os.path.lexists(path):
        return {}
    barrier = _read_json(path, "native-LRAT all-start barrier", mode=0o600)
    identities = barrier.get("pid_start_identities")
    if (
        barrier.get("kind") != "paper400-native-lrat-all-start-barrier-v1"
        or not _selfhash(barrier, "barrier_sha256")
        or barrier.get("all_start_receipts_complete") is not True
        or type(identities) is not list
        or len(identities) != len(config.cpus)
    ):
        raise NativeLeaseError("native-LRAT all-start barrier is malformed")
    result: dict[int, int] = {}
    observed_cpus: list[int] = []
    for item in identities:
        if (
            type(item) is not dict
            or set(item) != {"leaf_id", "pid", "proc_start_ticks", "cpu"}
            or type(item.get("pid")) is not int or item["pid"] <= 1
            or type(item.get("proc_start_ticks")) is not int
            or item["proc_start_ticks"] <= 0
            or type(item.get("cpu")) is not int
            or item["pid"] in result
        ):
            raise NativeLeaseError("native-LRAT barrier process identity is malformed")
        result[item["pid"]] = item["proc_start_ticks"]
        observed_cpus.append(item["cpu"])
    if sorted(observed_cpus) != list(config.cpus):
        raise NativeLeaseError("native-LRAT barrier CPU membership is cross-bound")
    return result


def _create_root(config: LeaseConfig, reservation: Mapping[str, Any], pending: Mapping[str, Any]) -> None:
    staging = config.run_root / f".{GATE}.{os.getpid()}.{uuid.uuid4().hex}.tmp"
    os.mkdir(staging, 0o700)
    try:
        _write_exclusive(staging / "cpu-reservation.json", reservation, mode=0o400)
        _write_exclusive(staging / STATE_FILE, pending, mode=0o600)
        os.mkdir(staging / "leaves", 0o700)
        _fsync_dir(staging)
        _rename_noreplace(staging, config.output_root)
        _fsync_dir(config.run_root)
    except BaseException:
        with contextlib.suppress(OSError):
            (staging / "cpu-reservation.json").unlink()
        with contextlib.suppress(OSError):
            (staging / STATE_FILE).unlink()
        with contextlib.suppress(OSError):
            (staging / "leaves").rmdir()
        with contextlib.suppress(OSError):
            staging.rmdir()
        raise


def _root_for_recovery(config: LeaseConfig) -> tuple[dict[str, Any], dict[str, Any]]:
    root = _normal_directory(config.output_root, "native-LRAT output root")
    if root != config.output_root:
        raise NativeLeaseError("native-LRAT output root identity changed")
    allowed = {
        "cpu-reservation.json", STATE_FILE, RELEASE_FILE, "leaves",
        "00-launch-intent.json", "05-runtime-binding.json",
        "20-all-start-barrier.json", "30-solver-group-result.json",
        "50-pilot-result.json", "99-failure.json",
    }
    entries = {item.name for item in root.iterdir()}
    required = {"cpu-reservation.json", STATE_FILE, "leaves"}
    if not entries.issubset(allowed) or not required.issubset(entries):
        raise NativeLeaseError("lease recovery root contains unexpected material")
    reservation = _load_reservation(config)
    state = _load_state(config, reservation)
    return reservation, state


def _append_missing_rows(
    config: LeaseConfig, catalogs: list[dict[str, Any]],
    reservation: Mapping[str, Any], *, fail_after_catalog: int | None,
) -> None:
    for index, (path, catalog) in enumerate(zip(config.catalogs, catalogs, strict=True)):
        _assert_transaction(catalog, reservation, allow_missing=True)
        rows = _matching_rows(catalog, reservation)
        present = {row["cpu"] for row in rows}
        if present != set(config.cpus):
            additions = [
                {
                    "cpu": cpu, "bundle": reservation["bundle"],
                    "reservation_sha256": reservation["reservation_sha256"],
                    "state": "RESERVED", "created_at": reservation["created_at"],
                    "released_at": None,
                }
                for cpu in config.cpus if cpu not in present
            ]
            catalogs[index] = _write_catalog(
                path, catalog, [*catalog["leases"], *additions], time.time(),
            )
        if fail_after_catalog == index + 1:
            raise RuntimeError("injected partial native lease acquire")


def acquire(
    config: LeaseConfig, *, _test_nonce: object | None = None,
    _fail_after_catalog: int | None = None,
) -> dict[str, Any]:
    test_mode = _test_nonce is _TEST_ONLY_NONCE
    checked = _validate_config(config, test_mode=test_mode)
    if _fail_after_catalog is not None and not test_mode:
        raise NativeLeaseError("fault injection is test-only")
    before = _resource_snapshot(checked)
    with _catalog_locks(checked.catalogs):
        recovery = os.path.lexists(checked.output_root)
        if recovery:
            reservation, state = _root_for_recovery(checked)
            if state["state"] == "RELEASED":
                raise NativeLeaseError("cannot reacquire a released native lease identity")
            if state["state"] == "RELEASING":
                raise NativeLeaseError("native lease release must finish before recovery")
        else:
            now = time.time()
            reservation = _reservation(checked, now)
            state = _state(
                reservation, state="PENDING", epoch=0,
                acquired_at=now, renewed_at=now,
                expires_at=now + checked.ttl_seconds,
            )
            _create_root(checked, reservation, state)
        catalogs = [_load_catalog(path) for path in checked.catalogs]
        _append_missing_rows(
            checked, catalogs, reservation,
            fail_after_catalog=_fail_after_catalog,
        )
        verified = [_load_catalog(path) for path in checked.catalogs]
        for catalog in verified:
            _assert_transaction(catalog, reservation, allow_missing=False)
            if any(row["state"] != "RESERVED" for row in _matching_rows(catalog, reservation)):
                raise NativeLeaseError("native lease row is not active after acquire")
        if state["state"] == "PENDING":
            now = time.time()
            state = _state(
                reservation, state="ACTIVE", epoch=1,
                acquired_at=state["acquired_at"], renewed_at=now,
                expires_at=now + checked.ttl_seconds,
            )
            _atomic_replace(checked.output_root / STATE_FILE, state, mode=0o600)
        elif state["state"] != "ACTIVE" or state["expires_at"] <= time.time():
            raise NativeLeaseError("recovered native lease is not live")
    after = _resource_snapshot(checked, baseline=before)
    return _seal({
        "schema_version": 1, "kind": ACQUIRE_KIND,
        "bundle": str(checked.output_root), "cpus": list(checked.cpus),
        "reservation_sha256": reservation["reservation_sha256"],
        "lease_state_sha256": state["record_sha256"],
        "recovery_replay": recovery,
        "all_three_catalogs_active": True,
        "resource_before": before, "resource_after": after,
        "process_control_authority": False,
        "proof_or_certificate_authority": False,
        "cleanup_authority": False,
    })


def renew(
    config: LeaseConfig, *, _test_nonce: object | None = None,
) -> dict[str, Any]:
    checked = _validate_config(
        config, test_mode=_test_nonce is _TEST_ONLY_NONCE,
    )
    reservation, state = _root_for_recovery(checked)
    if state["state"] != "ACTIVE" or state["expires_at"] <= time.time():
        raise NativeLeaseError("native lease is not renewable")
    owned = _owned_from_barrier(checked)
    before = _resource_snapshot(checked, owned=owned)
    with _catalog_locks(checked.catalogs):
        reservation, current = _root_for_recovery(checked)
        if (
            current["record_sha256"] != state["record_sha256"]
            or current["state"] != "ACTIVE"
            or current["expires_at"] <= time.time()
        ):
            raise NativeLeaseError("native lease state changed or expired before renewal")
        catalogs = [_load_catalog(path) for path in checked.catalogs]
        for catalog in catalogs:
            _assert_transaction(catalog, reservation, allow_missing=False)
            if any(row["state"] != "RESERVED" for row in _matching_rows(catalog, reservation)):
                raise NativeLeaseError("cannot renew a non-active catalog row")
        now = time.time()
        replacement = _state(
            reservation, state="ACTIVE", epoch=current["epoch"] + 1,
            acquired_at=current["acquired_at"], renewed_at=now,
            expires_at=now + checked.ttl_seconds,
        )
        _atomic_replace(checked.output_root / STATE_FILE, replacement, mode=0o600)
    after = _resource_snapshot(checked, owned=owned, baseline=before)
    return _seal({
        "schema_version": 1, "kind": RENEW_KIND,
        "bundle": str(checked.output_root),
        "reservation_sha256": reservation["reservation_sha256"],
        "epoch": replacement["epoch"], "renewed_at": replacement["renewed_at"],
        "expires_at": replacement["expires_at"],
        "lease_state_sha256": replacement["record_sha256"],
        "all_three_catalogs_active": True,
        "resource_before": before, "resource_after": after,
        "process_control_authority": False,
        "proof_or_certificate_authority": False,
        "cleanup_authority": False,
    })


def _release_evidence(config: LeaseConfig, reservation: Mapping[str, Any]) -> dict[str, Any]:
    success_path = config.output_root / "50-pilot-result.json"
    failure_path = config.output_root / "99-failure.json"
    present = [path for path in (success_path, failure_path) if os.path.lexists(path)]
    if len(present) != 1:
        # A pristine, never-launched reservation may be safely aborted.
        leaves = config.output_root / "leaves"
        if not os.path.lexists(config.output_root / "00-launch-intent.json") and not any(leaves.iterdir()):
            return {"kind": "PRISTINE_ABORT", "record_sha256": "0" * 64}
        raise NativeLeaseError("release requires exactly one final launcher record")
    value = _read_json(present[0], "native-LRAT final launcher record", mode=0o600)
    if value.get("plan_sha256") is None or type(value.get("plan_sha256")) is not str:
        raise NativeLeaseError("launcher final record lacks a plan binding")
    if value.get("kind") == LAUNCHER_RUN_KIND:
        if (
            value.get("status") != "PILOT_VERIFIED"
            or value.get("scheduler_reservation_release") is not False
            or value.get("terminal_publication") is not False
            or not _selfhash(value, "record_sha256")
        ):
            raise NativeLeaseError("native-LRAT success record is not releasable")
    elif value.get("kind") == LAUNCHER_FAILURE_KIND:
        if (
            value.get("owned_process_termination_error") is not None
            or value.get("terminal_publication") is not False
            or not _selfhash(value, "record_sha256")
        ):
            raise NativeLeaseError("native-LRAT failure record is not safely releasable")
    else:
        raise NativeLeaseError("release record is outside the native-LRAT namespace")
    if value.get("reservation_sha256") != reservation["reservation_sha256"]:
        raise NativeLeaseError("launcher final record belongs to another reservation")
    return value


def release(
    config: LeaseConfig, *, _test_nonce: object | None = None,
    _fail_after_catalog: int | None = None,
) -> dict[str, Any]:
    test_mode = _test_nonce is _TEST_ONLY_NONCE
    checked = _validate_config(config, test_mode=test_mode)
    if _fail_after_catalog is not None and not test_mode:
        raise NativeLeaseError("fault injection is test-only")
    reservation, state = _root_for_recovery(checked)
    evidence = _release_evidence(checked, reservation)
    # Deliberately do not exempt receipt identities: every live process pinned
    # to a leased CPU blocks release.  This sidecar has no signal authority.
    before = _resource_snapshot(checked)
    with _catalog_locks(checked.catalogs):
        reservation, state = _root_for_recovery(checked)
        if state["state"] == "RELEASED":
            release_record = _read_json(
                checked.output_root / RELEASE_FILE,
                "native-LRAT lease release", mode=0o400,
            )
            if not _selfhash(release_record, "record_sha256"):
                raise NativeLeaseError("existing release record is malformed")
            return release_record
        if state["state"] not in {"ACTIVE", "RELEASING"}:
            raise NativeLeaseError("native lease is not releasable")
        if state["state"] == "ACTIVE":
            now = time.time()
            state = _state(
                reservation, state="RELEASING", epoch=state["epoch"],
                acquired_at=state["acquired_at"], renewed_at=state["renewed_at"],
                expires_at=state["expires_at"], release_requested_at=now,
            )
            _atomic_replace(checked.output_root / STATE_FILE, state, mode=0o600)
        released_at = state["release_requested_at"]
        catalogs = [_load_catalog(path) for path in checked.catalogs]
        for index, (path, catalog) in enumerate(zip(checked.catalogs, catalogs, strict=True)):
            _assert_transaction(catalog, reservation, allow_missing=False)
            rows = _matching_rows(catalog, reservation)
            states = {row["state"] for row in rows}
            if not states.issubset({"RESERVED", "RELEASED"}):
                raise NativeLeaseError("native lease catalog has an invalid release state")
            if "RESERVED" in states:
                updated = [
                    {
                        **row,
                        "state": "RELEASED",
                        "released_at": released_at,
                    }
                    if row in rows else row
                    for row in catalog["leases"]
                ]
                catalogs[index] = _write_catalog(path, catalog, updated, released_at)
            elif any(row["released_at"] != released_at for row in rows):
                raise NativeLeaseError("partial release timestamp is inconsistent")
            if _fail_after_catalog == index + 1:
                raise RuntimeError("injected partial native lease release")
        final_catalogs = [_load_catalog(path) for path in checked.catalogs]
        for catalog in final_catalogs:
            _assert_transaction(catalog, reservation, allow_missing=False)
            if any(row["state"] != "RELEASED" for row in _matching_rows(catalog, reservation)):
                raise NativeLeaseError("native lease release is incomplete")
        released_state = _state(
            reservation, state="RELEASED", epoch=state["epoch"],
            acquired_at=state["acquired_at"], renewed_at=state["renewed_at"],
            expires_at=state["expires_at"], release_requested_at=released_at,
            released_at=released_at,
        )
        release_record = _seal({
            "schema_version": 1, "kind": RELEASE_KIND,
            "bundle": str(checked.output_root), "cpus": list(checked.cpus),
            "reservation_sha256": reservation["reservation_sha256"],
            "release_evidence_sha256": evidence["record_sha256"],
            "released_at": released_at, "all_three_catalogs_released": True,
            "process_control_authority": False,
            "proof_or_certificate_authority": False,
            "cleanup_authority": False,
        })
        if not os.path.lexists(checked.output_root / RELEASE_FILE):
            _write_exclusive(checked.output_root / RELEASE_FILE, release_record, mode=0o400)
        else:
            existing = _read_json(
                checked.output_root / RELEASE_FILE,
                "native-LRAT lease release", mode=0o400,
            )
            if existing != release_record:
                raise NativeLeaseError("release replay record differs")
        _atomic_replace(checked.output_root / STATE_FILE, released_state, mode=0o600)
    return release_record


def _parse_cpus(value: str) -> tuple[int, ...]:
    try:
        cpus = tuple(sorted(int(item) for item in value.split(",")))
    except ValueError as exc:
        raise argparse.ArgumentTypeError("CPUs must be comma-separated integers") from exc
    if not cpus or len(set(cpus)) != len(cpus) or any(cpu < 0 for cpu in cpus):
        raise argparse.ArgumentTypeError("CPU set is empty, duplicate, or negative")
    return cpus


def _parser() -> argparse.ArgumentParser:
    parser = argparse.ArgumentParser(description=__doc__, allow_abbrev=False)
    parser.add_argument("command", choices=("acquire", "renew", "release"))
    parser.add_argument("--output-root", type=Path, required=True)
    parser.add_argument("--catalog", type=Path, action="append", required=True)
    parser.add_argument("--cpus", type=_parse_cpus, required=True)
    parser.add_argument("--ttl-seconds", type=float, default=DEFAULT_TTL_SECONDS)
    parser.add_argument("--min-host-available-bytes", type=int,
                        default=DEFAULT_HOST_MEMORY_RESERVE_BYTES)
    parser.add_argument("--min-cgroup-available-bytes", type=int,
                        default=DEFAULT_CGROUP_MEMORY_RESERVE_BYTES)
    parser.add_argument("--max-host-psi-some-avg10", type=float,
                        default=DEFAULT_HOST_PSI_SOME_AVG10)
    parser.add_argument("--max-host-psi-full-avg10", type=float,
                        default=DEFAULT_HOST_PSI_FULL_AVG10)
    parser.add_argument("--max-cgroup-psi-some-avg10", type=float,
                        default=DEFAULT_CGROUP_PSI_SOME_AVG10)
    parser.add_argument("--max-cgroup-psi-full-avg10", type=float,
                        default=DEFAULT_CGROUP_PSI_FULL_AVG10)
    return parser


def main(argv: Sequence[str] | None = None) -> int:
    args = _parser().parse_args(argv)
    config = LeaseConfig(
        run_root=RUN_ROOT,
        output_root=args.output_root.resolve(strict=False),
        catalogs=tuple(sorted(
            (path.resolve(strict=True) for path in args.catalog), key=str,
        )),
        cpus=args.cpus,
        ttl_seconds=args.ttl_seconds,
        resource=resource_gate.ResourceGateConfig(
            proc_root=Path("/proc"), cgroup_mount=Path("/sys/fs/cgroup"),
            min_host_available_bytes=args.min_host_available_bytes,
            min_cgroup_available_bytes=args.min_cgroup_available_bytes,
            max_host_psi_some_avg10=args.max_host_psi_some_avg10,
            max_host_psi_full_avg10=args.max_host_psi_full_avg10,
            max_cgroup_psi_some_avg10=args.max_cgroup_psi_some_avg10,
            max_cgroup_psi_full_avg10=args.max_cgroup_psi_full_avg10,
        ),
    )
    try:
        if args.command == "acquire":
            result = acquire(config)
        elif args.command == "renew":
            result = renew(config)
        else:
            result = release(config)
    except (NativeLeaseError, resource_gate.ResourceGateError, OSError) as exc:
        print(f"ERROR: {exc}", file=sys.stderr)
        return 2
    print(_canonical(result).decode("ascii"))
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
