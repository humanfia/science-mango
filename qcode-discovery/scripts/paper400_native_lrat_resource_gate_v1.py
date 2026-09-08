#!/usr/bin/env python3
"""Fail-closed host/cgroup resource admission for native-LRAT pilots.

The module has no mutation or process-control authority.  Callers explicitly
provide the procfs and cgroup-v2 roots, which makes every test hermetic while
the launcher pins the real roots for non-test CLI execution.
"""

from __future__ import annotations

import hashlib
import json
import math
import os
import re
import stat
import time
from dataclasses import dataclass
from pathlib import Path
from typing import Any, Mapping, Sequence


SCHEMA_VERSION = 1
GATE = "paper400-native-lrat-resource-gate-v1"
SNAPSHOT_KIND = GATE + "-snapshot"
MAX_TEXT_BYTES = 4 << 20
MAX_PROC_ENTRIES = 1_000_000
CPU_LIST_RE = re.compile(r"[0-9]+(?:-[0-9]+)?(?:,[0-9]+(?:-[0-9]+)?)*\Z")
COMPUTE_NAMES = frozenset({
    "cadical", "lrat-check", "drat-trim", "gratgen", "gratchk",
})


class ResourceGateError(RuntimeError):
    """A resource observation could not establish safe admission."""


@dataclass(frozen=True)
class ResourceGateConfig:
    proc_root: Path
    cgroup_mount: Path
    min_host_available_bytes: int
    min_cgroup_available_bytes: int
    max_host_psi_some_avg10: float
    max_host_psi_full_avg10: float
    max_cgroup_psi_some_avg10: float
    max_cgroup_psi_full_avg10: float


def _canonical(value: Any) -> bytes:
    try:
        return json.dumps(
            value, sort_keys=True, separators=(",", ":"), ensure_ascii=True,
            allow_nan=False,
        ).encode("ascii")
    except (TypeError, ValueError, UnicodeEncodeError) as exc:
        raise ResourceGateError(f"non-canonical resource record: {exc}") from exc


def _seal(value: Mapping[str, Any]) -> dict[str, Any]:
    result = dict(value)
    result["record_sha256"] = hashlib.sha256(_canonical(result)).hexdigest()
    return result


def _normal_directory(path: Path, role: str) -> Path:
    if not path.is_absolute() or os.path.normpath(str(path)) != str(path):
        raise ResourceGateError(f"{role} is not an absolute normalized path")
    try:
        result = path.resolve(strict=True)
        info = result.stat()
    except OSError as exc:
        raise ResourceGateError(f"cannot resolve {role}") from exc
    if result != path or not stat.S_ISDIR(info.st_mode):
        raise ResourceGateError(f"{role} is not an exact directory")
    return result


def _read(path: Path, role: str, *, allow_missing: bool = False) -> str | None:
    flags = os.O_RDONLY | os.O_CLOEXEC | getattr(os, "O_NOFOLLOW", 0)
    try:
        fd = os.open(path, flags)
    except FileNotFoundError:
        if allow_missing:
            return None
        raise ResourceGateError(f"missing {role}")
    except OSError as exc:
        raise ResourceGateError(f"cannot open {role}") from exc
    try:
        before = os.fstat(fd)
        if not stat.S_ISREG(before.st_mode) or before.st_size > MAX_TEXT_BYTES:
            raise ResourceGateError(f"{role} is not a bounded regular file")
        chunks: list[bytes] = []
        total = 0
        while True:
            chunk = os.read(fd, min(1 << 16, MAX_TEXT_BYTES + 1 - total))
            if not chunk:
                break
            total += len(chunk)
            if total > MAX_TEXT_BYTES:
                raise ResourceGateError(f"{role} exceeds its size cap")
            chunks.append(chunk)
        after = os.fstat(fd)
        identity = lambda item: (
            item.st_dev, item.st_ino, item.st_mode, item.st_uid,
            item.st_size, item.st_mtime_ns, item.st_ctime_ns,
        )
        if identity(before) != identity(after):
            raise ResourceGateError(f"{role} changed while reading")
        return b"".join(chunks).decode("ascii")
    except UnicodeDecodeError as exc:
        raise ResourceGateError(f"{role} is not ASCII") from exc
    finally:
        os.close(fd)


def _parse_uint_fields(payload: str, role: str) -> dict[str, int]:
    result: dict[str, int] = {}
    for raw in payload.splitlines():
        fields = raw.split()
        key = fields[0].rstrip(":") if fields else ""
        if len(fields) < 2 or not fields[1].isdigit() or key in result:
            raise ResourceGateError(f"malformed {role}")
        result[key] = int(fields[1])
    return result


def _parse_psi(payload: str, role: str) -> dict[str, float]:
    result: dict[str, float] = {}
    for raw in payload.splitlines():
        fields = raw.split()
        if not fields or fields[0] not in {"some", "full"}:
            raise ResourceGateError(f"malformed {role}")
        values: dict[str, str] = {}
        for field in fields[1:]:
            if "=" not in field:
                raise ResourceGateError(f"malformed {role}")
            key, value = field.split("=", 1)
            values[key] = value
        try:
            avg10 = float(values["avg10"])
        except (KeyError, ValueError) as exc:
            raise ResourceGateError(f"malformed {role}") from exc
        if not math.isfinite(avg10) or avg10 < 0:
            raise ResourceGateError(f"malformed {role}")
        result[fields[0]] = avg10
    if set(result) != {"some", "full"}:
        raise ResourceGateError(f"incomplete {role}")
    return result


def _parse_cpu_list(value: str) -> set[int]:
    value = value.strip()
    if not value or CPU_LIST_RE.fullmatch(value) is None:
        raise ResourceGateError("malformed Cpus_allowed_list")
    result: set[int] = set()
    for item in value.split(","):
        if "-" in item:
            first_text, last_text = item.split("-", 1)
            first, last = int(first_text), int(last_text)
        else:
            first = last = int(item)
        if first > last or last > 1_048_575 or last - first > MAX_PROC_ENTRIES:
            raise ResourceGateError("invalid Cpus_allowed_list range")
        result.update(range(first, last + 1))
    return result


def _proc_stat(payload: str, pid: int) -> tuple[str, str, int]:
    left = payload.find("(")
    right = payload.rfind(")")
    if left <= 0 or right <= left or payload[:left].strip() != str(pid):
        raise ResourceGateError("malformed process stat")
    fields = payload[right + 1:].split()
    if len(fields) < 20 or len(fields[0]) != 1 or not fields[19].isdigit():
        raise ResourceGateError("malformed process stat")
    return payload[left + 1:right], fields[0], int(fields[19])


def _status_affinity(payload: str) -> set[int]:
    matches = [
        line.split(":", 1)[1].strip()
        for line in payload.splitlines()
        if line.startswith("Cpus_allowed_list:")
    ]
    if len(matches) != 1:
        raise ResourceGateError("process status lacks one Cpus_allowed_list")
    return _parse_cpu_list(matches[0])


def _cmdline_name(payload: str, comm: str) -> str:
    raw = payload.split("\0", 1)[0]
    return Path(raw).name if raw else comm


def _process_conflicts(
    proc_root: Path, cpus: set[int], owned: Mapping[int, int],
) -> tuple[list[dict[str, Any]], list[dict[str, Any]]]:
    conflicts: list[dict[str, Any]] = []
    races: list[dict[str, Any]] = []
    entries = list(proc_root.iterdir())
    if len(entries) > MAX_PROC_ENTRIES:
        raise ResourceGateError("procfs entry cap exceeded")
    for entry in entries:
        if not entry.name.isdigit():
            continue
        pid = int(entry.name)
        if pid == os.getpid():
            continue
        try:
            stat_payload = _read(entry / "stat", "process stat", allow_missing=True)
            if stat_payload is None:
                continue
            comm, state, start_ticks = _proc_stat(stat_payload, pid)
            if owned.get(pid) == start_ticks:
                continue
            if state in {"Z", "X", "x"}:
                continue
            status = _read(entry / "status", "process status", allow_missing=True)
            cmdline = _read(entry / "cmdline", "process cmdline", allow_missing=True)
            if status is None or cmdline is None:
                races.append({"pid": pid, "start_ticks": start_ticks})
                continue
            affinity = _status_affinity(status)
            overlap = sorted(affinity & cpus)
            if not overlap:
                continue
            command = _cmdline_name(cmdline, comm)
            pinned = affinity.issubset(cpus)
            known_compute = command in COMPUTE_NAMES or comm in COMPUTE_NAMES
            broad_running_compute = state in {"R", "D"} and known_compute
            if pinned or broad_running_compute:
                conflicts.append({
                    "pid": pid, "start_ticks": start_ticks, "state": state,
                    "command": command, "affinity": sorted(affinity),
                    "overlap": overlap, "pinned_to_requested_set": pinned,
                    "known_compute": known_compute,
                })
        except (FileNotFoundError, ProcessLookupError):
            continue
    return conflicts, races


def _self_cgroup(proc_root: Path, mount: Path) -> Path:
    payload = _read(proc_root / "self/cgroup", "self cgroup membership")
    assert payload is not None
    rows = [line.split(":", 2) for line in payload.splitlines()]
    unified = [row[2] for row in rows if len(row) == 3 and row[0] == "0" and row[1] == ""]
    if len(unified) != 1 or not unified[0].startswith("/"):
        raise ResourceGateError("cannot resolve one unified cgroup-v2 membership")
    components = Path(unified[0]).parts[1:]
    if any(item in {"", ".", ".."} for item in components):
        raise ResourceGateError("unsafe cgroup-v2 membership path")
    candidate = mount.joinpath(*components)
    resolved = _normal_directory(candidate, "current cgroup-v2 directory")
    try:
        resolved.relative_to(mount)
    except ValueError as exc:
        raise ResourceGateError("current cgroup escapes the cgroup-v2 mount") from exc
    return resolved


def _validate_config(config: ResourceGateConfig) -> ResourceGateConfig:
    proc_root = _normal_directory(config.proc_root, "procfs root")
    cgroup_mount = _normal_directory(config.cgroup_mount, "cgroup-v2 mount")
    for value, role in (
        (config.min_host_available_bytes, "host memory reserve"),
        (config.min_cgroup_available_bytes, "cgroup memory reserve"),
    ):
        if type(value) is not int or value < 0:
            raise ResourceGateError(f"invalid {role}")
    for value, role in (
        (config.max_host_psi_some_avg10, "host PSI some threshold"),
        (config.max_host_psi_full_avg10, "host PSI full threshold"),
        (config.max_cgroup_psi_some_avg10, "cgroup PSI some threshold"),
        (config.max_cgroup_psi_full_avg10, "cgroup PSI full threshold"),
    ):
        if type(value) not in {int, float} or not math.isfinite(float(value)) or value < 0:
            raise ResourceGateError(f"invalid {role}")
    return ResourceGateConfig(
        proc_root=proc_root, cgroup_mount=cgroup_mount,
        min_host_available_bytes=config.min_host_available_bytes,
        min_cgroup_available_bytes=config.min_cgroup_available_bytes,
        max_host_psi_some_avg10=float(config.max_host_psi_some_avg10),
        max_host_psi_full_avg10=float(config.max_host_psi_full_avg10),
        max_cgroup_psi_some_avg10=float(config.max_cgroup_psi_some_avg10),
        max_cgroup_psi_full_avg10=float(config.max_cgroup_psi_full_avg10),
    )


def snapshot(
    config: ResourceGateConfig, cpus: Sequence[int], *,
    owned_processes: Mapping[int, int] | None = None,
    baseline: Mapping[str, Any] | None = None,
) -> dict[str, Any]:
    """Observe and enforce CPU, memory, PSI and OOM invariants."""

    checked = _validate_config(config)
    owned_processes = {} if owned_processes is None else owned_processes
    if (
        not cpus or list(cpus) != sorted(cpus) or len(set(cpus)) != len(cpus)
        or any(type(cpu) is not int or cpu < 0 for cpu in cpus)
    ):
        raise ResourceGateError("requested CPU set is invalid")
    if any(type(pid) is not int or type(ticks) is not int or pid <= 0 or ticks <= 0
           for pid, ticks in owned_processes.items()):
        raise ResourceGateError("owned process identity map is invalid")
    conflicts, races = _process_conflicts(
        checked.proc_root, set(cpus), owned_processes,
    )

    meminfo_payload = _read(checked.proc_root / "meminfo", "host meminfo")
    vmstat_payload = _read(checked.proc_root / "vmstat", "host vmstat")
    host_psi_payload = _read(checked.proc_root / "pressure/memory", "host memory PSI")
    assert meminfo_payload is not None and vmstat_payload is not None
    assert host_psi_payload is not None
    meminfo = _parse_uint_fields(meminfo_payload, "host meminfo")
    vmstat = _parse_uint_fields(vmstat_payload, "host vmstat")
    if "MemAvailable" not in meminfo or "oom_kill" not in vmstat:
        raise ResourceGateError("host memory/OOM counters are incomplete")
    host_available = meminfo["MemAvailable"] * 1024
    host_psi = _parse_psi(host_psi_payload, "host memory PSI")

    cgroup = _self_cgroup(checked.proc_root, checked.cgroup_mount)
    current_text = _read(cgroup / "memory.current", "cgroup memory.current")
    maximum_text = _read(cgroup / "memory.max", "cgroup memory.max")
    events_text = _read(cgroup / "memory.events", "cgroup memory.events")
    cgroup_psi_text = _read(cgroup / "memory.pressure", "cgroup memory PSI")
    assert None not in {current_text, maximum_text, events_text, cgroup_psi_text}
    if not str(current_text).strip().isdigit():
        raise ResourceGateError("malformed cgroup memory.current")
    current = int(str(current_text).strip())
    maximum_raw = str(maximum_text).strip()
    if maximum_raw == "max":
        maximum: int | None = None
        cgroup_available: int | None = None
    elif maximum_raw.isdigit():
        maximum = int(maximum_raw)
        if current > maximum:
            raise ResourceGateError("cgroup memory.current exceeds memory.max")
        cgroup_available = maximum - current
    else:
        raise ResourceGateError("malformed cgroup memory.max")
    events = _parse_uint_fields(str(events_text), "cgroup memory.events")
    if not {"oom", "oom_kill"}.issubset(events):
        raise ResourceGateError("cgroup OOM counters are incomplete")
    cgroup_psi = _parse_psi(str(cgroup_psi_text), "cgroup memory PSI")

    blockers: list[str] = []
    if conflicts:
        blockers.append("live CPU conflict")
    if races:
        blockers.append("process scan race")
    if host_available < checked.min_host_available_bytes:
        blockers.append("host MemAvailable below reserve")
    if cgroup_available is not None and cgroup_available < checked.min_cgroup_available_bytes:
        blockers.append("cgroup memory headroom below reserve")
    if host_psi["some"] > checked.max_host_psi_some_avg10:
        blockers.append("host memory PSI some exceeds threshold")
    if host_psi["full"] > checked.max_host_psi_full_avg10:
        blockers.append("host memory PSI full exceeds threshold")
    if cgroup_psi["some"] > checked.max_cgroup_psi_some_avg10:
        blockers.append("cgroup memory PSI some exceeds threshold")
    if cgroup_psi["full"] > checked.max_cgroup_psi_full_avg10:
        blockers.append("cgroup memory PSI full exceeds threshold")
    if baseline is not None:
        try:
            prior_host_oom = baseline["host"]["oom_kill"]
            prior_cgroup_oom = baseline["cgroup"]["events"]["oom"]
            prior_cgroup_kill = baseline["cgroup"]["events"]["oom_kill"]
        except (KeyError, TypeError) as exc:
            raise ResourceGateError("resource baseline is malformed") from exc
        if vmstat["oom_kill"] != prior_host_oom:
            blockers.append("host oom_kill counter changed")
        if events["oom"] != prior_cgroup_oom:
            blockers.append("cgroup oom counter changed")
        if events["oom_kill"] != prior_cgroup_kill:
            blockers.append("cgroup oom_kill counter changed")

    value = _seal({
        "schema_version": SCHEMA_VERSION, "kind": SNAPSHOT_KIND,
        "observed_at": time.time(), "cpus": list(cpus),
        "owned_processes": [
            {"pid": pid, "start_ticks": ticks}
            for pid, ticks in sorted(owned_processes.items())
        ],
        "cpu_conflicts": conflicts, "process_scan_races": races,
        "host": {
            "mem_available_bytes": host_available,
            "oom_kill": vmstat["oom_kill"], "memory_psi_avg10": host_psi,
        },
        "cgroup": {
            "path": str(cgroup), "memory_current": current,
            "memory_max": maximum, "memory_available": cgroup_available,
            "events": {"oom": events["oom"], "oom_kill": events["oom_kill"]},
            "memory_psi_avg10": cgroup_psi,
        },
        "thresholds": {
            "min_host_available_bytes": checked.min_host_available_bytes,
            "min_cgroup_available_bytes": checked.min_cgroup_available_bytes,
            "max_host_psi_some_avg10": checked.max_host_psi_some_avg10,
            "max_host_psi_full_avg10": checked.max_host_psi_full_avg10,
            "max_cgroup_psi_some_avg10": checked.max_cgroup_psi_some_avg10,
            "max_cgroup_psi_full_avg10": checked.max_cgroup_psi_full_avg10,
        },
        "blockers": blockers, "go": not blockers,
        "mutation": False, "process_control": False,
    })
    if blockers:
        raise ResourceGateError("resource admission is NO-GO: " + "; ".join(blockers))
    return value
