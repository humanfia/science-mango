#!/usr/bin/env python3
"""Audited sidecar supervisor for recursive Paper400 timeout splitting.

The legacy campaign roots are immutable evidence.  This sidecar never resumes
their supervisors and never deletes their unverified files.  It can:

* bind one live, uncheckpointed legacy generation to a hardness-only CPU-time
  audit;
* publish an exact complementary 2/4/8-way cover and durable queue;
* checkpoint that one legacy leaf through its frozen runner only after the
  audit/bundle is durable;
* start new isolated recursive child roots on scheduler-level CPU leases;
* renew leases, fresh-verify final child proofs, and aggregate exact siblings.

CPU reservations are deliberately described as scheduler leases, not hardware
isolation: existing proof checkers may have broad kernel affinity.  A lease is
still useful to prevent this sidecar from dispatching two recursive children to
the same selected CPU.
"""

from __future__ import annotations

import argparse
import contextlib
import fcntl
import hashlib
import json
import os
import stat
import subprocess
import sys
import time
import uuid
from collections.abc import Iterator, Mapping, Sequence
from pathlib import Path
from typing import Any


PROJECT = Path(__file__).resolve().parent.parent
if str(PROJECT) not in sys.path:
    sys.path.insert(0, str(PROJECT))

from investigations import paper400_dic5_recursive_split_v1 as recursive
from scripts import run_paper400_dic5_recursive_child_resume_proof_v1 as child_runner


SCHEMA_VERSION = 1
GATE = "paper400-dic5-recursive-split-supervisor-v1"
BUNDLE_KIND = "paper400-dic5-recursive-split-bundle-v1"
CPU_CATALOG_KIND = "paper400-dic5-recursive-cpu-lease-catalog-v1"
CPU_RESERVATION_KIND = "paper400-dic5-recursive-cpu-reservation-v1"
WORKER_RECORD_KIND = "paper400-dic5-recursive-child-worker-v1"
PARENT_CHECKPOINT_KIND = "paper400-dic5-recursive-parent-checkpoint-v1"
PARENT_AGGREGATE_KIND = "paper400-dic5-recursive-parent-aggregate-v1"

RUNS = Path("/home/jing/paper400-runs")
CONTROL_ROOT = RUNS / ".paper400-recursive-split-v1"
LEGACY_PROJECT = Path("/home/jing/science-mango-r4/qcode-discovery")
LEGACY_RUNNER = LEGACY_PROJECT / "scripts/run_paper400_dic5_nested_width10_child_resume_proof_v1.py"
LEGACY_RUNNER_SHA256 = (
    "f1d0b162d3ef90a1eb608a3ce3306eb7c2aa9188947624c357e32d90a59b49ca"
)
LEGACY_PYTHON = PROJECT / ".venv/bin/python"
MAX_JSON_BYTES = 256 << 20
MAX_DIMACS_BYTES = 1 << 30
DEFAULT_POLL_SECONDS = 60.0
RENEW_BEFORE_SECONDS = 24 * 60 * 60
LEASE_SECONDS = recursive.QUEUE_MAX_LEASE_SECONDS

PARENT_DIMACS = Path("parent.cnf")
PARENT_AUDIT = Path("parent-audit.json")
SPLIT_MANIFEST = Path("split-manifest.json")
QUEUE = Path("queue.json")
CPU_RESERVATION = Path("cpu-reservation.json")
BUNDLE_COMMIT = Path("BUNDLE.json")
PARENT_CHECKPOINT = Path("parent-checkpoint.json")
PARENT_AGGREGATE = Path("parent-aggregate.json")
WORKERS_DIR = Path("workers")
CHILDREN_DIR = Path("children")
CATALOG = Path("cpu-leases.json")
CATALOG_LOCK = Path("cpu-leases.lock")


class RecursiveSplitSupervisorError(RuntimeError):
    """An audit, lease, legacy transition, or child dispatch check failed."""


def canonical_bytes(value: Any) -> bytes:
    return recursive.canonical_bytes(value)


def seal(value: Mapping[str, Any], field: str = "record_sha256") -> dict[str, Any]:
    return recursive.seal(value, field)


def _same(left: Any, right: Any) -> bool:
    return canonical_bytes(left) == canonical_bytes(right)


def _identity(info: os.stat_result) -> tuple[int, ...]:
    return (
        int(info.st_dev), int(info.st_ino), int(info.st_mode), int(info.st_uid),
        int(info.st_nlink), int(info.st_size), int(info.st_mtime_ns),
        int(info.st_ctime_ns),
    )


def _safe_directory(path: Path, *, require_mode_0700: bool = False) -> Path:
    target = Path(path)
    if not target.is_absolute() or str(target) != os.path.abspath(str(target)):
        raise RecursiveSplitSupervisorError("directory path must be absolute and normalized")
    try:
        info = target.lstat()
        resolved = target.resolve(strict=True)
    except (OSError, RuntimeError) as exc:
        raise RecursiveSplitSupervisorError(f"directory is unavailable: {target}") from exc
    if (
        resolved != target or stat.S_ISLNK(info.st_mode) or not stat.S_ISDIR(info.st_mode)
        or info.st_uid != os.geteuid()
        or (require_mode_0700 and stat.S_IMODE(info.st_mode) != 0o700)
    ):
        raise RecursiveSplitSupervisorError(f"directory is unsafe: {target}")
    return target


def _root_identity(root: Path) -> dict[str, Any]:
    info = root.lstat()
    return {
        "path": str(root), "device": int(info.st_dev), "inode": int(info.st_ino),
        "mode": int(stat.S_IMODE(info.st_mode)), "uid": int(info.st_uid),
    }


def _stable_bytes(path: Path, *, cap: int, executable: bool | None = None) -> bytes:
    target = Path(path)
    try:
        lexical = target.lstat()
        resolved = target.resolve(strict=True)
    except (OSError, RuntimeError) as exc:
        raise RecursiveSplitSupervisorError(f"cannot resolve file: {target}") from exc
    if (
        resolved != target or stat.S_ISLNK(lexical.st_mode) or not stat.S_ISREG(lexical.st_mode)
        or lexical.st_uid != os.geteuid() or lexical.st_nlink != 1 or lexical.st_size > cap
        or (executable is True and not (lexical.st_mode & stat.S_IXUSR))
        or (executable is False and (lexical.st_mode & stat.S_IXUSR))
    ):
        raise RecursiveSplitSupervisorError(f"unsafe file: {target}")
    fd = os.open(target, os.O_RDONLY | os.O_CLOEXEC | os.O_NOFOLLOW)
    chunks: list[bytes] = []
    size = 0
    try:
        before = os.fstat(fd)
        if _identity(before) != _identity(lexical):
            raise RecursiveSplitSupervisorError("file changed before read")
        while True:
            chunk = os.read(fd, min(8 << 20, cap + 1 - size))
            if not chunk:
                break
            size += len(chunk)
            if size > cap:
                raise RecursiveSplitSupervisorError("file exceeds cap")
            chunks.append(chunk)
        after = os.fstat(fd)
    finally:
        os.close(fd)
    if _identity(before) != _identity(after) or size != before.st_size:
        raise RecursiveSplitSupervisorError("file changed during read")
    return b"".join(chunks)


def _json_pairs(pairs: list[tuple[str, Any]]) -> dict[str, Any]:
    result: dict[str, Any] = {}
    for key, value in pairs:
        if key in result:
            raise RecursiveSplitSupervisorError("JSON has duplicate key")
        result[key] = value
    return result


def _read_json(path: Path, *, cap: int = MAX_JSON_BYTES) -> dict[str, Any]:
    payload = _stable_bytes(path, cap=cap, executable=False)
    try:
        value = json.loads(payload, object_pairs_hook=_json_pairs)
    except (UnicodeDecodeError, json.JSONDecodeError) as exc:
        raise RecursiveSplitSupervisorError(f"invalid JSON: {path}") from exc
    if type(value) is not dict or payload not in {canonical_bytes(value), canonical_bytes(value) + b"\n"}:
        raise RecursiveSplitSupervisorError(f"noncanonical JSON: {path}")
    return value


def _write_all(fd: int, payload: bytes) -> None:
    view = memoryview(payload)
    while view:
        count = os.write(fd, view)
        if count <= 0:
            raise RecursiveSplitSupervisorError("short file write")
        view = view[count:]


def _fsync_dir(path: Path) -> None:
    fd = os.open(path, os.O_RDONLY | os.O_DIRECTORY | os.O_CLOEXEC | os.O_NOFOLLOW)
    try:
        os.fsync(fd)
    finally:
        os.close(fd)


def _publish_new(path: Path, payload: bytes) -> None:
    if path.exists() or path.is_symlink():
        raise RecursiveSplitSupervisorError(f"immutable target exists: {path}")
    temporary = path.parent / f".{path.name}.private-{uuid.uuid4().hex}"
    fd = os.open(temporary, os.O_WRONLY | os.O_CREAT | os.O_EXCL | os.O_CLOEXEC | os.O_NOFOLLOW, 0o600)
    linked = False
    try:
        _write_all(fd, payload)
        os.fsync(fd)
        os.close(fd)
        fd = -1
        os.link(temporary, path, follow_symlinks=False)
        linked = True
        _fsync_dir(path.parent)
    except FileExistsError as exc:
        raise RecursiveSplitSupervisorError(f"immutable target exists: {path}") from exc
    finally:
        if fd >= 0:
            os.close(fd)
        with contextlib.suppress(FileNotFoundError):
            temporary.unlink()
        if linked:
            _fsync_dir(path.parent)


def _publish_json(path: Path, value: Mapping[str, Any]) -> None:
    _publish_new(path, canonical_bytes(dict(value)) + b"\n")


def _atomic_rewrite(path: Path, payload: bytes) -> None:
    temporary = path.parent / f".{path.name}.replace-{os.getpid()}-{uuid.uuid4().hex}"
    fd = os.open(temporary, os.O_WRONLY | os.O_CREAT | os.O_EXCL | os.O_CLOEXEC | os.O_NOFOLLOW, 0o600)
    try:
        _write_all(fd, payload)
        os.fsync(fd)
    finally:
        os.close(fd)
    os.replace(temporary, path)
    _fsync_dir(path.parent)


def _ensure_control_root(root: Path = CONTROL_ROOT) -> Path:
    target = Path(root)
    if target.exists():
        return _safe_directory(target, require_mode_0700=True)
    parent = _safe_directory(target.parent)
    try:
        os.mkdir(target, 0o700)
        _fsync_dir(parent)
    except FileExistsError:
        pass
    return _safe_directory(target, require_mode_0700=True)


@contextlib.contextmanager
def _catalog_lock(control_root: Path) -> Iterator[None]:
    lock = control_root / CATALOG_LOCK
    fd = os.open(lock, os.O_RDWR | os.O_CREAT | os.O_CLOEXEC | os.O_NOFOLLOW, 0o600)
    try:
        info = os.fstat(fd)
        if (
            not stat.S_ISREG(info.st_mode) or info.st_uid != os.geteuid()
            or info.st_nlink != 1 or stat.S_IMODE(info.st_mode) != 0o600
        ):
            raise RecursiveSplitSupervisorError("CPU catalog lock is unsafe")
        fcntl.flock(fd, fcntl.LOCK_EX)
        yield
    finally:
        with contextlib.suppress(OSError):
            fcntl.flock(fd, fcntl.LOCK_UN)
        os.close(fd)


def _new_catalog() -> dict[str, Any]:
    return seal({
        "schema_version": SCHEMA_VERSION,
        "kind": CPU_CATALOG_KIND,
        "leases": [],
        "updated_at": time.time(),
    }, "catalog_sha256")


def _load_catalog(control_root: Path) -> dict[str, Any]:
    path = control_root / CATALOG
    if not path.exists():
        return _new_catalog()
    value = _read_json(path)
    if (
        set(value) != {"schema_version", "kind", "leases", "updated_at", "catalog_sha256"}
        or not recursive.selfhash_valid(value, "catalog_sha256")
        or value.get("schema_version") != SCHEMA_VERSION or value.get("kind") != CPU_CATALOG_KIND
        or type(value.get("leases")) is not list
        or type(value.get("updated_at")) not in {int, float}
    ):
        raise RecursiveSplitSupervisorError("CPU catalog is malformed")
    seen: set[int] = set()
    for entry in value["leases"]:
        if (
            type(entry) is not dict
            or set(entry) != {"cpu", "bundle", "reservation_sha256", "state", "created_at", "released_at"}
            or type(entry.get("cpu")) is not int or entry["cpu"] < 0
            or entry["cpu"] in seen or type(entry.get("bundle")) is not str
            or not recursive.is_sha256(entry.get("reservation_sha256"))
            or entry.get("state") not in {"RESERVED", "RELEASED"}
            or type(entry.get("created_at")) not in {int, float}
            or (entry.get("released_at") is not None and type(entry.get("released_at")) not in {int, float})
        ):
            raise RecursiveSplitSupervisorError("CPU catalog lease is malformed")
        seen.add(entry["cpu"])
    return value


def _store_catalog(control_root: Path, catalog: Mapping[str, Any]) -> dict[str, Any]:
    value = dict(catalog)
    value.pop("catalog_sha256", None)
    value["updated_at"] = time.time()
    sealed = seal(value, "catalog_sha256")
    _atomic_rewrite(control_root / CATALOG, canonical_bytes(sealed) + b"\n")
    return sealed


def _proc_cpu_observation(cpu: int) -> dict[str, Any]:
    """Capture the non-isolation caveat and current singleton CPU occupants."""

    pinned: list[dict[str, Any]] = []
    broad: list[int] = []
    for proc in Path("/proc").iterdir():
        if not proc.name.isdecimal():
            continue
        try:
            status = (proc / "status").read_text(encoding="ascii")
            state_line = next(line for line in status.splitlines() if line.startswith("State:"))
            state = state_line.split()[1]
            allowed = next(line.split(":", 1)[1].strip() for line in status.splitlines() if line.startswith("Cpus_allowed_list:"))
            if state not in {"R", "D"}:
                continue
            if allowed == str(cpu):
                command = (proc / "comm").read_text(encoding="utf-8", errors="replace").strip()
                pinned.append({"pid": int(proc.name), "state": state, "command": command})
            elif "-" in allowed or "," in allowed:
                broad.append(int(proc.name))
        except (OSError, StopIteration, IndexError):
            continue
    return {
        "cpu": cpu,
        "pinned_running_processes": pinned,
        "broad_affinity_running_process_count": len(broad),
        "kernel_hardware_exclusive": False,
        "lease_scope": "recursive-sidecar-dispatch-only",
    }


def _validate_cpu_pool(cpus: Sequence[int]) -> tuple[list[int], list[dict[str, Any]]]:
    pool = list(cpus)
    if (
        type(cpus) not in {list, tuple} or len(pool) not in recursive.SUPPORTED_FANOUTS
        or any(type(cpu) is not int or cpu < 0 for cpu in pool)
        or pool != sorted(set(pool))
    ):
        raise RecursiveSplitSupervisorError("CPU pool must be sorted unique and have fanout 2/4/8")
    allowed = os.sched_getaffinity(0)
    if any(cpu not in allowed for cpu in pool):
        raise RecursiveSplitSupervisorError("requested CPU is outside supervisor affinity")
    observations = [_proc_cpu_observation(cpu) for cpu in pool]
    busy = [value for value in observations if value["pinned_running_processes"]]
    if busy:
        raise RecursiveSplitSupervisorError(f"requested CPU already has pinned running work: {busy}")
    return pool, observations


def _reserve_cpus(control_root: Path, *, bundle: Path, cpus: Sequence[int], observations: Sequence[Mapping[str, Any]]) -> dict[str, Any]:
    reservation = seal({
        "schema_version": SCHEMA_VERSION,
        "kind": CPU_RESERVATION_KIND,
        "bundle": str(bundle),
        "cpus": list(cpus),
        "observations": [dict(value) for value in observations],
        "kernel_hardware_exclusive": False,
        "scheduler_lease_only": True,
        "created_at": time.time(),
    }, "reservation_sha256")
    with _catalog_lock(control_root):
        catalog = _load_catalog(control_root)
        occupied = {item["cpu"] for item in catalog["leases"] if item["state"] == "RESERVED"}
        conflict = sorted(occupied.intersection(cpus))
        if conflict:
            raise RecursiveSplitSupervisorError(f"CPU lease already reserved: {conflict}")
        unsigned = dict(catalog)
        unsigned.pop("catalog_sha256")
        unsigned["leases"] = [
            *unsigned["leases"],
            *[
                {
                    "cpu": cpu, "bundle": str(bundle),
                    "reservation_sha256": reservation["reservation_sha256"],
                    "state": "RESERVED", "created_at": reservation["created_at"],
                    "released_at": None,
                }
                for cpu in cpus
            ],
        ]
        _store_catalog(control_root, unsigned)
    return reservation


def _release_cpus(control_root: Path, reservation: Mapping[str, Any]) -> None:
    with _catalog_lock(control_root):
        catalog = _load_catalog(control_root)
        changed = False
        leases: list[dict[str, Any]] = []
        for item in catalog["leases"]:
            value = dict(item)
            if (
                value["reservation_sha256"] == reservation["reservation_sha256"]
                and value["state"] == "RESERVED"
            ):
                value["state"] = "RELEASED"
                value["released_at"] = time.time()
                changed = True
            leases.append(value)
        if changed:
            unsigned = dict(catalog)
            unsigned.pop("catalog_sha256")
            unsigned["leases"] = leases
            _store_catalog(control_root, unsigned)


def _legacy_source_binding() -> dict[str, Any]:
    payload = _stable_bytes(LEGACY_RUNNER, cap=32 << 20, executable=False)
    digest = hashlib.sha256(payload).hexdigest()
    if digest != LEGACY_RUNNER_SHA256:
        raise RecursiveSplitSupervisorError("legacy runner source is not frozen revision")
    sources = {
        "supervisor": {
            "path": str(Path(__file__).resolve(strict=True)),
            "sha256": hashlib.sha256(_stable_bytes(Path(__file__).resolve(strict=True), cap=32 << 20, executable=False)).hexdigest(),
        },
        "recursive_split": {
            "path": str(Path(recursive.__file__).resolve(strict=True)),
            "sha256": hashlib.sha256(_stable_bytes(Path(recursive.__file__).resolve(strict=True), cap=32 << 20, executable=False)).hexdigest(),
        },
        "recursive_child_runner": {
            "path": str(Path(child_runner.__file__).resolve(strict=True)),
            "sha256": hashlib.sha256(_stable_bytes(Path(child_runner.__file__).resolve(strict=True), cap=32 << 20, executable=False)).hexdigest(),
        },
        "legacy_runner": {"path": str(LEGACY_RUNNER), "sha256": digest},
    }
    return {
        "method": "exact-source-sha256-replay-v1",
        "sources": sources,
        "source_sequence_sha256": recursive.canonical_sha256(sources),
    }


def _read_proc_identity(pid: int) -> dict[str, Any]:
    observation = recursive.observe_proc_cpu_seconds(pid)
    if observation["state"] == "Z":
        raise RecursiveSplitSupervisorError("legacy solver is a zombie")
    return observation


def _legacy_controller_status(root: Path) -> dict[str, Any]:
    with child_runner._clean_controller_environment():
        return child_runner.controller.inspect(root / "runtime/dmtcp", verify_hashes=False)


def _unlocked_legacy_root(root: Path) -> None:
    lock = root / ".hierarchical-resume.lock"
    fd = os.open(lock, os.O_RDWR | os.O_CLOEXEC | os.O_NOFOLLOW)
    try:
        info = os.fstat(fd)
        if (
            not stat.S_ISREG(info.st_mode) or info.st_uid != os.geteuid()
            or info.st_nlink != 1 or stat.S_IMODE(info.st_mode) != 0o600
        ):
            raise RecursiveSplitSupervisorError("legacy root lock metadata is unsafe")
        try:
            fcntl.flock(fd, fcntl.LOCK_EX | fcntl.LOCK_NB)
        except BlockingIOError as exc:
            raise RecursiveSplitSupervisorError("legacy root is busy; defer split audit") from exc
        fcntl.flock(fd, fcntl.LOCK_UN)
    finally:
        os.close(fd)


def _legacy_terminal_absent(root: Path) -> None:
    terminal = [
        root / "COMMIT.json", root / "certificate.json", root / "validation.json",
        root / "state/20-proof-harvest.claim",
    ]
    present = [str(path.relative_to(root)) for path in terminal if path.exists()]
    if present:
        raise RecursiveSplitSupervisorError(f"legacy root has terminal evidence/claim: {present}")


def _legacy_parent_material(root: Path) -> tuple[dict[str, Any], dict[str, Any], bytes, dict[str, Any], dict[str, Any]]:
    static = _read_json(root / "state/00-resume-static.json")
    session = _read_json(root / "state/11-session.json")
    if (
        not recursive.selfhash_valid(static, "record_sha256")
        or not recursive.selfhash_valid(session, "record_sha256")
        or static.get("state") != "RESUMABLE_STATIC_SEALED"
        or session.get("state") != "RUNNING"
        or static.get("root") != str(root) or session.get("root") != str(root)
    ):
        raise RecursiveSplitSupervisorError("legacy static/session record is malformed")
    child = static.get("child")
    if type(child) is not dict or type(child.get("child_id")) is not str:
        raise RecursiveSplitSupervisorError("legacy static child binding is malformed")
    payload = _stable_bytes(root / "static/cube.cnf", cap=MAX_DIMACS_BYTES, executable=False)
    if (
        hashlib.sha256(payload).hexdigest() != child.get("child_dimacs_sha256")
        or len(payload) != child.get("child_dimacs_bytes")
    ):
        raise RecursiveSplitSupervisorError("legacy parent DIMACS hash mismatch")
    status = _legacy_controller_status(root)
    if status.get("state") != "RUNNING":
        raise RecursiveSplitSupervisorError(f"legacy root is not a running generation: {status.get('state')}")
    generations = status.get("generations")
    if type(generations) is not list or len(generations) != 1 or type(generations[0]) is not dict:
        raise RecursiveSplitSupervisorError("legacy root is not an uncheckpointed single generation")
    generation = generations[0]
    if (
        generation.get("generation") != 0 or generation.get("active_kind") != "start.commit"
        or generation.get("checkpointed") is not False or generation.get("pid_identity_alive") is not True
        or generation.get("active_manifest_sha256") != session.get("controller_start_sha256")
    ):
        raise RecursiveSplitSupervisorError("legacy generation has checkpoint/resume ambiguity")
    active = child_runner.controller._active_commit(
        child_runner.controller._generation_dir(root / "runtime/dmtcp", 0), 0,
    )
    if active.get("self_sha256") != generation.get("active_manifest_sha256"):
        raise RecursiveSplitSupervisorError("legacy controller summary/active commit mismatch")
    pid = active.get("pid")
    ticks = active.get("proc_start_ticks")
    if type(pid) is not int or type(ticks) is not int:
        raise RecursiveSplitSupervisorError("legacy generation PID identity is malformed")
    proc = _read_proc_identity(pid)
    if proc["proc_start_ticks"] != ticks or proc["state"] not in {"R", "D"}:
        raise RecursiveSplitSupervisorError("legacy live process identity/state changed")
    return static, session, payload, status, proc


def audit_parent(root: Path, *, fanout: int) -> tuple[dict[str, Any], dict[str, Any]]:
    """Read one legacy parent into a hardness-only, current-generation audit."""

    target = _safe_directory(root, require_mode_0700=True)
    if fanout not in recursive.SUPPORTED_FANOUTS:
        raise RecursiveSplitSupervisorError("fanout must be 2, 4, or 8")
    _unlocked_legacy_root(target)
    _legacy_terminal_absent(target)
    static, session, parent_payload, status, proc = _legacy_parent_material(target)
    child = static["child"]
    # The legacy root has exactly one never-checkpointed generation.  Under
    # that narrow condition /proc utime+stime is the complete current solver
    # CPU counter, rather than a checkpoint-spanning or PID-reused estimate.
    ledger = recursive.new_timing_ledger(child["child_id"])
    ledger = recursive.update_timing_ledger(ledger, {
        "state": "RUNNING", "generation": 0, "pid": proc["pid"],
        "proc_start_ticks": proc["proc_start_ticks"],
        "cpu_seconds": proc["cpu_seconds"], "observed_monotonic": time.monotonic(),
        "baseline": True,
    })
    if not recursive.timeout_reached(ledger):
        raise RecursiveSplitSupervisorError("legacy parent is below the 12-hour solver CPU threshold")
    evidence = recursive.build_timeout_evidence(ledger, observed_state="RUNNING")
    parent_id = f"{child['child_id']}-g000000"
    manifest, _payloads = recursive.split_plan(
        parent_payload, parent_id=parent_id, fanout=fanout, ledger=ledger,
        observed_state="RUNNING", ancestry_sha256=static["record_sha256"],
    )
    trigger = manifest.get("trigger")
    if type(trigger) is not dict:
        raise RecursiveSplitSupervisorError("recursive split manifest omitted timeout trigger")
    audit = seal({
        "schema_version": SCHEMA_VERSION,
        "kind": child_runner.PARENT_AUDIT_KIND,
        "parent_root": str(target),
        "parent_root_identity": _root_identity(target),
        "parent_static_sha256": static["record_sha256"],
        "parent_session_sha256": session["record_sha256"],
        "parent_dimacs_sha256": hashlib.sha256(parent_payload).hexdigest(),
        "parent_dimacs_bytes": len(parent_payload),
        "parent_generation": 0,
        "parent_pid": proc["pid"],
        "parent_proc_start_ticks": proc["proc_start_ticks"],
        "observed_state": "RUNNING",
        "timing_ledger": ledger,
        "timing_evidence": evidence,
        "timing_trigger": trigger,
        "split_allowed": True,
        "hardness_only": True,
        "solver_terminal_claim": False,
        "source_binding": {
            **_legacy_source_binding(),
            "admission_method": "single-uncheckpointed-generation-proc-cpu-counter-baseline-v1",
            "controller_status_sha256": recursive.canonical_sha256(status),
            "proc_cpu_counter_adopted": True,
        },
    }, "audit_sha256")
    child_runner._validate_parent_audit(audit)
    return audit, manifest


def _bundle_value(bundle: Path, audit: Mapping[str, Any], manifest: Mapping[str, Any], reservation: Mapping[str, Any], queue: Mapping[str, Any]) -> dict[str, Any]:
    return seal({
        "schema_version": SCHEMA_VERSION,
        "kind": BUNDLE_KIND,
        "gate": GATE,
        "bundle_root": str(bundle),
        "bundle_root_identity": _root_identity(bundle),
        "parent_audit_sha256": audit["audit_sha256"],
        "split_manifest_sha256": manifest["manifest_sha256"],
        "cpu_reservation_sha256": reservation["reservation_sha256"],
        "queue_sha256": queue["queue_sha256"],
        "fanout": manifest["split_policy"]["fanout"],
        "source_binding": _legacy_source_binding(),
        "hardness_only": True,
        "parent_solver_terminal_claim": False,
        "global_distance_claim": None,
        "publication_certificate": False,
        "upload_authorized": False,
    }, "bundle_sha256")


def create_bundle(
    bundle: Path, *, parent_root: Path, cpus: Sequence[int],
    control_root: Path = CONTROL_ROOT,
) -> dict[str, Any]:
    """Publish all pre-checkpoint material and reserve scheduler CPU slots."""

    control = _ensure_control_root(control_root)
    target = Path(bundle)
    if not target.is_absolute() or str(target) != os.path.abspath(str(target)):
        raise RecursiveSplitSupervisorError("bundle path must be absolute and normalized")
    if target.exists() or target.is_symlink():
        raise RecursiveSplitSupervisorError("bundle path already exists")
    if target.parent != control:
        raise RecursiveSplitSupervisorError("bundle must be a direct child of the control root")
    pool, observations = _validate_cpu_pool(cpus)
    audit, manifest = audit_parent(parent_root, fanout=len(pool))
    reservation = _reserve_cpus(control, bundle=target, cpus=pool, observations=observations)
    try:
        os.mkdir(target, 0o700)
        _fsync_dir(control)
        for name in (WORKERS_DIR.name, CHILDREN_DIR.name):
            os.mkdir(target / name, 0o700)
        _publish_new(target / PARENT_DIMACS, _stable_bytes(parent_root / "static/cube.cnf", cap=MAX_DIMACS_BYTES, executable=False))
        _publish_json(target / PARENT_AUDIT, audit)
        _publish_json(target / SPLIT_MANIFEST, manifest)
        _publish_json(target / CPU_RESERVATION, reservation)
        queue = recursive.create_split_queue(
            target / QUEUE, manifest, cpu_pool=pool,
            parent_manifest_sha256=audit["parent_static_sha256"],
            lease_seconds=LEASE_SECONDS,
        )
        bundle_value = _bundle_value(target, audit, manifest, reservation, queue)
        _publish_json(target / BUNDLE_COMMIT, bundle_value)
        _load_bundle(target, control_root=control)
        return bundle_value
    except BaseException:
        # The CPU reservation is only released if the bundle was not
        # committed; a committed bundle remains forensic/recoverable evidence.
        if not (target / BUNDLE_COMMIT).exists():
            _release_cpus(control, reservation)
        raise


def _load_bundle(bundle: Path, *, control_root: Path = CONTROL_ROOT) -> dict[str, Any]:
    target = _safe_directory(bundle, require_mode_0700=True)
    control = _safe_directory(control_root, require_mode_0700=True)
    if target.parent != control:
        raise RecursiveSplitSupervisorError("bundle is outside control root")
    value = _read_json(target / BUNDLE_COMMIT)
    fields = {
        "schema_version", "kind", "gate", "bundle_root", "bundle_root_identity",
        "parent_audit_sha256", "split_manifest_sha256", "cpu_reservation_sha256",
        "queue_sha256", "fanout", "source_binding", "hardness_only",
        "parent_solver_terminal_claim", "global_distance_claim",
        "publication_certificate", "upload_authorized", "bundle_sha256",
    }
    if (
        set(value) != fields or not recursive.selfhash_valid(value, "bundle_sha256")
        or value.get("schema_version") != SCHEMA_VERSION or value.get("kind") != BUNDLE_KIND
        or value.get("gate") != GATE or value.get("bundle_root") != str(target)
        or not _same(value.get("bundle_root_identity"), _root_identity(target))
        or value.get("hardness_only") is not True or value.get("parent_solver_terminal_claim") is not False
        or value.get("global_distance_claim") is not None or value.get("publication_certificate") is not False
        or value.get("upload_authorized") is not False or not _same(value.get("source_binding"), _legacy_source_binding())
    ):
        raise RecursiveSplitSupervisorError("recursive split bundle is malformed")
    audit = _read_json(target / PARENT_AUDIT)
    child_runner._validate_parent_audit(audit)
    manifest = _read_json(target / SPLIT_MANIFEST)
    parent = _stable_bytes(target / PARENT_DIMACS, cap=MAX_DIMACS_BYTES, executable=False)
    recursive.verify_cover(manifest, parent)
    reservation = _read_json(target / CPU_RESERVATION)
    if (
        not recursive.selfhash_valid(reservation, "reservation_sha256")
        or reservation.get("kind") != CPU_RESERVATION_KIND
        or reservation.get("bundle") != str(target)
        or reservation.get("kernel_hardware_exclusive") is not False
        or reservation.get("scheduler_lease_only") is not True
    ):
        raise RecursiveSplitSupervisorError("bundle CPU reservation is malformed")
    queue = recursive.load_split_queue(target / QUEUE)
    if (
        audit["audit_sha256"] != value["parent_audit_sha256"]
        or manifest["manifest_sha256"] != value["split_manifest_sha256"]
        or reservation["reservation_sha256"] != value["cpu_reservation_sha256"]
        or queue["queue_sha256"] != value["queue_sha256"]
        or manifest["split_policy"]["fanout"] != value["fanout"]
        or queue["split_manifest_sha256"] != manifest["manifest_sha256"]
    ):
        raise RecursiveSplitSupervisorError("bundle component binding mismatch")
    return {
        "bundle": value, "audit": audit, "manifest": manifest, "parent": parent,
        "reservation": reservation, "queue": queue, "root": target, "control_root": control,
    }


def _legacy_cli(action: str, root: Path, *, timeout: float = 600.0) -> dict[str, Any]:
    if action not in {"status", "checkpoint-stop", "verify-checkpoint", "prune-transport"}:
        raise RecursiveSplitSupervisorError("legacy action is not admitted")
    payload = _stable_bytes(LEGACY_RUNNER, cap=32 << 20, executable=False)
    if hashlib.sha256(payload).hexdigest() != LEGACY_RUNNER_SHA256:
        raise RecursiveSplitSupervisorError("legacy runner source changed")
    result = subprocess.run(
        [str(LEGACY_PYTHON), str(LEGACY_RUNNER), action, "--root", str(root)],
        stdin=subprocess.DEVNULL, stdout=subprocess.PIPE, stderr=subprocess.PIPE,
        timeout=timeout, check=False,
    )
    if result.returncode != 0:
        raise RecursiveSplitSupervisorError(
            f"legacy {action} failed rc={result.returncode}: {result.stderr.decode('utf-8', 'replace')[-2000:]}"
        )
    try:
        value = json.loads(result.stdout)
    except (UnicodeDecodeError, json.JSONDecodeError) as exc:
        raise RecursiveSplitSupervisorError("legacy action emitted invalid JSON") from exc
    if type(value) is not dict:
        raise RecursiveSplitSupervisorError("legacy action output is not an object")
    return {
        "action": action, "returncode": result.returncode,
        "stdout_sha256": hashlib.sha256(result.stdout).hexdigest(),
        "stderr_sha256": hashlib.sha256(result.stderr).hexdigest(),
        "result": value,
    }


def checkpoint_parent(bundle: Path, *, control_root: Path = CONTROL_ROOT) -> dict[str, Any]:
    """Checkpoint the audited legacy parent exactly once through frozen code."""

    loaded = _load_bundle(bundle, control_root=control_root)
    root = Path(loaded["audit"]["parent_root"])
    checkpoint_path = loaded["root"] / PARENT_CHECKPOINT
    if checkpoint_path.exists():
        value = _read_json(checkpoint_path)
        if not recursive.selfhash_valid(value, "record_sha256"):
            raise RecursiveSplitSupervisorError("stored parent checkpoint receipt is malformed")
        return value
    # Re-read the parent at the dispatch boundary.  Its CPU counter may have
    # advanced, but static/session/PID/start-tick must remain exactly audited.
    _unlocked_legacy_root(root)
    _legacy_terminal_absent(root)
    static, session, payload, _status, proc = _legacy_parent_material(root)
    audit = loaded["audit"]
    if (
        static["record_sha256"] != audit["parent_static_sha256"]
        or session["record_sha256"] != audit["parent_session_sha256"]
        or hashlib.sha256(payload).hexdigest() != audit["parent_dimacs_sha256"]
        or proc["pid"] != audit["parent_pid"]
        or proc["proc_start_ticks"] != audit["parent_proc_start_ticks"]
    ):
        raise RecursiveSplitSupervisorError("legacy parent identity changed after split audit")
    action = _legacy_cli("checkpoint-stop", root)
    status = _legacy_cli("status", root)
    if status["result"].get("state") != "CHECKPOINTED":
        raise RecursiveSplitSupervisorError("legacy parent did not reach CHECKPOINTED state")
    receipt = seal({
        "schema_version": SCHEMA_VERSION,
        "kind": PARENT_CHECKPOINT_KIND,
        "bundle_sha256": loaded["bundle"]["bundle_sha256"],
        "parent_root": str(root),
        "parent_static_sha256": audit["parent_static_sha256"],
        "parent_session_sha256": audit["parent_session_sha256"],
        "parent_pid": audit["parent_pid"],
        "parent_proc_start_ticks": audit["parent_proc_start_ticks"],
        "checkpoint_action": action,
        "status_after": status,
        "parent_state": "CHECKPOINTED",
        "hardness_only": True,
        "solver_terminal_claim": False,
    }, "record_sha256")
    _publish_json(checkpoint_path, receipt)
    return receipt


def _worker_path(bundle: Path, item_id: str, token: str) -> Path:
    safe = item_id.replace(":", "_")
    return bundle / WORKERS_DIR / f"{safe}-{token[:16]}.json"


def _worker_value(
    loaded: Mapping[str, Any], claim: Mapping[str, Any], *, child_root: Path,
    state: str, error: str | None = None,
) -> dict[str, Any]:
    item = claim["item"]
    return seal({
        "schema_version": SCHEMA_VERSION,
        "kind": WORKER_RECORD_KIND,
        "bundle_sha256": loaded["bundle"]["bundle_sha256"],
        "queue_sha256_at_claim": claim["queue_sha256"],
        "item_id": item["item_id"], "leaf_id": item["leaf_id"],
        "leaf_sha256": item["leaf_sha256"], "token": claim["claim"]["token"],
        "worker_id": claim["claim"]["worker_id"], "cpu_ids": claim["claim"]["cpu_ids"],
        "claim_expires_at": claim["claim"]["lease_expires_at"],
        "child_root": str(child_root), "state": state, "error": error,
        "created_at": time.time(),
    }, "worker_sha256")


def _worker_records(loaded: Mapping[str, Any]) -> list[tuple[Path, dict[str, Any]]]:
    root = loaded["root"] / WORKERS_DIR
    records: list[tuple[Path, dict[str, Any]]] = []
    for path in sorted(root.glob("*.json")):
        if path.name.endswith(".started.json") or path.name.endswith(".orphan.json"):
            # These immutable event receipts supplement the primary claim
            # record.  They are not independent queue workers.
            continue
        value = _read_json(path)
        fields = {
            "schema_version", "kind", "bundle_sha256", "queue_sha256_at_claim", "item_id",
            "leaf_id", "leaf_sha256", "token", "worker_id", "cpu_ids", "claim_expires_at",
            "child_root", "state", "error", "created_at", "worker_sha256",
        }
        if (
            set(value) != fields or not recursive.selfhash_valid(value, "worker_sha256")
            or value.get("schema_version") != SCHEMA_VERSION or value.get("kind") != WORKER_RECORD_KIND
            or value.get("bundle_sha256") != loaded["bundle"]["bundle_sha256"]
            or value.get("state") not in {"CLAIMED", "STARTED", "CERTIFIED", "ORPHAN_UNRESOLVED"}
            or type(value.get("child_root")) is not str or type(value.get("cpu_ids")) is not list
        ):
            raise RecursiveSplitSupervisorError("worker record is malformed")
        records.append((path, value))
    return records


def _legacy_parent_still_split_eligible(audit: Mapping[str, Any]) -> None:
    root = Path(audit["parent_root"])
    _legacy_terminal_absent(root)
    status = _legacy_cli("status", root)
    if status["result"].get("state") != "CHECKPOINTED":
        raise RecursiveSplitSupervisorError("parent stopped being checkpointed before child dispatch")


def dispatch_children(bundle: Path, *, control_root: Path = CONTROL_ROOT, worker_prefix: str | None = None) -> list[dict[str, Any]]:
    """Claim and start every unstarted child in one already-checkpointed bundle."""

    loaded = _load_bundle(bundle, control_root=control_root)
    if not (loaded["root"] / PARENT_CHECKPOINT).exists():
        raise RecursiveSplitSupervisorError("parent must be checkpointed before child dispatch")
    _legacy_parent_still_split_eligible(loaded["audit"])
    existing = {record[1]["item_id"] for record in _worker_records(loaded)}
    results: list[dict[str, Any]] = []
    prefix = worker_prefix or f"recursive-{os.uname().nodename}-{os.getpid()}"
    while True:
        claim = recursive.claim_queue_item(
            loaded["root"] / QUEUE, worker_id=prefix, lease_seconds=LEASE_SECONDS,
        )
        if claim is None:
            break
        item = claim["item"]
        if item["item_id"] in existing:
            raise RecursiveSplitSupervisorError("queue has duplicate durable worker record")
        child_root = loaded["root"] / CHILDREN_DIR / item["path"]
        initial = _worker_value(loaded, claim, child_root=child_root, state="CLAIMED")
        record_path = _worker_path(loaded["root"], item["item_id"], claim["claim"]["token"])
        _publish_json(record_path, initial)
        try:
            child_runner.prepare_root_from_material(
                child_root, parent_dimacs=loaded["parent"], split_manifest=loaded["manifest"],
                leaf_path=item["path"], parent_audit=loaded["audit"],
            )
            session = child_runner.start_root(child_root, cpu=item["cpu_ids"][0])
        except BaseException as exc:
            # A claimed record is intentionally retained.  If a start was
            # partly successful, automatic release could create a duplicate
            # live solver; recovery must inspect the recorded child root.
            orphan = _worker_value(
                loaded, claim, child_root=child_root, state="ORPHAN_UNRESOLVED",
                error=f"{type(exc).__name__}: {exc}",
            )
            _publish_json(record_path.with_name(record_path.stem + ".orphan.json"), orphan)
            raise
        results.append({"item_id": item["item_id"], "child_root": str(child_root), "session": session})
        existing.add(item["item_id"])
    return results


def _active_queue_item(queue: Mapping[str, Any], item_id: str) -> dict[str, Any] | None:
    items = queue.get("items")
    if type(items) is not list:
        return None
    return next((item for item in items if type(item) is dict and item.get("item_id") == item_id), None)


def tick_bundle(bundle: Path, *, control_root: Path = CONTROL_ROOT, verify_final: bool = True) -> dict[str, Any]:
    """Renew active work, certify final children, and aggregate exact siblings."""

    loaded = _load_bundle(bundle, control_root=control_root)
    queue_path = loaded["root"] / QUEUE
    records = _worker_records(loaded)
    actions: list[dict[str, Any]] = []
    now = time.time()
    for _path, record in records:
        queue = recursive.load_split_queue(queue_path)
        item = _active_queue_item(queue, record["item_id"])
        if item is None:
            raise RecursiveSplitSupervisorError("worker item disappeared from queue")
        if item["state"] == "CLAIMED":
            claim = item["claim"]
            if (
                type(claim) is not dict or claim.get("token") != record["token"]
                or claim.get("worker_id") != record["worker_id"]
            ):
                raise RecursiveSplitSupervisorError("worker claim token changed; refuse duplicate recovery")
            if claim["lease_expires_at"] - now < RENEW_BEFORE_SECONDS:
                queue = recursive.renew_queue_item(
                    queue_path, item_id=item["item_id"], worker_id=record["worker_id"],
                    token=record["token"], lease_seconds=LEASE_SECONDS,
                )
                item = _active_queue_item(queue, record["item_id"])
                actions.append({"item_id": record["item_id"], "action": "LEASE_RENEWED", "queue_sha256": queue["queue_sha256"]})
            status = child_runner.status_root(Path(record["child_root"]), verify_hashes=False)
            if status["state"] in {"PREPARED", "START_RECOVERY_REQUIRED"}:
                # A durable queue claim alone is never authorization to start
                # a solver after the legacy parent has become terminal.  This
                # also recovers the narrow controller-start/session-receipt
                # crash window without releasing or duplicating the claim.
                _legacy_parent_still_split_eligible(loaded["audit"])
                child_runner.start_root(
                    Path(record["child_root"]), cpu=record["cpu_ids"][0],
                )
                status = child_runner.status_root(Path(record["child_root"]), verify_hashes=False)
                actions.append({
                    "item_id": record["item_id"], "action": "START_RECOVERED",
                    "state": status["state"],
                })
            if status["state"] == "PROOF_CARRYING_CHILD_UNSAT":
                fresh = child_runner.verify_final_root(Path(record["child_root"])) if verify_final else _read_json(Path(record["child_root"]) / VALIDATION)
                certificate = _read_json(Path(record["child_root"]) / CERTIFICATE)
                recursive.certify_queue_item(
                    queue_path, item_id=item["item_id"], worker_id=record["worker_id"],
                    token=record["token"], certificate=certificate, validation=fresh,
                )
                actions.append({"item_id": record["item_id"], "action": "CERTIFIED", "certificate_sha256": certificate["certificate_sha256"]})
            else:
                actions.append({"item_id": record["item_id"], "action": "OBSERVED", "state": status["state"]})
        elif item["state"] == "CERTIFIED":
            actions.append({"item_id": record["item_id"], "action": "ALREADY_CERTIFIED"})
        elif item["state"] in {"PENDING", "FAILED"}:
            raise RecursiveSplitSupervisorError("durable worker record lost its live queue claim")
    status = recursive.split_queue_status(queue_path)
    aggregate: dict[str, Any] | None = None
    if status["status"] == recursive.QUEUE_STATUS_COMPLETE:
        paths = {record[1]["item_id"]: Path(record[1]["child_root"]) for record in records}
        certificates: list[dict[str, Any]] = []
        for item in recursive.load_split_queue(queue_path)["items"]:
            root = paths.get(item["item_id"])
            if root is None:
                raise RecursiveSplitSupervisorError("complete queue lacks a durable child root record")
            certificates.append(_read_json(root / CERTIFICATE))
        aggregate = recursive.aggregate_child_certificates(loaded["manifest"], certificates)
        if aggregate["status"] != "PARENT_CUBE_UNSAT":
            raise RecursiveSplitSupervisorError("complete queue did not aggregate to parent UNSAT")
        path = loaded["root"] / PARENT_AGGREGATE
        if path.exists():
            stored = _read_json(path)
            if not _same(stored, aggregate):
                raise RecursiveSplitSupervisorError("stored aggregate does not replay child certificates")
        else:
            record = seal({
                "schema_version": SCHEMA_VERSION, "kind": PARENT_AGGREGATE_KIND,
                "bundle_sha256": loaded["bundle"]["bundle_sha256"],
                "aggregate": aggregate, "aggregate_sha256": aggregate["aggregate_sha256"],
                "hardness_only": False, "parent_solver_terminal_claim": True,
                "global_distance_claim": None, "publication_certificate": False,
                "upload_authorized": False,
            }, "record_sha256")
            _publish_json(path, record)
        _release_cpus(loaded["control_root"], loaded["reservation"])
    return seal({
        "schema_version": SCHEMA_VERSION,
        "kind": "paper400-dic5-recursive-split-tick-v1",
        "bundle_sha256": loaded["bundle"]["bundle_sha256"],
        "queue_status": status, "actions": actions, "aggregate": aggregate,
        "complete": status["status"] == recursive.QUEUE_STATUS_COMPLETE,
    }, "record_sha256")


def build_parser() -> argparse.ArgumentParser:
    parser = argparse.ArgumentParser(description=__doc__, allow_abbrev=False)
    parser.add_argument("--control-root", type=Path, default=CONTROL_ROOT)
    sub = parser.add_subparsers(dest="action", required=True)
    audit = sub.add_parser("audit-parent", allow_abbrev=False)
    audit.add_argument("--parent-root", type=Path, required=True)
    audit.add_argument("--fanout", type=int, choices=recursive.SUPPORTED_FANOUTS, default=4)
    admit = sub.add_parser("create-bundle", allow_abbrev=False)
    admit.add_argument("--parent-root", type=Path, required=True)
    admit.add_argument("--bundle-name", required=True)
    admit.add_argument("--cpu", type=int, action="append", required=True)
    checkpoint = sub.add_parser("checkpoint-parent", allow_abbrev=False)
    checkpoint.add_argument("--bundle", type=Path, required=True)
    dispatch = sub.add_parser("dispatch", allow_abbrev=False)
    dispatch.add_argument("--bundle", type=Path, required=True)
    tick = sub.add_parser("tick", allow_abbrev=False)
    tick.add_argument("--bundle", type=Path, required=True)
    tick.add_argument("--skip-fresh-final-replay", action="store_true")
    loop = sub.add_parser("run-loop", allow_abbrev=False)
    loop.add_argument("--bundle", type=Path, required=True)
    loop.add_argument("--interval-seconds", type=float, default=DEFAULT_POLL_SECONDS)
    return parser


def main(argv: Sequence[str] | None = None) -> int:
    args = build_parser().parse_args(argv)
    control = Path(args.control_root)
    if args.action == "audit-parent":
        audit, manifest = audit_parent(args.parent_root, fanout=args.fanout)
        result: Mapping[str, Any] = {
            "audit": audit, "split_manifest": manifest,
            "hardness_only": True, "scientific_claim": False,
        }
    elif args.action == "create-bundle":
        if "/" in args.bundle_name or not args.bundle_name or args.bundle_name.startswith("."):
            raise RecursiveSplitSupervisorError("bundle name is not a safe direct-child name")
        result = create_bundle(control / args.bundle_name, parent_root=args.parent_root, cpus=args.cpu, control_root=control)
    elif args.action == "checkpoint-parent":
        result = checkpoint_parent(args.bundle, control_root=control)
    elif args.action == "dispatch":
        result = {"children": dispatch_children(args.bundle, control_root=control)}
    elif args.action == "tick":
        result = tick_bundle(args.bundle, control_root=control, verify_final=not args.skip_fresh_final_replay)
    elif args.action == "run-loop":
        if args.interval_seconds <= 0 or args.interval_seconds > 3600:
            raise RecursiveSplitSupervisorError("loop interval must be in (0, 3600]")
        while True:
            result = tick_bundle(args.bundle, control_root=control)
            sys.stdout.buffer.write(canonical_bytes(result) + b"\n")
            sys.stdout.buffer.flush()
            time.sleep(args.interval_seconds)
    else:  # pragma: no cover
        raise RecursiveSplitSupervisorError("unknown action")
    sys.stdout.buffer.write(canonical_bytes(result) + b"\n")
    sys.stdout.buffer.flush()
    return 0


if __name__ == "__main__":
    try:
        raise SystemExit(main())
    except (
        RecursiveSplitSupervisorError, recursive.RecursiveSplitError,
        child_runner.RecursiveChildRunnerError, OSError, subprocess.SubprocessError,
    ) as exc:
        print(f"ERROR: {exc}", file=sys.stderr)
        raise SystemExit(2)
