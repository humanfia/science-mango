"""Operate the Stage 2 exactification sidecar without touching pipeline state.

The module intentionally imports the scientific exactification implementation
only after native thread limits, CPU affinity and process priority are set.
"""

from __future__ import annotations

import argparse
import fcntl
import hashlib
import json
import math
import os
import re
import signal
import stat
import subprocess
import sys
import tempfile
import threading
import time
from dataclasses import dataclass, replace
from datetime import datetime, timezone
from pathlib import Path
from typing import Any, Callable, Mapping, Sequence


PROCESS_SCHEMA_VERSION = 1
PROCESS_KIND = "qcode-stage2-exactification-process"
SIDECAR_NAME = "stage2-exactification-v1"
_RUN_ID = re.compile(r"[A-Za-z0-9][A-Za-z0-9_.-]{0,127}")
_RECORD_LOCK = threading.Lock()


class ExactificationControlError(RuntimeError):
    """Invalid or unsafe sidecar process operation."""


class AlreadyRunningError(ExactificationControlError):
    """The sidecar lock is already held."""


class UnsafeProcessError(ExactificationControlError):
    """A process record cannot safely be signalled."""


class ResourceWait(ExactificationControlError):
    """The sidecar may not consume the reserved foreground capacity."""


@dataclass(frozen=True)
class ControlPaths:
    run_root: Path
    root: Path
    process: Path
    lock: Path
    log: Path


def _strict_int(value: Any, *, name: str) -> int:
    if isinstance(value, bool) or not isinstance(value, int):
        raise ValueError(f"{name} must be an integer")
    return value


def _strict_float(value: Any, *, name: str) -> float:
    if isinstance(value, bool) or not isinstance(value, (int, float)):
        raise ValueError(f"{name} must be numeric")
    result = float(value)
    if not math.isfinite(result):
        raise ValueError(f"{name} must be finite")
    return result


@dataclass(frozen=True)
class ResourcePolicy:
    solver_slots: int = 1
    reserve_foreground_cpus: int = 12
    nice: int = 15
    cpu_list: tuple[int, ...] | None = None
    heartbeat_s: float = 15.0
    capacity_poll_s: float = 30.0
    termination_grace_s: float = 180.0

    @classmethod
    def from_mapping(
        cls, value: Mapping[str, Any], *, overrides: argparse.Namespace | None = None
    ) -> "ResourcePolicy":
        raw = value.get("resources", {})
        if not isinstance(raw, Mapping):
            raise ValueError("config resources must be an object")
        cpu_value: Any = raw.get("cpu_list")
        if overrides is not None and getattr(overrides, "cpu_list", None) is not None:
            cpu_value = overrides.cpu_list
        cpu_list = parse_cpu_list(cpu_value) if cpu_value is not None else None
        nice_value = (
            getattr(overrides, "nice", None)
            if overrides is not None and getattr(overrides, "nice", None) is not None
            else raw.get("nice", 15)
        )
        policy = cls(
            solver_slots=_strict_int(raw.get("solver_slots", 1), name="solver_slots"),
            reserve_foreground_cpus=_strict_int(
                raw.get("reserve_foreground_cpus", 12),
                name="reserve_foreground_cpus",
            ),
            nice=_strict_int(nice_value, name="nice"),
            cpu_list=cpu_list,
            heartbeat_s=_strict_float(
                raw.get("heartbeat_s", 15.0), name="heartbeat_s"
            ),
            capacity_poll_s=_strict_float(
                raw.get("capacity_poll_s", 30.0), name="capacity_poll_s"
            ),
            termination_grace_s=_strict_float(
                raw.get("termination_grace_s", 180.0),
                name="termination_grace_s",
            ),
        )
        if policy.solver_slots != 1:
            raise ValueError("exactification sidecar currently requires solver_slots=1")
        if policy.reserve_foreground_cpus < 12:
            raise ValueError("reserve_foreground_cpus must be at least 12")
        if not 0 <= policy.nice <= 19:
            raise ValueError("nice must be between 0 and 19")
        for name, number in (
            ("heartbeat_s", policy.heartbeat_s),
            ("capacity_poll_s", policy.capacity_poll_s),
            ("termination_grace_s", policy.termination_grace_s),
        ):
            if number <= 0:
                raise ValueError(f"{name} must be positive")
        return policy

    def as_dict(self) -> dict[str, Any]:
        return {
            "solver_slots": self.solver_slots,
            "reserve_foreground_cpus": self.reserve_foreground_cpus,
            "nice": self.nice,
            "cpu_list": list(self.cpu_list) if self.cpu_list is not None else None,
            "heartbeat_s": self.heartbeat_s,
            "capacity_poll_s": self.capacity_poll_s,
            "termination_grace_s": self.termination_grace_s,
        }


def utc_now() -> str:
    return datetime.now(timezone.utc).isoformat()


def parse_cpu_list(value: Any) -> tuple[int, ...]:
    if isinstance(value, (list, tuple)):
        if any(isinstance(item, bool) or not isinstance(item, int) for item in value):
            raise ValueError("cpu_list entries must be integers")
        cpus = set(value)
    elif isinstance(value, str):
        cpus: set[int] = set()
        for part in value.split(","):
            part = part.strip()
            if not part:
                continue
            if "-" in part:
                lower_text, upper_text = part.split("-", 1)
                lower, upper = int(lower_text), int(upper_text)
                if upper < lower:
                    raise ValueError("invalid descending CPU range")
                cpus.update(range(lower, upper + 1))
            else:
                cpus.add(int(part))
    else:
        raise ValueError("cpu_list must be a list or cpuset string")
    if not cpus or min(cpus) < 0:
        raise ValueError("cpu_list must contain non-negative CPUs")
    return tuple(sorted(cpus))


def _validate_run_id(run_id: str) -> str:
    if not isinstance(run_id, str) or not _RUN_ID.fullmatch(run_id):
        raise ValueError("run_id contains unsafe characters")
    if run_id in {".", ".."}:
        raise ValueError("invalid run_id")
    return run_id


def _resolve_repo(repo_dir: Path) -> Path:
    repo = Path(repo_dir).expanduser().resolve(strict=True)
    if not repo.is_dir() or not (repo / "humanize").is_dir():
        raise ValueError(f"not a qcode-discovery repository: {repo}")
    return repo


def control_paths(repo_dir: Path, run_id: str, *, create: bool = False) -> ControlPaths:
    repo = _resolve_repo(repo_dir)
    safe_id = _validate_run_id(run_id)
    pipelines = repo / "results" / "humanize" / "pipelines"
    run_path = pipelines / safe_id
    run_root = run_path.resolve(strict=True)
    try:
        run_root.relative_to(pipelines.resolve(strict=True))
    except ValueError as exc:
        raise ValueError("pipeline run path escapes repository") from exc
    sidecars = run_root / "sidecars"
    root = sidecars / SIDECAR_NAME
    if create:
        if not sidecars.exists() and not sidecars.is_symlink():
            sidecars.mkdir(mode=0o700)
        if not root.exists() and not root.is_symlink():
            root.mkdir(mode=0o700)
    resolved = root.resolve(strict=create)
    try:
        resolved.relative_to(run_root)
    except ValueError as exc:
        raise ValueError("sidecar path escapes pipeline run") from exc
    return ControlPaths(
        run_root=run_root,
        root=resolved,
        process=resolved / "process.json",
        lock=resolved / "process.lock",
        log=resolved / "worker.log",
    )


def _canonical(value: Mapping[str, Any]) -> bytes:
    return json.dumps(
        value, ensure_ascii=False, sort_keys=True, separators=(",", ":"), allow_nan=False
    ).encode("utf-8")


def _record_hash(value: Mapping[str, Any]) -> str:
    unsigned = dict(value)
    unsigned.pop("process_record_sha256", None)
    return hashlib.sha256(_canonical(unsigned)).hexdigest()


def _atomic_write_json(path: Path, value: Mapping[str, Any]) -> None:
    path.parent.mkdir(parents=True, exist_ok=True)
    fd, temporary_name = tempfile.mkstemp(prefix=f".{path.name}.tmp-", dir=path.parent)
    temporary = Path(temporary_name)
    try:
        with os.fdopen(fd, "w", encoding="utf-8") as stream:
            json.dump(value, stream, ensure_ascii=False, indent=2, sort_keys=True, allow_nan=False)
            stream.write("\n")
            stream.flush()
            os.fsync(stream.fileno())
        os.chmod(temporary, 0o600)
        os.replace(temporary, path)
        directory_fd = os.open(path.parent, os.O_RDONLY | os.O_DIRECTORY)
        try:
            os.fsync(directory_fd)
        finally:
            os.close(directory_fd)
    finally:
        temporary.unlink(missing_ok=True)


def write_process_record(path: Path, value: Mapping[str, Any]) -> dict[str, Any]:
    record = dict(value)
    record["process_record_sha256"] = _record_hash(record)
    _atomic_write_json(path, record)
    return record


def read_process_record(path: Path) -> dict[str, Any] | None:
    if path.is_symlink():
        raise ExactificationControlError("process record may not be a symlink")
    if not path.is_file():
        return None
    if not stat.S_ISREG(path.stat().st_mode):
        raise ExactificationControlError("process record is not a regular file")
    try:
        value = json.loads(path.read_text(encoding="utf-8"))
    except (OSError, json.JSONDecodeError) as exc:
        raise ExactificationControlError(f"cannot read process record: {exc}") from exc
    if not isinstance(value, dict):
        raise ExactificationControlError("process record is not an object")
    if value.get("process_record_sha256") != _record_hash(value):
        raise ExactificationControlError("process record self-hash mismatch")
    if value.get("schema_version") != PROCESS_SCHEMA_VERSION or value.get("kind") != PROCESS_KIND:
        raise ExactificationControlError("unsupported process record")
    return value


def _update_record(path: Path, *, pid: int, starttime: int, **updates: Any) -> bool:
    with _RECORD_LOCK:
        record = read_process_record(path)
        if record is None:
            return False
        if record.get("pid") != pid or record.get("proc_starttime") != starttime:
            return False
        record.update(updates)
        record["updated_at"] = utc_now()
        write_process_record(path, record)
        return True


def _proc_identity(pid: int) -> dict[str, Any] | None:
    if not isinstance(pid, int) or isinstance(pid, bool) or pid <= 1:
        return None
    try:
        raw = Path(f"/proc/{pid}/stat").read_text(encoding="utf-8")
        right = raw.rfind(")")
        fields = raw[right + 2 :].split()
        if right < 0 or len(fields) < 20 or fields[0] == "Z":
            return None
        cmdline = Path(f"/proc/{pid}/cmdline").read_bytes()
        if not cmdline:
            return None
        return {
            "pid": pid,
            "proc_starttime": int(fields[19]),
            "pgid": int(fields[2]),
            "session_id": int(fields[3]),
            "uid": int(Path(f"/proc/{pid}").stat().st_uid),
            "cmdline_sha256": hashlib.sha256(cmdline).hexdigest(),
        }
    except (OSError, ValueError, IndexError):
        return None


def process_matches(
    record: Mapping[str, Any],
    *,
    identity_reader: Callable[[int], dict[str, Any] | None] = _proc_identity,
) -> tuple[bool, str]:
    try:
        pid = int(record["pid"])
        identity = identity_reader(pid)
    except (KeyError, TypeError, ValueError):
        return False, "missing process identity"
    if identity is None:
        return False, "process is not running"
    for field in ("proc_starttime", "pgid", "session_id", "uid", "cmdline_sha256"):
        if identity.get(field) != record.get(field):
            return False, f"process identity mismatch: {field}"
    return True, "process identity matches"


def _acquire_lock(path: Path) -> int:
    path.parent.mkdir(parents=True, exist_ok=True)
    fd = os.open(path, os.O_RDWR | os.O_CREAT | getattr(os, "O_NOFOLLOW", 0), 0o600)
    try:
        if not stat.S_ISREG(os.fstat(fd).st_mode):
            raise ExactificationControlError("sidecar lock is not a regular file")
        fcntl.flock(fd, fcntl.LOCK_EX | fcntl.LOCK_NB)
    except BlockingIOError as exc:
        os.close(fd)
        raise AlreadyRunningError("exactification sidecar lock is held") from exc
    except BaseException:
        os.close(fd)
        raise
    return fd


def _validate_lock(fd: int, path: Path) -> None:
    descriptor, target = os.fstat(fd), path.stat()
    if descriptor.st_dev != target.st_dev or descriptor.st_ino != target.st_ino:
        raise ExactificationControlError("inherited descriptor is not the sidecar lock")


def _load_config(path: Path) -> tuple[dict[str, Any], str, Path]:
    resolved = Path(path).expanduser().resolve(strict=True)
    raw = resolved.read_bytes()
    try:
        value = json.loads(raw)
    except json.JSONDecodeError as exc:
        raise ValueError(f"invalid exactification JSON config: {exc}") from exc
    if not isinstance(value, dict):
        raise ValueError("exactification config must be an object")
    return value, hashlib.sha256(raw).hexdigest(), resolved


def _solver_termination_grace(document: Mapping[str, Any]) -> float:
    queue = document.get("queue", document)
    if not isinstance(queue, Mapping):
        raise ValueError("config queue must be an object")
    value = _strict_float(
        queue.get("termination_grace_s", 120.0),
        name="queue termination_grace_s",
    )
    if value <= 0:
        raise ValueError("queue termination_grace_s must be positive")
    return value


def _native_thread_limits() -> None:
    for name in (
        "OMP_NUM_THREADS",
        "OPENBLAS_NUM_THREADS",
        "MKL_NUM_THREADS",
        "NUMEXPR_NUM_THREADS",
        "VECLIB_MAXIMUM_THREADS",
        "BLIS_NUM_THREADS",
        "NUMBA_NUM_THREADS",
        "GOTO_NUM_THREADS",
    ):
        os.environ[name] = "1"


def _selected_cpus(policy: ResourcePolicy) -> tuple[int, ...]:
    try:
        allowed = set(os.sched_getaffinity(0))
    except (AttributeError, OSError):
        allowed = set(range(os.cpu_count() or 1))
    selected = policy.cpu_list or (max(allowed),)
    if len(selected) != 1:
        raise ValueError("the sidecar must be pinned to exactly one CPU")
    if not set(selected).issubset(allowed):
        raise ValueError("cpu_list includes a CPU outside current affinity")
    return tuple(selected)


def _apply_resources(policy: ResourcePolicy, selected: tuple[int, ...]) -> None:
    _native_thread_limits()
    if hasattr(os, "sched_setaffinity"):
        os.sched_setaffinity(0, set(selected))
    if hasattr(os, "setpriority"):
        os.setpriority(os.PRIO_PROCESS, 0, policy.nice)
    elif policy.nice:
        os.nice(policy.nice)


_AUDIT_ENTRYPOINTS = (
    "scripts/audit_candidate_pool.py",
    "scripts/audit_direction_pool.py",
)


def _audit_entrypoint(argv: Sequence[str]) -> str | None:
    for value in argv:
        normalized = str(value).replace("\\", "/")
        for entrypoint in _AUDIT_ENTRYPOINTS:
            if normalized == entrypoint or normalized.endswith(f"/{entrypoint}"):
                return entrypoint
    return None


def _deduplicate_audit_pool_processes(processes: Sequence[Any]) -> list[Any]:
    """Mask duplicate multiprocessing argv without removing ancestry.

    Spawned ProcessPoolExecutor workers retain the audit script's exact argv.
    The legacy global budget scanner consequently treats every worker as
    another full campaign.  Only mask a record when an ancestor in the same
    process group has the same audit entrypoint, exact argv and cwd.  Keeping
    the record itself preserves descendant coverage for standalone SAT/MIP
    children.  Independent roots, differing commands and differing working
    directories remain fully counted.
    """

    by_pid = {int(record.pid): record for record in processes}
    masked: list[Any] = []
    for record in processes:
        entrypoint = _audit_entrypoint(record.argv)
        duplicate = False
        if entrypoint is not None:
            signature = (
                entrypoint,
                tuple(record.argv),
                record.cwd,
                int(record.pgid),
            )
            seen: set[int] = set()
            ancestor_pid = int(record.ppid)
            while ancestor_pid > 0 and ancestor_pid not in seen:
                seen.add(ancestor_pid)
                ancestor = by_pid.get(ancestor_pid)
                if ancestor is None:
                    break
                ancestor_entrypoint = _audit_entrypoint(ancestor.argv)
                ancestor_signature = (
                    ancestor_entrypoint,
                    tuple(ancestor.argv),
                    ancestor.cwd,
                    int(ancestor.pgid),
                )
                if ancestor.state != "Z" and ancestor_signature == signature:
                    duplicate = True
                    break
                ancestor_pid = int(ancestor.ppid)
        masked.append(replace(record, argv=()) if duplicate else record)
    return masked


def _capacity_lease(
    policy: ResourcePolicy, capacity_affinity: Sequence[int] | None = None
) -> Any:
    # This lightweight import does not initialize the scientific array stack.
    from evaluation.solver_budget import (
        _read_processes,
        acquire_solver_budget,
        detect_cpu_budget,
    )

    budget = detect_cpu_budget(affinity=capacity_affinity)
    processes = _deduplicate_audit_pool_processes(_read_processes())
    lease = acquire_solver_budget(
        policy.solver_slots,
        cpu_budget=budget,
        processes=processes,
        current_pid=os.getpid(),
    )
    free_before = (
        budget.capacity
        - lease.cooperative_slots_before
        - lease.unmanaged_usage.workers
    )
    if free_before - policy.solver_slots < policy.reserve_foreground_cpus:
        lease.release()
        raise ResourceWait(
            "RESOURCE_WAIT: exactification would reduce foreground reserve below "
            f"{policy.reserve_foreground_cpus} CPUs (capacity={budget.capacity}, "
            f"available_before={free_before})"
        )
    return lease


class _Heartbeat:
    def __init__(self, path: Path, identity: Mapping[str, Any], interval: float):
        self.path = path
        self.pid = int(identity["pid"])
        self.starttime = int(identity["proc_starttime"])
        self.interval = interval
        self.stop_event = threading.Event()
        self.thread = threading.Thread(target=self._run, daemon=True)

    def _run(self) -> None:
        while not self.stop_event.wait(self.interval):
            _update_record(
                self.path,
                pid=self.pid,
                starttime=self.starttime,
                heartbeat_at=utc_now(),
            )

    def start(self) -> None:
        self.thread.start()

    def stop(self) -> None:
        self.stop_event.set()
        self.thread.join(timeout=min(2.0, self.interval + 0.1))


def _source_kwargs(args: argparse.Namespace, paths: ControlPaths) -> dict[str, Any]:
    if args.ledger_path is None and args.stage2_state_dir is None:
        return {}
    if args.ledger_path is None or args.stage2_state_dir is None:
        raise ValueError("--ledger-path and --stage2-state-dir must be supplied together")
    ledger_input = Path(args.ledger_path).expanduser()
    state_input = Path(args.stage2_state_dir).expanduser()
    if ledger_input.is_symlink() or state_input.is_symlink():
        raise ValueError("Stage 2 source paths may not be symlinks")
    ledger = ledger_input.resolve(strict=True)
    stage2_state = state_input.resolve(strict=True)
    if not ledger.is_file() or not stage2_state.is_dir():
        raise ValueError("Stage 2 ledger/state sources have the wrong type")
    for source in (ledger, stage2_state):
        try:
            source.relative_to(paths.run_root)
        except ValueError as exc:
            raise ValueError("Stage 2 source path escapes the pipeline run") from exc
    return {
        "ledger_path": ledger,
        "stage2_state_dir": stage2_state,
        "run_root": paths.run_root,
    }


def _run_scientific(
    *,
    args: argparse.Namespace,
    paths: ControlPaths,
    config_document: Mapping[str, Any],
    once: bool,
    stop_event: threading.Event,
) -> dict[str, Any]:
    # Deliberately lazy: resources are already constrained before this import.
    from . import exactification_queue as core

    config = core.QueueConfig.from_json(config_document).validate()
    queue = core.queue_paths(paths.run_root)
    source = _source_kwargs(args, paths)

    def refresh_callback() -> dict[str, Any] | None:
        if not source:
            return None
        return core.refresh_queue(config=config, **source)

    if source and not queue.queue.is_file():
        refresh_callback()
    return core.worker_loop(
        paths=queue,
        config=config,
        once=once,
        refresh_callback=refresh_callback if source else None,
        stop_event=stop_event,
    )


def _execute_worker(
    *,
    args: argparse.Namespace,
    paths: ControlPaths,
    lock_fd: int,
    isolated: bool,
    start_fd: int | None = None,
) -> dict[str, Any]:
    _validate_lock(lock_fd, paths.lock)
    if start_fd is not None:
        try:
            if os.read(start_fd, 1) != b"1":
                raise ExactificationControlError("parent launch barrier failed")
        finally:
            os.close(start_fd)
    config_document, config_sha, config_path = _load_config(args.config)
    if isolated:
        starting = read_process_record(paths.process)
        if starting is None or starting.get("config_sha256") != config_sha:
            raise ExactificationControlError("worker config differs from launch record")
    policy = ResourcePolicy.from_mapping(config_document, overrides=args)
    _native_thread_limits()
    try:
        capacity_affinity = tuple(os.sched_getaffinity(0))
    except (AttributeError, OSError):
        capacity_affinity = tuple(range(os.cpu_count() or 1))
    selected = _selected_cpus(policy)
    identity = _proc_identity(os.getpid())
    if identity is None:
        raise ExactificationControlError("cannot establish worker identity")
    now = utc_now()
    record = {
        "schema_version": PROCESS_SCHEMA_VERSION,
        "kind": PROCESS_KIND,
        "run_id": args.run_id,
        "repo_dir": str(_resolve_repo(args.repo_dir)),
        "sidecar_root": str(paths.root),
        "status": "capacity-check",
        **identity,
        "isolated_session": isolated,
        "config_path": str(config_path),
        "config_sha256": config_sha,
        "command": list(sys.argv),
        "resources": {**policy.as_dict(), "selected_cpus": list(selected)},
        "solver_termination_grace_s": _solver_termination_grace(config_document),
        "started_at": (starting.get("started_at") if isolated else now),
        "heartbeat_at": now,
        "updated_at": now,
    }
    write_process_record(paths.process, record)
    heartbeat = _Heartbeat(paths.process, identity, policy.heartbeat_s)
    heartbeat.start()
    stop_event = threading.Event()

    def request_stop(_signum: int, _frame: Any) -> None:
        stop_event.set()

    previous_term = signal.signal(signal.SIGTERM, request_stop)
    previous_hup = signal.signal(signal.SIGHUP, signal.SIG_IGN) if isolated else None
    lease = None
    try:
        while not stop_event.is_set():
            try:
                lease = _capacity_lease(policy, capacity_affinity)
            except Exception as exc:
                from evaluation.solver_budget import SolverBudgetError

                if not isinstance(exc, (ResourceWait, SolverBudgetError)):
                    raise
                _update_record(
                    paths.process,
                    pid=identity["pid"],
                    starttime=identity["proc_starttime"],
                    status="RESOURCE_WAIT",
                    resource_wait_reason=str(exc),
                )
                if args.once:
                    result = {"status": "RESOURCE_WAIT", "reason": str(exc)}
                    _update_record(
                        paths.process,
                        pid=identity["pid"],
                        starttime=identity["proc_starttime"],
                        status="RESOURCE_WAIT",
                        finished_at=utc_now(),
                    )
                    return result
                stop_event.wait(policy.capacity_poll_s)
                continue
            _apply_resources(policy, selected)
            _update_record(
                paths.process,
                pid=identity["pid"],
                starttime=identity["proc_starttime"],
                status="running",
                resource_wait_reason=None,
            )
            result = _run_scientific(
                args=args,
                paths=paths,
                config_document=config_document,
                once=True,
                stop_event=stop_event,
            )
            lease.release()
            lease = None
            normalized = result if isinstance(result, dict) else {"status": "completed"}
            if args.once or stop_event.is_set():
                terminal = "cancelled" if stop_event.is_set() else "completed"
                _update_record(
                    paths.process,
                    pid=identity["pid"],
                    starttime=identity["proc_starttime"],
                    status=terminal,
                    result_status=normalized.get("status"),
                    finished_at=utc_now(),
                )
                return normalized
            _update_record(
                paths.process,
                pid=identity["pid"],
                starttime=identity["proc_starttime"],
                status="idle",
                result_status=normalized.get("status"),
            )
            stop_event.wait(policy.capacity_poll_s)
        result = {"status": "cancelled"}
        _update_record(
            paths.process,
            pid=identity["pid"],
            starttime=identity["proc_starttime"],
            status="cancelled",
            finished_at=utc_now(),
        )
        return result
    except BaseException as exc:
        _update_record(
            paths.process,
            pid=identity["pid"],
            starttime=identity["proc_starttime"],
            status="failed",
            error=f"{type(exc).__name__}: {exc}",
            finished_at=utc_now(),
        )
        raise
    finally:
        if lease is not None:
            lease.release()
        heartbeat.stop()
        signal.signal(signal.SIGTERM, previous_term)
        if isolated and previous_hup is not None:
            signal.signal(signal.SIGHUP, previous_hup)


def start_background(args: argparse.Namespace, paths: ControlPaths) -> dict[str, Any]:
    config_document, config_sha, config_path = _load_config(args.config)
    policy = ResourcePolicy.from_mapping(config_document, overrides=args)
    lock_fd = _acquire_lock(paths.lock)
    read_fd = write_fd = log_fd = -1
    process: subprocess.Popen[Any] | None = None
    try:
        read_fd, write_fd = os.pipe()
        command = [
            str(Path(args.python_executable).expanduser()),
            "-m",
            "humanize.exactification_cli",
            "_worker",
            "--repo-dir",
            str(_resolve_repo(args.repo_dir)),
            "--run-id",
            args.run_id,
            "--config",
            str(config_path),
            "--lock-fd",
            str(lock_fd),
            "--start-fd",
            str(read_fd),
        ]
        if args.once:
            command.append("--once")
        if args.ledger_path is not None:
            command.extend(["--ledger-path", str(args.ledger_path)])
        if args.stage2_state_dir is not None:
            command.extend(["--stage2-state-dir", str(args.stage2_state_dir)])
        if args.cpu_list is not None:
            command.extend(["--cpu-list", args.cpu_list])
        if args.nice is not None:
            command.extend(["--nice", str(args.nice)])
        log_fd = os.open(
            paths.log,
            os.O_WRONLY | os.O_CREAT | os.O_APPEND | getattr(os, "O_NOFOLLOW", 0),
            0o600,
        )
        process = subprocess.Popen(
            command,
            cwd=_resolve_repo(args.repo_dir),
            stdin=subprocess.DEVNULL,
            stdout=log_fd,
            stderr=subprocess.STDOUT,
            close_fds=True,
            pass_fds=(lock_fd, read_fd),
            start_new_session=True,
            shell=False,
        )
        os.close(read_fd)
        read_fd = -1
        identity = None
        for _ in range(100):
            identity = _proc_identity(process.pid)
            if identity is not None or process.poll() is not None:
                break
            time.sleep(0.01)
        if identity is None:
            raise ExactificationControlError("detached worker exited before identity capture")
        if identity["pgid"] != process.pid or identity["session_id"] != process.pid:
            raise ExactificationControlError("detached worker did not create an isolated session")
        now = utc_now()
        record = write_process_record(
            paths.process,
            {
                "schema_version": PROCESS_SCHEMA_VERSION,
                "kind": PROCESS_KIND,
                "run_id": args.run_id,
                "repo_dir": str(_resolve_repo(args.repo_dir)),
                "sidecar_root": str(paths.root),
                "status": "starting",
                **identity,
                "isolated_session": True,
                "config_path": str(config_path),
                "config_sha256": config_sha,
                "command": command,
                "resources": policy.as_dict(),
                "solver_termination_grace_s": _solver_termination_grace(config_document),
                "started_at": now,
                "heartbeat_at": now,
                "updated_at": now,
            },
        )
        os.write(write_fd, b"1")
        os.close(write_fd)
        write_fd = -1
        os.close(lock_fd)
        lock_fd = -1
        return record
    except BaseException:
        if process is not None and process.poll() is None:
            process.terminate()
            try:
                process.wait(timeout=2.0)
            except subprocess.TimeoutExpired:
                process.kill()
                process.wait(timeout=2.0)
        raise
    finally:
        for fd in (read_fd, write_fd, log_fd, lock_fd):
            if fd >= 0:
                try:
                    os.close(fd)
                except OSError:
                    pass


def _status(args: argparse.Namespace, paths: ControlPaths) -> dict[str, Any]:
    record = read_process_record(paths.process)
    if record is None:
        alive, reason = False, "no process record"
    else:
        alive, reason = process_matches(record)
    _native_thread_limits()
    from . import exactification_queue as core

    queue_paths = core.queue_paths(paths.run_root)
    queue_exists = queue_paths.queue.is_file()
    if queue_exists:
        queue = core.queue_status(queue_paths)
    else:
        queue = {"status": "not-started", "queue_path": str(queue_paths.queue)}
    stored_status = record.get("status") if record else None
    if alive:
        operational_status = stored_status or "running"
    elif stored_status in {"completed", "failed", "cancelled", "termination-pending", "RESOURCE_WAIT"}:
        operational_status = stored_status
    else:
        operational_status = "idle" if queue_exists else "not-started"
    return {
        "schema_version": PROCESS_SCHEMA_VERSION,
        "run_id": args.run_id,
        "status": operational_status,
        "alive": alive,
        "identity_reason": reason,
        "process": record,
        "queue": queue,
        "paths": {"root": str(paths.root), "process": str(paths.process), "log": str(paths.log)},
    }


def _session_group_members(*, pgid: int, session_id: int, uid: int) -> list[int]:
    """Return live same-uid members of the exact recorded session/group."""
    members: list[int] = []
    for entry in Path("/proc").iterdir():
        if not entry.name.isdigit():
            continue
        try:
            raw = (entry / "stat").read_text(encoding="utf-8")
            right = raw.rfind(")")
            fields = raw[right + 2 :].split()
            if (
                right >= 0
                and len(fields) >= 4
                and fields[0] != "Z"
                and int(fields[2]) == pgid
                and int(fields[3]) == session_id
                and entry.stat().st_uid == uid
            ):
                members.append(int(entry.name))
        except (OSError, ValueError, IndexError):
            continue
    return members


def cancel_worker(
    args: argparse.Namespace,
    paths: ControlPaths,
    *,
    identity_reader: Callable[[int], dict[str, Any] | None] = _proc_identity,
    kill_group: Callable[[int, int], None] = os.killpg,
    group_members_reader: Callable[..., list[int]] = _session_group_members,
) -> dict[str, Any]:
    record = read_process_record(paths.process)
    if record is None:
        raise UnsafeProcessError("no process record; refusing to signal")
    expected_repo = str(_resolve_repo(args.repo_dir))
    if record.get("run_id") != args.run_id or record.get("repo_dir") != expected_repo:
        raise UnsafeProcessError("process record belongs to another run")
    alive, reason = process_matches(record, identity_reader=identity_reader)
    if not alive:
        raise UnsafeProcessError(f"refusing to signal: {reason}")
    pid, pgid, session_id = int(record["pid"]), int(record["pgid"]), int(record["session_id"])
    if record.get("isolated_session") is not True or pgid != pid or session_id != pid:
        raise UnsafeProcessError("record does not identify an isolated worker session")
    resources = record.get("resources")
    configured_grace = _strict_float(
        resources.get("termination_grace_s", 120.0)
        if isinstance(resources, Mapping)
        else 120.0,
        name="recorded process termination grace",
    )
    solver_grace = _strict_float(
        record.get("solver_termination_grace_s", 120.0),
        name="recorded solver termination grace",
    )
    grace_seconds = _strict_float(args.grace_seconds, name="cancel grace")
    if grace_seconds < max(120.0, configured_grace, solver_grace):
        raise ValueError("cancel grace must cover the solver termination grace")

    uid = int(record["uid"])

    def group_stopped() -> bool:
        leader_alive = process_matches(record, identity_reader=identity_reader)[0]
        members = group_members_reader(pgid=pgid, session_id=session_id, uid=uid)
        return not leader_alive and not members

    kill_group(pgid, signal.SIGTERM)
    deadline = time.monotonic() + grace_seconds
    while time.monotonic() < deadline and not group_stopped():
        time.sleep(0.1)
    stopped = group_stopped()
    forced = False
    if not stopped:
        members = group_members_reader(pgid=pgid, session_id=session_id, uid=uid)
        leader_alive = process_matches(record, identity_reader=identity_reader)[0]
        if members or leader_alive:
            kill_group(pgid, signal.SIGKILL)
            forced = True
            deadline = time.monotonic() + 2.0
            while time.monotonic() < deadline and not group_stopped():
                time.sleep(0.1)
        stopped = group_stopped()
    _update_record(
        paths.process,
        pid=pid,
        starttime=int(record["proc_starttime"]),
        status="cancelled" if stopped else "termination-pending",
        finished_at=utc_now() if stopped else None,
    )
    return {"status": "cancelled" if stopped else "termination-pending", "stopped": stopped, "forced": forced, "pid": pid}


def _default_repo() -> Path:
    return Path(__file__).resolve().parent.parent


def _common(parser: argparse.ArgumentParser, *, config: bool = False) -> None:
    parser.add_argument("--repo-dir", type=Path, default=_default_repo())
    parser.add_argument("--run-id", required=True)
    if config:
        parser.add_argument("--config", type=Path, required=True)


def _sources(parser: argparse.ArgumentParser) -> None:
    parser.add_argument("--ledger-path", type=Path)
    parser.add_argument("--stage2-state-dir", type=Path)


def _resources(parser: argparse.ArgumentParser) -> None:
    parser.add_argument("--cpu-list")
    parser.add_argument("--nice", type=int)


def build_parser() -> argparse.ArgumentParser:
    parser = argparse.ArgumentParser(description=__doc__)
    subs = parser.add_subparsers(dest="command", required=True)
    refresh = subs.add_parser("refresh")
    _common(refresh, config=True)
    _sources(refresh)
    run = subs.add_parser("run")
    _common(run, config=True)
    _sources(run)
    _resources(run)
    run.set_defaults(once=True)
    start = subs.add_parser("start")
    _common(start, config=True)
    _sources(start)
    _resources(start)
    start.add_argument("--python-executable", default=sys.executable)
    start.add_argument("--once", action="store_true")
    status = subs.add_parser("status")
    _common(status)
    cancel = subs.add_parser("cancel")
    _common(cancel)
    cancel.add_argument("--grace-seconds", type=float, default=180.0)
    worker = subs.add_parser("_worker", help=argparse.SUPPRESS)
    _common(worker, config=True)
    _sources(worker)
    _resources(worker)
    worker.add_argument("--lock-fd", type=int, required=True)
    worker.add_argument("--start-fd", type=int, required=True)
    worker.add_argument("--once", action="store_true")
    return parser


def _print(value: Any, *, stream: Any = sys.stdout) -> None:
    print(json.dumps(value, ensure_ascii=False, indent=2, default=str), file=stream, flush=True)


def _refresh(args: argparse.Namespace, paths: ControlPaths) -> dict[str, Any]:
    if args.ledger_path is None or args.stage2_state_dir is None:
        raise ValueError("refresh requires --ledger-path and --stage2-state-dir")
    document, _, _ = _load_config(args.config)
    _native_thread_limits()
    from . import exactification_queue as core

    config = core.QueueConfig.from_json(document).validate()
    result = core.refresh_queue(config=config, **_source_kwargs(args, paths))
    core.validate_queue(core.queue_paths(paths.run_root).queue)
    return result


def main(argv: Sequence[str] | None = None) -> int:
    try:
        args = build_parser().parse_args(argv)
        create = args.command in {"refresh", "run", "start", "_worker"}
        paths = control_paths(args.repo_dir, args.run_id, create=create)
        if args.command == "refresh":
            result = _refresh(args, paths)
        elif args.command == "run":
            lock_fd = _acquire_lock(paths.lock)
            try:
                result = _execute_worker(args=args, paths=paths, lock_fd=lock_fd, isolated=False)
            finally:
                os.close(lock_fd)
        elif args.command == "start":
            record = start_background(args, paths)
            result = {"status": record["status"], "pid": record["pid"], "process": str(paths.process), "log": str(paths.log)}
        elif args.command == "status":
            result = _status(args, paths)
        elif args.command == "cancel":
            if args.grace_seconds < 0:
                raise ValueError("grace-seconds must be non-negative")
            result = cancel_worker(args, paths)
        elif args.command == "_worker":
            result = _execute_worker(
                args=args,
                paths=paths,
                lock_fd=args.lock_fd,
                isolated=True,
                start_fd=args.start_fd,
            )
        else:
            raise AssertionError(args.command)
        _print(result)
        return 0
    except KeyboardInterrupt:
        _print({"status": "interrupted"}, stream=sys.stderr)
        return 130
    except (AlreadyRunningError, ExactificationControlError, OSError, ValueError) as exc:
        _print({"status": "error", "error": f"{type(exc).__name__}: {exc}"}, stream=sys.stderr)
        return 2


if __name__ == "__main__":
    raise SystemExit(main())
