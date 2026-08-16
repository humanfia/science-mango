"""Operate the isolated Stage-2 strict deep proof sidecar.

The control plane never mutates pipeline state.  Scientific imports are lazy so
native thread limits, process priority, capacity reservation and (optional) CPU
affinity are established before candidate reconstruction or SAT work begins.
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
from dataclasses import dataclass
from datetime import datetime, timezone
from pathlib import Path
from typing import Any, Callable, Mapping, Sequence

PROCESS_SCHEMA_VERSION = 1
PROCESS_KIND = "qcode-stage2-strict-deep-process"
SIDECAR_NAME = "stage2-strict-deep-v1"
EXPECTED_DIGESTS = (
    "9dc2d985f37c4e4d1a40c90eab49de8dc63b0f600944016c7fcb8a2692e84ab7",
    "5a1b12bcbe2a85fca6bfc77d1cbfe03a3bf539655f21f5f52c0befda2c4f1043",
)
_RUN_ID = re.compile(r"[A-Za-z0-9][A-Za-z0-9_.-]{0,127}")
_RECORD_LOCK = threading.Lock()

try:
    _SOURCE_SHA256 = hashlib.sha256(Path(__file__).read_bytes()).hexdigest()
except OSError:
    _SOURCE_SHA256 = None


class StrictDeepControlError(RuntimeError):
    """Invalid or unsafe strict-deep process operation."""


class AlreadyRunningError(StrictDeepControlError):
    """The strict-deep process lock is already held."""


class UnsafeProcessError(StrictDeepControlError):
    """A process record cannot safely be signalled."""


class ResourceWait(StrictDeepControlError):
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
    number = float(value)
    if not math.isfinite(number):
        raise ValueError(f"{name} must be finite")
    return number


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
    if len(cpus) < 4 or min(cpus) < 0:
        raise ValueError("cpu_list must contain at least four non-negative CPUs")
    return tuple(sorted(cpus))


@dataclass(frozen=True)
class ResourcePolicy:
    solver_slots: int = 4
    reserve_foreground_cpus: int = 12
    nice: int = 15
    cpu_list: tuple[int, ...] | None = None
    heartbeat_s: float = 15.0
    capacity_poll_s: float = 30.0
    termination_grace_s: float = 180.0

    @classmethod
    def from_mapping(cls, value: Mapping[str, Any]) -> "ResourcePolicy":
        raw = value.get("resources", {})
        if not isinstance(raw, Mapping):
            raise ValueError("config resources must be an object")
        allowed = {
            "solver_slots",
            "reserve_foreground_cpus",
            "nice",
            "cpu_list",
            "heartbeat_s",
            "capacity_poll_s",
            "termination_grace_s",
        }
        if set(raw) - allowed:
            raise ValueError("unknown strict deep resource settings")
        cpu_value = raw.get("cpu_list")
        policy = cls(
            solver_slots=_strict_int(raw.get("solver_slots", 4), name="solver_slots"),
            reserve_foreground_cpus=_strict_int(
                raw.get("reserve_foreground_cpus", 12),
                name="reserve_foreground_cpus",
            ),
            nice=_strict_int(raw.get("nice", 15), name="nice"),
            cpu_list=parse_cpu_list(cpu_value) if cpu_value is not None else None,
            heartbeat_s=_strict_float(raw.get("heartbeat_s", 15.0), name="heartbeat_s"),
            capacity_poll_s=_strict_float(
                raw.get("capacity_poll_s", 30.0),
                name="capacity_poll_s",
            ),
            termination_grace_s=_strict_float(
                raw.get("termination_grace_s", 180.0),
                name="termination_grace_s",
            ),
        )
        if policy.solver_slots != 4:
            raise ValueError("strict deep sidecar requires solver_slots=4")
        if policy.reserve_foreground_cpus != 12:
            raise ValueError("strict deep sidecar requires reserve_foreground_cpus=12")
        if policy.nice != 15:
            raise ValueError("strict deep sidecar requires nice=15")
        for name, number in (
            ("heartbeat_s", policy.heartbeat_s),
            ("capacity_poll_s", policy.capacity_poll_s),
        ):
            if number <= 0:
                raise ValueError(f"{name} must be positive")
        if policy.termination_grace_s < 180:
            raise ValueError("termination_grace_s must be at least 180 seconds")
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


def _assert_source_unchanged() -> str:
    if _SOURCE_SHA256 is None:
        raise StrictDeepControlError("launcher source could not be sealed")
    if hashlib.sha256(Path(__file__).read_bytes()).hexdigest() != _SOURCE_SHA256:
        raise StrictDeepControlError("launcher source changed while worker was running")
    return _SOURCE_SHA256


def _file_sha256(path: Path) -> str:
    digest = hashlib.sha256()
    with path.open("rb") as stream:
        while chunk := stream.read(1024 * 1024):
            digest.update(chunk)
    return digest.hexdigest()


def _queue_source_sha(repo: Path) -> str:
    source = repo / "humanize" / "strict_deep_queue.py"
    if source.is_symlink() or not source.is_file():
        raise ValueError("strict deep queue source is not a regular repository file")
    return _file_sha256(source)


def _validate_run_id(run_id: str) -> str:
    if not isinstance(run_id, str) or _RUN_ID.fullmatch(run_id) is None:
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
    pipelines = (repo / "results" / "humanize" / "pipelines").resolve(strict=True)
    run_root = (pipelines / safe_id).resolve(strict=True)
    try:
        run_root.relative_to(pipelines)
    except ValueError as exc:
        raise ValueError("pipeline run path escapes repository") from exc
    sidecars = run_root / "sidecars"
    root = sidecars / SIDECAR_NAME
    if create:
        sidecars.mkdir(mode=0o700, exist_ok=True)
        root.mkdir(mode=0o700, exist_ok=True)
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
        value,
        ensure_ascii=False,
        sort_keys=True,
        separators=(",", ":"),
        allow_nan=False,
    ).encode("utf-8")


def _record_hash(value: Mapping[str, Any]) -> str:
    unsigned = dict(value)
    unsigned.pop("process_record_sha256", None)
    return hashlib.sha256(_canonical(unsigned)).hexdigest()


def _atomic_write_json(path: Path, value: Mapping[str, Any]) -> None:
    path.parent.mkdir(parents=True, exist_ok=True)
    descriptor, temporary_name = tempfile.mkstemp(
        prefix=f".{path.name}.tmp-",
        dir=path.parent,
    )
    temporary = Path(temporary_name)
    try:
        with os.fdopen(descriptor, "w", encoding="utf-8") as stream:
            json.dump(
                value,
                stream,
                ensure_ascii=False,
                indent=2,
                sort_keys=True,
                allow_nan=False,
            )
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
        raise StrictDeepControlError("process record may not be a symlink")
    if not path.is_file():
        return None
    if not stat.S_ISREG(path.stat().st_mode):
        raise StrictDeepControlError("process record is not a regular file")
    try:
        value = json.loads(path.read_text(encoding="utf-8"))
    except (OSError, json.JSONDecodeError) as exc:
        raise StrictDeepControlError(f"cannot read process record: {exc}") from exc
    if not isinstance(value, dict):
        raise StrictDeepControlError("process record is not an object")
    if value.get("process_record_sha256") != _record_hash(value):
        raise StrictDeepControlError("process record self-hash mismatch")
    if (
        value.get("schema_version") != PROCESS_SCHEMA_VERSION
        or value.get("kind") != PROCESS_KIND
    ):
        raise StrictDeepControlError("unsupported process record")
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
        identity = identity_reader(int(record["pid"]))
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
    descriptor = os.open(
        path,
        os.O_RDWR | os.O_CREAT | getattr(os, "O_NOFOLLOW", 0),
        0o600,
    )
    try:
        if not stat.S_ISREG(os.fstat(descriptor).st_mode):
            raise StrictDeepControlError("sidecar lock is not a regular file")
        fcntl.flock(descriptor, fcntl.LOCK_EX | fcntl.LOCK_NB)
    except BlockingIOError as exc:
        os.close(descriptor)
        raise AlreadyRunningError("strict deep sidecar lock is held") from exc
    except BaseException:
        os.close(descriptor)
        raise
    return descriptor


def _validate_lock(descriptor: int, path: Path) -> None:
    opened, current = os.fstat(descriptor), path.stat()
    if opened.st_dev != current.st_dev or opened.st_ino != current.st_ino:
        raise StrictDeepControlError("inherited descriptor is not the sidecar lock")


def _load_config(path: Path) -> tuple[dict[str, Any], str, Path]:
    supplied = Path(path).expanduser()
    if supplied.is_symlink():
        raise ValueError("strict deep config must be a regular non-symlink file")
    resolved = supplied.resolve(strict=True)
    if not resolved.is_file():
        raise ValueError("strict deep config must be a regular non-symlink file")
    payload = resolved.read_bytes()
    try:
        value = json.loads(payload)
    except json.JSONDecodeError as exc:
        raise ValueError(f"invalid strict deep JSON config: {exc}") from exc
    if not isinstance(value, dict):
        raise ValueError("strict deep config must be an object")
    if value.get("expected_digests") != list(EXPECTED_DIGESTS):
        raise ValueError("config must bind the two fixed strict deep digests in order")
    policy = ResourcePolicy.from_mapping(value)
    queue = value.get("queue")
    if not isinstance(queue, Mapping):
        raise ValueError("config queue must be an object")
    if queue.get("max_workers") != policy.solver_slots:
        raise ValueError("queue max_workers must equal the four leased solver slots")
    queue_grace = _strict_float(
        queue.get("termination_grace_s", 0),
        name="queue termination_grace_s",
    )
    if queue_grace < 180:
        raise ValueError("queue termination_grace_s must be at least 180 seconds")
    return value, hashlib.sha256(payload).hexdigest(), resolved


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
    selected = policy.cpu_list or tuple(sorted(allowed))
    if len(selected) < policy.solver_slots:
        raise ValueError("worker affinity must expose at least four CPUs")
    if not set(selected).issubset(allowed):
        raise ValueError("cpu_list includes a CPU outside current affinity")
    return tuple(selected)


def _apply_resources(policy: ResourcePolicy, selected: Sequence[int]) -> None:
    _native_thread_limits()
    if hasattr(os, "sched_setaffinity"):
        os.sched_setaffinity(0, set(selected))
    if hasattr(os, "setpriority"):
        os.setpriority(os.PRIO_PROCESS, 0, policy.nice)
    elif policy.nice:
        os.nice(policy.nice)


def _capacity_lease(
    policy: ResourcePolicy,
    capacity_affinity: Sequence[int] | None = None,
) -> Any:
    from evaluation.solver_budget import (
        _read_processes,
        acquire_solver_budget,
        detect_cpu_budget,
    )
    from humanize.exactification_cli import _deduplicate_audit_pool_processes

    budget = detect_cpu_budget(affinity=capacity_affinity)
    processes = _deduplicate_audit_pool_processes(_read_processes())
    lease = acquire_solver_budget(
        policy.solver_slots,
        cpu_budget=budget,
        processes=processes,
        current_pid=os.getpid(),
    )
    free_before = (
        budget.capacity - lease.cooperative_slots_before - lease.unmanaged_usage.workers
    )
    if free_before - policy.solver_slots < policy.reserve_foreground_cpus:
        lease.release()
        raise ResourceWait(
            "RESOURCE_WAIT: strict deep queue would reduce foreground reserve below "
            f"{policy.reserve_foreground_cpus} CPUs (capacity={budget.capacity}, "
            f"available_before={free_before}, requested={policy.solver_slots})"
        )
    return lease


def _source_info(args: argparse.Namespace, paths: ControlPaths) -> dict[str, Any]:
    values: dict[str, Any] = {}
    for attribute, label in (
        ("ranked_input", "strict ranked input"),
        ("summary_input", "strict summary input"),
    ):
        source = Path(getattr(args, attribute)).expanduser()
        if source.is_symlink():
            raise ValueError(f"{label} may not be a symlink")
        resolved = source.resolve(strict=True)
        try:
            resolved.relative_to(paths.run_root)
        except ValueError as exc:
            raise ValueError(f"{label} escapes the pipeline run") from exc
        if not resolved.is_file() or resolved.is_symlink():
            raise ValueError(f"{label} must be a regular non-symlink file")
        values[attribute] = str(resolved)
        values[f"{attribute}_sha256"] = _file_sha256(resolved)
    values["expected_digests"] = list(EXPECTED_DIGESTS)
    return values


class _Heartbeat:
    def __init__(
        self,
        path: Path,
        identity: Mapping[str, Any],
        interval: float,
        stop_event: threading.Event,
    ) -> None:
        self.path = path
        self.pid = int(identity["pid"])
        self.starttime = int(identity["proc_starttime"])
        self.interval = interval
        self.stop_event = stop_event
        self.finished = threading.Event()
        self.failure: BaseException | None = None
        self.thread = threading.Thread(target=self._run, daemon=True)

    def _run(self) -> None:
        try:
            while not self.finished.wait(self.interval):
                _assert_source_unchanged()
                _update_record(
                    self.path,
                    pid=self.pid,
                    starttime=self.starttime,
                    heartbeat_at=utc_now(),
                )
        except BaseException as exc:
            self.failure = exc
            self.stop_event.set()
            _update_record(
                self.path,
                pid=self.pid,
                starttime=self.starttime,
                status="failed",
                error=f"{type(exc).__name__}: {exc}",
            )

    def start(self) -> None:
        self.thread.start()

    def stop(self) -> None:
        self.finished.set()
        self.thread.join(timeout=min(2.0, self.interval + 0.1))


def _run_scientific(
    *,
    paths: ControlPaths,
    config_document: Mapping[str, Any],
    source: Mapping[str, Any],
    stop_event: threading.Event,
) -> dict[str, Any]:
    from . import strict_deep_queue as core

    config = core.DeepConfig.from_json(config_document).validate()
    if config.max_workers != 4:
        raise ValueError("strict deep scientific queue requires max_workers=4")
    queue_paths = core.deep_paths(paths.run_root)
    core.initialize_queue(
        queue_paths,
        ranked_input=source["ranked_input"],
        summary_input=source["summary_input"],
        expected_digests=EXPECTED_DIGESTS,
        config=config,
    )
    queue = core.run_queue(queue_paths, stop_event=stop_event)
    return {
        "status": queue["status"],
        "revision": queue["revision"],
        "candidates": [
            {
                "canonical_digest": candidate["canonical_digest"],
                "status": candidate["status"],
                "bounds": candidate["bounds"],
                "proven_lanes": candidate.get("proven_lanes", []),
            }
            for candidate in queue["candidates"]
        ],
        "publication_certificate": False,
        "pipeline_promotion": False,
    }


def _initialize(
    args: argparse.Namespace,
    paths: ControlPaths,
    config_document: Mapping[str, Any],
) -> dict[str, Any]:
    _native_thread_limits()
    from . import strict_deep_queue as core

    config = core.DeepConfig.from_json(config_document).validate()
    if config.max_workers != 4:
        raise ValueError("strict deep scientific queue requires max_workers=4")
    source = _source_info(args, paths)
    queue_paths = core.deep_paths(paths.run_root)
    core.initialize_queue(
        queue_paths,
        ranked_input=source["ranked_input"],
        summary_input=source["summary_input"],
        expected_digests=EXPECTED_DIGESTS,
        config=config,
    )
    return core.queue_status(queue_paths)


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
                raise StrictDeepControlError("parent launch barrier failed")
        finally:
            os.close(start_fd)
    document, config_sha, config_path = _load_config(args.config)
    policy = ResourcePolicy.from_mapping(document)
    repo = _resolve_repo(args.repo_dir)
    source = _source_info(args, paths)
    launcher_sha = _assert_source_unchanged()
    queue_source_sha = _queue_source_sha(repo)
    _native_thread_limits()
    try:
        capacity_affinity = tuple(os.sched_getaffinity(0))
    except (AttributeError, OSError):
        capacity_affinity = tuple(range(os.cpu_count() or 1))
    selected = _selected_cpus(policy)
    identity = _proc_identity(os.getpid())
    if identity is None:
        raise StrictDeepControlError("cannot establish worker identity")
    starting = read_process_record(paths.process) if isolated else None
    if isolated:
        if starting is None:
            raise StrictDeepControlError("detached worker lacks launch record")
        matched, reason = process_matches(starting)
        if not matched:
            raise StrictDeepControlError(f"detached launch identity failed: {reason}")
        expected = {
            "config_sha256": config_sha,
            "launcher_source_sha256": launcher_sha,
            "queue_source_sha256": queue_source_sha,
            "inputs": source,
        }
        if any(starting.get(key) != value for key, value in expected.items()):
            raise StrictDeepControlError(
                "detached worker inputs differ from launch record"
            )
    now = utc_now()
    record = {
        "schema_version": PROCESS_SCHEMA_VERSION,
        "kind": PROCESS_KIND,
        "run_id": args.run_id,
        "repo_dir": str(repo),
        "sidecar_root": str(paths.root),
        "status": "capacity-check",
        **identity,
        "isolated_session": isolated,
        "config_path": str(config_path),
        "config_sha256": config_sha,
        "launcher_source_sha256": launcher_sha,
        "queue_source_sha256": queue_source_sha,
        "command": list(sys.argv),
        "inputs": source,
        "resources": {**policy.as_dict(), "selected_cpus": list(selected)},
        "solver_termination_grace_s": float(document["queue"]["termination_grace_s"]),
        "started_at": starting.get("started_at", now) if starting else now,
        "heartbeat_at": now,
        "updated_at": now,
    }
    write_process_record(paths.process, record)
    stop_event = threading.Event()
    heartbeat = _Heartbeat(
        paths.process,
        identity,
        policy.heartbeat_s,
        stop_event,
    )
    heartbeat.start()

    def request_stop(_signum: int, _frame: Any) -> None:
        stop_event.set()

    previous_term = signal.signal(signal.SIGTERM, request_stop)
    previous_hup = signal.signal(signal.SIGHUP, signal.SIG_IGN) if isolated else None
    lease = None
    try:
        while not stop_event.is_set():
            _assert_source_unchanged()
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
                paths=paths,
                config_document=document,
                source=source,
                stop_event=stop_event,
            )
            lease.release()
            lease = None
            if heartbeat.failure is not None:
                raise heartbeat.failure
            scientific_terminal = result.get("status") in {
                "STRICT_THRESHOLD_PROVEN",
                "WITNESS_REJECTED",
            }
            terminal = (
                "cancelled"
                if stop_event.is_set() and not scientific_terminal
                else "completed"
            )
            _update_record(
                paths.process,
                pid=identity["pid"],
                starttime=identity["proc_starttime"],
                status=terminal,
                result_status=result.get("status"),
                finished_at=utc_now(),
            )
            return result
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
    document, config_sha, config_path = _load_config(args.config)
    policy = ResourcePolicy.from_mapping(document)
    repo = _resolve_repo(args.repo_dir)
    source = _source_info(args, paths)
    launcher_sha = _assert_source_unchanged()
    queue_source_sha = _queue_source_sha(repo)
    lock_fd = _acquire_lock(paths.lock)
    read_fd = write_fd = log_fd = -1
    process: subprocess.Popen[Any] | None = None
    try:
        read_fd, write_fd = os.pipe()
        # Preserve a virtual environment's interpreter entry point.  Resolving
        # the symlink to the base interpreter changes ``sys.prefix`` and drops
        # the venv's site-packages (the production venv is symlink-based).
        python = Path(
            os.path.abspath(os.fspath(Path(args.python_executable).expanduser()))
        )
        try:
            python_info = python.stat()
        except OSError as exc:
            raise ValueError(
                f"cannot inspect python executable {python}: {exc}"
            ) from exc
        if not stat.S_ISREG(python_info.st_mode) or not os.access(python, os.X_OK):
            raise ValueError(
                f"python executable must name an executable regular file: {python}"
            )
        command = [
            str(python),
            "-m",
            "humanize.strict_deep_cli",
            "_worker",
            "--repo-dir",
            str(repo),
            "--run-id",
            args.run_id,
            "--config",
            str(config_path),
            "--ranked-input",
            source["ranked_input"],
            "--summary-input",
            source["summary_input"],
            "--lock-fd",
            str(lock_fd),
            "--start-fd",
            str(read_fd),
        ]
        log_fd = os.open(
            paths.log,
            os.O_WRONLY | os.O_CREAT | os.O_APPEND | getattr(os, "O_NOFOLLOW", 0),
            0o600,
        )
        process = subprocess.Popen(
            command,
            cwd=repo,
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
            raise StrictDeepControlError(
                "detached worker exited before identity capture"
            )
        if identity["pgid"] != process.pid or identity["session_id"] != process.pid:
            raise StrictDeepControlError(
                "detached worker did not create an isolated session"
            )
        now = utc_now()
        record = write_process_record(
            paths.process,
            {
                "schema_version": PROCESS_SCHEMA_VERSION,
                "kind": PROCESS_KIND,
                "run_id": args.run_id,
                "repo_dir": str(repo),
                "sidecar_root": str(paths.root),
                "status": "starting",
                **identity,
                "isolated_session": True,
                "config_path": str(config_path),
                "config_sha256": config_sha,
                "launcher_source_sha256": launcher_sha,
                "queue_source_sha256": queue_source_sha,
                "command": command,
                "inputs": source,
                "resources": policy.as_dict(),
                "solver_termination_grace_s": float(
                    document["queue"]["termination_grace_s"]
                ),
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
        for descriptor in (read_fd, write_fd, log_fd, lock_fd):
            if descriptor >= 0:
                try:
                    os.close(descriptor)
                except OSError:
                    pass


def _status(args: argparse.Namespace, paths: ControlPaths) -> dict[str, Any]:
    record = read_process_record(paths.process)
    if record is None:
        alive, reason = False, "no process record"
    else:
        alive, reason = process_matches(record)
    _native_thread_limits()
    from . import strict_deep_queue as core

    queue = core.queue_status(core.deep_paths(paths.run_root))
    stored = record.get("status") if record else None
    if alive:
        operational = stored or "running"
    elif stored in {"completed", "failed", "cancelled", "termination-pending"}:
        operational = stored
    else:
        operational = "idle" if queue["status"] != "NOT_STARTED" else "not-started"
    return {
        "schema_version": PROCESS_SCHEMA_VERSION,
        "run_id": args.run_id,
        "status": operational,
        "alive": alive,
        "identity_reason": reason,
        "process": record,
        "queue": queue,
        "paths": {
            "root": str(paths.root),
            "process": str(paths.process),
            "log": str(paths.log),
        },
        "publication_certificate": False,
        "pipeline_promotion": False,
    }


def _session_group_members(*, pgid: int, session_id: int, uid: int) -> list[int]:
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
    if (
        record.get("run_id") != args.run_id
        or record.get("repo_dir") != expected_repo
        or record.get("sidecar_root") != str(paths.root)
    ):
        raise UnsafeProcessError("process record belongs to another run")
    command = record.get("command")
    is_deep_command = isinstance(command, list) and any(
        value == "humanize.strict_deep_cli"
        or str(value).replace("\\", "/").endswith("/humanize/strict_deep_cli.py")
        for value in command
    )
    if not is_deep_command:
        raise UnsafeProcessError("process record is not a strict deep worker")
    alive, reason = process_matches(record, identity_reader=identity_reader)
    if not alive:
        raise UnsafeProcessError(f"refusing to signal: {reason}")
    pid = int(record["pid"])
    pgid = int(record["pgid"])
    session_id = int(record["session_id"])
    if record.get("isolated_session") is not True or pgid != pid or session_id != pid:
        raise UnsafeProcessError("record does not identify an isolated worker session")
    resources = record.get("resources")
    configured_grace = _strict_float(
        (
            resources.get("termination_grace_s", 180.0)
            if isinstance(resources, Mapping)
            else 180.0
        ),
        name="recorded process termination grace",
    )
    solver_grace = _strict_float(
        record.get("solver_termination_grace_s", 180.0),
        name="recorded solver termination grace",
    )
    grace = _strict_float(args.grace_seconds, name="cancel grace")
    if grace < max(180.0, configured_grace, solver_grace):
        raise ValueError(
            "cancel grace must cover at least 180s solver termination grace"
        )
    uid = int(record["uid"])

    def group_stopped() -> bool:
        leader_alive = process_matches(record, identity_reader=identity_reader)[0]
        members = group_members_reader(pgid=pgid, session_id=session_id, uid=uid)
        return not leader_alive and not members

    kill_group(pgid, signal.SIGTERM)
    deadline = time.monotonic() + grace
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
    return {
        "status": "cancelled" if stopped else "termination-pending",
        "stopped": stopped,
        "forced": forced,
        "pid": pid,
    }


def _default_repo() -> Path:
    return Path(__file__).resolve().parent.parent


def _common(parser: argparse.ArgumentParser, *, config: bool = False) -> None:
    parser.add_argument("--repo-dir", type=Path, default=_default_repo())
    parser.add_argument("--run-id", required=True)
    if config:
        parser.add_argument("--config", type=Path, required=True)


def _sources(parser: argparse.ArgumentParser) -> None:
    parser.add_argument("--ranked-input", type=Path, required=True)
    parser.add_argument("--summary-input", type=Path, required=True)


def build_parser() -> argparse.ArgumentParser:
    parser = argparse.ArgumentParser(description=__doc__)
    subparsers = parser.add_subparsers(dest="command", required=True)
    initialize = subparsers.add_parser("init")
    _common(initialize, config=True)
    _sources(initialize)
    run = subparsers.add_parser("run")
    _common(run, config=True)
    _sources(run)
    start = subparsers.add_parser("start")
    _common(start, config=True)
    _sources(start)
    start.add_argument("--python-executable", default=sys.executable)
    status = subparsers.add_parser("status")
    _common(status)
    cancel = subparsers.add_parser("cancel")
    _common(cancel)
    cancel.add_argument("--grace-seconds", type=float, default=180.0)
    worker = subparsers.add_parser("_worker", help=argparse.SUPPRESS)
    _common(worker, config=True)
    _sources(worker)
    worker.add_argument("--lock-fd", type=int, required=True)
    worker.add_argument("--start-fd", type=int, required=True)
    return parser


def _print(value: Any, *, stream: Any = sys.stdout) -> None:
    print(
        json.dumps(value, ensure_ascii=False, indent=2, default=str),
        file=stream,
        flush=True,
    )


def main(argv: Sequence[str] | None = None) -> int:
    try:
        args = build_parser().parse_args(argv)
        create = args.command in {"init", "run", "start", "_worker"}
        paths = control_paths(args.repo_dir, args.run_id, create=create)
        if args.command == "init":
            document, _, _ = _load_config(args.config)
            lock_fd = _acquire_lock(paths.lock)
            try:
                result = _initialize(args, paths, document)
            finally:
                os.close(lock_fd)
        elif args.command == "run":
            lock_fd = _acquire_lock(paths.lock)
            try:
                result = _execute_worker(
                    args=args,
                    paths=paths,
                    lock_fd=lock_fd,
                    isolated=False,
                )
            finally:
                os.close(lock_fd)
        elif args.command == "start":
            record = start_background(args, paths)
            result = {
                "status": record["status"],
                "pid": record["pid"],
                "process": str(paths.process),
                "log": str(paths.log),
            }
        elif args.command == "status":
            result = _status(args, paths)
        elif args.command == "cancel":
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
    except (
        AlreadyRunningError,
        StrictDeepControlError,
        OSError,
        ValueError,
    ) as exc:
        _print(
            {"status": "error", "error": f"{type(exc).__name__}: {exc}"},
            stream=sys.stderr,
        )
        return 2


if __name__ == "__main__":
    raise SystemExit(main())
