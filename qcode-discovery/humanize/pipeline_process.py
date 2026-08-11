"""Safe process control for the detached five-stage qcode pipeline.

The process record is deliberately independent from the scientific pipeline
state.  It answers only operational questions: which process owns a run, is it
still the same Linux process, and can it safely be signalled?
"""

from __future__ import annotations

import fcntl
import hashlib
import json
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
DEFAULT_HEARTBEAT_SECONDS = 15.0
SUCCESSFUL_TERMINAL_STATUSES = frozenset(
    {
        "COMPLETED_WIN",
        "COMPLETED_NO_WIN",
    }
)
ESCALATION_PARENT_STATUSES = frozenset({"COMPLETED_NO_WIN", "INCOMPLETE"})
_RUN_ID = re.compile(r"[A-Za-z0-9][A-Za-z0-9_.-]{0,127}")


class ProcessControlError(RuntimeError):
    """Base error for process-control failures."""


class AlreadyRunningError(ProcessControlError):
    """Raised when another process holds the per-run lock."""


class UnsafeProcessError(ProcessControlError):
    """Raised when stored identity is insufficient to signal a process."""


@dataclass(frozen=True)
class ControlPaths:
    """Fixed paths used by one pipeline run."""

    root: Path
    state: Path
    process: Path
    lock: Path
    log: Path
    escalation_policy: Path


@dataclass(frozen=True)
class ProcessMatch:
    """Result of comparing a process record with Linux ``/proc``."""

    alive: bool
    reason: str
    identity: dict[str, Any] | None = None


def utc_now() -> str:
    return datetime.now(timezone.utc).isoformat()


def validate_run_id(run_id: str) -> str:
    """Return a safe run id without silently rewriting user input."""
    if not isinstance(run_id, str) or not _RUN_ID.fullmatch(run_id):
        raise ValueError("run_id must match [A-Za-z0-9][A-Za-z0-9_.-]{0,127}")
    if run_id in {".", ".."}:
        raise ValueError("run_id may not be '.' or '..'")
    return run_id


def resolve_repo_dir(repo_dir: Path) -> Path:
    resolved = Path(repo_dir).expanduser().resolve(strict=True)
    if not resolved.is_dir():
        raise ValueError(f"repo_dir is not a directory: {resolved}")
    if not (resolved / "humanize").is_dir():
        raise ValueError(f"repo_dir does not contain the Humanize package: {resolved}")
    return resolved


def resolve_config_path(config_path: Path) -> Path:
    resolved = Path(config_path).expanduser().resolve(strict=True)
    if not resolved.is_file():
        raise ValueError(f"config is not a regular file: {resolved}")
    return resolved


def control_paths(repo_dir: Path, run_id: str, *, create: bool = False) -> ControlPaths:
    """Resolve one run below the fixed pipeline state root.

    Resolving the final directory catches a pre-existing symlink that escapes
    the repository.  The run id itself is never path-normalized.
    """
    repo = resolve_repo_dir(repo_dir)
    safe_id = validate_run_id(run_id)
    base = repo
    for component in ("results", "humanize", "pipelines"):
        candidate = base / component
        if create and not candidate.exists() and not candidate.is_symlink():
            candidate.mkdir(mode=0o700)
        resolved_candidate = candidate.resolve(strict=create)
        try:
            resolved_candidate.relative_to(repo)
        except ValueError as exc:
            raise ValueError(
                "pipeline control path escapes repository: "
                f"{candidate} -> {resolved_candidate}"
            ) from exc
        if create and not resolved_candidate.is_dir():
            raise ValueError(f"pipeline control path is not a directory: {candidate}")
        base = resolved_candidate
    resolved_base = base
    run_root = resolved_base / safe_id
    if create and not run_root.exists() and not run_root.is_symlink():
        run_root.mkdir(mode=0o700)
    resolved_root = run_root.resolve(strict=create)
    try:
        resolved_root.relative_to(resolved_base)
    except ValueError as exc:
        raise ValueError(f"pipeline state path escapes repository: {run_root}") from exc
    return ControlPaths(
        root=resolved_root,
        state=resolved_root / "state.json",
        process=resolved_root / "process.json",
        lock=resolved_root / "process.lock",
        log=resolved_root / "pipeline.log",
        escalation_policy=resolved_root / "auto-escalation-policy.json",
    )


def atomic_write_json(path: Path, value: Mapping[str, Any]) -> None:
    """Atomically replace JSON and fsync both the file and parent directory."""
    path.parent.mkdir(parents=True, exist_ok=True)
    descriptor, temporary_name = tempfile.mkstemp(
        prefix=f".{path.name}.tmp-", dir=path.parent
    )
    temporary = Path(temporary_name)
    try:
        with os.fdopen(descriptor, "w", encoding="utf-8") as stream:
            json.dump(value, stream, ensure_ascii=False, indent=2, sort_keys=True)
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
        try:
            temporary.unlink()
        except FileNotFoundError:
            pass


def _canonical_json_file_bytes(value: Mapping[str, Any]) -> bytes:
    return (
        json.dumps(
            value,
            ensure_ascii=False,
            sort_keys=True,
            separators=(",", ":"),
            allow_nan=False,
        )
        + "\n"
    ).encode("utf-8")


def _exclusive_create_or_compare_json(
    path: Path, value: Mapping[str, Any]
) -> dict[str, Any]:
    """Durably create one immutable snapshot, or require exact prior bytes."""

    payload = _canonical_json_file_bytes(value)
    path.parent.mkdir(parents=True, exist_ok=True)
    descriptor, temporary_name = tempfile.mkstemp(
        prefix=f".{path.name}.tmp-", dir=path.parent
    )
    temporary = Path(temporary_name)
    try:
        with os.fdopen(descriptor, "wb") as stream:
            stream.write(payload)
            stream.flush()
            os.fsync(stream.fileno())
        os.chmod(temporary, 0o600)
        try:
            os.link(temporary, path, follow_symlinks=False)
        except FileExistsError:
            if path.is_symlink() or not path.is_file():
                raise ProcessControlError(
                    f"unsafe durable escalation policy snapshot: {path}"
                )
            if path.read_bytes() != payload:
                raise ProcessControlError(
                    "launch policy differs from the durable run snapshot"
                )
        directory_fd = os.open(path.parent, os.O_RDONLY | os.O_DIRECTORY)
        try:
            os.fsync(directory_fd)
        finally:
            os.close(directory_fd)
    finally:
        temporary.unlink(missing_ok=True)
    return dict(value)


def read_json_object(path: Path) -> dict[str, Any] | None:
    if not path.is_file():
        return None
    try:
        value = json.loads(path.read_text(encoding="utf-8"))
    except (OSError, json.JSONDecodeError) as exc:
        raise ProcessControlError(f"cannot read JSON object {path}: {exc}") from exc
    if not isinstance(value, dict):
        raise ProcessControlError(f"expected a JSON object in {path}")
    return value


def _proc_stat(pid: int) -> tuple[str, list[str]]:
    raw = Path(f"/proc/{pid}/stat").read_text(encoding="utf-8")
    end = raw.rfind(")")
    if end < 0:
        raise ValueError(f"invalid /proc/{pid}/stat")
    return raw[raw.find("(") + 1 : end], raw[end + 2 :].split()


def _cmdline_digest(pid: int) -> str:
    raw = Path(f"/proc/{pid}/cmdline").read_bytes()
    if not raw:
        raise ProcessLookupError(pid)
    return hashlib.sha256(raw).hexdigest()


def read_proc_identity(pid: int) -> dict[str, Any] | None:
    """Read the fields needed to detect PID reuse.

    Linux field 22 (``starttime``) is stable for a process lifetime.  The uid
    and command-line digest are additional defence-in-depth checks.
    """
    if isinstance(pid, bool) or not isinstance(pid, int) or pid <= 1:
        return None
    try:
        command_name, fields = _proc_stat(pid)
        if len(fields) < 20:
            return None
        state = fields[0]
        if state == "Z":
            return None
        stat_result = Path(f"/proc/{pid}").stat()
        return {
            "pid": pid,
            "command_name": command_name,
            "state": state,
            "pgid": int(fields[2]),
            "session_id": int(fields[3]),
            "proc_starttime": int(fields[19]),
            "uid": int(stat_result.st_uid),
            "cmdline_sha256": _cmdline_digest(pid),
        }
    except (
        FileNotFoundError,
        ProcessLookupError,
        PermissionError,
        OSError,
        ValueError,
    ):
        return None


def process_matches(
    metadata: Mapping[str, Any],
    *,
    identity_reader: Callable[[int], dict[str, Any] | None] = read_proc_identity,
) -> ProcessMatch:
    """Verify that a process record still names the original process."""
    if metadata.get("schema_version") != PROCESS_SCHEMA_VERSION:
        return ProcessMatch(False, "unsupported process metadata schema")
    try:
        pid = int(metadata["pid"])
        expected = {
            "proc_starttime": int(metadata["proc_starttime"]),
            "uid": int(metadata["uid"]),
            "cmdline_sha256": str(metadata["cmdline_sha256"]),
        }
    except (KeyError, TypeError, ValueError):
        return ProcessMatch(False, "process metadata is missing identity fields")
    identity = identity_reader(pid)
    if identity is None:
        return ProcessMatch(False, "process is not running")
    for field, expected_value in expected.items():
        if identity.get(field) != expected_value:
            return ProcessMatch(False, f"process identity mismatch: {field}", identity)
    try:
        expected_pgid = int(metadata["pgid"])
        expected_session = int(metadata["session_id"])
    except (KeyError, TypeError, ValueError):
        return ProcessMatch(
            False, "process metadata is missing group identity", identity
        )
    if identity.get("pgid") != expected_pgid:
        return ProcessMatch(False, "process identity mismatch: pgid", identity)
    if identity.get("session_id") != expected_session:
        return ProcessMatch(False, "process identity mismatch: session_id", identity)
    return ProcessMatch(True, "process identity matches", identity)


def process_scope_error(
    metadata: Mapping[str, Any],
    *,
    repo_dir: Path,
    run_id: str,
) -> str | None:
    """Return why a durable process record belongs to a different run."""
    expected_repo = resolve_repo_dir(repo_dir)
    safe_id = validate_run_id(run_id)
    if metadata.get("run_id") != safe_id:
        return (
            "process metadata run_id mismatch: "
            f"expected {safe_id!r}, found {metadata.get('run_id')!r}"
        )
    recorded_repo = metadata.get("repo_dir")
    if not isinstance(recorded_repo, str) or not recorded_repo:
        return "process metadata is missing repo_dir"
    try:
        resolved_recorded_repo = Path(recorded_repo).expanduser().resolve()
    except OSError as exc:
        return f"process metadata repo_dir is invalid: {exc}"
    if resolved_recorded_repo != expected_repo:
        return (
            "process metadata repo_dir mismatch: "
            f"expected {expected_repo}, found {resolved_recorded_repo}"
        )
    return None


def acquire_run_lock(path: Path) -> int:
    path.parent.mkdir(parents=True, exist_ok=True)
    descriptor = os.open(
        path,
        os.O_RDWR | os.O_CREAT | getattr(os, "O_NOFOLLOW", 0),
        0o600,
    )
    try:
        if not stat.S_ISREG(os.fstat(descriptor).st_mode):
            raise ProcessControlError(f"pipeline lock is not a regular file: {path}")
        fcntl.flock(descriptor, fcntl.LOCK_EX | fcntl.LOCK_NB)
    except BlockingIOError as exc:
        os.close(descriptor)
        raise AlreadyRunningError(f"pipeline lock is already held: {path}") from exc
    except BaseException:
        os.close(descriptor)
        raise
    return descriptor


def close_run_lock(descriptor: int, *, unlock: bool) -> None:
    try:
        if unlock:
            fcntl.flock(descriptor, fcntl.LOCK_UN)
    finally:
        os.close(descriptor)


def validate_inherited_lock(descriptor: int, path: Path) -> None:
    """Require the worker's inherited descriptor to name its exact lock file."""
    try:
        descriptor_stat = os.fstat(descriptor)
        path_stat = path.stat()
    except (OSError, ValueError) as exc:
        raise ProcessControlError("invalid inherited pipeline lock") from exc
    if (
        descriptor_stat.st_dev != path_stat.st_dev
        or descriptor_stat.st_ino != path_stat.st_ino
    ):
        raise ProcessControlError("inherited descriptor is not the pipeline lock")


def _base_metadata(
    *,
    run_id: str,
    identity: Mapping[str, Any],
    isolated_session: bool,
    config_path: Path,
    paths: ControlPaths,
    command: Sequence[str],
    status: str,
    config_sha256: str | None = None,
) -> dict[str, Any]:
    now = utc_now()
    observed_config_sha256 = hashlib.sha256(config_path.read_bytes()).hexdigest()
    if (
        config_sha256 is not None
        and observed_config_sha256 != config_sha256
    ):
        raise ProcessControlError("pipeline config changed during process setup")
    return {
        "schema_version": PROCESS_SCHEMA_VERSION,
        "run_id": run_id,
        "status": status,
        "pid": identity["pid"],
        "proc_starttime": identity["proc_starttime"],
        "pgid": identity["pgid"],
        "session_id": identity["session_id"],
        "uid": identity["uid"],
        "cmdline_sha256": identity["cmdline_sha256"],
        "isolated_session": isolated_session,
        "repo_dir": str(paths.root.parents[3]),
        "config_path": str(config_path),
        "config_sha256": observed_config_sha256,
        "log_path": str(paths.log),
        "command": list(command),
        "started_at": now,
        "heartbeat_at": now,
        "updated_at": now,
    }


def _update_process_record(
    path: Path,
    *,
    pid: int,
    proc_starttime: int,
    updates: Mapping[str, Any],
) -> bool:
    """Update a record only if it still belongs to the caller."""
    try:
        record = read_json_object(path)
    except ProcessControlError:
        return False
    if record is None:
        return False
    try:
        same_owner = (
            int(record.get("pid")) == pid
            and int(record.get("proc_starttime")) == proc_starttime
        )
    except (TypeError, ValueError):
        return False
    if not same_owner:
        return False
    record.update(updates)
    record["updated_at"] = utc_now()
    atomic_write_json(path, record)
    return True


def pipeline_result_succeeded(result: Mapping[str, Any]) -> bool:
    """Return true only for the two successful terminal pipeline states."""
    return result.get("status") in SUCCESSFUL_TERMINAL_STATUSES


def finalize_process_result(
    process_path: Path,
    *,
    pid: int,
    proc_starttime: int,
    result: Mapping[str, Any],
) -> bool:
    """Persist terminal process status and return its success classification."""
    succeeded = pipeline_result_succeeded(result)
    result_status = result.get("status")
    updates: dict[str, Any] = {
        "status": "completed" if succeeded else "failed",
        "finished_at": utc_now(),
        "result_status": result_status,
    }
    escalation = result.get("campaign_escalation")
    if isinstance(escalation, Mapping):
        # Operational provenance only.  Release eligibility continues to be
        # decided solely by the scientific pipeline terminal status.
        updates["campaign_escalation"] = dict(escalation)
    if not succeeded:
        updates["error"] = (
            f"pipeline returned a non-success terminal status: {result_status!r}"
        )
    _update_process_record(
        process_path,
        pid=pid,
        proc_starttime=proc_starttime,
        updates=updates,
    )
    return succeeded


class Heartbeat:
    """Periodically refresh process metadata while the pipeline is blocked."""

    def __init__(
        self,
        process_path: Path,
        *,
        pid: int,
        proc_starttime: int,
        interval: float = DEFAULT_HEARTBEAT_SECONDS,
    ):
        if interval <= 0:
            raise ValueError("heartbeat interval must be positive")
        self.process_path = process_path
        self.pid = pid
        self.proc_starttime = proc_starttime
        self.interval = interval
        self._stop = threading.Event()
        self._thread = threading.Thread(
            target=self._run,
            name=f"pipeline-heartbeat-{pid}",
            daemon=True,
        )

    def _run(self) -> None:
        while not self._stop.wait(self.interval):
            _update_process_record(
                self.process_path,
                pid=self.pid,
                proc_starttime=self.proc_starttime,
                updates={"heartbeat_at": utc_now()},
            )

    def start(self) -> None:
        self._thread.start()

    def stop(self) -> None:
        self._stop.set()
        self._thread.join(timeout=min(5.0, self.interval + 0.5))


def _wait_for_start_signal(descriptor: int) -> None:
    try:
        signal_byte = os.read(descriptor, 1)
    finally:
        os.close(descriptor)
    if signal_byte != b"1":
        raise ProcessControlError("parent did not complete detached-process setup")


def _open_bound_config(
    *,
    config_path: Path,
    paths: ControlPaths,
    run_id: str,
    isolated_session: bool,
) -> tuple[int, bytes, str]:
    """Open one immutable config inode and bind it to the start record."""

    expected_sha256: str | None = None
    if isolated_session:
        starting = read_json_object(paths.process)
        if starting is None or starting.get("run_id") != run_id:
            raise ProcessControlError("detached worker lacks its parent start record")
        try:
            recorded_path = Path(str(starting["config_path"])).resolve(strict=True)
        except (KeyError, OSError, TypeError, ValueError) as exc:
            raise ProcessControlError("invalid config path in parent start record") from exc
        if recorded_path != config_path.resolve(strict=True):
            raise ProcessControlError("worker config differs from parent start record")
        expected_sha256 = starting.get("config_sha256")
        if not isinstance(expected_sha256, str) or re.fullmatch(
            r"[0-9a-f]{64}", expected_sha256
        ) is None:
            raise ProcessControlError("invalid config hash in parent start record")

    descriptor = os.open(
        config_path,
        os.O_RDONLY | getattr(os, "O_NOFOLLOW", 0),
    )
    try:
        if not stat.S_ISREG(os.fstat(descriptor).st_mode):
            raise ProcessControlError("pipeline config is not a regular file")
        chunks: list[bytes] = []
        while True:
            chunk = os.read(descriptor, 1024 * 1024)
            if not chunk:
                break
            chunks.append(chunk)
        payload = b"".join(chunks)
        os.lseek(descriptor, 0, os.SEEK_SET)
        observed = hashlib.sha256(payload).hexdigest()
        if expected_sha256 is not None and observed != expected_sha256:
            raise ProcessControlError("pipeline config changed before worker start")
        return descriptor, payload, observed
    except BaseException:
        os.close(descriptor)
        raise


def _capture_durable_escalation_policy(
    *,
    repo_dir: Path,
    config_path: Path,
    config_sha256: str,
    run_id: str,
    snapshot_path: Path,
) -> dict[str, Any]:
    """Freeze config, registry and route authorization before science starts."""

    from .escalation import parse_auto_escalation_policy

    policy = parse_auto_escalation_policy(
        repo_dir=repo_dir,
        pipeline_config_path=config_path,
        expected_pipeline_config_sha256=config_sha256,
    )
    snapshot = {
        "schema_version": 1,
        "kind": "qcode-auto-escalation-launch-policy",
        "run_id": run_id,
        "pipeline_config_path": policy.pipeline_config_path,
        "enabled": policy.enabled,
        "registry_path": policy.registry_path,
        "registry_sha256": policy.registry_sha256,
        "template_by_regime": dict(policy.template_by_regime),
        "source_search_representation_id": (
            policy.source_search_representation_id
        ),
    }
    # V4 is the first policy whose no-WIN round budget directly authorizes a
    # representation handoff.  Bind that authority into the launch snapshot
    # without changing historical V1-V3 snapshot bytes.
    if policy.source_search_regime_policy_version == 4:
        snapshot.update({
            "source_search_regime_policy_version": 4,
            "source_max_rounds": policy.source_max_rounds,
            "source_stop_on_representation_change": (
                policy.source_stop_on_representation_change
            ),
        })
    return _exclusive_create_or_compare_json(snapshot_path, snapshot)


def _pending_escalation_parent_result(paths: ControlPaths) -> dict[str, Any] | None:
    """Recover a completed scientific result for reconciliation-only retry."""

    outcome = read_json_object(paths.root / "campaign-escalation.json")
    if outcome is None or outcome.get("disposition") != "pending":
        return None
    state = read_json_object(paths.state)
    if state is None or state.get("status") not in ESCALATION_PARENT_STATUSES:
        raise ProcessControlError(
            "pending escalation lacks a retryable parent scientific state"
        )
    recovered = dict(state)
    recovered["escalation_retry_only"] = True
    return recovered


def execute_pipeline(
    *,
    repo_dir: Path,
    config_path: Path,
    run_id: str,
    paths: ControlPaths,
    lock_fd: int,
    isolated_session: bool,
    command: Sequence[str],
    start_fd: int | None = None,
    heartbeat_interval: float = DEFAULT_HEARTBEAT_SECONDS,
    stage_review: bool | None = None,
    reviewer_model: str | None = None,
    reviewer_effort: str | None = None,
) -> dict[str, Any]:
    """Run the core pipeline while holding a lock and refreshing metadata."""
    identity: dict[str, Any] | None = None
    heartbeat: Heartbeat | None = None
    config_fd = -1
    try:
        validate_inherited_lock(lock_fd, paths.lock)
        if start_fd is not None:
            barrier_fd, start_fd = start_fd, None
            _wait_for_start_signal(barrier_fd)
        config_fd, _config_payload, launch_config_sha256 = _open_bound_config(
            config_path=config_path,
            paths=paths,
            run_id=run_id,
            isolated_session=isolated_session,
        )
        identity = read_proc_identity(os.getpid())
        if identity is None:
            raise ProcessControlError("cannot establish current process identity")
        record = _base_metadata(
            run_id=run_id,
            identity=identity,
            isolated_session=isolated_session,
            config_path=config_path,
            paths=paths,
            command=command,
            status="running",
            config_sha256=launch_config_sha256,
        )
        atomic_write_json(paths.process, record)
        heartbeat = Heartbeat(
            paths.process,
            pid=identity["pid"],
            proc_starttime=identity["proc_starttime"],
            interval=heartbeat_interval,
        )
        heartbeat.start()
        try:
            # Importing the scientific pipeline is intentionally delayed until
            # the lock, process identity, and output paths are established.
            from .pipeline import PipelineConfig, run_pipeline
            from .escalation import verify_materialized_child_pipeline

            policy_snapshot = _capture_durable_escalation_policy(
                repo_dir=repo_dir,
                config_path=config_path,
                config_sha256=launch_config_sha256,
                run_id=run_id,
                snapshot_path=paths.escalation_policy,
            )
            verify_materialized_child_pipeline(
                repo_dir=repo_dir,
                config_path=config_path,
                expected_pipeline_sha256=launch_config_sha256,
                required=False,
            )

            config_options: dict[str, Any] = {
                "repo_dir": repo_dir,
                "run_id": run_id,
            }
            if stage_review is not None:
                config_options["stage_review"] = stage_review
            if reviewer_model is not None:
                config_options["reviewer_model"] = reviewer_model
            if reviewer_effort is not None:
                config_options["reviewer_effort"] = reviewer_effort
            # Parse the already-open inode.  Replacing the pathname after the
            # launch barrier cannot change the scientific config used here.
            config = PipelineConfig.from_json(
                Path(f"/proc/self/fd/{config_fd}"), **config_options
            )
            result = _pending_escalation_parent_result(paths)
            if result is None:
                result = run_pipeline(config)
            if not isinstance(result, dict):
                raise ProcessControlError("run_pipeline must return a JSON object")
            escalation = reconcile_completed_campaign_escalation(
                repo_dir=repo_dir,
                pipeline_config_path=config_path,
                parent_run_id=run_id,
                result=result,
                python_executable=config.python_executable,
                expected_pipeline_config_sha256=launch_config_sha256,
                expected_registry_sha256=policy_snapshot.get("registry_sha256"),
            )
            if escalation is not None:
                # Do not mutate the in-memory object owned by FiveStagePipeline;
                # the link is operational metadata, not scientific gate state.
                result = dict(result)
                result["campaign_escalation"] = escalation
                if escalation.get("disposition") in {"blocked", "pending"}:
                    result["scientific_status"] = result.get("status")
                    result["status"] = "ESCALATION_PENDING"
        except BaseException as exc:
            heartbeat.stop()
            _update_process_record(
                paths.process,
                pid=identity["pid"],
                proc_starttime=identity["proc_starttime"],
                updates={
                    "status": "failed",
                    "finished_at": utc_now(),
                    "error": f"{type(exc).__name__}: {exc}",
                },
            )
            raise
        else:
            heartbeat.stop()
            finalize_process_result(
                paths.process,
                pid=identity["pid"],
                proc_starttime=identity["proc_starttime"],
                result=result,
            )
            return result
    finally:
        if config_fd >= 0:
            os.close(config_fd)
        if start_fd is not None:
            try:
                os.close(start_fd)
            except OSError:
                pass
        # An inherited flock must only be closed, never explicitly unlocked:
        # the parent and child initially share one open file description.
        close_run_lock(lock_fd, unlock=False)


def start_background(
    *,
    repo_dir: Path,
    config_path: Path,
    run_id: str,
    python_executable: str | Path = sys.executable,
    stage_review: bool | None = None,
    reviewer_model: str | None = None,
    reviewer_effort: str | None = None,
    expected_config_sha256: str | None = None,
    popen_factory: Callable[..., subprocess.Popen[Any]] = subprocess.Popen,
    identity_reader: Callable[[int], dict[str, Any] | None] = read_proc_identity,
) -> dict[str, Any]:
    """Start one detached worker and return its durable process record."""
    repo = resolve_repo_dir(repo_dir)
    config = resolve_config_path(config_path)
    launch_config_sha256 = hashlib.sha256(config.read_bytes()).hexdigest()
    if (
        expected_config_sha256 is not None
        and launch_config_sha256 != expected_config_sha256
    ):
        raise ProcessControlError("pipeline config changed before detached launch")
    safe_id = validate_run_id(run_id)
    paths = control_paths(repo, safe_id, create=True)
    lock_fd = acquire_run_lock(paths.lock)
    start_read_fd = start_write_fd = log_fd = -1
    process: subprocess.Popen[Any] | None = None
    try:
        start_read_fd, start_write_fd = os.pipe()
        command = [
            str(Path(python_executable).expanduser()),
            "-m",
            "humanize.pipeline_cli",
            "_worker",
            "--repo-dir",
            str(repo),
            "--config",
            str(config),
            "--run-id",
            safe_id,
            "--lock-fd",
            str(lock_fd),
            "--start-fd",
            str(start_read_fd),
        ]
        if stage_review is True:
            command.append("--stage-review")
        elif stage_review is False:
            command.append("--no-stage-review")
        if reviewer_model is not None:
            command.extend(["--reviewer-model", reviewer_model])
        if reviewer_effort is not None:
            command.extend(["--reviewer-effort", reviewer_effort])
        log_fd = os.open(
            paths.log,
            os.O_WRONLY | os.O_CREAT | os.O_APPEND | getattr(os, "O_NOFOLLOW", 0),
            0o600,
        )
        if not stat.S_ISREG(os.fstat(log_fd).st_mode):
            raise ProcessControlError(
                f"pipeline log is not a regular file: {paths.log}"
            )
        process = popen_factory(
            command,
            cwd=repo,
            stdin=subprocess.DEVNULL,
            stdout=log_fd,
            stderr=subprocess.STDOUT,
            close_fds=True,
            pass_fds=(lock_fd, start_read_fd),
            start_new_session=True,
            shell=False,
        )
        os.close(start_read_fd)
        start_read_fd = -1
        identity = None
        for _ in range(100):
            identity = identity_reader(int(process.pid))
            if identity is not None:
                break
            if process.poll() is not None:
                break
            time.sleep(0.01)
        if identity is None:
            raise ProcessControlError(
                f"detached worker exited before identity capture (pid={process.pid})"
            )
        if identity["pgid"] != process.pid or identity["session_id"] != process.pid:
            raise ProcessControlError(
                "detached worker did not establish an isolated process session"
            )
        record = _base_metadata(
            run_id=safe_id,
            identity=identity,
            isolated_session=True,
            config_path=config,
            paths=paths,
            command=command,
            status="starting",
            config_sha256=launch_config_sha256,
        )
        atomic_write_json(paths.process, record)
        os.write(start_write_fd, b"1")
        os.close(start_write_fd)
        start_write_fd = -1
        # Do not unlock: the worker inherited this open file description.
        close_run_lock(lock_fd, unlock=False)
        lock_fd = -1
        return record
    except BaseException:
        if start_read_fd >= 0:
            os.close(start_read_fd)
        if start_write_fd >= 0:
            os.close(start_write_fd)
        if process is not None and process.poll() is None:
            process.terminate()
            try:
                process.wait(timeout=2)
            except subprocess.TimeoutExpired:
                process.kill()
        if lock_fd >= 0:
            close_run_lock(lock_fd, unlock=False)
        raise
    finally:
        if log_fd >= 0:
            os.close(log_fd)


def run_foreground(
    *,
    repo_dir: Path,
    config_path: Path,
    run_id: str,
    heartbeat_interval: float = DEFAULT_HEARTBEAT_SECONDS,
    stage_review: bool | None = None,
    reviewer_model: str | None = None,
    reviewer_effort: str | None = None,
) -> dict[str, Any]:
    repo = resolve_repo_dir(repo_dir)
    config = resolve_config_path(config_path)
    safe_id = validate_run_id(run_id)
    paths = control_paths(repo, safe_id, create=True)
    lock_fd = acquire_run_lock(paths.lock)
    return execute_pipeline(
        repo_dir=repo,
        config_path=config,
        run_id=safe_id,
        paths=paths,
        lock_fd=lock_fd,
        isolated_session=False,
        command=sys.argv,
        heartbeat_interval=heartbeat_interval,
        stage_review=stage_review,
        reviewer_model=reviewer_model,
        reviewer_effort=reviewer_effort,
    )


def _safe_read(path: Path) -> tuple[dict[str, Any] | None, str | None]:
    try:
        return read_json_object(path), None
    except ProcessControlError as exc:
        return None, str(exc)


def status_for_run(
    *,
    repo_dir: Path,
    run_id: str,
    identity_reader: Callable[[int], dict[str, Any] | None] = read_proc_identity,
) -> dict[str, Any]:
    """Combine core state, process metadata, and live Linux identity."""
    repo = resolve_repo_dir(repo_dir)
    safe_id = validate_run_id(run_id)
    paths = control_paths(repo, safe_id, create=False)
    process, process_error = _safe_read(paths.process)
    state, state_error = _safe_read(paths.state)
    scope_error = (
        process_scope_error(process, repo_dir=repo, run_id=safe_id)
        if process is not None
        else None
    )
    if scope_error is not None:
        match = ProcessMatch(False, scope_error)
    elif process is not None:
        match = process_matches(process, identity_reader=identity_reader)
    else:
        match = ProcessMatch(False, process_error or "no process metadata")
    stored_status = process.get("status") if process else None
    state_status = state.get("status") if state else None
    if match.alive:
        status = stored_status or "running"
    elif process and process.get("result_status") == "ESCALATION_PENDING":
        status = "ESCALATION_PENDING"
    elif state_status in {
        "completed",
        "complete",
        "failed",
        "FAILED",
        "cancelled",
        "COMPLETED_NO_WIN",
        "COMPLETED_WIN",
        "INCOMPLETE",
    }:
        status = state_status
    elif stored_status in {"completed", "failed", "cancelled"}:
        status = stored_status
    elif process is not None:
        status = "stale"
    else:
        status = "not-started"
    return {
        "schema_version": PROCESS_SCHEMA_VERSION,
        "run_id": safe_id,
        "status": status,
        "alive": match.alive,
        "identity_reason": match.reason,
        "heartbeat_at": (
            process.get("heartbeat_at")
            if process
            else (state.get("heartbeat_at") if state else None)
        ),
        "state_updated_at": state.get("updated_at") if state else None,
        "process": process,
        "state": state,
        "errors": [
            error for error in (process_error, state_error) if error is not None
        ],
        "paths": {
            "root": str(paths.root),
            "state": str(paths.state),
            "process": str(paths.process),
            "log": str(paths.log),
        },
    }


def _validated_escalation_child_process(
    status: Mapping[str, Any],
    *,
    config_path: Path,
    config_sha256: str,
    child_run_id: str,
) -> Mapping[str, Any] | None:
    """Bind an existing child process record to its immutable child config."""

    process = status.get("process")
    if process is None:
        return None
    if not isinstance(process, Mapping):
        raise ProcessControlError("child process metadata is not an object")
    if process.get("run_id") != child_run_id:
        raise ProcessControlError("child process metadata has a different run_id")
    recorded_path = process.get("config_path")
    recorded_sha256 = process.get("config_sha256")
    try:
        resolved_recorded = Path(str(recorded_path)).resolve(strict=True)
    except (OSError, TypeError, ValueError) as exc:
        raise ProcessControlError(
            "child process metadata has an invalid config path"
        ) from exc
    if resolved_recorded != config_path.resolve(strict=True):
        raise ProcessControlError(
            "child process metadata points at a different config"
        )
    if recorded_sha256 != config_sha256:
        raise ProcessControlError(
            "child process metadata has a different config hash"
        )
    return process


def reconcile_completed_campaign_escalation(
    *,
    repo_dir: Path,
    pipeline_config_path: Path,
    parent_run_id: str,
    result: Mapping[str, Any],
    python_executable: str | Path,
    expected_pipeline_config_sha256: str | None = None,
    expected_registry_sha256: str | None = None,
    launcher: Callable[..., Mapping[str, Any]] | None = None,
    status_reader: Callable[..., Mapping[str, Any]] | None = None,
) -> dict[str, Any] | None:
    """Materialize and start one hash-bound child after a clean no-WIN run.

    The scientific pipeline and its Humanize lease have already unwound when
    this function is called.  A crash between child spawn and parent bookkeeping
    is recovered by adopting the exact child process/config binding.
    """

    if result.get("status") not in ESCALATION_PARENT_STATUSES:
        return None
    repo = resolve_repo_dir(repo_dir)
    safe_parent = validate_run_id(parent_run_id)
    parent_paths = control_paths(repo, safe_parent, create=True)
    state_path = repo / "results" / "humanize" / safe_parent / "state.json"
    destination = parent_paths.root / "escalation" / "child-pipeline.json"
    outcome_path = parent_paths.root / "campaign-escalation.json"

    try:
        from .escalation import (
            reconcile_campaign_escalation,
            verify_materialized_child_pipeline,
        )

        reconciliation = reconcile_campaign_escalation(
            repo_dir=repo,
            parent_state_path=state_path,
            pipeline_config_path=pipeline_config_path,
            destination=destination,
            expected_pipeline_config_sha256=expected_pipeline_config_sha256,
            expected_registry_sha256=expected_registry_sha256,
        )
        outcome = reconciliation.serializable()
        outcome["reconciled_at"] = utc_now()
        if reconciliation.disposition == "disabled":
            # A prior launch-intent may survive a crash followed by an
            # explicitly disabled policy.  Record the successful reconciliation
            # so future starts do not remain trapped in retry-only mode.
            outcome["launch"] = {"status": "not-started"}
            atomic_write_json(outcome_path, outcome)
            return None
        if reconciliation.materialized is None:
            outcome["launch"] = {"status": "not-started"}
            if reconciliation.disposition == "blocked":
                outcome["disposition"] = "pending"
                outcome["retryable"] = True
            atomic_write_json(outcome_path, outcome)
            return outcome

        child = reconciliation.materialized
        child_config = child.path.resolve(strict=True)
        if hashlib.sha256(child_config.read_bytes()).hexdigest() != child.pipeline_sha256:
            raise ProcessControlError(
                "materialized child config changed before process reconciliation"
            )
        verify_materialized_child_pipeline(
            repo_dir=repo,
            config_path=child_config,
            expected_pipeline_sha256=child.pipeline_sha256,
            required=True,
        )

        # Parsing the complete child config before Popen catches any mismatch
        # between the registry's shallow launch claim and the real five-stage
        # configuration contract.
        from .pipeline import PipelineConfig

        PipelineConfig.from_json(
            child_config,
            repo_dir=repo,
            run_id=child.child_run_id,
        )

        # Commit intent before the first operation that can spawn the child.
        # If this process is killed after start_background() succeeds but before
        # final bookkeeping, the next parent invocation sees ``pending`` and
        # performs reconciliation only instead of rerunning Stages 1--5.
        launch_intent = dict(outcome)
        launch_intent["disposition"] = "pending"
        launch_intent["retryable"] = True
        launch_intent["launch"] = {
            "status": "pending-launch-intent",
            "child_run_id": child.child_run_id,
            "config_path": str(child_config),
            "config_sha256": child.pipeline_sha256,
        }
        launch_intent["reconciled_at"] = utc_now()
        atomic_write_json(outcome_path, launch_intent)

        read_status = status_reader or status_for_run
        child_status = read_status(repo_dir=repo, run_id=child.child_run_id)
        process = _validated_escalation_child_process(
            child_status,
            config_path=child_config,
            config_sha256=child.pipeline_sha256,
            child_run_id=child.child_run_id,
        )

        if child_status.get("alive") is True:
            assert process is not None
            launch = {
                "status": "adopted-running",
                "pid": process.get("pid"),
                "proc_starttime": process.get("proc_starttime"),
            }
        elif child_status.get("status") in {
            "COMPLETED_WIN",
            "COMPLETED_NO_WIN",
            "completed",
        }:
            launch = {
                "status": "existing-terminal",
                "child_status": child_status.get("status"),
            }
        elif child_status.get("status") in {"INCOMPLETE", "cancelled"}:
            raise ProcessControlError(
                "existing escalation child ended unsuccessfully; manual audit required"
            )
        elif child_status.get("status") not in {
            "stale",
            "not-started",
            "FAILED",
            "failed",
        }:
            raise ProcessControlError(
                "existing child process is neither live, terminal, nor safely stale"
            )
        else:
            resume_failed_child = child_status.get("status") in {
                "FAILED",
                "failed",
            }
            start = launcher or start_background
            try:
                record = start(
                    repo_dir=repo,
                    config_path=child_config,
                    run_id=child.child_run_id,
                    python_executable=python_executable,
                    expected_config_sha256=child.pipeline_sha256,
                )
            except AlreadyRunningError:
                # A concurrent reconciler may have won after our status read.
                raced_status = read_status(
                    repo_dir=repo, run_id=child.child_run_id
                )
                raced = _validated_escalation_child_process(
                    raced_status,
                    config_path=child_config,
                    config_sha256=child.pipeline_sha256,
                    child_run_id=child.child_run_id,
                )
                if raced_status.get("alive") is not True or raced is None:
                    raise
                record = raced
                launch_status = "adopted-racing-start"
            else:
                launch_status = (
                    "resumed-failed" if resume_failed_child else "started"
                )
                _validated_escalation_child_process(
                    {"process": record},
                    config_path=child_config,
                    config_sha256=child.pipeline_sha256,
                    child_run_id=child.child_run_id,
                )
            launch = {
                "status": launch_status,
                "pid": record.get("pid"),
                "proc_starttime": record.get("proc_starttime"),
            }
        outcome["launch"] = launch
        outcome["reconciled_at"] = utc_now()
        atomic_write_json(outcome_path, outcome)
        return outcome
    except Exception as exc:
        blocked = {
            "schema_version": 1,
            "kind": "qcode-campaign-escalation-reconciliation",
            "disposition": "pending",
            "classification": type(exc).__name__,
            "error": str(exc),
            "retryable": True,
            "parent_result_status": result.get("status"),
            "reconciled_at": utc_now(),
            "launch": {"status": "not-started"},
        }
        atomic_write_json(outcome_path, blocked)
        return blocked


def _session_group_members(
    *,
    pgid: int,
    session_id: int,
    uid: int,
) -> list[int]:
    """Return same-uid members proving that a process group is still ours."""
    members: list[int] = []
    for entry in Path("/proc").iterdir():
        if not entry.name.isdigit():
            continue
        pid = int(entry.name)
        try:
            _, fields = _proc_stat(pid)
            if (
                len(fields) >= 4
                and fields[0] != "Z"
                and int(fields[2]) == pgid
                and int(fields[3]) == session_id
                and entry.stat().st_uid == uid
            ):
                members.append(pid)
        except (FileNotFoundError, PermissionError, OSError, ValueError):
            continue
    return members


def _wait_until_group_stops(
    *,
    metadata: Mapping[str, Any],
    deadline: float,
    poll_interval: float,
    identity_reader: Callable[[int], dict[str, Any] | None],
    group_members_reader: Callable[..., list[int]],
    sleep: Callable[[float], None],
    monotonic: Callable[[], float],
) -> bool:
    if metadata.get("isolated_session") is True:
        pgid = int(metadata["pgid"])
        session_id = int(metadata["session_id"])
        uid = int(metadata["uid"])
        while monotonic() < deadline:
            leader = process_matches(metadata, identity_reader=identity_reader)
            members = group_members_reader(pgid=pgid, session_id=session_id, uid=uid)
            if not leader.alive and not members:
                return True
            sleep(poll_interval)
        return False
    while monotonic() < deadline:
        if not process_matches(metadata, identity_reader=identity_reader).alive:
            return True
        sleep(poll_interval)
    return False


def cancel_run(
    *,
    repo_dir: Path,
    run_id: str,
    grace_seconds: float = 30.0,
    poll_interval: float = 0.2,
    identity_reader: Callable[[int], dict[str, Any] | None] = read_proc_identity,
    group_members_reader: Callable[..., list[int]] = _session_group_members,
    kill_process: Callable[[int, int], None] = os.kill,
    kill_group: Callable[[int, int], None] = os.killpg,
    sleep: Callable[[float], None] = time.sleep,
    monotonic: Callable[[], float] = time.monotonic,
) -> dict[str, Any]:
    """Safely terminate a recorded run without signalling a reused PID."""
    if grace_seconds < 0:
        raise ValueError("grace_seconds must be non-negative")
    if poll_interval <= 0:
        raise ValueError("poll_interval must be positive")
    repo = resolve_repo_dir(repo_dir)
    safe_id = validate_run_id(run_id)
    paths = control_paths(repo, safe_id, create=False)
    metadata = read_json_object(paths.process)
    if metadata is None:
        raise UnsafeProcessError("no process metadata; refusing to signal")
    scope_error = process_scope_error(metadata, repo_dir=repo, run_id=safe_id)
    if scope_error is not None:
        raise UnsafeProcessError(f"refusing to signal: {scope_error}")
    match = process_matches(metadata, identity_reader=identity_reader)
    if not match.alive:
        raise UnsafeProcessError(f"refusing to signal: {match.reason}")

    pid = int(metadata["pid"])
    isolated = metadata.get("isolated_session") is True
    pgid = int(metadata["pgid"])
    session_id = int(metadata["session_id"])
    if isolated:
        if pgid != pid or session_id != pid:
            raise UnsafeProcessError(
                "isolated worker metadata does not identify its own session/group"
            )
        kill_group(pgid, signal.SIGTERM)
    else:
        kill_process(pid, signal.SIGTERM)

    stopped = _wait_until_group_stops(
        metadata=metadata,
        deadline=monotonic() + grace_seconds,
        poll_interval=poll_interval,
        identity_reader=identity_reader,
        group_members_reader=group_members_reader,
        sleep=sleep,
        monotonic=monotonic,
    )
    forced = False
    if not stopped:
        if isolated:
            members = group_members_reader(
                pgid=pgid,
                session_id=session_id,
                uid=int(metadata["uid"]),
            )
            leader_match = process_matches(metadata, identity_reader=identity_reader)
            if not leader_match.alive and not members:
                stopped = True
            elif members or leader_match.alive:
                kill_group(pgid, signal.SIGKILL)
                forced = True
        else:
            leader_match = process_matches(metadata, identity_reader=identity_reader)
            if leader_match.alive:
                kill_process(pid, signal.SIGKILL)
                forced = True

    final_deadline = monotonic() + max(1.0, poll_interval * 5)
    stopped = _wait_until_group_stops(
        metadata=metadata,
        deadline=final_deadline,
        poll_interval=poll_interval,
        identity_reader=identity_reader,
        group_members_reader=group_members_reader,
        sleep=sleep,
        monotonic=monotonic,
    )
    result_status = "cancelled" if stopped else "termination-pending"
    _update_process_record(
        paths.process,
        pid=pid,
        proc_starttime=int(metadata["proc_starttime"]),
        updates={
            "status": result_status,
            "finished_at": utc_now() if stopped else None,
            "termination_signal": "SIGKILL" if forced else "SIGTERM",
        },
    )
    return {
        "run_id": safe_id,
        "status": result_status,
        "pid": pid,
        "pgid": pgid,
        "forced": forced,
        "stopped": stopped,
    }
