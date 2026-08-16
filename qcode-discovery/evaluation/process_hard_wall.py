"""Small process-enforced hard-wall primitives for proof solver phases.

``concurrent.futures`` timeouts do not stop the worker that is executing C
code. Proof work therefore runs behind a verified private process/session
boundary; legacy pools can still be abandoned with
:func:`terminate_process_pool` when a wall deadline expires.
"""

from __future__ import annotations

import multiprocessing
import math
import os
import select
import signal
import traceback
from concurrent.futures import ProcessPoolExecutor
from ctypes import CDLL, c_int, c_ulong, get_errno
from dataclasses import dataclass, field
from multiprocessing.connection import Connection
from multiprocessing.process import BaseProcess
from pathlib import Path
from time import monotonic as _monotonic
from time import sleep as _sleep
from typing import Any, Callable, Mapping, Sequence


DEFAULT_TERMINATION_GRACE_S = 1.0
DEFAULT_READY_TIMEOUT_S = 5.0


def positive_wall_timeout(value: float, label: str) -> float:
    """Validate and normalize one process-enforced wall budget."""

    timeout = float(value)
    if not math.isfinite(timeout) or timeout <= 0:
        raise ValueError(f"{label} must be a positive finite number")
    return timeout


def set_linux_parent_death_signal(expected_parent_pid: int) -> None:
    """Kill a worker when its exact creating process disappears.

    Isolated proof workers deliberately leave their parent's process group, so
    an outer controller cancellation cannot rely on group inheritance alone.
    Linux ``PR_SET_PDEATHSIG`` closes that gap.  The PPID check handles the race
    where the parent exits between ``fork`` and ``prctl``.
    """

    if not sys_platform_linux():
        return
    libc = CDLL(None, use_errno=True)
    prctl = libc.prctl
    prctl.restype = c_int
    result = prctl(
        c_int(1),  # PR_SET_PDEATHSIG
        c_ulong(signal.SIGKILL),
        c_ulong(0),
        c_ulong(0),
        c_ulong(0),
    )
    if result != 0:
        error_number = get_errno()
        raise OSError(error_number, os.strerror(error_number))
    if os.getppid() != expected_parent_pid:
        os.kill(os.getpid(), signal.SIGKILL)
        os._exit(128 + signal.SIGKILL)


def sys_platform_linux() -> bool:
    """Keep the Linux probe tiny and easy to monkeypatch in process tests."""

    import sys

    return sys.platform.startswith("linux")


def _parse_linux_process_stat(stat_line: str) -> tuple[str, int, int, int]:
    suffix = stat_line[stat_line.rindex(")") + 2 :].split()
    return (
        suffix[0],
        int(suffix[2]),
        int(suffix[3]),
        int(suffix[19]),
    )


def linux_process_start_time(pid: int) -> int | None:
    """Return Linux /proc start ticks, used as a PID/session reuse guard."""

    if not sys_platform_linux():
        return None
    try:
        _, _, _, start_time = _parse_linux_process_stat(
            Path(f"/proc/{pid}/stat").read_text()
        )
    except (OSError, ValueError, IndexError):
        return None
    return start_time


def _isolated_call_entry(
    connection: Connection,
    expected_parent_pid: int,
    operation: Callable[..., Any],
    args: tuple[Any, ...],
    kwargs: dict[str, Any],
) -> None:
    """Run one potentially blocking proof call in its own session."""

    try:
        signal.signal(signal.SIGTERM, signal.SIG_DFL)
        set_linux_parent_death_signal(expected_parent_pid)
        isolated = False
        if hasattr(os, "setsid"):
            os.setsid()
            isolated = True
        identity = {
            "pid": os.getpid(),
            "pgid": os.getpgid(0) if hasattr(os, "getpgid") else os.getpid(),
            "session_id": os.getsid(0) if hasattr(os, "getsid") else os.getpid(),
            "start_time_ticks": linux_process_start_time(os.getpid()),
            "isolated_session": isolated,
        }
        connection.send(("ready", identity))
        try:
            value = operation(*args, **kwargs)
        except BaseException as exc:
            connection.send((
                "error",
                type(exc).__name__,
                str(exc),
                traceback.format_exc(),
            ))
        else:
            connection.send(("result", value))
    except BaseException:
        # The parent treats EOF before a valid result as an operational error.
        # Avoid a second best-effort send here: setup failures can include a
        # broken communication channel.
        pass
    finally:
        connection.close()


@dataclass
class IsolatedCallOutcome:
    """Terminal state of one process-enforced proof call."""

    status: str
    value: Any = None
    error: str | None = None
    traceback: str | None = None
    hard_wall: dict[str, Any] | None = None


class IsolatedCallStartupTimeout(TimeoutError):
    """An isolated worker exhausted its wall before the identity handshake."""

    def __init__(
        self,
        message: str,
        *,
        timeout_s: float,
        hard_wall: Mapping[str, Any],
    ) -> None:
        super().__init__(message)
        self.timeout_s = timeout_s
        self.hard_wall = dict(hard_wall)


@dataclass
class IsolatedCallHandle:
    """A live isolated proof call that can be polled alongside peer calls."""

    process: BaseProcess
    connection: Connection
    deadline: float
    timeout_s: float
    identity: dict[str, Any]
    termination_grace_s: float
    message: tuple[Any, ...] | None = None
    closed: bool = False
    started_at: float = field(default_factory=_monotonic)

    @property
    def pid(self) -> int:
        if self.process.pid is None:
            raise RuntimeError("isolated proof worker has no pid")
        return int(self.process.pid)

    def remaining(self) -> float:
        return max(0.0, self.deadline - _monotonic())


def _multiprocessing_context() -> multiprocessing.context.BaseContext:
    """Use a fresh interpreter so inherited native-library threads are absent."""

    return multiprocessing.get_context("spawn")


def _receive_ready(
    process: BaseProcess,
    connection: Connection,
    *,
    deadline: float,
) -> dict[str, Any]:
    ready_deadline = min(deadline, _monotonic() + DEFAULT_READY_TIMEOUT_S)
    while _monotonic() < ready_deadline:
        if connection.poll(min(0.01, max(0.0, ready_deadline - _monotonic()))):
            try:
                message = connection.recv()
            except EOFError as exc:
                raise RuntimeError(
                    "isolated proof worker exited before its ready handshake"
                ) from exc
            if (
                not isinstance(message, tuple)
                or len(message) != 2
                or message[0] != "ready"
                or not isinstance(message[1], Mapping)
            ):
                raise RuntimeError("isolated proof worker sent an invalid handshake")
            identity = dict(message[1])
            pid = process.pid
            if (
                pid is None
                or identity.get("pid") != int(pid)
                or not isinstance(identity.get("pgid"), int)
                or not isinstance(identity.get("session_id"), int)
            ):
                raise RuntimeError("isolated proof worker identity is inconsistent")
            if sys_platform_linux():
                reported_start = identity.get("start_time_ticks")
                observed_start = linux_process_start_time(int(pid))
                if (
                    not isinstance(reported_start, int)
                    or observed_start != reported_start
                ):
                    raise RuntimeError(
                        "isolated proof worker start identity is inconsistent"
                    )
            if hasattr(os, "setsid") and not (
                identity.get("isolated_session") is True
                and identity["pgid"] == int(pid)
                and identity["session_id"] == int(pid)
            ):
                raise RuntimeError(
                    "isolated proof worker did not establish its own session"
                )
            return identity
        if process.exitcode is not None:
            raise RuntimeError(
                "isolated proof worker exited before its ready handshake"
            )
    raise TimeoutError("isolated proof worker ready handshake timed out")


def start_isolated_call(
    operation: Callable[..., Any],
    *,
    args: Sequence[Any] = (),
    kwargs: Mapping[str, Any] | None = None,
    timeout_s: float,
    termination_grace_s: float = DEFAULT_TERMINATION_GRACE_S,
) -> IsolatedCallHandle:
    """Start one proof operation behind a submit-time process hard wall."""

    timeout = positive_wall_timeout(timeout_s, "isolated call timeout")
    grace = positive_wall_timeout(termination_grace_s, "termination grace")
    context = _multiprocessing_context()
    parent, child = context.Pipe(duplex=False)
    started = _monotonic()
    process = context.Process(
        target=_isolated_call_entry,
        args=(
            child,
            os.getpid(),
            operation,
            tuple(args),
            dict(kwargs or {}),
        ),
        daemon=False,
        name="qcode-isolated-proof-call",
    )
    try:
        process.start()
    except BaseException:
        child.close()
        parent.close()
        raise
    child.close()
    deadline = started + timeout
    try:
        identity = _receive_ready(process, parent, deadline=deadline)
    except BaseException as exc:
        pid = process.pid
        observed_identity: dict[str, Any] = {
            "pid": pid,
            "pgid": None,
            "session_id": None,
            "start_time_ticks": (
                None if pid is None else linux_process_start_time(int(pid))
            ),
            "isolated_session": False,
        }
        if pid is not None and hasattr(os, "getpgid") and hasattr(os, "getsid"):
            try:
                observed_pgid = os.getpgid(int(pid))
                observed_session = os.getsid(int(pid))
            except ProcessLookupError:
                pass
            else:
                observed_identity.update(
                    {
                        "pgid": observed_pgid,
                        "session_id": observed_session,
                        "isolated_session": (
                            observed_pgid == int(pid)
                            and observed_session == int(pid)
                        ),
                    }
                )
        provisional = IsolatedCallHandle(
            process=process,
            connection=parent,
            deadline=deadline,
            timeout_s=timeout,
            identity=observed_identity,
            termination_grace_s=grace,
            started_at=started,
        )
        report = terminate_isolated_call(provisional)
        if isinstance(exc, TimeoutError):
            raise IsolatedCallStartupTimeout(
                str(exc),
                timeout_s=timeout,
                hard_wall={
                    **report,
                    "timed_out": True,
                    "startup_timed_out": True,
                    "timeout_s": timeout,
                },
            ) from exc
        raise
    return IsolatedCallHandle(
        process=process,
        connection=parent,
        deadline=deadline,
        timeout_s=timeout,
        identity=identity,
        termination_grace_s=grace,
        started_at=started,
    )


def _linux_group_has_live_members(
    pgid: int,
    session_id: int | None,
    session_leader_start_time: int | None,
) -> bool | None:
    """Distinguish live members from already-killed orphan zombies."""

    if not sys_platform_linux():
        return None
    proc = "/proc"
    try:
        entries = os.listdir(proc)
    except OSError:
        return None
    has_live_member = False
    session_identity_reused = False
    for entry in entries:
        if not entry.isdigit():
            continue
        try:
            (
                state,
                process_group,
                process_session,
                start_time,
            ) = _parse_linux_process_stat(
                Path(f"{proc}/{entry}/stat").read_text()
            )
        except PermissionError:
            return None
        except (OSError, ValueError, IndexError):
            continue
        if process_group != pgid or (
            session_id is not None and process_session != session_id
        ):
            continue
        if (
            session_id is not None
            and session_leader_start_time is not None
            and int(entry) == session_id
            and start_time != session_leader_start_time
        ):
            session_identity_reused = True
        if state not in {"Z", "X"}:
            has_live_member = True
    if session_identity_reused:
        return False
    return has_live_member


def process_group_alive(
    pgid: int,
    *,
    session_id: int | None = None,
    session_leader_start_time: int | None = None,
) -> bool:
    """Return whether a process group contains at least one runnable member."""

    try:
        os.killpg(pgid, 0)
    except ProcessLookupError:
        return False
    except PermissionError:
        return True
    linux_live = _linux_group_has_live_members(
        pgid,
        session_id,
        session_leader_start_time,
    )
    return True if linux_live is None else linux_live


def _verified_isolated_group(handle: IsolatedCallHandle) -> int | None:
    pid = handle.process.pid
    pgid = handle.identity.get("pgid")
    session_id = handle.identity.get("session_id")
    start_time = handle.identity.get("start_time_ticks")
    if (
        pid is None
        or not isinstance(pgid, int)
        or not isinstance(session_id, int)
        or (sys_platform_linux() and not isinstance(start_time, int))
        or pgid != int(pid)
        or session_id != int(pid)
        or handle.identity.get("isolated_session") is not True
        or not hasattr(os, "killpg")
    ):
        return None
    try:
        observed_pgid = os.getpgid(int(pid))
        observed_session = os.getsid(int(pid))
    except ProcessLookupError:
        # The leader may have exited while descendants in its private group are
        # still alive.  The recorded group remains safe to target because it was
        # created uniquely for this handle and has not yet been declared closed.
        return (
            pgid
            if process_group_alive(
                pgid,
                session_id=session_id,
                session_leader_start_time=start_time,
            )
            else None
        )
    if observed_pgid != pgid or observed_session != session_id:
        raise RuntimeError("isolated proof worker process identity changed")
    if (
        sys_platform_linux()
        and linux_process_start_time(int(pid)) != start_time
    ):
        raise RuntimeError("isolated proof worker PID identity changed")
    return pgid


def terminate_isolated_call(handle: IsolatedCallHandle) -> dict[str, Any]:
    """TERM then KILL exactly one verified isolated worker/session."""

    if handle.closed:
        return {
            "worker_pid": handle.process.pid,
            "process_group_id": handle.identity.get("pgid"),
            "forced": False,
            "already_closed": True,
        }
    grace = handle.termination_grace_s
    session_id = handle.identity.get("session_id")
    session_leader_start_time = handle.identity.get("start_time_ticks")
    identity_error: RuntimeError | None = None
    try:
        pgid = _verified_isolated_group(handle)
    except RuntimeError as exc:
        # Never signal an unverified group.  The exact multiprocessing child is
        # still safe to terminate, and PDEATHSIG cleans its proof descendants.
        identity_error = exc
        pgid = None
    pid = handle.process.pid
    if pgid is not None:
        try:
            os.killpg(pgid, signal.SIGTERM)
        except ProcessLookupError:
            pass
    elif handle.process.is_alive():
        handle.process.terminate()

    deadline = _monotonic() + grace
    while (
        handle.process.is_alive()
        or (
            pgid is not None
            and process_group_alive(
                pgid,
                session_id=session_id,
                session_leader_start_time=session_leader_start_time,
            )
        )
    ) and _monotonic() < deadline:
        handle.process.join(
            timeout=min(0.01, max(0.0, deadline - _monotonic()))
        )
    forced = False
    group_survived = pgid is not None and process_group_alive(
        pgid,
        session_id=session_id,
        session_leader_start_time=session_leader_start_time,
    )
    if handle.process.is_alive() or group_survived:
        forced = True
        if pgid is not None:
            try:
                os.killpg(pgid, signal.SIGKILL)
            except ProcessLookupError:
                pass
        elif handle.process.is_alive():
            handle.process.kill()
        kill_deadline = _monotonic() + grace
        while (
            handle.process.is_alive()
            or (
                pgid is not None
                and process_group_alive(
                    pgid,
                    session_id=session_id,
                    session_leader_start_time=session_leader_start_time,
                )
            )
        ) and _monotonic() < kill_deadline:
            handle.process.join(
                timeout=min(
                    0.01,
                    max(0.0, kill_deadline - _monotonic()),
                )
            )

    lingering = bool(
        handle.process.is_alive()
        or (
            pgid is not None
            and process_group_alive(
                pgid,
                session_id=session_id,
                session_leader_start_time=session_leader_start_time,
            )
        )
    )
    handle.connection.close()
    handle.closed = True
    if lingering:
        raise RuntimeError(
            "isolated proof process group still has live members after SIGKILL"
        )
    if identity_error is not None:
        raise RuntimeError(
            "isolated proof worker identity changed; exact worker was killed"
        ) from identity_error
    return {
        "worker_pid": pid,
        "process_group_id": pgid,
        "forced": forced,
        "termination_grace_s": grace,
    }


def poll_isolated_call(
    handle: IsolatedCallHandle,
) -> IsolatedCallOutcome | None:
    """Poll one handle without blocking peer proof calls."""

    if handle.closed:
        raise RuntimeError("isolated proof call is already closed")
    if handle.message is None and handle.connection.poll(0):
        try:
            raw = handle.connection.recv()
        except EOFError:
            raw = None
        if isinstance(raw, tuple):
            handle.message = raw
    handle.process.join(timeout=0)
    if handle.process.exitcode is not None:
        # The worker may have sent its envelope between the first nonblocking
        # poll and exit observation.  Give the already-closed writer a bounded
        # final drain so a valid proof result is never misclassified as a
        # worker crash.
        if handle.message is None and handle.connection.poll(0.05):
            try:
                raw = handle.connection.recv()
            except EOFError:
                raw = None
            if isinstance(raw, tuple):
                handle.message = raw
        message = handle.message
        pgid = handle.identity.get("pgid")
        session_id = handle.identity.get("session_id")
        start_time = handle.identity.get("start_time_ticks")
        descendant_cleanup = bool(
            isinstance(pgid, int)
            and isinstance(session_id, int)
            and process_group_alive(
                pgid,
                session_id=session_id,
                session_leader_start_time=(
                    start_time if isinstance(start_time, int) else None
                ),
            )
        )
        cleanup_report = terminate_isolated_call(handle)
        cleanup_evidence = (
            {
                **cleanup_report,
                "descendant_cleanup": True,
            }
            if descendant_cleanup
            else None
        )
        if not message:
            return IsolatedCallOutcome(
                status="error",
                error=(
                    "isolated proof worker exited without a result "
                    f"(exitcode={handle.process.exitcode})"
                ),
                hard_wall=cleanup_evidence,
            )
        if message[0] == "result" and len(message) == 2:
            return IsolatedCallOutcome(
                status="completed",
                value=message[1],
                hard_wall=cleanup_evidence,
            )
        if message[0] == "error" and len(message) == 4:
            return IsolatedCallOutcome(
                status="error",
                error=f"{message[1]}: {message[2]}",
                traceback=str(message[3]),
                hard_wall=cleanup_evidence,
            )
        return IsolatedCallOutcome(
            status="error",
            error="isolated proof worker returned an invalid result envelope",
            hard_wall=cleanup_evidence,
        )
    if _monotonic() < handle.deadline:
        return None
    report = terminate_isolated_call(handle)
    # A result sent before a worker became stuck in interpreter/native cleanup
    # is complete evidence.  Preserve it while still reporting the forced
    # cleanup so no child process is leaked.
    message = handle.message
    if message and message[0] == "result" and len(message) == 2:
        return IsolatedCallOutcome(
            status="completed",
            value=message[1],
            hard_wall={**report, "cleanup_forced": True},
        )
    return IsolatedCallOutcome(
        status="timeout",
        error=f"isolated proof call exceeded {handle.timeout_s:g}s",
        hard_wall={
            **report,
            "timed_out": True,
            "timeout_s": handle.timeout_s,
        },
    )


def run_isolated_call(
    operation: Callable[..., Any],
    *,
    args: Sequence[Any] = (),
    kwargs: Mapping[str, Any] | None = None,
    timeout_s: float,
    termination_grace_s: float = DEFAULT_TERMINATION_GRACE_S,
) -> IsolatedCallOutcome:
    """Synchronously run one isolated proof call with a process hard wall."""

    try:
        handle = start_isolated_call(
            operation,
            args=args,
            kwargs=kwargs,
            timeout_s=timeout_s,
            termination_grace_s=termination_grace_s,
        )
    except IsolatedCallStartupTimeout as exc:
        return IsolatedCallOutcome(
            status="timeout",
            error=str(exc),
            hard_wall=dict(exc.hard_wall),
        )
    while True:
        outcome = poll_isolated_call(handle)
        if outcome is not None:
            return outcome
        _sleep(min(0.01, handle.remaining()))


def terminate_process_pool(
    executor: ProcessPoolExecutor,
    *,
    grace_s: float = DEFAULT_TERMINATION_GRACE_S,
) -> dict[str, Any]:
    """Stop every current pool worker with TERM, then KILL survivors.

    ``ProcessPoolExecutor`` has no public API for terminating an executing
    future.  Taking a snapshot of its worker processes is intentionally kept
    in this one compatibility shim.  Callers abandon the whole pool on a hard
    timeout; completed proof artifacts/checkpoints remain durable and a fresh
    pool is created by the next controller retry.
    """

    grace = positive_wall_timeout(grace_s, "termination grace")
    raw_processes = getattr(executor, "_processes", None)
    if not isinstance(raw_processes, dict):
        raise RuntimeError("process executor does not expose managed workers")
    processes: list[BaseProcess] = list(raw_processes.values())
    workers: list[dict[str, Any]] = []
    for process in processes:
        if process.pid is None:
            continue
        pid = int(process.pid)
        start_time = linux_process_start_time(pid)
        pidfd: int | None = None
        if sys_platform_linux() and start_time is not None and hasattr(
            os, "pidfd_open"
        ):
            try:
                candidate_fd = os.pidfd_open(pid, 0)
            except OSError:
                candidate_fd = None
            if candidate_fd is not None:
                # Opening by numeric PID and signalling later must never cross
                # a PID-reuse boundary. A pidfd is stable after opening, but
                # compare /proc identities on both sides of the open so the
                # descriptor is known to name this exact BaseProcess child.
                if linux_process_start_time(pid) == start_time:
                    pidfd = candidate_fd
                else:
                    os.close(candidate_fd)
        workers.append({
            "process": process,
            "pid": pid,
            "start_time": start_time,
            "pidfd": pidfd,
        })
    pids = [int(worker["pid"]) for worker in workers]

    def worker_alive(worker: Mapping[str, Any]) -> bool:
        descriptor = worker["pidfd"]
        if descriptor is not None:
            poller = select.poll()
            poller.register(int(descriptor), select.POLLIN)
            return not bool(poller.poll(0))
        pid = int(worker["pid"])
        start_time = worker["start_time"]
        if sys_platform_linux() and start_time is not None:
            # This also rejects a reused PID without signalling the new owner.
            return linux_process_start_time(pid) == start_time
        return bool(worker["process"].is_alive())

    def signal_worker(worker: Mapping[str, Any], *, force: bool) -> None:
        if not worker_alive(worker):
            return
        descriptor = worker["pidfd"]
        try:
            if descriptor is not None and hasattr(signal, "pidfd_send_signal"):
                signum = signal.SIGKILL if force else signal.SIGTERM
                signal.pidfd_send_signal(int(descriptor), signum, None, 0)
            else:
                # Keep the portable multiprocessing fallback on platforms
                # without Linux pidfds. BaseProcess owns the child identity
                # there and implements the appropriate OS-specific signal.
                process = worker["process"]
                if force and hasattr(process, "kill"):
                    process.kill()
                else:
                    process.terminate()
        except ProcessLookupError:
            return

    def wait_for_exit(deadline: float) -> None:
        while any(worker_alive(worker) for worker in workers):
            remaining = deadline - _monotonic()
            if remaining <= 0:
                return
            _sleep(min(0.01, remaining))

    try:
        for worker in workers:
            signal_worker(worker, force=False)
        wait_for_exit(_monotonic() + grace)

        forced = [
            int(worker["pid"])
            for worker in workers
            if worker_alive(worker)
        ]
        forced_set = set(forced)
        for worker in workers:
            if int(worker["pid"]) in forced_set:
                signal_worker(worker, force=True)
        wait_for_exit(_monotonic() + grace)

        lingering = [
            int(worker["pid"])
            for worker in workers
            if worker_alive(worker)
        ]
        # Refresh BaseProcess bookkeeping only after the kernel says the exact
        # pidfd has exited. ProcessPoolExecutor's management thread may have
        # won the waitpid race; join(timeout=0) is therefore best-effort and
        # its stale is_alive() result is deliberately not authoritative.
        for worker in workers:
            if int(worker["pid"]) not in lingering:
                worker["process"].join(timeout=0)
    finally:
        for worker in workers:
            descriptor = worker["pidfd"]
            if descriptor is not None:
                os.close(int(descriptor))
    # The processes are already reaped above, so this never waits on solver C
    # code.  It asks the executor's management thread to discard queued work.
    executor.shutdown(wait=False, cancel_futures=True)
    if lingering:
        raise RuntimeError(
            "hard-wall process pool still has live workers: "
            + ", ".join(map(str, lingering))
        )
    return {
        "worker_pids": pids,
        "forced_worker_pids": forced,
        "termination_grace_s": grace,
    }
