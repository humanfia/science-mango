"""Crash-safe process-group supervisor for the external DistQLDPC solver.

The Stage-3 candidate worker and each DistQLDPC lane deliberately use distinct
sessions. This small exec boundary gives the lane a Linux parent-death signal
without using ``preexec_fn`` in the multi-threaded candidate worker. The
supervisor and every solver descendant remain in one private process group, so
an unexpected candidate-worker death still terminates the full solver tree.
"""

from __future__ import annotations

import argparse
import ctypes
import math
import os
import signal
import subprocess
import sys
import time
from pathlib import Path
from typing import Sequence


SUPERVISOR_PROTOCOL = "qcode-distqldpc-supervisor-v1"
_TERMINATION_TERM_PHASE_MAX_S = 1.0
_STOP_REQUESTED = False


def _request_stop(_signum: int, _frame: object) -> None:
    global _STOP_REQUESTED
    _STOP_REQUESTED = True


def _set_parent_death_signal(expected_parent_pid: int) -> None:
    if not sys.platform.startswith("linux"):
        raise RuntimeError("DistQLDPC supervisor requires Linux PDEATHSIG")
    libc = ctypes.CDLL(None, use_errno=True)
    prctl = libc.prctl
    prctl.restype = ctypes.c_int
    result = prctl(
        ctypes.c_int(1),  # PR_SET_PDEATHSIG
        ctypes.c_ulong(signal.SIGTERM),
        ctypes.c_ulong(0),
        ctypes.c_ulong(0),
        ctypes.c_ulong(0),
    )
    if result != 0:
        error_number = ctypes.get_errno()
        raise OSError(error_number, os.strerror(error_number))
    # Close the fork/exec/prctl race: the configured signal is only useful if
    # the exact process which launched us is still our parent.
    if os.getppid() != expected_parent_pid:
        raise RuntimeError("DistQLDPC supervisor parent disappeared at startup")


def _parse_linux_stat(path: Path) -> tuple[str, int, int]:
    line = path.read_text(encoding="ascii")
    fields = line[line.rindex(")") + 2 :].split()
    return fields[0], int(fields[2]), int(fields[3])


def _live_group_members(process_group: int) -> set[int]:
    members: set[int] = set()
    for entry in os.scandir("/proc"):
        if not entry.name.isdigit():
            continue
        try:
            state, pgid, session_id = _parse_linux_stat(
                Path(entry.path) / "stat"
            )
        except (OSError, ValueError, IndexError):
            continue
        if (
            pgid == process_group
            and session_id == process_group
            and state not in {"Z", "X"}
        ):
            members.add(int(entry.name))
    return members


def _signal_own_group(signum: int) -> None:
    pid = os.getpid()
    if os.getpgrp() != pid or os.getsid(0) != pid:
        raise RuntimeError("DistQLDPC supervisor lost its private group identity")
    os.killpg(pid, signum)


def _terminate_group(
    child: subprocess.Popen[bytes], *, deadline: float
) -> None:
    """TERM then KILL the private group within one fixed total deadline."""

    _signal_own_group(signal.SIGTERM)
    own_pid = os.getpid()
    now = time.monotonic()
    remaining = max(0.0, deadline - now)
    term_deadline = min(
        deadline,
        now + min(_TERMINATION_TERM_PHASE_MAX_S, remaining / 2.0),
    )
    while time.monotonic() < term_deadline:
        child.poll()
        if not (_live_group_members(own_pid) - {own_pid}):
            return
        time.sleep(min(0.01, max(0.0, term_deadline - time.monotonic())))
    if _live_group_members(own_pid) - {own_pid}:
        # SIGKILL includes this supervisor. That is intentional: it leaves no
        # process able to outlive the group fence when a descendant ignores
        # SIGTERM. The adapter treats a non-zero/negative exit as nonterminal.
        _signal_own_group(signal.SIGKILL)
        os._exit(128 + signal.SIGKILL)


def _parser() -> argparse.ArgumentParser:
    parser = argparse.ArgumentParser(add_help=False)
    parser.add_argument("--expected-parent-pid", type=int, required=True)
    parser.add_argument("--termination-grace-s", type=float, required=True)
    parser.add_argument(
        "--absolute-cleanup-deadline", type=float, required=True,
    )
    parser.add_argument("command", nargs=argparse.REMAINDER)
    return parser


def main(argv: Sequence[str] | None = None) -> int:
    global _STOP_REQUESTED
    _STOP_REQUESTED = False
    args = _parser().parse_args(argv)
    if args.command[:1] != ["--"] or len(args.command) < 2:
        raise SystemExit("supervisor requires -- followed by a solver command")
    if args.expected_parent_pid < 1:
        raise SystemExit("expected parent PID must be positive")
    grace = float(args.termination_grace_s)
    if not math.isfinite(grace) or grace < 0:
        raise SystemExit("termination grace must be finite and nonnegative")
    absolute_cleanup_deadline = float(args.absolute_cleanup_deadline)
    if not math.isfinite(absolute_cleanup_deadline):
        raise SystemExit("absolute cleanup deadline must be finite")

    def cleanup_deadline() -> float:
        return min(
            absolute_cleanup_deadline,
            time.monotonic() + grace,
        )
    if not sys.platform.startswith("linux"):
        raise SystemExit("DistQLDPC supervisor requires Linux")
    own_pid = os.getpid()
    if os.getpgrp() != own_pid or os.getsid(0) != own_pid:
        raise SystemExit("DistQLDPC supervisor requires a private session")

    signal.signal(signal.SIGTERM, _request_stop)
    signal.signal(signal.SIGINT, _request_stop)
    try:
        _set_parent_death_signal(args.expected_parent_pid)
    except (OSError, RuntimeError) as exc:
        raise SystemExit(str(exc)) from exc
    if _STOP_REQUESTED or os.getppid() != args.expected_parent_pid:
        return 128 + signal.SIGTERM

    command = args.command[1:]
    try:
        child = subprocess.Popen(
            command,
            stdin=subprocess.DEVNULL,
            # The supervisor itself is already the private session/group
            # leader. Descendants must inherit this exact containment fence.
            start_new_session=False,
        )
    except OSError as exc:
        raise SystemExit(f"could not launch DistQLDPC: {exc}") from exc

    try:
        child_pgid = os.getpgid(child.pid)
        child_session = os.getsid(child.pid)
    except ProcessLookupError:
        child_pgid = child_session = None
    if child_pgid != own_pid or child_session != own_pid:
        # A fast solver leader can fork and exit before the first identity
        # probe.  Always sweep the known private group before returning; if
        # the live leader escaped that group, kill and reap it directly too.
        mismatch_cleanup_deadline = cleanup_deadline()
        if child.poll() is None and child_pgid not in {None, own_pid}:
            try:
                child.kill()
            except ProcessLookupError:
                pass
        _terminate_group(child, deadline=mismatch_cleanup_deadline)
        try:
            child.wait(
                timeout=max(
                    0.0, mismatch_cleanup_deadline - time.monotonic(),
                )
            )
        except subprocess.TimeoutExpired:
            child.kill()
            child.wait()
        raise SystemExit(
            "DistQLDPC child did not inherit the supervisor process group"
        )

    # A parent-death signal may arrive while Popen is returning. The handler
    # only sets a flag, so the just-created child is always fenced here.
    if _STOP_REQUESTED or os.getppid() != args.expected_parent_pid:
        _terminate_group(child, deadline=cleanup_deadline())
        return 128 + signal.SIGTERM

    while True:
        returncode = child.poll()
        if returncode is not None:
            lingering = _live_group_members(own_pid) - {own_pid}
            if lingering:
                _terminate_group(child, deadline=cleanup_deadline())
                return 125
            return returncode if returncode >= 0 else 128 + -returncode
        if _STOP_REQUESTED or os.getppid() != args.expected_parent_pid:
            _terminate_group(child, deadline=cleanup_deadline())
            return 128 + signal.SIGTERM
        time.sleep(0.05)


if __name__ == "__main__":
    raise SystemExit(main())
