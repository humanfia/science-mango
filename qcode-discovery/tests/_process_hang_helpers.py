"""Lightweight spawn targets for proof-process liveness tests."""

from __future__ import annotations

import ctypes
import json
import os
import signal
import subprocess
import sys
import time
from pathlib import Path


def native_pause_forever() -> None:
    signal.signal(signal.SIGTERM, signal.SIG_IGN)
    libc = ctypes.CDLL(None)
    while True:
        libc.pause()


def hang_with_group_child(
    parent_pid_path: str,
    child_pid_path: str,
    checkpoint_path: str,
) -> None:
    child_code = (
        "import ctypes,os,signal,sys;"
        "signal.signal(signal.SIGTERM,signal.SIG_IGN);"
        "open(sys.argv[1],'w').write(str(os.getpid()));"
        "libc=ctypes.CDLL(None);"
        "libc.pause()"
    )
    subprocess.Popen([sys.executable, "-c", child_code, child_pid_path])
    Path(parent_pid_path).write_text(str(os.getpid()))
    Path(checkpoint_path).write_text('{"completed": 1}\n')
    deadline = time.monotonic() + 2
    while not Path(child_pid_path).exists() and time.monotonic() < deadline:
        time.sleep(0.01)
    native_pause_forever()


def _fork_native_child(pid_path: str) -> None:
    child_pid = os.fork()
    if child_pid == 0:
        Path(pid_path).write_text(str(os.getpid()))
        native_pause_forever()
        os._exit(0)
    deadline = time.monotonic() + 2
    while not Path(pid_path).exists() and time.monotonic() < deadline:
        time.sleep(0.01)


def fork_child_then_return(pid_path: str):
    _fork_native_child(pid_path)
    return {"proof": "complete"}


def fork_child_then_exit(pid_path: str) -> None:
    _fork_native_child(pid_path)
    os._exit(17)


def stage3_hang_or_complete(candidate, *, output, **_kwargs):
    digest = candidate["canonical_digest"]
    if digest.startswith("hang"):
        output.parent.mkdir(parents=True, exist_ok=True)
        output.write_text(
            json.dumps(
                {
                    "status": "UNRESOLVED",
                    "completed_directions": 3,
                    "expected_directions": 24,
                }
            )
            + "\n"
        )
        pid_dir = Path(os.environ["QCODE_STAGE35_PID_DIR"])
        (pid_dir / f"{digest}.pid").write_text(str(os.getpid()))
        native_pause_forever()
    return {
        "status": "THRESHOLD_PROVEN",
        "completed_directions": 24,
        "expected_directions": 24,
    }


def stage5_hang_or_accept(certificate, **kwargs):
    if certificate["certificate_sha256"] == "hang":
        checkpoint = Path(kwargs["checkpoint_path"])
        checkpoint.parent.mkdir(parents=True, exist_ok=True)
        checkpoint.write_text('{"completed_directions": 1}\n')
        pid_dir = Path(os.environ["QCODE_STAGE35_PID_DIR"])
        (pid_dir / "stage5-hang.pid").write_text(str(os.getpid()))
        native_pause_forever()
    return {"passed": True, "accepted": True, "failures": []}


def strict_integrity_hang(*_args, **_kwargs):
    pid_dir = Path(os.environ["QCODE_STAGE35_PID_DIR"])
    (pid_dir / "strict-hang.pid").write_text(str(os.getpid()))
    native_pause_forever()
