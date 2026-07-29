"""Small process-pool hard-wall primitives for proof solver phases.

``concurrent.futures`` timeouts do not stop the worker that is executing C
code.  Proof workers therefore use the worker process itself as the kill
boundary and call :func:`terminate_process_pool` when a wall deadline expires.
"""

from __future__ import annotations

import math
import time
from concurrent.futures import ProcessPoolExecutor
from multiprocessing.process import BaseProcess
from typing import Any


DEFAULT_TERMINATION_GRACE_S = 1.0


def positive_wall_timeout(value: float, label: str) -> float:
    """Validate and normalize one process-enforced wall budget."""

    timeout = float(value)
    if not math.isfinite(timeout) or timeout <= 0:
        raise ValueError(f"{label} must be a positive finite number")
    return timeout


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
    pids = [
        int(process.pid)
        for process in processes
        if process.pid is not None
    ]

    for process in processes:
        if process.is_alive():
            process.terminate()

    deadline = time.monotonic() + grace
    for process in processes:
        remaining = max(0.0, deadline - time.monotonic())
        process.join(timeout=remaining)

    forced: list[int] = []
    for process in processes:
        if process.is_alive():
            if process.pid is not None:
                forced.append(int(process.pid))
            process.kill()

    kill_deadline = time.monotonic() + grace
    for process in processes:
        remaining = max(0.0, kill_deadline - time.monotonic())
        process.join(timeout=remaining)

    lingering = [
        int(process.pid)
        for process in processes
        if process.pid is not None and process.is_alive()
    ]
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
