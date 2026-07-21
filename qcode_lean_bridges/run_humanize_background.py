#!/usr/bin/env python3
"""Wait for an existing exact batch, then supervise Humanize qcode discovery."""

from __future__ import annotations

import argparse
import fcntl
import json
import os
import signal
import subprocess
import time
from datetime import datetime, timezone
from pathlib import Path
from typing import Any


PROJECT = Path("/root/proposal_for_physic/science-mango")
QCODE_REPO = PROJECT / "qcode-discovery"
LEAN_PROJECT = PROJECT / "qcode_lean_bridges" / "qcode_bridge"
REFERENCE = QCODE_REPO / "results" / "ilp_catalog.json"
ARCHON = PROJECT / ".venv" / "bin" / "archon"


def now() -> str:
    return datetime.now(timezone.utc).isoformat()


def memory_bytes() -> int:
    try:
        return int(Path("/sys/fs/cgroup/memory.current").read_text().strip())
    except (FileNotFoundError, ValueError):
        return 0


def process_matches(pid: int, needle: str) -> bool:
    try:
        command = (Path("/proc") / str(pid) / "cmdline").read_bytes()
        return needle in command.replace(b"\0", b" ").decode()
    except (FileNotFoundError, PermissionError, ProcessLookupError):
        return False


def count_lines(path: Path) -> int:
    try:
        with path.open("rb") as stream:
            return sum(1 for _ in stream)
    except FileNotFoundError:
        return 0


def read_json(path: Path) -> dict[str, Any]:
    try:
        return json.loads(path.read_text())
    except (FileNotFoundError, json.JSONDecodeError):
        return {}


def write_json(path: Path, data: dict[str, Any]) -> None:
    temporary = path.with_suffix(path.suffix + ".tmp")
    temporary.write_text(json.dumps(data, ensure_ascii=False, indent=2) + "\n")
    temporary.replace(path)


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--run-id", default="humanize-full-20260721")
    parser.add_argument("--wait-pid", type=int, default=508318)
    parser.add_argument("--safe-memory-gib", type=float, default=40.0)
    parser.add_argument("--poll-seconds", type=int, default=30)
    parser.add_argument("--rounds", type=int, default=5)
    parser.add_argument("--iterations-per-round", type=int, default=20)
    parser.add_argument("--model", default="gpt-5.5")
    parser.add_argument("--review-model", default="gpt-5.5")
    parser.add_argument("--reasoning-effort", default="xhigh")
    parser.add_argument("--review-effort", default="xhigh")
    args = parser.parse_args()

    control = PROJECT / ".archon" / "qcode-background" / args.run_id
    control.mkdir(parents=True, exist_ok=True)
    if (control / "exit-code").is_file():
        print(f"Run already finished: {control}", flush=True)
        return 0
    lock_stream = (control / "supervisor.lock").open("w")
    try:
        fcntl.flock(lock_stream, fcntl.LOCK_EX | fcntl.LOCK_NB)
    except BlockingIOError:
        print(f"Supervisor already running for {args.run_id}", flush=True)
        return 2
    (control / "supervisor.pid").write_text(f"{os.getpid()}\n")

    stopping = False
    child: subprocess.Popen | None = None

    def stop(signum, _frame):
        nonlocal stopping
        stopping = True
        if child is not None and child.poll() is None:
            child.send_signal(signum)

    signal.signal(signal.SIGTERM, stop)
    signal.signal(signal.SIGINT, stop)

    status: dict[str, Any] = {
        "run_id": args.run_id,
        "supervisor_pid": os.getpid(),
        "phase": "queued",
        "created_at": now(),
        "dependency_pid": args.wait_pid,
        "rounds": args.rounds,
        "iterations_per_round": args.iterations_per_round,
        "model": args.model,
        "review_model": args.review_model,
        "reasoning_effort": args.reasoning_effort,
        "review_effort": args.review_effort,
        "model_backend": "codex-cli",
    }
    status_path = control / "status.json"
    safe_bytes = int(args.safe_memory_gib * 1024**3)

    while not stopping and process_matches(args.wait_pid, "run_exact_batch.py"):
        status.update({
            "phase": "queued-waiting-for-existing-lean-batch",
            "updated_at": now(),
            "memory_bytes": memory_bytes(),
        })
        write_json(status_path, status)
        time.sleep(args.poll_seconds)

    consecutive_safe = 0
    while not stopping and consecutive_safe < 2:
        current = memory_bytes()
        consecutive_safe = consecutive_safe + 1 if current <= safe_bytes else 0
        status.update({
            "phase": "queued-waiting-for-memory",
            "updated_at": now(),
            "memory_bytes": current,
            "safe_memory_bytes": safe_bytes,
            "safe_samples": consecutive_safe,
        })
        write_json(status_path, status)
        if consecutive_safe < 2:
            time.sleep(args.poll_seconds)
    if stopping:
        status.update({"phase": "stopped", "updated_at": now()})
        write_json(status_path, status)
        return 130

    command = [
        str(ARCHON), "qcode-humanize", str(PROJECT),
        "--repo-dir", str(QCODE_REPO),
        "--run-id", args.run_id,
        "--rounds", str(args.rounds),
        "--iterations-per-round", str(args.iterations_per_round),
        "--model", args.model,
        "--review-model", args.review_model,
        "--reasoning-effort", args.reasoning_effort,
        "--review-effort", args.review_effort,
        "--codex-cli",
        "--milp-top", "3",
        "--milp-timeout-per-logical", "300",
        "--milp-total-timeout", "7200",
        "--milp-early-stop", "0",
        "--patience", "3",
        "--install",
        "--formalize", "--prove", "--formalize-top", "3",
        "--lean-project", str(LEAN_PROJECT),
        "--bridge-dir", str(PROJECT / "qcode_lean_bridges"),
        "--witness-timeout", "10800", "--sat-timeout", "10800",
        "--lean-jobs", "1",
        "--metrics-reference", str(REFERENCE),
    ]
    env = os.environ.copy()
    env["ELAN_HOME"] = "/root/.elan"
    env["QCODE_CODEX_CWD"] = str(QCODE_REPO)
    env["PATH"] = ":".join([
        "/root/.elan/bin", str(PROJECT / ".venv" / "bin"),
        "/root/.local/bin", "/root/.nvm/versions/node/v24.18.0/bin",
        env.get("PATH", ""),
    ])
    env["PYTHONPATH"] = str(PROJECT / "src") + (
        ":" + env["PYTHONPATH"] if env.get("PYTHONPATH") else ""
    )

    (control / "command.json").write_text(
        json.dumps(command, ensure_ascii=False, indent=2) + "\n"
    )
    pipeline_log = (control / "pipeline.log").open("a", buffering=1)
    print("Starting Humanize qcode pipeline", flush=True)
    child = subprocess.Popen(
        command,
        cwd=PROJECT,
        env=env,
        stdout=pipeline_log,
        stderr=subprocess.STDOUT,
    )
    (control / "pipeline.pid").write_text(f"{child.pid}\n")

    humanize_state = QCODE_REPO / "results" / "humanize" / args.run_id / "state.json"
    evaluations = QCODE_REPO / "results" / "runs" / args.run_id / "evaluations.jsonl"
    while child.poll() is None and not stopping:
        run_state = read_json(humanize_state)
        status.update({
            "phase": "running",
            "pipeline_pid": child.pid,
            "updated_at": now(),
            "memory_bytes": memory_bytes(),
            "current_round": int(run_state.get("current_round", 0) or 0),
            "round_phase": run_state.get("round_phase"),
            "best_fom": float(run_state.get("best_fom", 0.0) or 0.0),
            "milp_audited": count_lines(evaluations),
        })
        write_json(status_path, status)
        time.sleep(args.poll_seconds)

    return_code = child.wait() if child is not None else 130
    pipeline_log.close()
    run_state = read_json(humanize_state)
    status.update({
        "phase": "completed" if return_code == 0 else "failed",
        "return_code": return_code,
        "updated_at": now(),
        "current_round": int(run_state.get("current_round", 0) or 0),
        "humanize_status": run_state.get("status"),
        "best_fom": float(run_state.get("best_fom", 0.0) or 0.0),
        "milp_audited": count_lines(evaluations),
    })
    write_json(status_path, status)
    (control / "exit-code").write_text(f"{return_code}\n")
    return return_code


if __name__ == "__main__":
    raise SystemExit(main())
