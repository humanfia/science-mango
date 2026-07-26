#!/usr/bin/env python3
"""Supervise the complete qcode cascade without depending on an open session."""

from __future__ import annotations

import argparse
import fcntl
import json
import os
import signal
import subprocess
import sys
import time
from datetime import datetime, timezone
from pathlib import Path

PROJECT = Path("/root/proposal_for_physic/science-mango")
QCODE_REPO = Path("/root/proposal_for_physic/qcode-discovery")
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
        return needle in (Path("/proc") / str(pid) / "cmdline").read_bytes().replace(b"\0", b" ").decode()
    except (FileNotFoundError, PermissionError, ProcessLookupError):
        return False


def count_lines(path: Path) -> int:
    try:
        with path.open("rb") as stream:
            return sum(1 for _ in stream)
    except FileNotFoundError:
        return 0


def write_json(path: Path, data: dict) -> None:
    temporary = path.with_suffix(path.suffix + ".tmp")
    temporary.write_text(json.dumps(data, ensure_ascii=False, indent=2) + "\n")
    temporary.replace(path)


def generate_metrics(run_id: str, run_root: Path) -> None:
    sys.path.insert(0, str(PROJECT / "src"))
    from archon.commands.qcode_metrics import write_metrics
    lean_root = LEAN_PROJECT / ".archon" / "qcode-runs" / run_id
    write_metrics(
        repo_dir=QCODE_REPO,
        run_id=run_id,
        reference_catalog=REFERENCE,
        lean_run_root=lean_root if lean_root.is_dir() else None,
    )


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--run-id", default="archon-full-20260721")
    parser.add_argument("--wait-pid", type=int, default=508318)
    parser.add_argument("--safe-memory-gib", type=float, default=40.0)
    parser.add_argument("--poll-seconds", type=int, default=30)
    args = parser.parse_args()

    control = PROJECT / ".archon" / "qcode-background" / args.run_id
    control.mkdir(parents=True, exist_ok=True)
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

    status = {
        "run_id": args.run_id,
        "supervisor_pid": os.getpid(),
        "phase": "queued",
        "created_at": now(),
        "dependency_pid": args.wait_pid,
        "expected_lattices": 18,
        "expected_candidates": 38964,
        "milp_survivor_limit": 54,
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
        str(ARCHON), "qcode", str(PROJECT),
        "--repo-dir", str(QCODE_REPO), "--full",
        "--run-id", args.run_id,
        "--quick-trials", "100", "--refine-trials", "1000",
        "--fom-threshold-refine", "6", "--fom-threshold-exact", "8",
        "--milp-top", "3", "--milp-timeout-per-logical", "300",
        "--milp-total-timeout", "7200", "--milp-early-stop", "0",
        "--formalize", "--prove", "--formalize-top", "0",
        "--lean-project", str(LEAN_PROJECT),
        "--bridge-dir", str(PROJECT / "qcode_lean_bridges"),
        "--witness-timeout", "10800", "--sat-timeout", "10800",
        "--lean-jobs", "1", "--no-update-repo", "--no-install",
        "--metrics-reference", str(REFERENCE), "--top", "10", "--verbose",
    ]
    env = os.environ.copy()
    env["ELAN_HOME"] = "/root/.elan"
    env["PATH"] = ":".join([
        "/root/.elan/bin", str(PROJECT / ".venv" / "bin"),
        "/root/.local/bin", "/root/.nvm/versions/node/v24.18.0/bin",
        env.get("PATH", ""),
    ])
    env["PYTHONPATH"] = str(PROJECT / "src") + (":" + env["PYTHONPATH"] if env.get("PYTHONPATH") else "")
    for name in ("OPENAI_API_KEY", "OPENAI_BASE_URL", "OPENAI_MODEL",
                 "ANTHROPIC_AUTH_TOKEN", "ARCHON_MLLM_BASE_URL", "ARCHON_MLLM_MODEL"):
        env.pop(name, None)

    (control / "command.json").write_text(json.dumps(command, ensure_ascii=False, indent=2) + "\n")
    print("Starting: " + " ".join(command), flush=True)
    child = subprocess.Popen(command, cwd=PROJECT, env=env)
    (control / "pipeline.pid").write_text(f"{child.pid}\n")
    last_metrics = 0.0
    run_dir = QCODE_REPO / "results" / "runs" / args.run_id
    while child.poll() is None and not stopping:
        current_time = time.time()
        if current_time - last_metrics >= 300:
            try:
                generate_metrics(args.run_id, run_dir)
            except Exception as exc:
                print(f"metrics update failed: {exc}", flush=True)
            last_metrics = current_time
        status.update({
            "phase": "running",
            "pipeline_pid": child.pid,
            "updated_at": now(),
            "memory_bytes": memory_bytes(),
            "evaluations_logged": count_lines(run_dir / "evaluations.jsonl"),
            "lattices_completed": count_lines(run_dir / "generations.jsonl"),
        })
        write_json(status_path, status)
        time.sleep(args.poll_seconds)

    return_code = child.wait() if child is not None else 130
    try:
        generate_metrics(args.run_id, run_dir)
    except Exception as exc:
        print(f"final metrics update failed: {exc}", flush=True)
    status.update({
        "phase": "completed" if return_code == 0 else "failed",
        "return_code": return_code,
        "updated_at": now(),
        "evaluations_logged": count_lines(run_dir / "evaluations.jsonl"),
        "lattices_completed": count_lines(run_dir / "generations.jsonl"),
    })
    write_json(status_path, status)
    (control / "exit-code").write_text(f"{return_code}\n")
    return return_code


if __name__ == "__main__":
    raise SystemExit(main())
