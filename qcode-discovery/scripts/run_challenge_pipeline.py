#!/usr/bin/env python3
"""Run search, exact certification, and fail-closed finalization in one command."""

from __future__ import annotations

import argparse
import subprocess
import sys
from datetime import datetime, timezone
from pathlib import Path


def main() -> int:
    project = Path(__file__).resolve().parent.parent
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument(
        "--run-id",
        default=datetime.now(timezone.utc).strftime("challenge-%Y%m%d-%H%M%S"),
    )
    parser.add_argument("--candidate-limit", type=int, default=3)
    parser.add_argument("--known-answer-mode", choices=("fast", "strict"), default="fast")
    parser.add_argument("--timeout-per-logical", type=float, default=300)
    parser.add_argument("--total-timeout", type=float, default=7200)
    parser.add_argument(
        "search_args", nargs=argparse.REMAINDER,
        help="Arguments passed to main.py after '--'",
    )
    args = parser.parse_args()
    search_args = list(args.search_args)
    if search_args and search_args[0] == "--":
        search_args.pop(0)
    if "--quick" in search_args:
        print("challenge pipeline forbids --quick", file=sys.stderr)
        return 2
    search = [
        sys.executable, str(project / "main.py"),
        "--run-id", args.run_id,
        *search_args,
    ]
    completed = subprocess.run(search, cwd=project)
    if completed.returncode != 0:
        return completed.returncode
    certify = [
        sys.executable, str(project / "scripts" / "certify_run.py"),
        "--run-id", args.run_id,
        "--limit", str(args.candidate_limit),
        "--known-answer-mode", args.known_answer_mode,
        "--timeout-per-logical", str(args.timeout_per_logical),
        "--total-timeout", str(args.total_timeout),
    ]
    return subprocess.run(certify, cwd=project).returncode


if __name__ == "__main__":
    raise SystemExit(main())
