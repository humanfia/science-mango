#!/usr/bin/env python3
"""Burst-canary the authenticated Codex CLI backend used by OpenEvolve."""

from __future__ import annotations

import argparse
import asyncio
import json
import math
import os
import statistics
import sys
import time
from datetime import datetime, timezone
from pathlib import Path
from types import SimpleNamespace
from typing import Any


CGROUP_ROOT = Path("/sys/fs/cgroup")
REPO_ROOT = Path(__file__).resolve().parent.parent
if str(REPO_ROOT) not in sys.path:
    sys.path.insert(0, str(REPO_ROOT))


def _positive_int(value: str) -> int:
    parsed = int(value)
    if parsed < 1:
        raise argparse.ArgumentTypeError("value must be positive")
    return parsed


def _levels(value: str) -> list[int]:
    levels = [_positive_int(item.strip()) for item in value.split(",")]
    if len(set(levels)) != len(levels):
        raise argparse.ArgumentTypeError("levels must be unique")
    return levels


def _utc_now() -> str:
    return datetime.now(timezone.utc).isoformat()


def _read_keyed_ints(path: Path) -> dict[str, int]:
    result: dict[str, int] = {}
    for line in path.read_text().splitlines():
        fields = line.split()
        if len(fields) == 2:
            try:
                result[fields[0]] = int(fields[1])
            except ValueError:
                pass
    return result


def _snapshot() -> dict[str, Any]:
    return {
        "cpu": _read_keyed_ints(CGROUP_ROOT / "cpu.stat"),
        "memory_events": _read_keyed_ints(
            CGROUP_ROOT / "memory.events"
        ),
        "memory_current_bytes": int(
            (CGROUP_ROOT / "memory.current").read_text()
        ),
        "memory_swap_current_bytes": int(
            (CGROUP_ROOT / "memory.swap.current").read_text()
        ),
        "pids_current": int((CGROUP_ROOT / "pids.current").read_text()),
    }


def _delta(
    before: dict[str, Any], after: dict[str, Any], name: str
) -> dict[str, int]:
    left = before[name]
    right = after[name]
    return {
        key: int(right.get(key, 0)) - int(left.get(key, 0))
        for key in sorted(set(left) | set(right))
    }


def _percentile(values: list[float], quantile: float) -> float:
    if not values:
        return 0.0
    ordered = sorted(values)
    return ordered[max(0, math.ceil(quantile * len(ordered)) - 1)]


async def _one_call(client: Any, token: str, timeout: int) -> dict[str, Any]:
    started = time.monotonic()
    try:
        response = await client.generate_with_context(
            (
                "This is a transport capacity canary. Return the requested "
                "token exactly, with no explanation or formatting."
            ),
            [{"role": "user", "content": f"Return exactly: {token}"}],
            timeout=timeout,
            retries=0,
        )
    except Exception as exc:
        return {
            "token": token,
            "success": False,
            "latency_seconds": time.monotonic() - started,
            "error_type": type(exc).__name__,
            "error": str(exc)[-4000:],
        }
    return {
        "token": token,
        "success": response.strip() == token,
        "latency_seconds": time.monotonic() - started,
        "response": response,
        "error": (
            None
            if response.strip() == token
            else "response did not exactly match the canary token"
        ),
    }


async def _run_level(
    client: Any, *, level: int, timeout: int
) -> dict[str, Any]:
    before = _snapshot()
    started_at = _utc_now()
    started = time.monotonic()
    rows = await asyncio.gather(
        *(
            _one_call(
                client,
                f"QCODE_CANARY_L{level}_I{index:02d}",
                timeout,
            )
            for index in range(level)
        )
    )
    wall_seconds = time.monotonic() - started
    after = _snapshot()
    latencies = [float(row["latency_seconds"]) for row in rows]
    successful = sum(bool(row["success"]) for row in rows)
    return {
        "level": level,
        "started_at": started_at,
        "wall_seconds": wall_seconds,
        "successful": successful,
        "failed": level - successful,
        "throughput_per_second": successful / wall_seconds,
        "latency_seconds": {
            "p50": statistics.median(latencies),
            "p95": _percentile(latencies, 0.95),
            "max": max(latencies),
        },
        "cgroup_delta": {
            "cpu": _delta(before, after, "cpu"),
            "memory_events": _delta(
                before, after, "memory_events"
            ),
            "memory_current_bytes": (
                after["memory_current_bytes"]
                - before["memory_current_bytes"]
            ),
            "memory_swap_current_bytes": (
                after["memory_swap_current_bytes"]
                - before["memory_swap_current_bytes"]
            ),
            "pids_current": (
                after["pids_current"] - before["pids_current"]
            ),
        },
        "errors": [
            {
                "token": row["token"],
                "error_type": row.get("error_type"),
                "error": row.get("error"),
                "response": row.get("response"),
            }
            for row in rows
            if not row["success"]
        ],
    }


def _atomic_write(path: Path, value: Any) -> None:
    temporary = path.with_name(f".{path.name}.tmp-{os.getpid()}")
    temporary.write_text(
        json.dumps(value, indent=2, sort_keys=True) + "\n",
        encoding="utf-8",
    )
    os.replace(temporary, path)


def _parser() -> argparse.ArgumentParser:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--levels", type=_levels, default=[1, 6, 8, 12, 16])
    parser.add_argument("--model", default="gpt-5.5")
    parser.add_argument("--reasoning-effort", default="xhigh")
    parser.add_argument("--timeout", type=_positive_int, default=300)
    parser.add_argument("--output-dir", type=Path, required=True)
    return parser


def main() -> int:
    args = _parser().parse_args()
    output_dir = args.output_dir.resolve()
    if output_dir.exists():
        raise FileExistsError(
            f"refusing to reuse canary output directory: {output_dir}"
        )
    output_dir.mkdir(parents=True)
    os.environ["PYTHONDONTWRITEBYTECODE"] = "1"

    from evolve.codex_cli_llm import CodexCliLLM

    client = CodexCliLLM(
        SimpleNamespace(
            name=args.model,
            system_message="",
            reasoning_effort=args.reasoning_effort,
            timeout=args.timeout,
            retries=0,
            retry_delay=1,
        )
    )
    result = {
        "schema_version": 1,
        "kind": "qcode-codex-cli-concurrency-canary",
        "started_at": _utc_now(),
        "model": args.model,
        "reasoning_effort": args.reasoning_effort,
        "levels_requested": args.levels,
        "levels": [],
    }
    summary_path = output_dir / "summary.json"
    for level in args.levels:
        row = asyncio.run(
            _run_level(client, level=level, timeout=args.timeout)
        )
        result["levels"].append(row)
        _atomic_write(summary_path, result)
        print(json.dumps(row, sort_keys=True), flush=True)
        if row["failed"]:
            result["stopped_after_level"] = level
            break
    result["finished_at"] = _utc_now()
    _atomic_write(summary_path, result)
    print(json.dumps({"summary": str(summary_path)}, sort_keys=True))
    return int(any(row["failed"] for row in result["levels"]))


if __name__ == "__main__":
    raise SystemExit(main())
