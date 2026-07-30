#!/usr/bin/env python3
"""Capacity benchmark for the real OpenEvolve Stage 1 evaluator path.

The benchmark deliberately excludes LLM calls and Stage 2 distance estimation.
It exercises OpenEvolve's TaskPool, the private Stage 1 subprocess/guardian,
qLDPC k-only screening, shared candidate-log WAL writes, and MAP descriptors.
All generated artifacts live under an explicit benchmark output directory.
"""

from __future__ import annotations

import argparse
import asyncio
import json
import math
import os
import statistics
import tempfile
import threading
import time
from datetime import datetime, timezone
from pathlib import Path
from typing import Any


NUMERIC_THREAD_ENV = (
    "OMP_NUM_THREADS",
    "OPENBLAS_NUM_THREADS",
    "MKL_NUM_THREADS",
    "NUMEXPR_NUM_THREADS",
    "VECLIB_MAXIMUM_THREADS",
    "BLIS_NUM_THREADS",
)
CGROUP_ROOT = Path("/sys/fs/cgroup")
REQUIRED_METRICS = {
    "winner_preflight_complete": 1.0,
    "winner_preflight_incomplete": 0.0,
    "winner_preflight_hard_timeout": 0.0,
    "winner_preflight_subprocess_failed": 0.0,
    "map_descriptor_version": 2.0,
}


def _positive_int(value: str) -> int:
    parsed = int(value)
    if parsed < 1:
        raise argparse.ArgumentTypeError("value must be positive")
    return parsed


def _levels(value: str) -> list[int]:
    result = [_positive_int(item.strip()) for item in value.split(",")]
    if not result:
        raise argparse.ArgumentTypeError("at least one level is required")
    if len(set(result)) != len(result):
        raise argparse.ArgumentTypeError("levels must be unique")
    return result


def _utc_now() -> str:
    return datetime.now(timezone.utc).isoformat()


def _read_int(path: Path) -> int:
    return int(path.read_text().strip())


def _read_keyed_ints(path: Path) -> dict[str, int]:
    result: dict[str, int] = {}
    for line in path.read_text().splitlines():
        fields = line.split()
        if len(fields) == 2:
            try:
                result[fields[0]] = int(fields[1])
            except ValueError:
                continue
    return result


def _read_pressure(path: Path) -> dict[str, int]:
    result: dict[str, int] = {}
    for line in path.read_text().splitlines():
        fields = line.split()
        if not fields:
            continue
        for field in fields[1:]:
            key, separator, value = field.partition("=")
            if separator and key == "total":
                result[f"{fields[0]}_total_usec"] = int(value)
    return result


def _cgroup_snapshot() -> dict[str, Any]:
    memory_stat = _read_keyed_ints(CGROUP_ROOT / "memory.stat")
    return {
        "cpu": _read_keyed_ints(CGROUP_ROOT / "cpu.stat"),
        "memory_events": _read_keyed_ints(CGROUP_ROOT / "memory.events"),
        "memory_current_bytes": _read_int(CGROUP_ROOT / "memory.current"),
        "memory_swap_current_bytes": _read_int(
            CGROUP_ROOT / "memory.swap.current"
        ),
        "memory_anon_bytes": memory_stat.get("anon", 0),
        "memory_file_bytes": memory_stat.get("file", 0),
        "pids_current": _read_int(CGROUP_ROOT / "pids.current"),
        "cpu_pressure": _read_pressure(CGROUP_ROOT / "cpu.pressure"),
        "memory_pressure": _read_pressure(CGROUP_ROOT / "memory.pressure"),
        "io_pressure": _read_pressure(CGROUP_ROOT / "io.pressure"),
    }


def _nested_delta(
    before: dict[str, Any], after: dict[str, Any], name: str
) -> dict[str, int]:
    left = before.get(name, {})
    right = after.get(name, {})
    return {
        key: int(right.get(key, 0)) - int(left.get(key, 0))
        for key in sorted(set(left) | set(right))
    }


def _proc_rows() -> dict[int, dict[str, Any]]:
    rows: dict[int, dict[str, Any]] = {}
    page_size = os.sysconf("SC_PAGE_SIZE")
    for entry in Path("/proc").iterdir():
        if not entry.name.isdigit():
            continue
        pid = int(entry.name)
        try:
            encoded = (entry / "stat").read_text()
            right = encoded.rfind(")")
            if right < 0:
                continue
            fields = encoded[right + 2 :].split()
            rows[pid] = {
                "ppid": int(fields[1]),
                "ticks": int(fields[11]) + int(fields[12]),
                "threads": int(fields[17]),
                "rss_bytes": int(fields[21]) * page_size,
                "cmdline": (entry / "cmdline")
                .read_bytes()
                .replace(b"\0", b" ")
                .decode("utf-8", errors="replace"),
            }
        except (OSError, IndexError, ValueError):
            continue
    return rows


def _descendants(rows: dict[int, dict[str, Any]], root: int) -> set[int]:
    result = {root}
    changed = True
    while changed:
        changed = False
        for pid, row in rows.items():
            if pid not in result and row["ppid"] in result:
                result.add(pid)
                changed = True
    return result


class ResourceSampler:
    def __init__(self, interval: float = 0.2):
        self.interval = interval
        self.root_pid = os.getpid()
        self.stop_event = threading.Event()
        self.thread = threading.Thread(
            target=self._run,
            name="stage1-stress-resource-sampler",
            daemon=True,
        )
        self.clock_ticks = os.sysconf("SC_CLK_TCK")
        self.last_ticks: dict[int, int] = {}
        self.seen_pids: set[int] = set()
        self.cpu_ticks = 0
        self.samples = 0
        self.peak_processes = 0
        self.peak_threads = 0
        self.peak_rss_bytes = 0
        self.peak_single_process_rss_bytes = 0
        self.peak_cgroup_memory_bytes = 0
        self.peak_cgroup_anon_bytes = 0
        self.peak_cgroup_swap_bytes = 0
        self.peak_cgroup_pids = 0
        self.max_load1 = 0.0
        self.peak_single_threads_by_role: dict[str, int] = {}
        self.peak_total_threads_by_role: dict[str, int] = {}
        self.peak_rss_by_role: dict[str, int] = {}

    def start(self) -> None:
        rows = _proc_rows()
        root = rows.get(self.root_pid)
        if root is not None:
            self.last_ticks[self.root_pid] = root["ticks"]
        self._sample()
        self.thread.start()

    def stop(self) -> None:
        self.stop_event.set()
        self.thread.join()
        self._sample()

    def _run(self) -> None:
        while not self.stop_event.wait(self.interval):
            self._sample()

    def _sample(self) -> None:
        rows = _proc_rows()
        selected = _descendants(rows, self.root_pid)
        self.seen_pids.update(selected)
        visible = [rows[pid] for pid in selected if pid in rows]
        for pid in selected:
            row = rows.get(pid)
            if row is None:
                continue
            previous = self.last_ticks.get(pid)
            if previous is None:
                # Every non-root process is born during this tier.
                previous = 0
            if row["ticks"] >= previous:
                self.cpu_ticks += row["ticks"] - previous
            self.last_ticks[pid] = row["ticks"]
        self.samples += 1
        self.peak_processes = max(self.peak_processes, len(visible))
        self.peak_threads = max(
            self.peak_threads,
            sum(row["threads"] for row in visible),
        )
        self.peak_rss_bytes = max(
            self.peak_rss_bytes,
            sum(row["rss_bytes"] for row in visible),
        )
        self.peak_single_process_rss_bytes = max(
            self.peak_single_process_rss_bytes,
            max((row["rss_bytes"] for row in visible), default=0),
        )
        role_threads: dict[str, int] = {}
        role_rss: dict[str, int] = {}
        for pid in selected:
            row = rows.get(pid)
            if row is None:
                continue
            if pid == self.root_pid:
                role = "harness"
            elif "--stage1-worker" in row["cmdline"]:
                role = "stage1_worker_or_guardian"
            else:
                role = "other_descendant"
            self.peak_single_threads_by_role[role] = max(
                self.peak_single_threads_by_role.get(role, 0),
                row["threads"],
            )
            role_threads[role] = role_threads.get(role, 0) + row["threads"]
            role_rss[role] = role_rss.get(role, 0) + row["rss_bytes"]
        for role, threads in role_threads.items():
            self.peak_total_threads_by_role[role] = max(
                self.peak_total_threads_by_role.get(role, 0),
                threads,
            )
        for role, rss in role_rss.items():
            self.peak_rss_by_role[role] = max(
                self.peak_rss_by_role.get(role, 0),
                rss,
            )
        try:
            snapshot = _cgroup_snapshot()
            self.peak_cgroup_memory_bytes = max(
                self.peak_cgroup_memory_bytes,
                snapshot["memory_current_bytes"],
            )
            self.peak_cgroup_anon_bytes = max(
                self.peak_cgroup_anon_bytes,
                snapshot["memory_anon_bytes"],
            )
            self.peak_cgroup_swap_bytes = max(
                self.peak_cgroup_swap_bytes,
                snapshot["memory_swap_current_bytes"],
            )
            self.peak_cgroup_pids = max(
                self.peak_cgroup_pids,
                snapshot["pids_current"],
            )
        except (FileNotFoundError, OSError, ValueError):
            pass
        try:
            self.max_load1 = max(self.max_load1, os.getloadavg()[0])
        except OSError:
            pass

    def result(self, wall_seconds: float) -> dict[str, Any]:
        cpu_seconds = self.cpu_ticks / self.clock_ticks
        return {
            "samples": self.samples,
            "cpu_seconds_observed": cpu_seconds,
            "average_cpu_cores_observed": (
                cpu_seconds / wall_seconds if wall_seconds else 0.0
            ),
            "peak_processes": self.peak_processes,
            "peak_threads": self.peak_threads,
            "peak_rss_bytes": self.peak_rss_bytes,
            "peak_single_process_rss_bytes": (
                self.peak_single_process_rss_bytes
            ),
            "peak_cgroup_memory_bytes": self.peak_cgroup_memory_bytes,
            "peak_cgroup_anon_bytes": self.peak_cgroup_anon_bytes,
            "peak_cgroup_swap_bytes": self.peak_cgroup_swap_bytes,
            "peak_cgroup_pids": self.peak_cgroup_pids,
            "max_load1": self.max_load1,
            "seen_pids": sorted(self.seen_pids),
            "peak_single_threads_by_role": self.peak_single_threads_by_role,
            "peak_total_threads_by_role": self.peak_total_threads_by_role,
            "peak_rss_bytes_by_role": self.peak_rss_by_role,
        }


def _program_source(limit: int, variant: int) -> str:
    return (
        "from evolve.seed_solution_ansatz import generate_candidates as _base\n"
        f"_LIMIT = {limit}\n"
        f"_VARIANT = {variant}\n\n"
        "def generate_candidates(ell, m):\n"
        "    values = _base(ell, m)\n"
        "    if len(values) <= _LIMIT:\n"
        "        return values\n"
        "    offset = _VARIANT % len(values)\n"
        "    return [\n"
        "        values[(offset + (index * len(values)) // _LIMIT) % len(values)]\n"
        "        for index in range(_LIMIT)\n"
        "    ]\n"
    )


def _percentile(values: list[float], quantile: float) -> float:
    if not values:
        return 0.0
    ordered = sorted(values)
    index = max(0, math.ceil(quantile * len(ordered)) - 1)
    return ordered[index]


def _count_lines(path: Path) -> int:
    if not path.exists():
        return 0
    count = 0
    with path.open("rb") as stream:
        for block in iter(lambda: stream.read(1 << 20), b""):
            count += block.count(b"\n")
    return count


def _validate_metrics(metrics: dict[str, Any]) -> list[str]:
    errors: list[str] = []
    for name, expected in REQUIRED_METRICS.items():
        if metrics.get(name) != expected:
            errors.append(
                f"{name}: expected {expected!r}, got {metrics.get(name)!r}"
            )
    if metrics.get("timeout") is True:
        errors.append("OpenEvolve outer evaluator timed out")
    if metrics.get("error") not in (None, 0, 0.0):
        errors.append(f"OpenEvolve evaluator error={metrics.get('error')!r}")
    evaluated = metrics.get("winner_preflight_candidate_definitions_evaluated")
    if (
        isinstance(evaluated, bool)
        or not isinstance(evaluated, (int, float))
        or evaluated <= 0
    ):
        errors.append(
            "winner_preflight_candidate_definitions_evaluated is not positive"
        )
    return errors


async def _run_level(
    *,
    evaluator_path: Path,
    level: int,
    waves: int,
    candidate_limit: int,
    timeout: int,
    level_dir: Path,
) -> dict[str, Any]:
    programs: list[tuple[str, str]] = []
    for index in range(level * waves):
        programs.append(
            (
                _program_source(candidate_limit, index),
                f"level-{level}-program-{index:03d}",
            )
        )

    candidate_log = (level_dir / "all_codes.jsonl").resolve()
    os.environ["QCODE_CANDIDATE_LOG_PATH"] = str(candidate_log)
    os.environ["QCODE_WINNER_PREFLIGHT_CONTRACT_ID"] = "424242"
    os.environ["QCODE_EVALUATOR_OUTER_TIMEOUT_S"] = str(timeout)
    os.environ["ENABLE_ARTIFACTS"] = "false"
    os.environ["TMPDIR"] = str((level_dir / "tmp").resolve())
    Path(os.environ["TMPDIR"]).mkdir(parents=True)
    tempfile.tempdir = os.environ["TMPDIR"]

    from openevolve.config import EvaluatorConfig
    from openevolve.evaluator import Evaluator

    evaluator = Evaluator(
        EvaluatorConfig(
            timeout=timeout,
            max_retries=0,
            cascade_evaluation=True,
            cascade_thresholds=[2.0, 2.0],
            parallel_evaluations=level,
            use_llm_feedback=False,
            enable_artifacts=False,
        ),
        str(evaluator_path),
    )

    before = _cgroup_snapshot()
    sampler = ResourceSampler()
    sampler.start()
    started_at = _utc_now()
    started = time.monotonic()
    metrics = await evaluator.evaluate_multiple(programs)
    wall_seconds = time.monotonic() - started
    sampler.stop()
    after = _cgroup_snapshot()
    lingering = {
        pid
        for pid in sampler.seen_pids
        if pid != os.getpid() and Path(f"/proc/{pid}").exists()
    }
    deadline = time.monotonic() + 2.0
    while lingering and time.monotonic() < deadline:
        time.sleep(0.05)
        lingering = {
            pid for pid in lingering if Path(f"/proc/{pid}").exists()
        }
    lingering_pids = sorted(lingering)

    errors: list[dict[str, Any]] = []
    successful = 0
    definitions = 0
    for index, row in enumerate(metrics):
        row_errors = _validate_metrics(row)
        if row_errors:
            errors.append({"index": index, "errors": row_errors})
            continue
        successful += 1
        definitions += int(
            row["winner_preflight_candidate_definitions_evaluated"]
        )

    wal_paths = sorted(
        str(path.relative_to(level_dir))
        for path in level_dir.rglob("*")
        if path.name.endswith(".candidate-wal")
        or path.name.endswith(".candidate-wal.tmp")
    )
    if wal_paths:
        errors.append({"candidate_wal_residue": wal_paths})
    if lingering_pids:
        errors.append({"lingering_descendant_pids": lingering_pids})

    latencies = [
        float(row.get("evaluation_time", 0.0))
        for row in metrics
        if isinstance(row.get("evaluation_time"), (int, float))
    ]
    # OpenEvolve 0.2.26 logs but does not return evaluation_time. Under one
    # full wave, wall time is therefore the conservative per-task p95 proxy.
    if not latencies:
        latencies = [wall_seconds / waves] * len(metrics)

    cgroup_delta = {
        "cpu": _nested_delta(before, after, "cpu"),
        "memory_events": _nested_delta(
            before, after, "memory_events"
        ),
        "cpu_pressure": _nested_delta(
            before, after, "cpu_pressure"
        ),
        "memory_pressure": _nested_delta(
            before, after, "memory_pressure"
        ),
        "io_pressure": _nested_delta(before, after, "io_pressure"),
        "memory_current_bytes": (
            after["memory_current_bytes"] - before["memory_current_bytes"]
        ),
        "memory_swap_current_bytes": (
            after["memory_swap_current_bytes"]
            - before["memory_swap_current_bytes"]
        ),
        "memory_anon_bytes": (
            after["memory_anon_bytes"] - before["memory_anon_bytes"]
        ),
        "memory_file_bytes": (
            after["memory_file_bytes"] - before["memory_file_bytes"]
        ),
        "pids_current": after["pids_current"] - before["pids_current"],
    }
    oom_delta = cgroup_delta["memory_events"].get("oom", 0)
    oom_kill_delta = cgroup_delta["memory_events"].get("oom_kill", 0)
    if oom_delta or oom_kill_delta:
        errors.append({
            "cgroup_oom": oom_delta,
            "cgroup_oom_kill": oom_kill_delta,
        })
    summary = {
        "level": level,
        "waves": waves,
        "tasks": len(programs),
        "candidate_limit_per_lattice": candidate_limit,
        "started_at": started_at,
        "wall_seconds": wall_seconds,
        "successful": successful,
        "failed": len(programs) - successful,
        "task_throughput_per_second": (
            successful / wall_seconds if wall_seconds else 0.0
        ),
        "definition_throughput_per_second": (
            definitions / wall_seconds if wall_seconds else 0.0
        ),
        "winner_preflight_definitions": definitions,
        "latency_seconds": {
            "measurement": "full-wave wall-time proxy",
            "p50": statistics.median(latencies) if latencies else 0.0,
            "p95": _percentile(latencies, 0.95),
            "max": max(latencies, default=0.0),
        },
        "candidate_log": {
            "path": str(candidate_log),
            "bytes": candidate_log.stat().st_size if candidate_log.exists() else 0,
            "lines": _count_lines(candidate_log),
            "wal_residue": wal_paths,
        },
        "resources": sampler.result(wall_seconds),
        "cgroup_before": before,
        "cgroup_after": after,
        "cgroup_delta": cgroup_delta,
        "errors": errors,
    }
    return summary


def _atomic_write_json(path: Path, value: Any) -> None:
    temporary = path.with_name(f".{path.name}.tmp-{os.getpid()}")
    temporary.write_text(
        json.dumps(value, indent=2, sort_keys=True) + "\n",
        encoding="utf-8",
    )
    os.replace(temporary, path)


def _build_parser() -> argparse.ArgumentParser:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument(
        "--levels",
        type=_levels,
        default=[1, 6, 8, 12, 16, 24],
        help="comma-separated evaluator concurrency levels",
    )
    parser.add_argument("--waves", type=_positive_int, default=2)
    parser.add_argument(
        "--candidates-per-lattice",
        type=_positive_int,
        default=64,
    )
    parser.add_argument(
        "--output-dir",
        type=Path,
        help="new directory for benchmark artifacts; defaults under /tmp",
    )
    parser.add_argument(
        "--timeout",
        type=_positive_int,
        default=900,
        help="OpenEvolve timeout per program",
    )
    return parser


def main() -> int:
    args = _build_parser().parse_args()
    for variable in NUMERIC_THREAD_ENV:
        os.environ[variable] = "1"
    os.environ["PYTHONDONTWRITEBYTECODE"] = "1"

    if args.output_dir is None:
        output_dir = Path(
            tempfile.mkdtemp(prefix="qcode-stage1-concurrency-")
        ).resolve()
    else:
        output_dir = args.output_dir.resolve()
        if output_dir.exists():
            raise FileExistsError(
                f"refusing to reuse benchmark output directory: {output_dir}"
            )
        output_dir.mkdir(parents=True)

    repo = Path(__file__).resolve().parent.parent
    evaluator_path = repo / "evolve" / "openevolve_evaluator.py"

    result: dict[str, Any] = {
        "schema_version": 1,
        "kind": "qcode-stage1-concurrency-stress",
        "started_at": _utc_now(),
        "output_dir": str(output_dir),
        "levels_requested": args.levels,
        "waves": args.waves,
        "candidate_limit_per_lattice": args.candidates_per_lattice,
        "numeric_thread_environment": {
            name: os.environ.get(name) for name in NUMERIC_THREAD_ENV
        },
        "cgroup_limits": {
            "cpu_max": (CGROUP_ROOT / "cpu.max").read_text().strip(),
            "memory_max": (CGROUP_ROOT / "memory.max").read_text().strip(),
            "memory_swap_max": (
                CGROUP_ROOT / "memory.swap.max"
            ).read_text().strip(),
            "pids_max": (CGROUP_ROOT / "pids.max").read_text().strip(),
        },
        "levels": [],
    }
    summary_path = output_dir / "summary.json"

    for level in args.levels:
        level_dir = output_dir / f"level-{level}"
        level_dir.mkdir()
        summary = asyncio.run(
            _run_level(
                evaluator_path=evaluator_path,
                level=level,
                waves=args.waves,
                candidate_limit=args.candidates_per_lattice,
                timeout=args.timeout,
                level_dir=level_dir,
            )
        )
        result["levels"].append(summary)
        _atomic_write_json(level_dir / "summary.json", summary)
        _atomic_write_json(summary_path, result)
        print(json.dumps(summary, sort_keys=True), flush=True)
        if summary["errors"] or summary["failed"]:
            result["stopped_after_level"] = level
            break

    result["finished_at"] = _utc_now()
    _atomic_write_json(summary_path, result)
    print(json.dumps({"summary": str(summary_path)}, sort_keys=True))
    return int(any(row["failed"] for row in result["levels"]))


if __name__ == "__main__":
    raise SystemExit(main())
