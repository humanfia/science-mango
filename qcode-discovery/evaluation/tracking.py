"""Run tracking and structured JSONL logging for evolutionary search.

Provides per-evaluation and per-generation metrics logging, plus run-level
metadata.  Designed as a lightweight foundation that plugs directly into
Weights & Biases, TensorBoard, or simple matplotlib/pandas workflows.

Each run creates a directory under ``results/runs/<run_id>/`` containing
three files:

``evaluations.jsonl``
    One JSON object per line, per candidate evaluation.  Contains
    ``timestamp``, ``eval_num``, and all keys from the evaluation result
    dict (``n, k, d, fom, score, stage, ...``).

``generations.jsonl``
    One JSON object per line, per generation.  Contains summary statistics:
    ``total_candidates``, ``valid_candidates``, ``codes_with_positive_fom``,
    ``best_fom``, ``mean_fom``, ``median_fom``, ``global_best_fom``,
    ``stage_counts``, and timing.

``run_meta.json``
    Run configuration, start/end timestamps, final status, total
    evaluations, and the best code found during the run.

Typical usage::

    tracker = RunTracker("results/runs")
    tracker.start_run(run_id="run-001", config={...})

    for generation in range(num_generations):
        tracker.start_generation(generation)
        for result in results:
            tracker.log_evaluation(result)
        summary = tracker.end_generation(generation, results)

    meta = tracker.end_run()

Two standalone loaders are provided for post-hoc analysis:

* :func:`load_run_generations` -- read ``generations.jsonl``.
* :func:`load_run_meta` -- read ``run_meta.json``.

The JSONL format is directly loadable with ``pandas.read_json(..., lines=True)``
for plotting progress curves.
"""

from __future__ import annotations

import json
import time
from datetime import datetime, timezone
from pathlib import Path


def _median(values: list[float]) -> float:
    """Compute the true median (average of two middle elements for even-length)."""
    s = sorted(values)
    n = len(s)
    mid = n // 2
    if n % 2 == 0:
        return (s[mid - 1] + s[mid]) / 2.0
    return s[mid]


class RunTracker:
    """Tracks metrics for a single evolutionary run."""

    def __init__(self, base_dir: str | Path = "results/runs"):
        self.base_dir = Path(base_dir)
        self.run_dir: Path | None = None
        self.run_meta: dict = {}
        self._eval_file = None
        self._gen_file = None
        self._eval_count = 0
        self._best_fom = 0.0
        self._best_code: dict | None = None

    def start_run(self, run_id: str | None = None, config: dict | None = None) -> str:
        """Initialize a new run.

        Args:
            run_id: Unique run identifier. Auto-generated if None.
            config: Run configuration to record.

        Returns:
            The run_id.
        """
        if run_id is None:
            run_id = datetime.now(timezone.utc).strftime("run-%Y%m%d-%H%M%S")

        self.run_dir = self.base_dir / run_id
        self.run_dir.mkdir(parents=True, exist_ok=True)

        self.run_meta = {
            "run_id": run_id,
            "start_time": datetime.now(timezone.utc).isoformat(),
            "config": config or {},
            "status": "running",
        }
        self._write_meta()

        try:
            self._eval_file = open(self.run_dir / "evaluations.jsonl", "a")
            self._gen_file = open(self.run_dir / "generations.jsonl", "a")
        except Exception:
            # Close the first file if the second open fails
            if self._eval_file is not None:
                self._eval_file.close()
                self._eval_file = None
            raise
        self._eval_count = 0
        self._best_fom = 0.0
        self._best_code = None

        return run_id

    def log_evaluation(self, result: dict) -> None:
        """Log a single candidate evaluation.

        Args:
            result: Evaluation result dict from evaluate_candidate.
        """
        if self._eval_file is None:
            return

        self._eval_count += 1
        record = {
            "timestamp": time.time(),
            "eval_num": self._eval_count,
            **_serialize_result(result),
        }
        self._eval_file.write(json.dumps(record, default=str) + "\n")
        self._eval_file.flush()

        fom = result.get("fom", 0.0)
        if fom > self._best_fom:
            self._best_fom = fom
            self._best_code = _serialize_result(result)

    def start_generation(self, generation: int) -> None:
        """Mark the start of a generation (for timing)."""
        self._gen_start_time = time.time()

    def end_generation(self, generation: int, results: list[dict]) -> dict:
        """Log generation summary statistics.

        Args:
            generation: Generation number.
            results: All evaluation results for this generation.

        Returns:
            The summary dict.
        """
        start = getattr(self, "_gen_start_time", None)
        elapsed = time.time() - start if start is not None else 0.0

        valid = [r for r in results if r.get("k", 0) > 0]
        foms = [r.get("fom", 0.0) for r in valid if r.get("fom", 0.0) > 0]

        summary = {
            "generation": generation,
            "timestamp": time.time(),
            "elapsed_seconds": round(elapsed, 2),
            "total_candidates": len(results),
            "valid_candidates": len(valid),
            "codes_with_positive_fom": len(foms),
            "best_fom": max(foms) if foms else 0.0,
            "mean_fom": sum(foms) / len(foms) if foms else 0.0,
            "median_fom": _median(foms) if foms else 0.0,
            "global_best_fom": self._best_fom,
            "stage_counts": _count_stages(results),
        }

        if self._gen_file is not None:
            self._gen_file.write(json.dumps(summary, default=str) + "\n")
            self._gen_file.flush()

        return summary

    def end_run(self) -> dict:
        """Finalize the run and write final metadata.

        Returns:
            The run metadata dict.
        """
        self.run_meta["end_time"] = datetime.now(timezone.utc).isoformat()
        self.run_meta["status"] = "completed"
        self.run_meta["total_evaluations"] = self._eval_count
        self.run_meta["best_fom"] = self._best_fom
        self.run_meta["best_code"] = self._best_code
        self._write_meta()

        if self._eval_file is not None:
            self._eval_file.close()
            self._eval_file = None
        if self._gen_file is not None:
            self._gen_file.close()
            self._gen_file = None

        return self.run_meta

    def _write_meta(self) -> None:
        if self.run_dir is not None:
            with open(self.run_dir / "run_meta.json", "w") as f:
                json.dump(self.run_meta, f, indent=2, default=str)


def _serialize_result(result: dict) -> dict:
    """Convert result to a JSON-safe dict, preserving all keys."""
    out = {}
    for key, value in result.items():
        try:
            json.dumps(value)
            out[key] = value
        except (TypeError, ValueError):
            out[key] = str(value)
    return out


def _count_stages(results: list[dict]) -> dict[str, int]:
    """Count how many results ended at each cascade stage."""
    counts: dict[str, int] = {}
    for r in results:
        stage = r.get("stage", "unknown")
        counts[stage] = counts.get(stage, 0) + 1
    return counts


def load_run_generations(run_dir: str | Path) -> list[dict]:
    """Load generation summaries from a run directory.

    Args:
        run_dir: Path to a run directory (e.g. results/runs/run-20260216-...).

    Returns:
        List of generation summary dicts.
    """
    path = Path(run_dir) / "generations.jsonl"
    if not path.exists():
        return []
    generations = []
    with open(path) as f:
        for line in f:
            line = line.strip()
            if line:
                generations.append(json.loads(line))
    return generations


def load_run_meta(run_dir: str | Path) -> dict:
    """Load run metadata.

    Args:
        run_dir: Path to a run directory.

    Returns:
        Run metadata dict.
    """
    path = Path(run_dir) / "run_meta.json"
    if not path.exists():
        return {}
    with open(path) as f:
        return json.load(f)
