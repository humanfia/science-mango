"""Durability and concurrency tests for OpenEvolve's Stage 1 candidate log."""

from __future__ import annotations

import json
import multiprocessing
import os
from pathlib import Path

import pytest

import evolve.openevolve_evaluator as evaluator


def _result(worker: int, index: int) -> dict:
    return {
        "ell": 6 + worker,
        "m": 6 + index,
        "A_terms": [[0, 0], [0, 1], [1, 0]],
        "B_terms": [[0, 0], [0, 2], [2, 0]],
        "n": 2 * (6 + worker) * (6 + index),
        "k": 8,
        "d": 2 + index,
        "fom": float(worker * 1000 + index),
        "stage": "test",
    }


def _append_worker(
    project_root: str,
    run_name: str,
    worker: int,
    count: int,
) -> None:
    evaluator._PROJECT_ROOT = project_root
    for index in range(count):
        evaluator._log_code_jsonl(
            _result(worker, index),
            run_name=run_name,
        )


def test_candidate_jsonl_is_complete_under_multiprocess_append(tmp_path):
    workers = 4
    per_worker = 12
    run_name = "multiprocess-log"
    context = multiprocessing.get_context("fork")
    processes = [
        context.Process(
            target=_append_worker,
            args=(str(tmp_path), run_name, worker, per_worker),
        )
        for worker in range(workers)
    ]

    for process in processes:
        process.start()
    for process in processes:
        process.join(timeout=30)
        assert process.exitcode == 0

    path = (
        tmp_path / "results" / "evolution" / run_name / "all_codes.jsonl"
    )
    payload = path.read_bytes()
    assert payload.endswith(b"\n")
    rows = [json.loads(line) for line in payload.splitlines()]
    assert len(rows) == workers * per_worker
    assert {
        (row["ell"] - 6, int(row["fom"]) % 1000)
        for row in rows
    } == {
        (worker, index)
        for worker in range(workers)
        for index in range(per_worker)
    }


def test_candidate_jsonl_write_failure_propagates_and_rolls_back(
    tmp_path, monkeypatch
):
    monkeypatch.setattr(evaluator, "_PROJECT_ROOT", str(tmp_path))
    original_write = os.write
    calls = 0

    def short_then_fail(descriptor: int, payload: bytes) -> int:
        nonlocal calls
        calls += 1
        if calls == 1:
            return original_write(descriptor, payload[:7])
        raise OSError("simulated candidate-log write failure")

    monkeypatch.setattr(evaluator.os, "write", short_then_fail)
    with pytest.raises(
        evaluator.CandidateLogWriteError,
        match="failed to persist discovered candidate",
    ) as raised:
        evaluator._log_code_jsonl(_result(0, 0), run_name="write-failure")
    assert isinstance(raised.value.__cause__, OSError)

    path = (
        tmp_path
        / "results"
        / "evolution"
        / "write-failure"
        / "all_codes.jsonl"
    )
    assert path.read_bytes() == b""


def test_evaluation_does_not_downgrade_candidate_log_failure(monkeypatch):
    row = _result(0, 0)
    monkeypatch.setattr(
        evaluator,
        "evaluate_batch",
        lambda *_args, **_kwargs: [dict(row)],
    )
    monkeypatch.setattr(
        evaluator,
        "_filter_static_eligible",
        lambda rows: (rows, []),
    )

    def fail_log(*_args, **_kwargs):
        raise evaluator.CandidateLogWriteError("durable log unavailable")

    monkeypatch.setattr(evaluator, "_log_code_jsonl", fail_log)
    with pytest.raises(
        evaluator.CandidateLogWriteError,
        match="durable log unavailable",
    ):
        evaluator._run_evaluation(
            lambda _ell, _m: [(row["A_terms"], row["B_terms"])],
            [(6, 6)],
            quick=True,
        )
