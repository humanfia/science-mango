"""Durability and concurrency tests for OpenEvolve's Stage 1 candidate log."""

from __future__ import annotations

import json
import multiprocessing
import os
from pathlib import Path

import pytest

import evolve.openevolve_evaluator as evaluator
from evaluation.final_gate import classify_win


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


def test_k_below_eight_can_pass_the_real_win_rule_and_singleton_bound():
    assert classify_win(72, 4, 15)["passed"] is True
    assert classify_win(72, 4, 15)["fom"] == 12.5
    # Quantum Singleton: d <= floor((n-k)/2)+1 = 35.
    assert evaluator._winning_distance_window(72, 4) == (15, 35)


def test_oversized_candidate_sample_is_bounded_and_not_a_prefix():
    candidates = [
        (
            [(0, 0), (0, 1), (index + 1, 0)],
            [(0, 0), (0, 2), (index + 2, 0)],
        )
        for index in range(20)
    ]

    sampled = evaluator._bounded_candidate_sample(
        candidates,
        ell=31,
        m=7,
        limit=6,
        sampling_salt="program-a",
    )

    assert len(sampled) == 6
    assert candidates[0] in sampled
    assert candidates[-1] in sampled
    assert sampled != candidates[:6]
    assert sampled == evaluator._bounded_candidate_sample(
        candidates,
        ell=31,
        m=7,
        limit=6,
        sampling_salt="program-a",
    )


def test_dynamic_distance_lane_keeps_k4_and_bounds_quick_persistence(
    tmp_path, monkeypatch
):
    monkeypatch.setattr(evaluator, "_PROJECT_ROOT", str(tmp_path))
    monkeypatch.setattr(
        evaluator,
        "_filter_static_eligible",
        lambda rows: (rows, []),
    )
    monkeypatch.setattr(
        evaluator,
        "deduplicate_css_results",
        lambda rows: (rows, []),
    )

    candidates = [
        (
            [[0, 0], [0, 1], [index + 1, 0]],
            [[0, 0], [0, 2], [index + 2, 0]],
        )
        for index in range(20)
    ]
    distance_inputs = []

    def fake_batch(ell, m, rows, **kwargs):
        if kwargs.get("quick") is True:
            return [
                {
                    "ell": ell,
                    "m": m,
                    "A_terms": a_terms,
                    "B_terms": b_terms,
                    "n": 72,
                    "k": 4,
                    "d": 0,
                    "fom": 0.0,
                    "score": 4 / 72,
                    "stage": "quick_k_only",
                    "encoding_rate": 4 / 72,
                }
                for a_terms, b_terms in rows
            ]
        distance_inputs.extend(rows)
        return [
            {
                "ell": ell,
                "m": m,
                "A_terms": a_terms,
                "B_terms": b_terms,
                "n": 72,
                "k": 4,
                "d": 8,
                "fom": 4 * 8 * 8 / 72,
                "score": 4 * 8 * 8 / 72,
                "stage": "refined_estimate",
                "encoding_rate": 4 / 72,
            }
            for a_terms, b_terms in rows
        ]

    monkeypatch.setattr(evaluator, "evaluate_batch", fake_batch)
    metrics = evaluator._run_evaluation(
        lambda _ell, _m: candidates,
        [(6, 6)],
        quick=False,
        max_distance_per_lattice=2,
        run_name="bounded-quick-lane",
        sampling_salt="program-a",
    )

    # The removed k>=8 gate would have made this empty.
    assert len(distance_inputs) == 2
    assert all(result["k"] == 4 for result in metrics["all_results"])
    persisted = [
        json.loads(line)
        for line in (
            tmp_path
            / "results"
            / "evolution"
            / "bounded-quick-lane"
            / "all_codes.jsonl"
        ).read_text().splitlines()
    ]
    quick_rows = [
        row for row in persisted
        if row.get("candidate_persistence_lane")
        == evaluator.WINNER_CAPABLE_EXPLORATION_LANE
    ]
    assert len(quick_rows) == (
        evaluator.MAX_WINNER_CAPABLE_EXPLORATION_PER_LATTICE
    )
    assert all(row["d"] == 0 and row["fom"] == 0 for row in quick_rows)
    assert all(row["minimum_winning_distance"] == 15 for row in quick_rows)
    assert len(persisted) == len(distance_inputs) + len(quick_rows)


def test_unresolved_top_candidate_is_logged_exactly_once(tmp_path, monkeypatch):
    monkeypatch.setattr(evaluator, "_PROJECT_ROOT", str(tmp_path))
    monkeypatch.setattr(
        evaluator,
        "_filter_static_eligible",
        lambda rows: (rows, []),
    )
    monkeypatch.setattr(
        evaluator,
        "deduplicate_css_results",
        lambda rows: (rows, []),
    )
    definition = (
        [[0, 0], [0, 1], [1, 0]],
        [[0, 0], [0, 2], [2, 0]],
    )

    def fake_batch(ell, m, rows, **kwargs):
        stage = "quick_k_only" if kwargs.get("quick") is True else "refined_estimate"
        return [
            {
                "ell": ell,
                "m": m,
                "A_terms": a_terms,
                "B_terms": b_terms,
                "n": 72,
                "k": 4,
                "d": 0,
                "fom": 0.0,
                "score": 4 / 72,
                "stage": stage,
                "encoding_rate": 4 / 72,
            }
            for a_terms, b_terms in rows
        ]

    monkeypatch.setattr(evaluator, "evaluate_batch", fake_batch)
    metrics = evaluator._run_evaluation(
        lambda _ell, _m: [definition],
        [(6, 6)],
        quick=False,
        max_distance_per_lattice=1,
        run_name="unresolved-top",
        sampling_salt="program-a",
    )

    assert len(metrics["all_results"]) == 1
    persisted = [
        json.loads(line)
        for line in (
            tmp_path
            / "results"
            / "evolution"
            / "unresolved-top"
            / "all_codes.jsonl"
        ).read_text().splitlines()
    ]
    assert len(persisted) == 1
    assert persisted[0]["candidate_persistence_lane"] == (
        evaluator.WINNER_CAPABLE_EXPLORATION_LANE
    )


def test_large_lattice_specialist_has_low_frequency_escape_hatch(
    tmp_path, monkeypatch
):
    program = tmp_path / "specialist.py"
    program.write_text(
        "def generate_candidates(ell, m):\n"
        "    if (ell, m) != (30, 6):\n"
        "        return []\n"
        "    return [([(0, 0), (1, 0), (0, 1)], "
        "[(0, 0), (2, 0), (0, 2)])]\n"
    )
    monkeypatch.setattr(
        evaluator,
        "_stage1_specialist_exploration_pass",
        lambda _path: True,
    )

    result = evaluator.evaluate_stage1(str(program))

    assert result["total_candidates"] == 0.0
    assert result["combined_score"] == 0.02
    assert result["specialist_exploration"] == 1.0


def test_partial_stage1_coverage_only_escapes_on_specialist_sample(
    tmp_path, monkeypatch
):
    program = tmp_path / "partial.py"
    program.write_text("def generate_candidates(ell, m):\n    return []\n")
    row = {
        "ell": 6,
        "m": 6,
        "n": 72,
        "k": 4,
        "d": 0,
        "fom": 0.0,
        "encoding_rate": 4 / 72,
        "A_terms": [[0, 0], [0, 1], [1, 0]],
        "B_terms": [[0, 0], [0, 2], [2, 0]],
    }
    metrics = {
        "total_candidates": 1,
        "all_results": [row],
        "num_valid": 1,
        "num_high_k": 0,
        "lattices_with_high_k": 0,
    }
    monkeypatch.setattr(
        evaluator,
        "_run_evaluation",
        lambda *_args, **_kwargs: metrics,
    )

    monkeypatch.setattr(
        evaluator,
        "_stage1_specialist_exploration_pass",
        lambda _path: False,
    )
    ordinary = evaluator.evaluate_stage1(str(program))
    monkeypatch.setattr(
        evaluator,
        "_stage1_specialist_exploration_pass",
        lambda _path: True,
    )
    sampled = evaluator.evaluate_stage1(str(program))

    assert ordinary["combined_score"] == 0.001
    assert ordinary["specialist_exploration"] == 0.0
    assert sampled["combined_score"] == 0.02
    assert sampled["specialist_exploration"] == 1.0
