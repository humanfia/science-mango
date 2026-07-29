"""Durability and concurrency tests for OpenEvolve's Stage 1 candidate log."""

from __future__ import annotations

import json
import multiprocessing
import os
import signal
import subprocess
import sys
import time
from itertools import permutations
from pathlib import Path

import pytest

import evolve.openevolve_evaluator as evaluator
from evaluation.final_gate import classify_win
from evaluation.search_contract import (
    EVOLUTION_LATTICES,
    FINAL_GATE_PARETO_LATTICES,
    TARGET_LATTICES,
)


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


def test_distance_backend_error_record_is_json_safe_and_bounded():
    record = evaluator._distance_backend_error_record(
        RuntimeError("x" * 5000)
    )

    assert record["type"] == "RuntimeError"
    assert len(record["message"]) == (
        evaluator.MAX_DISTANCE_BACKEND_ERROR_MESSAGE_CHARS
    )
    assert record["message"].endswith("...")
    json.dumps(record, allow_nan=False)


def test_production_full_evaluation_covers_final_gate_pareto_lattices():
    required = {(6, 6), (15, 3), (9, 6)}
    contracted = set(FINAL_GATE_PARETO_LATTICES) | set(TARGET_LATTICES)

    assert set(evaluator.FINAL_GATE_PARETO_LATTICES) == required
    assert set(evaluator.STAGE2_LATTICES) == contracted
    assert tuple(evaluator.STAGE2_LATTICES) == EVOLUTION_LATTICES
    assert required <= set(evaluator.STAGE2_LATTICES_MILP)
    assert evaluator.STAGE2_LATTICES[:3] == (
        evaluator.FINAL_GATE_PARETO_LATTICES
    )
    assert {
        2 * ell * m for ell, m in evaluator.FINAL_GATE_PARETO_LATTICES
    } == {72, 90, 108}
    assert evaluator.MAX_FINAL_GATE_PARETO_DISTANCE_PER_LATTICE == 4


def test_full_evaluation_calls_generator_on_every_contracted_lattice():
    called = []

    def recorder(ell, m):
        called.append((ell, m))
        return []

    evaluator._run_evaluation(
        recorder,
        evaluator.STAGE2_LATTICES,
        quick=True,
    )

    assert called == list(EVOLUTION_LATTICES)


def test_stage2_preflights_all_targets_before_bounded_deep_evaluation(
    tmp_path, monkeypatch
):
    calls = []
    empty_metrics = {
        "best_fom": 0.0,
        "mean_fom": 0.0,
        "num_valid": 0,
        "num_above_6": 0,
        "num_above_12": 0,
        "total_candidates": 0,
        "unique_candidates": 0,
        "evaluated_candidate_definitions": 0,
        "duplicate_candidate_occurrences": 0,
        "winner_capable_quick_exploration_persisted": 0,
        "winner_capable_distance_pending_persisted": 0,
        "winner_capable_unresolved_top_persisted": 0,
        "winner_capable_distance_error_persisted": 0,
        "distance_backend_error_count": 0,
        "malformed_candidate_definitions": 0,
        "tier0_rejected": 0,
        "structural_rejected": 0,
        "best_encoding_rate": 0.0,
        "num_high_k": 0,
        "lattices_with_high_k": 0,
        "best_code": None,
        "all_results": [],
        "errors": [],
    }

    monkeypatch.setattr(
        evaluator,
        "_load_generate_candidates",
        lambda _path: lambda _ell, _m: [],
    )

    def fake_run(_generate, lattices, **kwargs):
        calls.append((tuple(lattices), dict(kwargs)))
        return dict(empty_metrics)

    monkeypatch.setattr(evaluator, "_run_evaluation", fake_run)
    monkeypatch.setattr(evaluator, "_write_metrics_jsonl", lambda _rows: None)

    evaluator._evaluate_stage2_impl(str(tmp_path / "program.py"))

    assert calls[0][0] == EVOLUTION_LATTICES
    assert calls[0][1]["quick"] is True
    assert calls[0][1]["persist_quick_exploration"] is True
    assert (
        calls[0][1]["candidate_limit"]
        == evaluator.STAGE2_PREFLIGHT_CANDIDATE_LIMIT
    )
    assert calls[1][0] == tuple(evaluator.STAGE2_DEEP_LATTICES)
    assert calls[1][1]["quick"] is False
    assert (
        calls[1][1]["refine_trials"]
        == evaluator.STAGE2_REFINE_TRIALS
    )
    assert (
        calls[1][1]["max_distance_per_lattice"]
        == evaluator.STAGE2_DEEP_DISTANCE_PER_LATTICE
    )
    assert (
        calls[1][1]["candidate_limit"]
        == evaluator.STAGE2_DEEP_CANDIDATE_LIMIT
    )


def test_stage2_killable_wrapper_round_trips_worker_result(monkeypatch):
    observed = {}

    class FakeProcess:
        pid = 4321

        def __init__(self, command, **kwargs):
            observed["command"] = command
            observed["kwargs"] = kwargs
            Path(command[4]).write_text(json.dumps({
                "schema_version": 1,
                "status": "completed",
                "metrics": {"combined_score": 7.5},
                "artifacts": {"summary": "bounded"},
            }))

        def wait(self, timeout=None):
            observed.setdefault("timeouts", []).append(timeout)
            return 0

    monkeypatch.setattr(evaluator.subprocess, "Popen", FakeProcess)

    result = evaluator.evaluate_stage2("/tmp/generated program.py")
    metrics = getattr(result, "metrics", result)
    artifacts = getattr(result, "artifacts", {})

    assert metrics["combined_score"] == 7.5
    assert artifacts["summary"] == "bounded"
    assert observed["command"][1] == str(Path(evaluator.__file__).resolve())
    assert observed["command"][2] == "--stage2-worker"
    assert observed["command"][3] == "/tmp/generated program.py"
    assert observed["kwargs"]["start_new_session"] is True
    assert all(
        observed["kwargs"]["env"][variable] == "1"
        for variable in evaluator.STAGE2_NUMERIC_THREAD_ENV
    )
    assert observed["timeouts"] == [evaluator._stage2_hard_timeout_s()]


def test_stage2_hard_timeout_stays_below_bound_outer_timeout(
    monkeypatch,
):
    monkeypatch.setenv(evaluator.STAGE2_OUTER_TIMEOUT_ENV, "1200")
    assert evaluator._stage2_hard_timeout_s() == 1050
    monkeypatch.setenv(evaluator.STAGE2_OUTER_TIMEOUT_ENV, "900")
    assert evaluator._stage2_hard_timeout_s() == 840
    monkeypatch.setenv(evaluator.STAGE2_OUTER_TIMEOUT_ENV, "30")
    with pytest.raises(RuntimeError, match="no hard-timeout margin"):
        evaluator._stage2_hard_timeout_s()


def test_stage2_killable_wrapper_terminates_group_on_timeout(monkeypatch):
    kills = []

    class TimedOutProcess:
        pid = 8765

        def __init__(self, _command, **_kwargs):
            self.wait_calls = 0

        def wait(self, timeout=None):
            self.wait_calls += 1
            if self.wait_calls == 1:
                raise evaluator.subprocess.TimeoutExpired(
                    "stage2", timeout
                )
            return -evaluator.signal.SIGTERM

    monkeypatch.setattr(
        evaluator.subprocess, "Popen", TimedOutProcess
    )
    monkeypatch.setattr(
        evaluator.os,
        "killpg",
        lambda pid, sig: kills.append((pid, sig)),
    )

    result = evaluator.evaluate_stage2("/tmp/slow-program.py")
    metrics = getattr(result, "metrics", result)

    assert metrics["stage2_hard_timeout"] == 1.0
    assert metrics["stage2_subprocess_failed"] == 1.0
    assert kills == [
        (8765, evaluator.signal.SIGTERM),
        (8765, evaluator.signal.SIGKILL),
    ]


@pytest.mark.skipif(
    not Path("/proc").is_dir(),
    reason="requires Linux process-group semantics",
)
def test_stage2_termination_kills_term_ignoring_descendant(tmp_path):
    child_pid_path = tmp_path / "child.pid"
    child_code = (
        "import signal,time; "
        "signal.signal(signal.SIGTERM, signal.SIG_IGN); "
        "time.sleep(300)"
    )
    leader_code = (
        "import pathlib,subprocess,sys,time; "
        f"child=subprocess.Popen([sys.executable, '-c', {child_code!r}]); "
        f"pathlib.Path({str(child_pid_path)!r}).write_text(str(child.pid)); "
        "time.sleep(300)"
    )
    leader = subprocess.Popen(
        [sys.executable, "-c", leader_code],
        start_new_session=True,
    )
    child_pid = None
    try:
        deadline = time.monotonic() + 10
        while time.monotonic() < deadline:
            try:
                child_pid = int(child_pid_path.read_text())
                break
            except (FileNotFoundError, ValueError):
                time.sleep(0.05)
        assert child_pid is not None

        evaluator._terminate_stage2_process_group(leader)

        deadline = time.monotonic() + 10
        while (
            time.monotonic() < deadline
            and Path(f"/proc/{child_pid}").exists()
        ):
            time.sleep(0.05)
        assert not Path(f"/proc/{child_pid}").exists()
    finally:
        if leader.poll() is None:
            try:
                os.killpg(leader.pid, signal.SIGKILL)
            except ProcessLookupError:
                pass
            leader.wait(timeout=10)


def test_stage2_worker_writes_strict_atomic_result(tmp_path, monkeypatch):
    result_path = tmp_path / "stage2-result.json"
    monkeypatch.setattr(
        evaluator,
        "_evaluate_stage2_impl",
        lambda _program: {
            "combined_score": 4.0,
            "term_count": 3.0,
        },
    )

    assert (
        evaluator._stage2_worker_main("program.py", str(result_path))
        == 0
    )
    assert json.loads(result_path.read_text()) == {
        "schema_version": 1,
        "status": "completed",
        "metrics": {
            "combined_score": 4.0,
            "term_count": 3.0,
        },
        "artifacts": {},
    }
    assert not list(tmp_path.glob(".*.tmp-*"))


def test_stage2_actual_subprocess_smoke(tmp_path):
    program = tmp_path / "empty-generator.py"
    program.write_text(
        "def generate_candidates(ell, m):\n"
        "    return []\n"
    )

    result = evaluator.evaluate_stage2(str(program))
    metrics = getattr(result, "metrics", result)

    assert "stage2_subprocess_failed" not in metrics
    assert metrics["combined_score"] == 0.0
    assert metrics["target_preflight_lattices"] == float(
        len(EVOLUTION_LATTICES)
    )


@pytest.mark.skipif(
    not Path("/proc").is_dir() or not hasattr(os, "fork"),
    reason="requires Linux process lifecycle semantics",
)
def test_stage2_process_group_dies_when_owner_is_killed(tmp_path):
    program = tmp_path / "blocking-generator.py"
    program.write_text(
        "import time\n"
        "def generate_candidates(ell, m):\n"
        "    time.sleep(300)\n"
        "    return []\n"
    )
    qcode_root = Path(evaluator.__file__).resolve().parent.parent
    environment = os.environ.copy()
    environment["PYTHONPATH"] = os.pathsep.join(
        filter(
            None,
            (
                str(qcode_root),
                environment.get("PYTHONPATH", ""),
            ),
        )
    )
    owner = subprocess.Popen(
        [
            sys.executable,
            "-c",
            (
                "from evolve.openevolve_evaluator import evaluate_stage2; "
                f"evaluate_stage2({str(program)!r})"
            ),
        ],
        cwd=qcode_root,
        env=environment,
        stdin=subprocess.DEVNULL,
        stdout=subprocess.DEVNULL,
        stderr=subprocess.DEVNULL,
    )
    stage2_pid = None
    guardian_pid = None

    def child_pids(pid):
        path = Path(f"/proc/{pid}/task/{pid}/children")
        try:
            return [int(value) for value in path.read_text().split()]
        except (FileNotFoundError, ProcessLookupError):
            return []

    try:
        deadline = time.monotonic() + 20
        while time.monotonic() < deadline:
            children = child_pids(owner.pid)
            if children:
                stage2_pid = children[0]
                break
            if owner.poll() is not None:
                pytest.fail("Stage 2 owner exited before spawning its worker")
            time.sleep(0.05)
        assert stage2_pid is not None

        deadline = time.monotonic() + 20
        while time.monotonic() < deadline:
            children = child_pids(stage2_pid)
            if children:
                guardian_pid = children[0]
                break
            time.sleep(0.05)
        assert guardian_pid is not None

        os.kill(owner.pid, signal.SIGKILL)
        owner.wait(timeout=10)
        deadline = time.monotonic() + 10
        while time.monotonic() < deadline:
            if not Path(f"/proc/{stage2_pid}").exists() and not Path(
                f"/proc/{guardian_pid}"
            ).exists():
                break
            time.sleep(0.05)
        assert not Path(f"/proc/{stage2_pid}").exists()
        assert not Path(f"/proc/{guardian_pid}").exists()
    finally:
        if owner.poll() is None:
            owner.kill()
            owner.wait(timeout=10)
        if stage2_pid is not None and Path(
            f"/proc/{stage2_pid}"
        ).exists():
            try:
                os.killpg(stage2_pid, signal.SIGKILL)
            except ProcessLookupError:
                pass


@pytest.mark.parametrize(
    "malformed",
    (
        ("bad", "shape", "entry"),
        ("not-terms", [[0, 0], [0, 1]]),
        ([[0, 0], [0, 1]], [[0, "bad"], [1, 0]]),
    ),
)
@pytest.mark.parametrize("bad_first", (False, True))
def test_malformed_generator_item_does_not_hide_valid_peer(
    monkeypatch, malformed, bad_first
):
    valid = (
        [(0, 0), (0, 1), (1, 0)],
        [(0, 0), (0, 2), (2, 0)],
    )
    evaluated = []

    def fake_batch(ell, m, rows, **_kwargs):
        evaluated.extend(rows)
        return [{
            "ell": ell,
            "m": m,
            "A_terms": a_terms,
            "B_terms": b_terms,
            "n": 72,
            "k": 12,
            "d": 0,
            "fom": 0.0,
            "score": 12 / 72,
            "stage": "quick_k_only",
            "encoding_rate": 12 / 72,
        } for a_terms, b_terms in rows]

    monkeypatch.setattr(evaluator, "evaluate_batch", fake_batch)
    monkeypatch.setattr(
        evaluator,
        "_filter_static_eligible",
        lambda rows: (rows, []),
    )
    generated = [malformed, valid] if bad_first else [valid, malformed]
    metrics = evaluator._run_evaluation(
        lambda _ell, _m: generated,
        [(6, 6)],
        quick=True,
    )

    assert evaluated == [valid]
    assert metrics["num_valid"] == 1
    assert metrics["malformed_candidate_definitions"] == 1
    assert len(metrics["errors"]) == 1
    assert "candidate[" in metrics["errors"][0]
    assert "malformed" in metrics["errors"][0]


def test_final_gate_persistence_probes_do_not_change_resumed_fitness_basis(
    tmp_path, monkeypatch
):
    critical = {
        "ell": 6,
        "m": 6,
        "A_terms": [[0, 0]],
        "B_terms": [[0, 0]],
        "n": 72,
        "k": 16,
        "d": 10,
        "fom": 16 * 10 * 10 / 72,
        "encoding_rate": 16 / 72,
    }
    historical = {
        "ell": 12,
        "m": 6,
        "A_terms": [[0, 0], [0, 1], [1, 0]],
        "B_terms": [[0, 0], [0, 2], [2, 0]],
        "n": 144,
        "k": 12,
        "d": 12,
        "fom": 12.0,
        "encoding_rate": 12 / 144,
    }
    metrics = {
        "best_fom": critical["fom"],
        "mean_fom": (critical["fom"] + historical["fom"]) / 2,
        "num_valid": 2,
        "num_high_k": 2,
        "lattices_with_high_k": 2,
        "best_encoding_rate": critical["encoding_rate"],
        "num_above_6": 2,
        "num_above_12": 2,
        "total_candidates": 2,
        "unique_candidates": 2,
        "evaluated_candidate_definitions": 2,
        "duplicate_candidate_occurrences": 0,
        "winner_capable_quick_exploration_persisted": 0,
        "winner_capable_unresolved_top_persisted": 0,
        "best_code": critical,
        "all_results": [critical, historical],
        "errors": [],
    }
    monkeypatch.setattr(
        evaluator,
        "_load_generate_candidates",
        lambda _path: lambda _ell, _m: [],
    )
    monkeypatch.setattr(
        evaluator,
        "_run_evaluation",
        lambda *_args, **_kwargs: metrics,
    )
    monkeypatch.setattr(evaluator, "_write_metrics_jsonl", lambda _metrics: None)
    monkeypatch.setattr(evaluator, "save_code", lambda _row: None)
    monkeypatch.setattr(evaluator, "update_pareto_front", lambda _rows: None)

    evaluated = evaluator._evaluate_stage2_impl(
        str(tmp_path / "program.py")
    )
    result = getattr(evaluated, "metrics", evaluated)

    assert result["best_fom"] == critical["fom"]
    assert result["combined_score"] == historical["fom"]
    assert result["term_count"] == 3


def test_quick_only_lane_is_k_stratified_and_keeps_low_k_reachable():
    rows = []
    for index in range(24):
        # Deliberately flood the pool with k=8 definitions; a global hash-only
        # sample can crowd out the lone [[72,4,*]]-capable definition.
        rows.append({
            "ell": 6,
            "m": 6,
            "A_terms": [[0, 0], [0, 1], [index + 1, 0]],
            "B_terms": [[0, 0], [0, 2], [index + 2, 0]],
            "n": 72,
            "k": 8,
            "d": 0,
        })
    low_k = {
        "ell": 6,
        "m": 6,
        "A_terms": [[0, 0], [0, 3], [31, 0]],
        "B_terms": [[0, 0], [0, 4], [32, 0]],
        "n": 72,
        "k": 4,
        "d": 0,
    }
    high_k = {
        "ell": 6,
        "m": 6,
        "A_terms": [[0, 0], [0, 5], [33, 0]],
        "B_terms": [[0, 0], [0, 6], [34, 0]],
        "n": 72,
        "k": 12,
        "d": 0,
    }

    selected = evaluator._select_quick_exploration(
        [*rows, low_k, high_k],
        ell=6,
        m=6,
        sampling_salt="fixed-production-salt",
        limit=3,
    )

    assert {row["k"] for row in selected} == {4, 8, 12}
    assert low_k in selected

    # With more k strata than the bounded quota, the program-derived salt
    # rotates which strata enter the lane. This fixed production salt proves
    # that k=4 remains reachable even in that crowded case.
    crowded_strata = [
        {
            "ell": 6,
            "m": 6,
            "A_terms": [[0, 0], [0, 1], [index + 1, 0]],
            "B_terms": [[0, 0], [0, 2], [index + 2, 0]],
            "n": 72,
            "k": k,
            "d": 0,
        }
        for index, k in enumerate(range(4, 38, 2))
    ]
    crowded_selected = evaluator._select_quick_exploration(
        crowded_strata,
        ell=6,
        m=6,
        sampling_salt="fixed-production-salt-0",
        limit=evaluator.MAX_WINNER_CAPABLE_EXPLORATION_PER_LATTICE,
    )

    assert len(crowded_selected) == 8
    assert 4 in {row["k"] for row in crowded_selected}


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


def test_candidate_sampling_deduplicates_term_order_before_any_cap():
    base_a = [(0, 0), (1, 0), (0, 1)]
    base_b = [(0, 0), (2, 0), (0, 2)]
    permuted = [
        (list(a_terms), list(b_terms))
        for a_terms in permutations(base_a)
        for b_terms in permutations(base_b)
    ]
    unique = (
        [(0, 0), (3, 0), (0, 1)],
        list(base_b),
    )

    sampled = evaluator._bounded_candidate_sample(
        [*permuted, unique],
        ell=6,
        m=6,
        limit=8,
        sampling_salt="p0",
    )

    assert len(sampled) == 2
    assert unique in sampled


def test_malformed_candidate_cannot_hide_strict_integer_definition():
    malformed = (
        [(0, 0), (True, 0), (0, 1)],
        [(0, 0), (2, 0), (0, 2)],
    )
    valid = (
        [(0, 0), (1, 0), (0, 1)],
        [(0, 0), (2, 0), (0, 2)],
    )

    unique, occurrences = evaluator._deduplicate_candidate_definitions(
        [malformed, valid],
        ell=6,
        m=6,
    )

    assert unique == [malformed, valid]
    assert sorted(occurrences.values()) == [1, 1]


def test_run_deduplicates_permutations_and_preserves_occurrence_count(
    monkeypatch,
):
    base_a = [(0, 0), (1, 0), (0, 1)]
    base_b = [(0, 0), (2, 0), (0, 2)]
    permuted = [
        (list(a_terms), list(b_terms))
        for a_terms in permutations(base_a)
        for b_terms in permutations(base_b)
    ]
    unique = (
        [(0, 0), (3, 0), (0, 1)],
        list(base_b),
    )
    evaluated = []

    def fake_batch(ell, m, rows, **_kwargs):
        evaluated.extend(rows)
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

    monkeypatch.setattr(evaluator, "evaluate_batch", fake_batch)
    monkeypatch.setattr(
        evaluator,
        "_filter_static_eligible",
        lambda rows: (rows, []),
    )
    metrics = evaluator._run_evaluation(
        lambda _ell, _m: [*permuted, unique],
        [(6, 6)],
        quick=True,
    )

    assert len(evaluated) == 2
    assert metrics["total_candidates"] == 37
    assert metrics["unique_candidates"] == 2
    assert metrics["evaluated_candidate_definitions"] == 2
    assert metrics["duplicate_candidate_occurrences"] == 35
    assert sorted(
        row["generator_occurrence_count"]
        for row in metrics["all_results"]
    ) == [1, 36]


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
        if row.get("candidate_persistence_reason")
        == evaluator.QUICK_EXPLORATION_PERSISTENCE_REASON
    ]
    assert len(quick_rows) == (
        evaluator.MAX_WINNER_CAPABLE_EXPLORATION_PER_LATTICE
    )
    pending_rows = [
        row for row in persisted
        if row.get("candidate_persistence_reason")
        == evaluator.DISTANCE_PENDING_PERSISTENCE_REASON
    ]
    assert len(pending_rows) == len(distance_inputs)
    assert all(row["d"] == 0 and row["fom"] == 0 for row in quick_rows)
    assert all(row["minimum_winning_distance"] == 15 for row in quick_rows)
    assert len(persisted) == (
        len(distance_inputs) + len(pending_rows) + len(quick_rows)
    )


def test_unresolved_top_upgrades_its_write_ahead_pending_row(
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
    assert len(persisted) == 2
    assert all(
        row["candidate_persistence_lane"]
        == evaluator.WINNER_CAPABLE_EXPLORATION_LANE
        for row in persisted
    )
    assert persisted[0]["candidate_persistence_reason"] == (
        evaluator.DISTANCE_PENDING_PERSISTENCE_REASON
    )
    assert persisted[1]["candidate_persistence_reason"] == (
        evaluator.UNRESOLVED_TOP_PERSISTENCE_REASON
    )
    assert metrics["winner_capable_distance_pending_persisted"] == 1
    assert metrics["winner_capable_unresolved_top_persisted"] == 1
    assert metrics["winner_capable_quick_exploration_persisted"] == 0


def test_distance_backend_error_has_write_ahead_top_and_independent_quick_quota(
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
    distance_keys = set()
    path = (
        tmp_path
        / "results"
        / "evolution"
        / "distance-error"
        / "all_codes.jsonl"
    )

    def fake_batch(ell, m, rows, **kwargs):
        quick = kwargs.get("quick") is True
        if not quick:
            distance_keys.update(
                (
                    tuple(sorted(map(tuple, a_terms))),
                    tuple(sorted(map(tuple, b_terms))),
                )
                for a_terms, b_terms in rows
            )
            # This assertion executes at the distance call site. It proves the
            # handoff is durable even when the backend never returns before the
            # outer OpenEvolve wall timeout.
            preexisting = [
                json.loads(line) for line in path.read_text().splitlines()
            ]
            assert sum(
                row.get("candidate_persistence_reason")
                == evaluator.DISTANCE_PENDING_PERSISTENCE_REASON
                for row in preexisting
            ) == len(rows)
            assert sum(
                row.get("candidate_persistence_reason")
                == evaluator.QUICK_EXPLORATION_PERSISTENCE_REASON
                for row in preexisting
            ) == evaluator.MAX_WINNER_CAPABLE_EXPLORATION_PER_LATTICE
            raise RuntimeError("simulated distance backend failure")
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

    monkeypatch.setattr(evaluator, "evaluate_batch", fake_batch)
    metrics = evaluator._run_evaluation(
        lambda _ell, _m: candidates,
        [(6, 6)],
        quick=False,
        max_distance_per_lattice=2,
        run_name="distance-error",
        sampling_salt="production-error-probe",
    )

    persisted = [json.loads(line) for line in path.read_text().splitlines()]
    pending = [
        row for row in persisted
        if row.get("candidate_persistence_reason")
        == evaluator.DISTANCE_PENDING_PERSISTENCE_REASON
    ]
    failed = [
        row for row in persisted
        if row.get("candidate_persistence_reason")
        == evaluator.DISTANCE_ERROR_PERSISTENCE_REASON
    ]
    quick = [
        row for row in persisted
        if row.get("candidate_persistence_reason")
        == evaluator.QUICK_EXPLORATION_PERSISTENCE_REASON
    ]

    def definitions(rows):
        return {
            (
                tuple(sorted(map(tuple, row["A_terms"]))),
                tuple(sorted(map(tuple, row["B_terms"]))),
            )
            for row in rows
        }

    assert definitions(pending) == distance_keys
    assert definitions(failed) == distance_keys
    assert definitions(quick).isdisjoint(distance_keys)
    assert len(pending) == len(failed) == 2
    assert len(quick) == evaluator.MAX_WINNER_CAPABLE_EXPLORATION_PER_LATTICE
    assert all(row["d"] == 0 for row in failed)
    assert all(row["d_is_exact"] is False for row in failed)
    assert all(row["distance_trusted"] is False for row in failed)
    assert all(row["milp_attempted"] is False for row in failed)
    assert all(
        row["distance_backend_error"]["type"] == "RuntimeError"
        for row in failed
    )
    assert metrics["winner_capable_distance_pending_persisted"] == 2
    assert metrics["winner_capable_distance_error_persisted"] == 2
    assert metrics["winner_capable_quick_exploration_persisted"] == len(quick)
    assert metrics["distance_backend_error_count"] == 1
    assert metrics["errors"] == [
        "(6,6): distance backend RuntimeError: "
        "simulated distance backend failure"
    ]

    monkeypatch.setattr(
        evaluator,
        "_load_generate_candidates",
        lambda _path: lambda _ell, _m: [],
    )
    monkeypatch.setattr(
        evaluator,
        "_run_evaluation",
        lambda *_args, **_kwargs: metrics,
    )
    monkeypatch.setattr(evaluator, "_write_metrics_jsonl", lambda _metrics: None)
    evaluated = evaluator._evaluate_stage2_impl(
        str(tmp_path / "program.py")
    )
    result = getattr(evaluated, "metrics", evaluated)
    artifacts = getattr(evaluated, "artifacts", {})
    assert result["distance_backend_error_count"] == 1.0
    assert artifacts["errors"] == metrics["errors"][0]
    assert "Distance backend failures: 1." in artifacts["summary"]


def test_write_ahead_log_failure_aborts_before_distance_backend(monkeypatch):
    definition = (
        [[0, 0], [0, 1], [1, 0]],
        [[0, 0], [0, 2], [2, 0]],
    )
    distance_called = False

    def fake_batch(ell, m, rows, **kwargs):
        nonlocal distance_called
        if kwargs.get("quick") is not True:
            distance_called = True
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

    def fail_log(*_args, **_kwargs):
        raise evaluator.CandidateLogWriteError("write-ahead unavailable")

    monkeypatch.setattr(evaluator, "evaluate_batch", fake_batch)
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
    monkeypatch.setattr(evaluator, "_log_code_jsonl", fail_log)

    with pytest.raises(
        evaluator.CandidateLogWriteError,
        match="write-ahead unavailable",
    ):
        evaluator._run_evaluation(
            lambda _ell, _m: [definition],
            [(6, 6)],
            quick=False,
            max_distance_per_lattice=1,
            run_name="write-ahead-failure",
        )
    assert distance_called is False


def test_all_unresolved_top_are_persisted_before_independent_quick_quota(
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
        for index in range(40)
    ]
    distance_keys = set()

    def fake_batch(ell, m, rows, **kwargs):
        quick = kwargs.get("quick") is True
        if not quick:
            distance_keys.update(
                (
                    tuple(sorted(map(tuple, a_terms))),
                    tuple(sorted(map(tuple, b_terms))),
                )
                for a_terms, b_terms in rows
            )
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
                "stage": (
                    "quick_k_only" if quick else "refined_estimate"
                ),
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
        run_name="mixed-unresolved-top",
        sampling_salt="p0",
    )

    path = (
        tmp_path
        / "results"
        / "evolution"
        / "mixed-unresolved-top"
        / "all_codes.jsonl"
    )
    persisted = [json.loads(line) for line in path.read_text().splitlines()]
    unresolved = [
        row for row in persisted
        if row.get("candidate_persistence_reason")
        == evaluator.UNRESOLVED_TOP_PERSISTENCE_REASON
    ]
    quick = [
        row for row in persisted
        if row.get("candidate_persistence_reason")
        == evaluator.QUICK_EXPLORATION_PERSISTENCE_REASON
    ]
    unresolved_keys = {
        (
            tuple(sorted(map(tuple, row["A_terms"]))),
            tuple(sorted(map(tuple, row["B_terms"]))),
        )
        for row in unresolved
    }

    assert unresolved_keys == distance_keys
    assert len(unresolved) == 2
    assert len(quick) == (
        evaluator.MAX_WINNER_CAPABLE_EXPLORATION_PER_LATTICE
    )
    assert metrics["winner_capable_unresolved_top_persisted"] == 2
    assert metrics["winner_capable_quick_exploration_persisted"] == len(quick)


def test_distance_adapter_cannot_overproduce_unresolved_top_silently(
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
        for index in range(2)
    ]

    def result(ell, m, a_terms, b_terms, *, stage):
        return {
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

    def fake_batch(ell, m, rows, **kwargs):
        if kwargs.get("quick") is True:
            return [
                result(
                    ell,
                    m,
                    a_terms,
                    b_terms,
                    stage="quick_k_only",
                )
                for a_terms, b_terms in rows
            ]
        # The selected universe is top-1. Returning an unrelated second row is
        # an adapter-contract violation and must abort, never truncate.
        selected_a, selected_b = rows[0]
        extra_a, extra_b = candidates[1]
        return [
            result(
                ell,
                m,
                selected_a,
                selected_b,
                stage="refined_estimate",
            ),
            result(
                ell,
                m,
                extra_a,
                extra_b,
                stage="refined_estimate",
            ),
        ]

    monkeypatch.setattr(evaluator, "evaluate_batch", fake_batch)

    with pytest.raises(
        evaluator.CandidateLogWriteError,
        match="returned 2 unresolved definitions for a top-1 selection",
    ):
        evaluator._run_evaluation(
            lambda _ell, _m: candidates,
            [(6, 6)],
            quick=False,
            max_distance_per_lattice=1,
            run_name="invalid-distance-adapter",
            sampling_salt="fixed-production-salt",
        )

    path = (
        tmp_path
        / "results"
        / "evolution"
        / "invalid-distance-adapter"
        / "all_codes.jsonl"
    )
    persisted = [json.loads(line) for line in path.read_text().splitlines()]
    assert any(
        row.get("candidate_persistence_reason")
        == evaluator.DISTANCE_PENDING_PERSISTENCE_REASON
        for row in persisted
    )
    assert not any(
        row.get("candidate_persistence_reason")
        == evaluator.UNRESOLVED_TOP_PERSISTENCE_REASON
        for row in persisted
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
