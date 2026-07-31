"""Durability and concurrency tests for OpenEvolve's Stage 1 candidate log."""

from __future__ import annotations

import json
import math
import multiprocessing
import os
import signal
import subprocess
import sys
import threading
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
from evaluation.search_sampling import DEFAULT_SPLITS


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


def _complete_preflight_metrics(
    contract_id: int,
    *,
    evaluated: int = 3,
    eligible: int = 2,
) -> dict[str, float]:
    return {
        evaluator.WINNER_PREFLIGHT_CONTRACT_VERSION_METRIC: float(
            evaluator.WINNER_PREFLIGHT_CONTRACT_VERSION
        ),
        evaluator.WINNER_PREFLIGHT_CONTRACT_ID_METRIC: float(contract_id),
        evaluator.WINNER_PREFLIGHT_COMPLETE_METRIC: 1.0,
        evaluator.WINNER_PREFLIGHT_INCOMPLETE_METRIC: 0.0,
        evaluator.WINNER_PREFLIGHT_LATTICES_METRIC: float(
            len(EVOLUTION_LATTICES)
        ),
        evaluator.WINNER_PREFLIGHT_EVALUATED_METRIC: float(evaluated),
        evaluator.WINNER_PREFLIGHT_ELIGIBLE_METRIC: float(eligible),
        evaluator.WINNER_PREFLIGHT_PERSISTED_METRIC: float(eligible),
        evaluator.WINNER_PREFLIGHT_OMITTED_METRIC: 0.0,
        evaluator.WINNER_PREFLIGHT_HARD_TIMEOUT_METRIC: 0.0,
        evaluator.WINNER_PREFLIGHT_SUBPROCESS_FAILED_METRIC: 0.0,
    }


def _support_metrics(
    *,
    unique: int = 0,
    eligible: int | None = None,
    rejected: int = 0,
    evaluated: int | None = None,
) -> dict:
    """Build the complete versioned support partition used by fake runs."""

    if eligible is None:
        eligible = unique - rejected
    if evaluated is None:
        evaluated = eligible
    return {
        evaluator.SUPPORT_FILTER_VERSION_METRIC: (
            evaluator.CHALLENGE_SUPPORT_FILTER_VERSION
        ),
        evaluator.SUPPORT_WEIGHT_ELIGIBLE_METRIC: eligible,
        evaluator.SUPPORT_WEIGHT_REJECTED_METRIC: rejected,
        evaluator.SUPPORT_WEIGHT_EVALUATED_METRIC: evaluated,
        evaluator.SUPPORT_WEIGHT_PARTITION_COMPLETE_METRIC: int(
            unique == eligible + rejected
        ),
        evaluator.SUPPORT_WEIGHT_EVALUATION_COVERAGE_METRIC: (
            evaluated / eligible if eligible else 1.0
        ),
        evaluator.SUPPORT_WEIGHT_ELIGIBLE_FRACTION_METRIC: (
            eligible / unique if unique else 0.0
        ),
        evaluator.SUPPORT_WEIGHT_REJECTION_FRACTION_METRIC: (
            rejected / unique if unique else 0.0
        ),
        evaluator.SUPPORT_SPLITS_COVERED_METRIC: 0,
        evaluator.SUPPORT_SPLITS_TOTAL_METRIC: len(
            evaluator.CHALLENGE_SUPPORT_SPLITS
        ),
        evaluator.SUPPORT_SPLIT_COVERAGE_METRIC: 0.0,
        evaluator.SUPPORT_SPLIT_LATTICE_COVERAGE_METRIC: 0.0,
        "support_split_counts": {},
        "support_weight_rejection_splits": {},
        evaluator.PATTERN_CLASSIFIER_VERSION_METRIC: (
            evaluator.PATTERN_CLASSIFIER_VERSION
        ),
    }


def _empty_stage2_lattice_metrics() -> dict:
    support = _support_metrics()
    support["support_split_counts"] = {
        f"{a_count}+{b_count}": 0
        for a_count, b_count in evaluator.CHALLENGE_SUPPORT_SPLITS
    }
    return {
        "best_fom": 0.0,
        "mean_fom": 0.0,
        "num_valid": 0,
        "num_above_6": 0,
        "num_above_12": 0,
        "total_candidates": 0,
        "unique_candidates": 0,
        "evaluated_candidate_definitions": 0,
        "duplicate_candidate_occurrences": 0,
        "winner_capable_quick_exploration_eligible": 0,
        "winner_capable_quick_exploration_persisted": 0,
        "winner_capable_quick_exploration_omitted": 0,
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
        "lattices_requested": 1,
        "lattices_completed": 1,
        "lattice_failures": 0,
        **support,
    }


def _stage1_summary(
    lattice: tuple[int, int],
    *,
    pool_sha256: str,
    unique: int = 1,
    rejected: int = 0,
    winner_eligible: int | None = None,
    candidate_log_records: int | None = None,
) -> dict[str, object]:
    support_eligible = unique - rejected
    if winner_eligible is None:
        winner_eligible = support_eligible
    if candidate_log_records is None:
        candidate_log_records = winner_eligible
    return evaluator._stage1_lattice_summary(
        {
            "unique_candidates": unique,
            "evaluated_candidate_definitions": support_eligible,
            "lattices_completed": 1,
            "lattice_failures": 0,
            "winner_capable_quick_exploration_eligible": winner_eligible,
            "winner_capable_quick_exploration_persisted": winner_eligible,
            "winner_capable_quick_exploration_omitted": 0,
            evaluator.STAGE1_CANDIDATE_LOG_RECORDS_FIELD: (
                candidate_log_records
            ),
            **_support_metrics(
                unique=unique,
                eligible=support_eligible,
                rejected=rejected,
                evaluated=support_eligible,
            ),
        },
        lattice=lattice,
        pool_sha256=pool_sha256,
    )


def test_direct_evaluator_contract_matches_launcher_for_same_run(
    tmp_path, monkeypatch
):
    import evolve.run_evolution as launcher

    candidate_log = (tmp_path / "direct-run" / "all_codes.jsonl").resolve()
    monkeypatch.delenv(
        evaluator.WINNER_PREFLIGHT_CONTRACT_ID_ENV,
        raising=False,
    )
    monkeypatch.setenv(
        evaluator.CANDIDATE_LOG_PATH_ENV,
        str(candidate_log),
    )

    expected = launcher._winner_preflight_contract_id(
        evaluator.__file__,
        launcher._evaluator_dependency_identities(),
        candidate_log_path=candidate_log,
    )

    assert evaluator._current_winner_preflight_contract_id() == expected


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


def _batch_append_worker(
    project_root: str,
    run_name: str,
    worker: int,
    count: int,
) -> None:
    evaluator._PROJECT_ROOT = project_root
    evaluator._log_codes_jsonl(
        [_result(worker, index) for index in range(count)],
        run_name=run_name,
    )


def _run_crashing_candidate_append(
    log_path: Path,
    rows: list[dict],
    *,
    crash_mode: str,
) -> subprocess.CompletedProcess:
    project_root = Path(evaluator.__file__).resolve().parent.parent
    script = r"""
import json
import os
import signal
import sys
from pathlib import Path

import evolve.openevolve_evaluator as evaluator

mode = sys.argv[1]
log_path = Path(sys.argv[2])
rows = json.loads(sys.argv[3])
if mode == "partial":
    def kill_after_partial(descriptor, payload):
        view = memoryview(payload)
        count = os.write(descriptor, view[:min(37, len(view) - 1)])
        if count <= 0 or count >= len(view):
            raise RuntimeError("crash injection did not make a partial write")
        os.fsync(descriptor)
        os.kill(os.getpid(), signal.SIGKILL)
    evaluator._write_candidate_log_payload = kill_after_partial
elif mode == "after-full":
    def kill_before_clear(_log_file):
        os.kill(os.getpid(), signal.SIGKILL)
    evaluator._clear_candidate_log_wal = kill_before_clear
else:
    raise RuntimeError(f"unknown crash mode: {mode}")
evaluator._log_codes_jsonl(rows, candidate_log_path=log_path)
"""
    environment = dict(os.environ)
    existing_path = environment.get("PYTHONPATH")
    environment["PYTHONPATH"] = (
        str(project_root)
        if not existing_path
        else str(project_root) + os.pathsep + existing_path
    )
    return subprocess.run(
        [
            sys.executable,
            "-c",
            script,
            crash_mode,
            str(log_path),
            json.dumps(rows),
        ],
        cwd=project_root,
        env=environment,
        check=False,
        capture_output=True,
        text=True,
        timeout=30,
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

    def short_then_fail(descriptor: int, payload: bytes) -> None:
        original_write(descriptor, memoryview(payload)[:7])
        raise OSError("simulated candidate-log write failure")

    monkeypatch.setattr(
        evaluator,
        "_write_candidate_log_payload",
        short_then_fail,
    )
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


def test_candidate_jsonl_batch_write_failure_rolls_back_entire_batch(
    tmp_path, monkeypatch
):
    monkeypatch.setattr(evaluator, "_PROJECT_ROOT", str(tmp_path))
    original_write = os.write

    def partial_batch_then_fail(descriptor: int, payload: bytes) -> None:
        original_write(descriptor, memoryview(payload)[:31])
        raise OSError("simulated batch append failure")

    monkeypatch.setattr(
        evaluator,
        "_write_candidate_log_payload",
        partial_batch_then_fail,
    )
    with pytest.raises(
        evaluator.CandidateLogWriteError,
        match="failed to persist discovered candidate batch",
    ):
        evaluator._log_codes_jsonl(
            [_result(0, index) for index in range(12)],
            run_name="batch-write-failure",
        )

    path = (
        tmp_path
        / "results"
        / "evolution"
        / "batch-write-failure"
        / "all_codes.jsonl"
    )
    assert path.read_bytes() == b""


def test_large_candidate_batch_is_persisted_in_bounded_fsync_chunks(
    tmp_path, monkeypatch
):
    monkeypatch.setattr(evaluator, "_PROJECT_ROOT", str(tmp_path))
    count = evaluator.CANDIDATE_LOG_CHUNK_MAX_RECORDS * 2 + 3
    original_append = evaluator._append_candidate_jsonl
    chunks = []

    def track_chunk(path, payload):
        chunks.append((payload.count(b"\n"), len(payload)))
        original_append(path, payload)

    monkeypatch.setattr(evaluator, "_append_candidate_jsonl", track_chunk)
    persisted = evaluator._log_codes_jsonl(
        [_result(0, index) for index in range(count)],
        run_name="bounded-chunks",
    )

    path = (
        tmp_path
        / "results"
        / "evolution"
        / "bounded-chunks"
        / "all_codes.jsonl"
    )
    rows = [json.loads(line) for line in path.read_bytes().splitlines()]
    assert persisted == count
    assert len(rows) == count
    assert [records for records, _size in chunks] == [
        evaluator.CANDIDATE_LOG_CHUNK_MAX_RECORDS,
        evaluator.CANDIDATE_LOG_CHUNK_MAX_RECORDS,
        3,
    ]
    assert all(
        records <= evaluator.CANDIDATE_LOG_CHUNK_MAX_RECORDS
        and size <= evaluator.CANDIDATE_LOG_CHUNK_MAX_BYTES
        for records, size in chunks
    )


def test_later_candidate_chunk_failure_surfaces_after_durable_prefix(
    tmp_path, monkeypatch
):
    monkeypatch.setattr(evaluator, "_PROJECT_ROOT", str(tmp_path))
    count = evaluator.CANDIDATE_LOG_CHUNK_MAX_RECORDS + 1
    original_append = evaluator._append_candidate_jsonl
    append_calls = 0

    def fail_second_chunk(path, payload):
        nonlocal append_calls
        append_calls += 1
        if append_calls == 2:
            raise OSError("simulated second chunk failure")
        original_append(path, payload)

    monkeypatch.setattr(
        evaluator,
        "_append_candidate_jsonl",
        fail_second_chunk,
    )
    with pytest.raises(
        evaluator.CandidateLogWriteError,
        match=(
            "after "
            f"{evaluator.CANDIDATE_LOG_CHUNK_MAX_RECORDS} complete records"
        ),
    ):
        evaluator._log_codes_jsonl(
            [_result(0, index) for index in range(count)],
            run_name="failed-second-chunk",
        )

    path = (
        tmp_path
        / "results"
        / "evolution"
        / "failed-second-chunk"
        / "all_codes.jsonl"
    )
    assert len(path.read_bytes().splitlines()) == (
        evaluator.CANDIDATE_LOG_CHUNK_MAX_RECORDS
    )


def test_oversized_candidate_record_uses_one_durable_chunk(
    tmp_path, monkeypatch
):
    path = (tmp_path / "all_codes.jsonl").resolve()
    original_append = evaluator._append_candidate_jsonl
    chunks = []

    def track_chunk(destination, payload):
        chunks.append(bytes(payload))
        original_append(destination, payload)

    monkeypatch.setattr(
        evaluator,
        "_append_candidate_jsonl",
        track_chunk,
    )
    monkeypatch.setattr(
        evaluator,
        "_candidate_jsonl_record",
        lambda _result: {
            "payload": "x" * evaluator.CANDIDATE_LOG_CHUNK_MAX_BYTES
        },
    )

    persisted = evaluator._log_codes_jsonl(
        [{}],
        candidate_log_path=path,
    )

    assert persisted == 1
    assert len(chunks) == 1
    assert len(chunks[0]) > evaluator.CANDIDATE_LOG_CHUNK_MAX_BYTES
    assert json.loads(path.read_text())["payload"].startswith("x")


def test_candidate_jsonl_concurrent_batches_never_interleave_records(tmp_path):
    workers = 4
    per_worker = 12
    run_name = "multiprocess-batch-log"
    context = multiprocessing.get_context("fork")
    processes = [
        context.Process(
            target=_batch_append_worker,
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
    rows = [json.loads(line) for line in path.read_bytes().splitlines()]
    assert len(rows) == workers * per_worker

    worker_order = [row["ell"] - 6 for row in rows]
    batch_order = [
        worker
        for index, worker in enumerate(worker_order)
        if index == 0 or worker_order[index - 1] != worker
    ]
    assert len(batch_order) == workers
    assert set(batch_order) == set(range(workers))
    for worker in range(workers):
        assert [
            row["m"] - 6
            for row in rows
            if row["ell"] - 6 == worker
        ] == list(range(per_worker))


def test_candidate_jsonl_recovers_sigkill_during_partial_batch(tmp_path):
    path = (tmp_path / "partial-kill" / "all_codes.jsonl").resolve()
    path.parent.mkdir()
    interrupted = [_result(7, index) for index in range(3)]

    crashed = _run_crashing_candidate_append(
        path,
        interrupted,
        crash_mode="partial",
    )

    assert crashed.returncode == -signal.SIGKILL
    wal_file, temporary = evaluator._candidate_log_wal_paths(path)
    assert wal_file.is_file()
    assert not temporary.exists()
    assert 0 < path.stat().st_size
    assert not path.read_bytes().endswith(b"\n")

    evaluator._log_codes_jsonl(
        [_result(8, 0)],
        candidate_log_path=path,
    )

    rows = [json.loads(line) for line in path.read_bytes().splitlines()]
    assert [(row["ell"] - 6, row["m"] - 6) for row in rows] == [
        (7, 0),
        (7, 1),
        (7, 2),
        (8, 0),
    ]
    assert not wal_file.exists()
    assert not temporary.exists()


def test_candidate_jsonl_recovers_sigkill_after_full_batch_before_clear(
    tmp_path,
):
    path = (tmp_path / "full-kill" / "all_codes.jsonl").resolve()
    path.parent.mkdir()
    interrupted = [_result(9, index) for index in range(2)]

    crashed = _run_crashing_candidate_append(
        path,
        interrupted,
        crash_mode="after-full",
    )

    assert crashed.returncode == -signal.SIGKILL
    wal_file, temporary = evaluator._candidate_log_wal_paths(path)
    assert wal_file.is_file()
    assert not temporary.exists()
    assert len(path.read_bytes().splitlines()) == len(interrupted)

    evaluator._log_codes_jsonl(
        [_result(10, 0)],
        candidate_log_path=path,
    )

    rows = [json.loads(line) for line in path.read_bytes().splitlines()]
    assert [(row["ell"] - 6, row["m"] - 6) for row in rows] == [
        (9, 0),
        (9, 1),
        (10, 0),
    ]
    assert not wal_file.exists()
    assert not temporary.exists()


def test_candidate_jsonl_residual_wal_temp_fails_closed(tmp_path):
    path = (tmp_path / "temp-residue" / "all_codes.jsonl").resolve()
    path.parent.mkdir()
    _wal_file, temporary = evaluator._candidate_log_wal_paths(path)
    temporary.write_bytes(b"incomplete intent")

    with pytest.raises(
        evaluator.CandidateLogWriteError,
        match="residual temp",
    ):
        evaluator._log_codes_jsonl(
            [_result(0, 0)],
            candidate_log_path=path,
        )

    assert path.read_bytes() == b""
    assert temporary.read_bytes() == b"incomplete intent"


@pytest.mark.parametrize("corruption", ["schema", "path", "hash"])
def test_candidate_jsonl_corrupt_or_misbound_wal_fails_closed(
    tmp_path,
    corruption,
):
    path = (tmp_path / corruption / "all_codes.jsonl").resolve()
    path.parent.mkdir()
    path.touch()
    wal_file, _temporary = evaluator._candidate_log_wal_paths(path)
    payload = b'{"candidate":"orphan"}\n'
    encoded = evaluator._candidate_log_wal_bytes(
        path,
        start_offset=0,
        payload=payload,
    )
    encoded_header, encoded_payload = encoded.split(b"\n", 1)
    header = json.loads(encoded_header)
    if corruption == "schema":
        header["schema_version"] += 1
    elif corruption == "path":
        header["log_path"] = str(path.with_name("other.jsonl"))
    else:
        header["payload_sha256"] = "0" * 64
    wal_file.write_bytes(
        json.dumps(
            header,
            sort_keys=True,
            separators=(",", ":"),
        ).encode("ascii")
        + b"\n"
        + encoded_payload
    )

    with pytest.raises(evaluator.CandidateLogWriteError):
        evaluator.recover_candidate_log_wal(path)

    assert path.read_bytes() == b""
    assert wal_file.is_file()


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
    program = tmp_path / "program.py"
    program.write_text("def generate_candidates(ell, m): return []\n")
    monkeypatch.setenv(
        evaluator.CANDIDATE_LOG_PATH_ENV,
        str((tmp_path / "run" / "all_codes.jsonl").resolve()),
    )

    monkeypatch.setattr(
        evaluator,
        "_load_generate_candidates",
        lambda _path: lambda _ell, _m: [],
    )

    def fake_run(_generate, lattices, **kwargs):
        calls.append((tuple(lattices), dict(kwargs)))
        if kwargs["quick"]:
            metrics = _empty_stage2_lattice_metrics()
            metrics["lattices_requested"] = len(EVOLUTION_LATTICES)
            metrics["lattices_completed"] = len(EVOLUTION_LATTICES)
            return metrics
        return _empty_stage2_lattice_metrics()

    monkeypatch.setattr(evaluator, "_run_evaluation", fake_run)
    monkeypatch.setattr(evaluator, "_write_metrics_jsonl", lambda _rows: None)

    evaluated = evaluator._evaluate_stage2_impl(str(program))
    result = getattr(evaluated, "metrics", evaluated)
    artifacts = getattr(evaluated, "artifacts", {})

    assert calls[0][0] == EVOLUTION_LATTICES
    assert calls[0][1]["quick"] is True
    assert calls[0][1]["persist_quick_exploration"] is True
    assert calls[0][1]["persist_all_quick_exploration"] is True
    assert (
        calls[0][1]["candidate_limit"]
        == evaluator.STAGE2_PREFLIGHT_CANDIDATE_LIMIT
    )
    assert [call[0] for call in calls[1:]] == [
        (lattice,) for lattice in evaluator.STAGE2_DEEP_LATTICES
    ]
    assert all(call[1]["quick"] is False for call in calls[1:])
    assert all(
        call[1]["refine_trials"] == evaluator.STAGE2_REFINE_TRIALS
        for call in calls[1:]
    )
    assert all(
        call[1]["max_distance_per_lattice"]
        == evaluator.STAGE2_DEEP_DISTANCE_PER_LATTICE
        for call in calls[1:]
    )
    assert all(
        call[1]["candidate_limit"]
        == evaluator.STAGE2_DEEP_CANDIDATE_LIMIT
        for call in calls[1:]
    )
    assert result[evaluator.SUPPORT_FILTER_VERSION_METRIC] == float(
        evaluator.CHALLENGE_SUPPORT_FILTER_VERSION
    )
    assert result["target_preflight_support_feedback_observed"] == 1.0
    assert "Challenge support filter v1" in artifacts["support_filter"]
    assert "Deep challenge support:" in artifacts["summary"]


def test_stage1_progress_journal_validates_prefix_and_aggregates(
    tmp_path, monkeypatch
):
    lattices = [(6, 6), (6, 7)]
    monkeypatch.setattr(evaluator, "EVOLUTION_LATTICES", lattices)
    candidate_log = (tmp_path / "run" / "all_codes.jsonl").resolve()
    source_sha256 = "a" * 64
    contract_id = 314159
    summaries = [
        _stage1_summary(
            lattices[0],
            pool_sha256="b" * 64,
            unique=2,
            rejected=1,
        ),
        _stage1_summary(
            lattices[1],
            pool_sha256="c" * 64,
            unique=3,
            winner_eligible=2,
        ),
    ]
    journal = evaluator._initial_stage1_preflight_journal(
        source_sha256=source_sha256,
        contract_id=contract_id,
        candidate_log_path=candidate_log,
    )

    validated = evaluator._validated_stage1_preflight_journal(
        {
            **journal,
            "completed_lattices": summaries[:1],
            "progress_sequence": 1,
        },
        source_sha256=source_sha256,
        contract_id=contract_id,
        candidate_log_path=candidate_log,
    )

    assert validated["status"] == "in_progress"
    assert validated["completed_lattices"] == summaries[:1]
    assert validated["progress_sequence"] == 1
    with pytest.raises(
        evaluator.CandidateLogWriteError,
        match="before every lattice is durable",
    ):
        evaluator._aggregate_stage1_lattice_summaries(summaries[:1])

    aggregate = evaluator._aggregate_stage1_lattice_summaries(summaries)
    assert aggregate == {
        "unique_candidates": 5,
        "evaluated_candidate_definitions": 4,
        "winner_capable_quick_exploration_eligible": 3,
        "winner_capable_quick_exploration_persisted": 3,
        "winner_capable_quick_exploration_omitted": 0,
        evaluator.STAGE1_CANDIDATE_LOG_RECORDS_FIELD: 3,
        evaluator.SUPPORT_WEIGHT_ELIGIBLE_METRIC: 4,
        evaluator.SUPPORT_WEIGHT_REJECTED_METRIC: 1,
        evaluator.SUPPORT_WEIGHT_EVALUATED_METRIC: 4,
        evaluator.SUPPORT_FILTER_VERSION_METRIC: (
            evaluator.CHALLENGE_SUPPORT_FILTER_VERSION
        ),
        evaluator.SUPPORT_WEIGHT_PARTITION_COMPLETE_METRIC: 1,
        "lattices_completed": 2,
        "lattice_failures": 0,
    }

    malformed = dict(summaries[1])
    malformed["winner_capable_quick_exploration_persisted"] = 3
    with pytest.raises(
        evaluator.CandidateLogWriteError,
        match="does not prove complete persistence",
    ):
        evaluator._validated_stage1_lattice_summary(
            malformed,
            expected_lattice=lattices[1],
        )


def test_stage1_spool_commits_one_atomic_lattice_with_provenance(
    tmp_path, monkeypatch
):
    lattice = (6, 6)
    source_sha256 = "d" * 64
    contract_id = 271828
    epoch_id = "c" * 64
    candidate_log = (tmp_path / "run" / "all_codes.jsonl").resolve()
    candidate_log.parent.mkdir(parents=True)
    spool = tmp_path / "candidates.jsonl"
    first = _result(0, 0)
    second = {
        **_result(0, 0),
        "A_terms": [[0, 0], [0, 1], [2, 0]],
        "fom": 2.5,
    }
    spool.write_text(
        "".join(
            json.dumps(row, sort_keys=True) + "\n"
            for row in (first, second)
        )
    )
    summary = _stage1_summary(
        lattice,
        pool_sha256="e" * 64,
        unique=2,
        winner_eligible=1,
        candidate_log_records=2,
    )

    payload = evaluator._stage1_lattice_commit_payload(
        spool,
        source_sha256=source_sha256,
        contract_id=contract_id,
        epoch_id=epoch_id,
        lattice=lattice,
        summary=summary,
    )
    installed = []
    original_install = evaluator._install_candidate_log_wal

    def capture_install(log_file, *, start_offset, payload):
        installed.append((log_file, start_offset, bytes(payload)))
        return original_install(
            log_file,
            start_offset=start_offset,
            payload=payload,
        )

    monkeypatch.setattr(
        evaluator,
        "_install_candidate_log_wal",
        capture_install,
    )
    evaluator._append_candidate_jsonl(candidate_log, payload)

    assert installed == [(candidate_log, 0, payload)]
    committed = [
        json.loads(line)
        for line in candidate_log.read_text().splitlines()
    ]
    assert len(committed) == 2
    for row in committed:
        assert (
            row[evaluator.STAGE1_PREFLIGHT_ROW_PROGRAM_SHA256]
            == source_sha256
        )
        assert (
            row[evaluator.STAGE1_PREFLIGHT_ROW_CONTRACT_ID]
            == contract_id
        )
        assert (
            row[evaluator.STAGE1_PREFLIGHT_ROW_EPOCH_ID]
            == epoch_id
        )
        assert row[evaluator.STAGE1_PREFLIGHT_ROW_LATTICE] == [6, 6]
    assert evaluator.STAGE1_PREFLIGHT_ROW_LATTICE_COMMIT not in committed[0]
    assert (
        committed[-1][evaluator.STAGE1_PREFLIGHT_ROW_LATTICE_COMMIT]
        is True
    )
    assert (
        committed[-1][evaluator.STAGE1_PREFLIGHT_ROW_LATTICE_SUMMARY]
        == summary
    )
    wal_file, temporary = evaluator._candidate_log_wal_paths(candidate_log)
    assert not wal_file.exists()
    assert not temporary.exists()


@pytest.mark.parametrize("spool_state", ("missing", "empty"))
def test_stage1_nonzero_persistence_rejects_missing_or_empty_spool(
    tmp_path, spool_state
):
    lattice = (6, 6)
    spool = tmp_path / "candidates.jsonl"
    if spool_state == "empty":
        spool.write_bytes(b"")
    summary = _stage1_summary(
        lattice,
        pool_sha256="f" * 64,
    )

    with pytest.raises(evaluator.CandidateLogWriteError):
        evaluator._stage1_lattice_commit_payload(
            spool,
            source_sha256="0" * 64,
            contract_id=223607,
            epoch_id="9" * 64,
            lattice=lattice,
            summary=summary,
        )


def test_stage1_recovers_commit_row_when_append_precedes_journal(
    tmp_path, monkeypatch
):
    lattice = (6, 6)
    monkeypatch.setattr(evaluator, "EVOLUTION_LATTICES", [lattice])
    source_sha256 = "1" * 64
    contract_id = 161803
    candidate_log = (tmp_path / "run" / "all_codes.jsonl").resolve()
    candidate_log.parent.mkdir(parents=True)
    spool = tmp_path / "candidates.jsonl"
    spool.write_text(json.dumps(_result(0, 0), sort_keys=True) + "\n")
    summary = _stage1_summary(
        lattice,
        pool_sha256="2" * 64,
    )
    journal = evaluator._initial_stage1_preflight_journal(
        source_sha256=source_sha256,
        contract_id=contract_id,
        candidate_log_path=candidate_log,
    )
    journal_path, _lock_path = evaluator._stage1_preflight_journal_paths(
        candidate_log,
        source_sha256=source_sha256,
        contract_id=contract_id,
    )
    payload = evaluator._stage1_lattice_commit_payload(
        spool,
        source_sha256=source_sha256,
        contract_id=contract_id,
        epoch_id=journal["epoch_id"],
        lattice=lattice,
        summary=summary,
    )
    evaluator._append_candidate_jsonl(candidate_log, payload)
    original_log = candidate_log.read_bytes()

    assert not journal_path.exists()

    def must_not_rerun(*_args, **_kwargs):
        raise AssertionError("durable lattice commit was rerun")

    monkeypatch.setattr(evaluator, "_run_evaluation", must_not_rerun)
    recovered = evaluator._recover_stage1_lattice_commits(
        candidate_log,
        journal,
    )
    recovered_again = evaluator._recover_stage1_lattice_commits(
        candidate_log,
        recovered,
    )

    assert recovered["completed_lattices"] == [summary]
    assert recovered["progress_sequence"] == 1
    assert recovered_again == recovered
    assert candidate_log.read_bytes() == original_log


@pytest.mark.parametrize("surviving_row", ("first", "last"))
def test_stage1_rejects_partial_unjournaled_lattice_commit(
    tmp_path, monkeypatch, surviving_row
):
    lattice = (6, 6)
    monkeypatch.setattr(evaluator, "EVOLUTION_LATTICES", [lattice])
    source_sha256 = "6" * 64
    contract_id = 223606
    candidate_log = (tmp_path / "run" / "all_codes.jsonl").resolve()
    candidate_log.parent.mkdir(parents=True)
    spool = tmp_path / "candidates.jsonl"
    spool.write_text(
        json.dumps(_result(0, 0), sort_keys=True)
        + "\n"
        + json.dumps(_result(0, 1), sort_keys=True)
        + "\n"
    )
    summary = _stage1_summary(
        lattice,
        pool_sha256="4" * 64,
        unique=2,
    )
    journal = evaluator._initial_stage1_preflight_journal(
        source_sha256=source_sha256,
        contract_id=contract_id,
        candidate_log_path=candidate_log,
    )
    payload = evaluator._stage1_lattice_commit_payload(
        spool,
        source_sha256=source_sha256,
        contract_id=contract_id,
        epoch_id=journal["epoch_id"],
        lattice=lattice,
        summary=summary,
    )
    rows = payload.splitlines(keepends=True)
    candidate_log.write_bytes(rows[0 if surviving_row == "first" else -1])

    with pytest.raises(evaluator.Stage1CandidateCommitMismatch):
        evaluator._recover_stage1_lattice_commits(
            candidate_log,
            journal,
        )


def test_stage1_recovery_scan_holds_candidate_lock_against_append(
    tmp_path, monkeypatch
):
    candidate_log = (tmp_path / "run" / "all_codes.jsonl").resolve()
    candidate_log.parent.mkdir(parents=True)
    candidate_log.write_text('{"unrelated":1}\n')
    journal = evaluator._initial_stage1_preflight_journal(
        source_sha256="5" * 64,
        contract_id=141421,
        candidate_log_path=candidate_log,
    )
    scan_entered = threading.Event()
    release_scan = threading.Event()
    writer_done = threading.Event()
    outcomes = []
    original_loads = evaluator.json.loads

    def gated_loads(value, *args, **kwargs):
        if isinstance(value, bytes) and b'"unrelated"' in value:
            scan_entered.set()
            if not release_scan.wait(timeout=5):
                raise AssertionError("test did not release recovery scan")
        return original_loads(value, *args, **kwargs)

    monkeypatch.setattr(evaluator.json, "loads", gated_loads)

    def recover():
        try:
            outcomes.append(
                evaluator._recover_stage1_lattice_commits(
                    candidate_log,
                    journal,
                )
            )
        except BaseException as exc:
            outcomes.append(exc)

    def append():
        try:
            evaluator._append_candidate_jsonl(
                candidate_log,
                b'{"writer":2}\n',
            )
        finally:
            writer_done.set()

    recovery_thread = threading.Thread(target=recover)
    recovery_thread.start()
    assert scan_entered.wait(timeout=5)
    writer_thread = threading.Thread(target=append)
    writer_thread.start()
    time.sleep(0.05)
    assert not writer_done.is_set()

    release_scan.set()
    recovery_thread.join(timeout=5)
    writer_thread.join(timeout=5)

    assert outcomes == [journal]
    assert writer_done.is_set()
    assert candidate_log.read_text().splitlines() == [
        '{"unrelated":1}',
        '{"writer":2}',
    ]


@pytest.mark.parametrize("damage", ("deleted_log", "missing_commit"))
def test_completed_stage1_journal_requires_candidate_commit_proof(
    tmp_path, monkeypatch, damage
):
    lattice = (6, 6)
    monkeypatch.setattr(evaluator, "EVOLUTION_LATTICES", [lattice])
    source_sha256 = "7" * 64
    contract_id = 244949
    candidate_log = (tmp_path / "run" / "all_codes.jsonl").resolve()
    candidate_log.parent.mkdir(parents=True)
    spool = tmp_path / "candidates.jsonl"
    spool.write_text(json.dumps(_result(0, 0), sort_keys=True) + "\n")
    summary = _stage1_summary(
        lattice,
        pool_sha256="8" * 64,
    )
    initial = evaluator._initial_stage1_preflight_journal(
        source_sha256=source_sha256,
        contract_id=contract_id,
        candidate_log_path=candidate_log,
    )
    aggregate = evaluator._aggregate_stage1_lattice_summaries([summary])
    journal = evaluator._validated_stage1_preflight_journal(
        {
            **initial,
            "status": "completed",
            "completed_lattices": [summary],
            "progress_sequence": 2,
            "markers": evaluator._winner_preflight_markers(
                aggregate,
                contract_id=contract_id,
            ),
        },
        source_sha256=source_sha256,
        contract_id=contract_id,
        candidate_log_path=candidate_log,
    )
    payload = evaluator._stage1_lattice_commit_payload(
        spool,
        source_sha256=source_sha256,
        contract_id=contract_id,
        epoch_id=journal["epoch_id"],
        lattice=lattice,
        summary=summary,
    )
    evaluator._append_candidate_jsonl(candidate_log, payload)

    if damage == "deleted_log":
        candidate_log.unlink()
    else:
        row = json.loads(candidate_log.read_text())
        row.pop(evaluator.STAGE1_PREFLIGHT_ROW_LATTICE_COMMIT)
        row.pop(evaluator.STAGE1_PREFLIGHT_ROW_LATTICE_SUMMARY)
        candidate_log.write_text(json.dumps(row, sort_keys=True) + "\n")

    with pytest.raises(evaluator.CandidateLogWriteError):
        evaluator._recover_stage1_lattice_commits(
            candidate_log,
            journal,
        )


def test_stage1_rotates_epoch_and_recomputes_after_candidate_tail_rollback(
    tmp_path, monkeypatch
):
    lattice = (6, 6)
    monkeypatch.setattr(evaluator, "EVOLUTION_LATTICES", [lattice])
    program = tmp_path / "program.py"
    program.write_text("def generate_candidates(ell, m): return []\n")
    source_sha256 = evaluator._freeze_program_source_sha256(str(program))
    contract_id = 264575
    candidate_log = (tmp_path / "run" / "all_codes.jsonl").resolve()
    candidate_log.parent.mkdir(parents=True)
    monkeypatch.setenv(
        evaluator.CANDIDATE_LOG_PATH_ENV,
        str(candidate_log),
    )
    monkeypatch.setenv(
        evaluator.WINNER_PREFLIGHT_CONTRACT_ID_ENV,
        str(contract_id),
    )
    pool_sha256 = evaluator._generated_pool_sha256(
        [],
        lattice=lattice,
    )
    summary = _stage1_summary(
        lattice,
        pool_sha256=pool_sha256,
    )
    stale_journal = evaluator._initial_stage1_preflight_journal(
        source_sha256=source_sha256,
        contract_id=contract_id,
        candidate_log_path=candidate_log,
    )
    journal_path, _lock_path = evaluator._stage1_preflight_journal_paths(
        candidate_log,
        source_sha256=source_sha256,
        contract_id=contract_id,
    )
    evaluator._write_stage1_preflight_journal(
        journal_path,
        {
            **stale_journal,
            "status": "completed",
            "completed_lattices": [summary],
            "progress_sequence": 2,
            "markers": evaluator._winner_preflight_markers(
                evaluator._aggregate_stage1_lattice_summaries([summary]),
                contract_id=contract_id,
            ),
        },
        source_sha256=source_sha256,
        contract_id=contract_id,
        candidate_log_path=candidate_log,
    )

    spool = tmp_path / "stale-spool.jsonl"
    spool.write_text(json.dumps(_result(0, 0), sort_keys=True) + "\n")
    evaluator._append_candidate_jsonl(
        candidate_log,
        evaluator._stage1_lattice_commit_payload(
            spool,
            source_sha256=source_sha256,
            contract_id=contract_id,
            epoch_id=stale_journal["epoch_id"],
            lattice=lattice,
            summary=summary,
        ),
    )
    candidate_log.unlink()

    monkeypatch.setattr(
        evaluator,
        "_load_generate_candidates",
        lambda _path: lambda _ell, _m: [],
    )
    fresh_metrics = {
        key: value
        for key, value in summary.items()
        if key not in {"lattice", "pool_sha256"}
    }

    def fake_run(_generate, lattices, *, candidate_log_path, **_kwargs):
        assert lattices == [lattice]
        candidate_log_path.write_text(
            json.dumps(_result(0, 0), sort_keys=True) + "\n"
        )
        return dict(fresh_metrics)

    monkeypatch.setattr(evaluator, "_run_evaluation", fake_run)

    markers, _generate, returned_log, returned_sha = (
        evaluator._run_resumable_winner_preflight(str(program))
    )
    recovered_journal = evaluator._load_stage1_preflight_journal(
        journal_path,
        source_sha256=source_sha256,
        contract_id=contract_id,
        candidate_log_path=candidate_log,
    )

    assert returned_log == candidate_log
    assert returned_sha == source_sha256
    assert markers[evaluator.WINNER_PREFLIGHT_COMPLETE_METRIC] == 1.0
    assert recovered_journal["status"] == "completed"
    assert recovered_journal["restart_count"] == 1
    assert recovered_journal["epoch_id"] != stale_journal["epoch_id"]
    committed = json.loads(candidate_log.read_text())
    assert (
        committed[evaluator.STAGE1_PREFLIGHT_ROW_EPOCH_ID]
        == recovered_journal["epoch_id"]
    )


@pytest.mark.parametrize(
    "tamper",
    ("program", "contract", "sink", "lattices", "markers"),
)
def test_completed_stage1_journal_reloads_and_binding_tamper_fails_closed(
    tmp_path, monkeypatch, tamper
):
    lattices = [(6, 6), (6, 7)]
    monkeypatch.setattr(evaluator, "EVOLUTION_LATTICES", lattices)
    source_sha256 = "3" * 64
    contract_id = 141421
    candidate_log = (tmp_path / "run" / "all_codes.jsonl").resolve()
    summaries = [
        _stage1_summary(lattices[0], pool_sha256="4" * 64),
        _stage1_summary(lattices[1], pool_sha256="5" * 64),
    ]
    aggregate = evaluator._aggregate_stage1_lattice_summaries(summaries)
    markers = evaluator._winner_preflight_markers(
        aggregate,
        contract_id=contract_id,
    )
    initial = evaluator._initial_stage1_preflight_journal(
        source_sha256=source_sha256,
        contract_id=contract_id,
        candidate_log_path=candidate_log,
    )
    journal_path, _lock_path = evaluator._stage1_preflight_journal_paths(
        candidate_log,
        source_sha256=source_sha256,
        contract_id=contract_id,
    )
    stored = evaluator._write_stage1_preflight_journal(
        journal_path,
        {
            **initial,
            "status": "completed",
            "completed_lattices": summaries,
            "progress_sequence": 2,
            "markers": markers,
        },
        source_sha256=source_sha256,
        contract_id=contract_id,
        candidate_log_path=candidate_log,
    )

    assert evaluator._load_stage1_preflight_journal(
        journal_path,
        source_sha256=source_sha256,
        contract_id=contract_id,
        candidate_log_path=candidate_log,
    ) == stored

    forged = json.loads(journal_path.read_text())
    if tamper == "program":
        forged["program_sha256"] = "6" * 64
    elif tamper == "contract":
        forged["contract_id"] += 1
    elif tamper == "sink":
        forged["candidate_log_path"] = str(
            candidate_log.with_name("redirected.jsonl")
        )
    elif tamper == "lattices":
        forged["lattices"] = list(reversed(forged["lattices"]))
    else:
        forged["markers"][
            evaluator.WINNER_PREFLIGHT_PERSISTED_METRIC
        ] += 1
    journal_path.write_text(json.dumps(forged))

    with pytest.raises(
        evaluator.CandidateLogWriteError,
        match="journal binding|markers",
    ):
        evaluator._load_stage1_preflight_journal(
            journal_path,
            source_sha256=source_sha256,
            contract_id=contract_id,
            candidate_log_path=candidate_log,
        )


def test_stage1_progress_resets_inactivity_deadline(
    tmp_path, monkeypatch
):
    program = tmp_path / "program.py"
    program.write_text("def generate_candidates(ell, m): return []\n")
    candidate_log = (tmp_path / "run" / "all_codes.jsonl").resolve()
    contract_id = 173205
    journal_snapshots = iter([
        {
            "status": "in_progress",
            "completed_lattices": [],
            "progress_sequence": 5,
            "epoch_id": "a" * 64,
            "restart_count": 0,
        },
        {
            "status": "in_progress",
            "completed_lattices": [],
            "progress_sequence": 5,
            "epoch_id": "a" * 64,
            "restart_count": 0,
        },
        {
            "status": "in_progress",
            "completed_lattices": [],
            "progress_sequence": 0,
            "epoch_id": "b" * 64,
            "restart_count": 1,
        },
    ])
    journal_loads = []
    registered = []
    terminated = []
    processes = []

    def load_journal(*_args, **_kwargs):
        journal_loads.append(True)
        return next(journal_snapshots)

    class FakeClock:
        def __init__(self):
            self.ticks = iter((0.0, 9.0, 9.0, 18.0))

        def monotonic(self):
            return next(self.ticks)

        def time_ns(self):
            return 1

    class ProgressProcess:
        pid = 43210

        def __init__(self, command, **_kwargs):
            self.result_path = Path(command[4])
            self.wait_timeouts = []
            processes.append(self)

        def wait(self, timeout=None):
            self.wait_timeouts.append(timeout)
            if len(self.wait_timeouts) == 1:
                raise evaluator.subprocess.TimeoutExpired(
                    "stage1",
                    timeout,
                )
            self.result_path.write_text(json.dumps({
                "schema_version": 1,
                "status": "completed",
                "metrics": {"combined_score": 7.0},
            }))
            return 0

        def poll(self):
            return None

    monkeypatch.setattr(
        evaluator,
        "_current_winner_preflight_contract_id",
        lambda: contract_id,
    )
    monkeypatch.setattr(
        evaluator,
        "_freeze_candidate_log_path",
        lambda *_args, **_kwargs: candidate_log,
    )
    monkeypatch.setattr(
        evaluator,
        "_load_stage1_preflight_journal",
        load_journal,
    )
    monkeypatch.setattr(
        evaluator,
        "_path_entry_exists",
        lambda _path: True,
    )
    monkeypatch.setattr(
        evaluator,
        "_winner_preflight_hard_timeout_s",
        lambda: 10.0,
    )
    monkeypatch.setattr(evaluator, "time", FakeClock())
    monkeypatch.setattr(evaluator.subprocess, "Popen", ProgressProcess)
    monkeypatch.setattr(
        evaluator,
        "_terminate_stage2_process_group",
        lambda process: terminated.append(process.pid),
    )
    monkeypatch.setattr(
        evaluator,
        "_register_stage1_preflight_completion",
        lambda path, metrics: registered.append((path, metrics)),
    )

    result = evaluator.evaluate_stage1(str(program))

    assert result == {"combined_score": 7.0}
    assert len(journal_loads) == 3
    assert processes[0].wait_timeouts == [0.25, 0.25]
    assert registered == [
        (str(program), {"combined_score": 7.0})
    ]
    assert terminated == []


def test_stage1_source_lock_wait_has_a_hard_bound(tmp_path):
    candidate_log = (tmp_path / "run" / "all_codes.jsonl").resolve()
    source_sha256 = "3" * 64
    contract_id = 271828
    journal_path, lock_path = evaluator._stage1_preflight_journal_paths(
        candidate_log,
        source_sha256=source_sha256,
        contract_id=contract_id,
    )
    owner = evaluator._open_stage1_preflight_lock(
        lock_path,
        journal_path=journal_path,
        source_sha256=source_sha256,
        contract_id=contract_id,
        candidate_log_path=candidate_log,
        inactivity_timeout=0.05,
    )
    started = time.monotonic()
    try:
        with pytest.raises(evaluator.Stage1PreflightLockTimeout):
            evaluator._open_stage1_preflight_lock(
                lock_path,
                journal_path=journal_path,
                source_sha256=source_sha256,
                contract_id=contract_id,
                candidate_log_path=candidate_log,
                inactivity_timeout=0.05,
            )
    finally:
        evaluator.fcntl.flock(owner, evaluator.fcntl.LOCK_UN)
        evaluator.os.close(owner)

    assert time.monotonic() - started < 0.5


def test_cascade_stage2_reuses_complete_stage1_preflight_without_rewriting(
    tmp_path, monkeypatch
):
    contract_id = 13579
    program = tmp_path / "program.py"
    program.write_text("def generate_candidates(ell, m): return []\n")
    markers = _complete_preflight_metrics(
        contract_id,
        evaluated=17,
        eligible=5,
    )
    monkeypatch.setenv(
        evaluator.WINNER_PREFLIGHT_CONTRACT_ID_ENV,
        str(contract_id),
    )
    monkeypatch.setenv(
        evaluator.WINNER_PREFLIGHT_REUSE_ENV,
        json.dumps({
            "schema_version": 1,
            "program_sha256": evaluator._program_source_sha256(str(program)),
            "contract_id": contract_id,
            "markers": markers,
        }),
    )
    monkeypatch.setenv(
        evaluator.CANDIDATE_LOG_PATH_ENV,
        str((tmp_path / "run" / "all_codes.jsonl").resolve()),
    )
    calls = []
    monkeypatch.setattr(
        evaluator,
        "_load_generate_candidates",
        lambda _path: lambda _ell, _m: [],
    )

    def fake_run(_generate, lattices, **kwargs):
        calls.append((tuple(lattices), dict(kwargs)))
        return _empty_stage2_lattice_metrics()

    monkeypatch.setattr(evaluator, "_run_evaluation", fake_run)
    monkeypatch.setattr(evaluator, "_write_metrics_jsonl", lambda _rows: None)

    result = evaluator._evaluate_stage2_impl(str(program))
    metrics = getattr(result, "metrics", result)
    artifacts = getattr(result, "artifacts", {})

    assert [lattices for lattices, _kwargs in calls] == [
        (lattice,) for lattice in evaluator.STAGE2_DEEP_LATTICES
    ]
    assert metrics["target_preflight_candidates_evaluated"] == 17.0
    assert metrics["target_preflight_winner_capable_persisted"] == 5.0
    assert metrics["target_preflight_support_feedback_observed"] == 0.0
    assert "per-split diagnostics unavailable" in artifacts["summary"]


def test_stage2_deep_resume_replays_generator_without_redoing_committed_bp(
    tmp_path, monkeypatch
):
    lattices = [(6, 6), (7, 6), (8, 6)]
    monkeypatch.setattr(evaluator, "STAGE2_DEEP_LATTICES", lattices)
    program = tmp_path / "program.py"
    program.write_text("def generate_candidates(ell, m): return []\n")
    candidate_log = (tmp_path / "run" / "all_codes.jsonl").resolve()
    source_sha256 = evaluator._freeze_program_source_sha256(str(program))
    contract_id = 112233
    preflight_sha256 = "a" * 64
    generated_calls = []
    evaluation_calls = []
    fail_second = True

    def generate(ell, m):
        generated_calls.append((ell, m))
        return []

    def fake_run(_generate, requested, **_kwargs):
        nonlocal fail_second
        lattice = tuple(requested[0])
        evaluation_calls.append(lattice)
        if lattice == lattices[1] and fail_second:
            fail_second = False
            raise RuntimeError("simulated BP worker loss")
        return _empty_stage2_lattice_metrics()

    monkeypatch.setattr(evaluator, "_run_evaluation", fake_run)

    with pytest.raises(RuntimeError, match="simulated BP worker loss"):
        evaluator._run_resumable_stage2_deep(
            str(program),
            generate_fn=generate,
            candidate_log_path=candidate_log,
            source_sha256=source_sha256,
            contract_id=contract_id,
            preflight_sha256=preflight_sha256,
        )

    generated_calls.clear()
    result = evaluator._run_resumable_stage2_deep(
        str(program),
        generate_fn=generate,
        candidate_log_path=candidate_log,
        source_sha256=source_sha256,
        contract_id=contract_id,
        preflight_sha256=preflight_sha256,
    )

    assert generated_calls == lattices
    assert evaluation_calls == [
        lattices[0],
        lattices[1],
        lattices[1],
        lattices[2],
    ]
    assert result["lattices_completed"] == len(lattices)
    journal_path, _lock_path = evaluator._stage2_deep_journal_paths(
        candidate_log,
        source_sha256=source_sha256,
        contract_id=contract_id,
        preflight_sha256=preflight_sha256,
    )
    journal = json.loads(journal_path.read_text())
    assert journal["status"] == "completed"
    assert len(journal["completed_lattices"]) == len(lattices)


def test_stage2_adopts_atomic_sidecar_after_crash_before_journal_commit(
    tmp_path, monkeypatch
):
    lattice = (6, 6)
    monkeypatch.setattr(
        evaluator, "STAGE2_DEEP_LATTICES", [lattice]
    )
    program = tmp_path / "program.py"
    program.write_text("def generate_candidates(ell, m): return []\n")
    candidate_log = (tmp_path / "run" / "all_codes.jsonl").resolve()
    source_sha256 = evaluator._freeze_program_source_sha256(str(program))
    contract_id = 445566
    preflight_sha256 = "b" * 64
    evaluations = 0

    def fake_run(_generate, _requested, **_kwargs):
        nonlocal evaluations
        evaluations += 1
        return _empty_stage2_lattice_metrics()

    monkeypatch.setattr(evaluator, "_run_evaluation", fake_run)
    original_write = evaluator._write_stage2_deep_journal
    crash_once = True

    def crash_after_sidecar(path, payload, **kwargs):
        nonlocal crash_once
        if payload.get("completed_lattices") and crash_once:
            crash_once = False
            raise OSError("simulated journal commit crash")
        return original_write(path, payload, **kwargs)

    monkeypatch.setattr(
        evaluator, "_write_stage2_deep_journal", crash_after_sidecar
    )
    with pytest.raises(OSError, match="journal commit crash"):
        evaluator._run_resumable_stage2_deep(
            str(program),
            generate_fn=lambda _ell, _m: [],
            candidate_log_path=candidate_log,
            source_sha256=source_sha256,
            contract_id=contract_id,
            preflight_sha256=preflight_sha256,
        )

    monkeypatch.setattr(
        evaluator, "_write_stage2_deep_journal", original_write
    )
    result = evaluator._run_resumable_stage2_deep(
        str(program),
        generate_fn=lambda _ell, _m: [],
        candidate_log_path=candidate_log,
        source_sha256=source_sha256,
        contract_id=contract_id,
        preflight_sha256=preflight_sha256,
    )

    assert evaluations == 1
    assert result["lattices_completed"] == 1


def test_stage2_rejects_tampered_committed_sidecar(
    tmp_path, monkeypatch
):
    lattice = (6, 6)
    monkeypatch.setattr(
        evaluator, "STAGE2_DEEP_LATTICES", [lattice]
    )
    program = tmp_path / "program.py"
    program.write_text("def generate_candidates(ell, m): return []\n")
    candidate_log = (tmp_path / "run" / "all_codes.jsonl").resolve()
    source_sha256 = evaluator._freeze_program_source_sha256(str(program))
    contract_id = 778899
    preflight_sha256 = "c" * 64
    monkeypatch.setattr(
        evaluator,
        "_run_evaluation",
        lambda *_args, **_kwargs: _empty_stage2_lattice_metrics(),
    )
    evaluator._run_resumable_stage2_deep(
        str(program),
        generate_fn=lambda _ell, _m: [],
        candidate_log_path=candidate_log,
        source_sha256=source_sha256,
        contract_id=contract_id,
        preflight_sha256=preflight_sha256,
    )
    journal_path, _lock_path = evaluator._stage2_deep_journal_paths(
        candidate_log,
        source_sha256=source_sha256,
        contract_id=contract_id,
        preflight_sha256=preflight_sha256,
    )
    journal = json.loads(journal_path.read_text())
    sidecar = evaluator._stage2_lattice_result_path(
        journal_path,
        epoch_id=journal["epoch_id"],
        index=0,
    )
    sidecar.write_bytes(sidecar.read_bytes() + b" ")

    with pytest.raises(
        evaluator.CandidateLogWriteError,
        match="no longer matches its journal",
    ):
        evaluator._run_resumable_stage2_deep(
            str(program),
            generate_fn=lambda _ell, _m: [],
            candidate_log_path=candidate_log,
            source_sha256=source_sha256,
            contract_id=contract_id,
            preflight_sha256=preflight_sha256,
        )


def test_stage2_lattice_aggregation_matches_monolithic_empty_run(
    tmp_path, monkeypatch
):
    lattices = [(6, 6), (7, 6), (8, 6)]
    monkeypatch.setattr(evaluator, "STAGE2_DEEP_LATTICES", lattices)
    monolithic = evaluator._run_evaluation(
        lambda _ell, _m: [],
        lattices,
        quick=False,
        candidate_log_path=tmp_path / "monolithic.jsonl",
    )
    per_lattice = [
        evaluator._run_evaluation(
            lambda _ell, _m: [],
            [lattice],
            quick=False,
            candidate_log_path=tmp_path / f"{index}.jsonl",
        )
        for index, lattice in enumerate(lattices)
    ]

    assert evaluator._aggregate_stage2_lattice_metrics(
        per_lattice
    ) == monolithic


def test_stage2_killable_wrapper_round_trips_worker_result(
    tmp_path, monkeypatch
):
    observed = {}
    contract_id = 2468
    program = tmp_path / "generated program.py"
    program.write_text("def generate_candidates(ell, m): return []\n")
    monkeypatch.setenv(
        evaluator.WINNER_PREFLIGHT_CONTRACT_ID_ENV,
        str(contract_id),
    )
    monkeypatch.setenv(
        evaluator.CANDIDATE_LOG_PATH_ENV,
        str((tmp_path / "run" / "all_codes.jsonl").resolve()),
    )

    class FakeProcess:
        pid = 4321

        def __init__(self, command, **kwargs):
            observed["command"] = command
            observed["kwargs"] = kwargs
            Path(command[4]).write_text(json.dumps({
                "schema_version": 1,
                "status": "completed",
                "metrics": {
                    "combined_score": 7.5,
                    evaluator.STAGE2_CONTRACT_VERSION_METRIC: float(
                        evaluator.STAGE2_DEEP_CONTRACT_VERSION
                    ),
                    evaluator.STAGE2_CONTRACT_ID_METRIC: float(
                        contract_id
                    ),
                    evaluator.STAGE2_COMPLETE_METRIC: 1.0,
                    evaluator.STAGE2_INCOMPLETE_METRIC: 0.0,
                    evaluator.STAGE2_LATTICES_METRIC: float(
                        len(evaluator.STAGE2_DEEP_LATTICES)
                    ),
                    evaluator.STAGE2_HARD_TIMEOUT_METRIC: 0.0,
                    evaluator.STAGE2_SUBPROCESS_FAILED_METRIC: 0.0,
                },
                "artifacts": {"summary": "bounded"},
            }))

        def wait(self, timeout=None):
            observed.setdefault("timeouts", []).append(timeout)
            return 0

    monkeypatch.setattr(evaluator.subprocess, "Popen", FakeProcess)

    result = evaluator.evaluate_stage2(str(program))
    metrics = getattr(result, "metrics", result)
    artifacts = getattr(result, "artifacts", {})

    assert metrics["combined_score"] == 7.5
    assert artifacts["summary"] == "bounded"
    assert observed["command"][1] == str(Path(evaluator.__file__).resolve())
    assert observed["command"][2] == "--stage2-worker"
    assert observed["command"][3] == str(program)
    assert observed["kwargs"]["start_new_session"] is True
    assert all(
        observed["kwargs"]["env"][variable] == "1"
        for variable in evaluator.STAGE2_NUMERIC_THREAD_ENV
    )
    assert len(observed["timeouts"]) == 1
    assert 0 < observed["timeouts"][0] <= 0.25


def test_stage2_worker_wall_renews_after_durable_lattice_progress(
    tmp_path, monkeypatch
):
    lattices = [(6, 6), (7, 6)]
    monkeypatch.setattr(evaluator, "STAGE2_DEEP_LATTICES", lattices)
    contract_id = 86420
    program = tmp_path / "program.py"
    program.write_text("def generate_candidates(ell, m): return []\n")
    candidate_log = (tmp_path / "run" / "all_codes.jsonl").resolve()
    source_sha256 = evaluator._freeze_program_source_sha256(str(program))
    preflight_sha256 = evaluator._stage2_preflight_sha256(
        None,
        contract_id=contract_id,
    )
    journal_path, _lock_path = evaluator._stage2_deep_journal_paths(
        candidate_log,
        source_sha256=source_sha256,
        contract_id=contract_id,
        preflight_sha256=preflight_sha256,
    )
    journal = evaluator._write_stage2_deep_journal(
        journal_path,
        evaluator._initial_stage2_deep_journal(
            source_sha256=source_sha256,
            contract_id=contract_id,
            candidate_log_path=candidate_log,
            preflight_sha256=preflight_sha256,
        ),
        source_sha256=source_sha256,
        contract_id=contract_id,
        candidate_log_path=candidate_log,
        preflight_sha256=preflight_sha256,
    )
    clock = {"now": 0.0}
    monkeypatch.setattr(
        evaluator.time, "monotonic", lambda: clock["now"]
    )

    class ProgressProcess:
        pid = 6420

        def __init__(self, command, **_kwargs):
            self.command = command
            self.calls = 0

        def wait(self, timeout=None):
            self.calls += 1
            clock["now"] += 0.6
            if self.calls <= len(lattices):
                entry = {
                    "lattice": list(lattices[self.calls - 1]),
                    "pool_sha256": f"{self.calls}" * 64,
                    "result_sha256": f"{self.calls + 2}" * 64,
                    "result_bytes": 1,
                }
                current = evaluator._load_stage2_deep_journal(
                    journal_path,
                    source_sha256=source_sha256,
                    contract_id=contract_id,
                    candidate_log_path=candidate_log,
                    preflight_sha256=preflight_sha256,
                )
                completed = [
                    *current["completed_lattices"],
                    entry,
                ]
                evaluator._write_stage2_deep_journal(
                    journal_path,
                    {
                        **current,
                        "status": (
                            "completed"
                            if len(completed) == len(lattices)
                            else "in_progress"
                        ),
                        "completed_lattices": completed,
                        "progress_sequence": (
                            current["progress_sequence"] + 1
                        ),
                    },
                    source_sha256=source_sha256,
                    contract_id=contract_id,
                    candidate_log_path=candidate_log,
                    preflight_sha256=preflight_sha256,
                )
                raise evaluator.subprocess.TimeoutExpired(
                    "stage2", timeout
                )
            Path(self.command[4]).write_text(json.dumps({
                "schema_version": 1,
                "status": "completed",
                "metrics": {
                    "combined_score": 3.0,
                    evaluator.STAGE2_CONTRACT_VERSION_METRIC: float(
                        evaluator.STAGE2_DEEP_CONTRACT_VERSION
                    ),
                    evaluator.STAGE2_CONTRACT_ID_METRIC: float(
                        contract_id
                    ),
                    evaluator.STAGE2_COMPLETE_METRIC: 1.0,
                    evaluator.STAGE2_INCOMPLETE_METRIC: 0.0,
                    evaluator.STAGE2_LATTICES_METRIC: float(
                        len(lattices)
                    ),
                    evaluator.STAGE2_HARD_TIMEOUT_METRIC: 0.0,
                    evaluator.STAGE2_SUBPROCESS_FAILED_METRIC: 0.0,
                },
                "artifacts": {},
            }))
            return 0

        def poll(self):
            return None

    monkeypatch.setattr(evaluator.subprocess, "Popen", ProgressProcess)
    payload, failure, timed_out = evaluator._run_stage2_worker_attempt(
        str(program),
        preflight_reuse=None,
        source_sha256=source_sha256,
        contract_id=contract_id,
        candidate_log_path=candidate_log,
        preflight_sha256=preflight_sha256,
        journal_path=journal_path,
        inactivity_timeout=1.0,
    )

    assert failure is None
    assert timed_out is False
    assert payload["metrics"]["combined_score"] == 3.0
    assert clock["now"] == pytest.approx(1.8)


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


def test_stage2_killable_wrapper_terminates_group_on_timeout(
    tmp_path, monkeypatch
):
    kills = []
    processes = {}
    program = tmp_path / "slow-program.py"
    program.write_text("def generate_candidates(ell, m): return []\n")
    monkeypatch.setenv(
        evaluator.WINNER_PREFLIGHT_CONTRACT_ID_ENV,
        "97531",
    )
    monkeypatch.setenv(
        evaluator.CANDIDATE_LOG_PATH_ENV,
        str((tmp_path / "run" / "all_codes.jsonl").resolve()),
    )
    monkeypatch.setattr(evaluator, "_stage2_hard_timeout_s", lambda: 0.01)

    class TimedOutProcess:
        next_pid = 8765

        def __init__(self, _command, **_kwargs):
            self.pid = self.next_pid
            type(self).next_pid += 1
            self.terminated = False
            processes[self.pid] = self

        def wait(self, timeout=None):
            if self.terminated:
                return -evaluator.signal.SIGTERM
            raise evaluator.subprocess.TimeoutExpired("stage2", timeout)

        def poll(self):
            return None if not self.terminated else -evaluator.signal.SIGTERM

    monkeypatch.setattr(
        evaluator.subprocess, "Popen", TimedOutProcess
    )
    monkeypatch.setattr(
        evaluator.os,
        "killpg",
        lambda pid, sig: (
            kills.append((pid, sig)),
            setattr(processes[pid], "terminated", True),
        ),
    )

    result = evaluator.evaluate_stage2(str(program))
    metrics = getattr(result, "metrics", result)

    assert metrics[evaluator.STAGE2_HARD_TIMEOUT_METRIC] == 1.0
    assert metrics[evaluator.STAGE2_SUBPROCESS_FAILED_METRIC] == 1.0
    assert metrics[evaluator.STAGE2_COMPLETE_METRIC] == 0.0
    assert metrics[evaluator.STAGE2_INCOMPLETE_METRIC] == 1.0
    assert "combined_score" not in metrics
    assert evaluator.MAP_DESCRIPTOR_VERSION_METRIC not in metrics
    assert kills == [
        (8765, evaluator.signal.SIGTERM),
        (8765, evaluator.signal.SIGKILL),
        (8766, evaluator.signal.SIGTERM),
        (8766, evaluator.signal.SIGKILL),
    ]


def test_stage1_preflight_timeout_is_explicitly_incomplete(
    tmp_path, monkeypatch
):
    kills = []
    program = tmp_path / "slow-program.py"
    program.write_text("def generate_candidates(ell, m): return []\n")
    candidate_log = (tmp_path / "run" / "all_codes.jsonl").resolve()

    class TimedOutProcess:
        pid = 7654

        def __init__(self, _command, **_kwargs):
            self.wait_calls = 0

        def wait(self, timeout=None):
            self.wait_calls += 1
            if self.wait_calls == 1:
                raise evaluator.subprocess.TimeoutExpired(
                    "stage1", timeout
                )
            return -evaluator.signal.SIGTERM

    class ExpiredClock:
        def __init__(self):
            self.ticks = iter((0.0, 1.0))

        def monotonic(self):
            return next(self.ticks)

        def time_ns(self):
            return 1

    monkeypatch.setenv(
        evaluator.CANDIDATE_LOG_PATH_ENV,
        str(candidate_log),
    )
    monkeypatch.setenv(
        evaluator.WINNER_PREFLIGHT_CONTRACT_ID_ENV,
        "12345",
    )
    monkeypatch.setattr(
        evaluator,
        "_winner_preflight_hard_timeout_s",
        lambda: 1.0,
    )
    monkeypatch.setattr(
        evaluator,
        "STAGE1_PREFLIGHT_WORKER_ATTEMPTS",
        1,
    )
    monkeypatch.setattr(evaluator, "time", ExpiredClock())
    monkeypatch.setattr(evaluator.subprocess, "Popen", TimedOutProcess)
    monkeypatch.setattr(
        evaluator.os,
        "killpg",
        lambda pid, sig: kills.append((pid, sig)),
    )

    result = evaluator.evaluate_stage1(str(program))

    assert result[evaluator.WINNER_PREFLIGHT_COMPLETE_METRIC] == 0.0
    assert result[evaluator.WINNER_PREFLIGHT_INCOMPLETE_METRIC] == 1.0
    assert result[evaluator.WINNER_PREFLIGHT_HARD_TIMEOUT_METRIC] == 1.0
    assert result[
        evaluator.WINNER_PREFLIGHT_SUBPROCESS_FAILED_METRIC
    ] == 1.0
    assert kills == [
        (7654, evaluator.signal.SIGTERM),
        (7654, evaluator.signal.SIGKILL),
    ]


@pytest.mark.parametrize("timed_out", (False, True))
def test_stage1_child_failure_retries_the_same_frozen_mutation(
    tmp_path, monkeypatch, timed_out
):
    program = tmp_path / "retry-program.py"
    program.write_text("def generate_candidates(ell, m): return []\n")
    candidate_log = (tmp_path / "run" / "all_codes.jsonl").resolve()
    contract_id = 112358
    markers = _complete_preflight_metrics(
        contract_id,
        evaluated=0,
        eligible=0,
    )
    attempts = []

    def fake_attempt(path, **kwargs):
        attempts.append((path, dict(kwargs)))
        if len(attempts) == 1:
            return None, "transient child failure", timed_out
        return {
            "schema_version": 1,
            "status": "completed",
            "metrics": {"combined_score": 0.25, **markers},
        }, None, False

    monkeypatch.setenv(
        evaluator.CANDIDATE_LOG_PATH_ENV,
        str(candidate_log),
    )
    monkeypatch.setenv(
        evaluator.WINNER_PREFLIGHT_CONTRACT_ID_ENV,
        str(contract_id),
    )
    monkeypatch.setattr(
        evaluator,
        "_winner_preflight_hard_timeout_s",
        lambda: 1.0,
    )
    monkeypatch.setattr(
        evaluator,
        "_run_stage1_worker_attempt",
        fake_attempt,
    )

    result = evaluator.evaluate_stage1(str(program))

    assert result["combined_score"] == 0.25
    assert len(attempts) == 2
    assert attempts[0][0] == attempts[1][0] == str(program)
    expected_sha256 = evaluator._freeze_program_source_sha256(str(program))
    for _path, kwargs in attempts:
        assert kwargs["source_sha256"] == expected_sha256
        assert kwargs["candidate_log_path"] == candidate_log
        assert kwargs["journal_path"].is_file()


def test_stage1_worker_contract_is_forwarded_once_to_cascade_stage2(
    tmp_path, monkeypatch
):
    contract_id = 246810
    observed = []
    program = tmp_path / "program.py"
    program.write_text("def generate_candidates(ell, m): return []\n")
    monkeypatch.setenv(
        evaluator.WINNER_PREFLIGHT_CONTRACT_ID_ENV,
        str(contract_id),
    )

    class FakeProcess:
        pid = 8642

        def __init__(self, command, **kwargs):
            observed.append((command[2], kwargs["env"]))
            if command[2] == "--stage1-worker":
                payload = {
                    "schema_version": 1,
                    "status": "completed",
                    "metrics": _complete_preflight_metrics(contract_id),
                }
            else:
                payload = {
                    "schema_version": 1,
                    "status": "completed",
                    "metrics": {"combined_score": 2.0},
                    "artifacts": {},
                }
            Path(command[4]).write_text(json.dumps(payload))

        def wait(self, timeout=None):
            return 0

    monkeypatch.setattr(evaluator.subprocess, "Popen", FakeProcess)
    result = evaluator.evaluate_stage1(str(program))
    evaluator.evaluate_stage2(str(program))

    assert observed[0][1][
        evaluator.WINNER_PREFLIGHT_CONTRACT_ID_ENV
    ] == str(contract_id)
    assert result[evaluator.WINNER_PREFLIGHT_CONTRACT_ID_METRIC] == float(
        contract_id
    )
    reuse = json.loads(
        observed[1][1][evaluator.WINNER_PREFLIGHT_REUSE_ENV]
    )
    assert reuse["program_sha256"] == evaluator._program_source_sha256(
        str(program)
    )
    assert reuse["contract_id"] == contract_id
    assert (
        reuse["markers"][evaluator.WINNER_PREFLIGHT_COMPLETE_METRIC]
        == 1.0
    )
    assert evaluator._take_stage1_preflight_completion(str(program)) is None


def test_any_preflight_lattice_failure_refuses_complete_markers():
    def generator(ell, m):
        if (ell, m) == EVOLUTION_LATTICES[-1]:
            raise RuntimeError("last lattice failed")
        return []

    with pytest.raises(
        evaluator.CandidateLogWriteError,
        match="lattices=20/21",
    ):
        evaluator._run_full_winner_preflight(
            generator,
            sampling_salt="program",
            contract_id=11,
        )


def test_full_preflight_candidate_log_failure_returns_no_complete_markers(
    monkeypatch,
):
    definition = (
        [[0, 0], [0, 1], [1, 0]],
        [[0, 0], [0, 2], [2, 0]],
    )

    def fake_batch(ell, m, rows, **_kwargs):
        return [
            {
                "ell": ell,
                "m": m,
                "A_terms": a_terms,
                "B_terms": b_terms,
                "n": 2 * ell * m,
                "k": 4,
                "d": 0,
                "fom": 0.0,
                "score": 0.1,
                "stage": "quick_k_only",
                "encoding_rate": 0.1,
            }
            for a_terms, b_terms in rows
        ]

    monkeypatch.setattr(evaluator, "evaluate_batch", fake_batch)
    monkeypatch.setattr(
        evaluator,
        "_filter_static_eligible",
        lambda rows: (rows, []),
    )
    monkeypatch.setattr(
        evaluator,
        "_log_codes_jsonl",
        lambda *_args, **_kwargs: (_ for _ in ()).throw(
            evaluator.CandidateLogWriteError("candidate log unavailable")
        ),
    )

    with pytest.raises(
        evaluator.CandidateLogWriteError,
        match="candidate log unavailable",
    ):
        evaluator._run_full_winner_preflight(
            lambda _ell, _m: [definition],
            sampling_salt="program",
            contract_id=12,
        )


def test_preflight_freezes_candidate_log_binding_before_untrusted_import(
    tmp_path, monkeypatch
):
    monkeypatch.setattr(evaluator, "_PROJECT_ROOT", str(tmp_path))
    monkeypatch.setenv("QCODE_RUN_NAME", "trusted-run")
    trusted_log = (tmp_path / "trusted-output" / "all_codes.jsonl").resolve()
    redirected_log = (
        tmp_path / "redirected-output" / "all_codes.jsonl"
    ).resolve()
    monkeypatch.setenv(
        evaluator.CANDIDATE_LOG_PATH_ENV,
        str(trusted_log),
    )
    program = tmp_path / "redirecting_program.py"
    program.write_text(
        "import os\n"
        "os.environ['QCODE_RUN_NAME'] = 'redirected-run'\n"
        f"os.environ['{evaluator.CANDIDATE_LOG_PATH_ENV}'] = "
        f"{str(redirected_log)!r}\n"
        "def generate_candidates(ell, m):\n"
        "    return [(\n"
        "        [(0, 0), (0, 1), (1, 0)],\n"
        "        [(0, 0), (0, 2), (2, 0)],\n"
        "    )]\n"
    )

    def fake_batch(ell, m, rows, **kwargs):
        assert kwargs["quick"] is True
        return [
            {
                "ell": ell,
                "m": m,
                "A_terms": a_terms,
                "B_terms": b_terms,
                "n": 2 * ell * m,
                "k": 4,
                "d": 0,
                "fom": 0.0,
                "score": 4 / (2 * ell * m),
                "stage": "quick_k_only",
                "encoding_rate": 4 / (2 * ell * m),
            }
            for a_terms, b_terms in rows
        ]

    monkeypatch.setattr(evaluator, "evaluate_batch", fake_batch)
    monkeypatch.setattr(
        evaluator,
        "_filter_static_eligible",
        lambda rows: (rows, []),
    )

    markers = evaluator._preflight_program(str(program))

    assert markers[evaluator.WINNER_PREFLIGHT_COMPLETE_METRIC] == 1.0
    assert len(trusted_log.read_text().splitlines()) == len(EVOLUTION_LATTICES)
    assert not redirected_log.exists()


def test_absolute_log_binding_routes_milp_copy_away_from_its_project_root(
    tmp_path, monkeypatch
):
    copied_evaluator_root = tmp_path / "results" / "evolution"
    trusted_log = (tmp_path / "actual-run" / "all_codes.jsonl").resolve()
    monkeypatch.setattr(
        evaluator,
        "_PROJECT_ROOT",
        str(copied_evaluator_root),
    )
    monkeypatch.setenv(
        evaluator.CANDIDATE_LOG_PATH_ENV,
        str(trusted_log),
    )

    evaluator._log_code_jsonl(_result(0, 0))

    assert len(trusted_log.read_text().splitlines()) == 1
    assert not (
        copied_evaluator_root
        / "results"
        / "evolution"
        / "all_codes.jsonl"
    ).exists()


def test_milp_cache_is_sibling_of_frozen_absolute_candidate_log(
    tmp_path, monkeypatch
):
    trusted_log = (tmp_path / "actual-run" / "all_codes.jsonl").resolve()
    program = tmp_path / "program.py"
    program.write_text("def generate_candidates(ell, m): return []\n")
    monkeypatch.setenv(
        evaluator.CANDIDATE_LOG_PATH_ENV,
        str(trusted_log),
    )
    monkeypatch.setattr(
        evaluator,
        "_MILP_CANDIDATE_LOG_PATH_BINDING",
        None,
    )
    monkeypatch.setattr(
        evaluator,
        "STAGE2_LATTICES_MILP",
        [(6, 6)],
    )
    monkeypatch.setattr(
        evaluator,
        "_load_generate_candidates",
        lambda _path: (
            lambda _ell, _m: [
                (
                    [[0, 0], [0, 1], [1, 0]],
                    [[0, 0], [0, 2], [2, 0]],
                )
            ]
        ),
    )
    quick = {
        "ell": 6,
        "m": 6,
        "A_terms": [[0, 0], [0, 1], [1, 0]],
        "B_terms": [[0, 0], [0, 2], [2, 0]],
        "n": 72,
        "k": 4,
        "d": 0,
        "d_symplectic": 5,
        "fom": 0.0,
        "stage": "quick_k_only",
    }
    monkeypatch.setattr(
        evaluator,
        "evaluate_batch_milp_parallel",
        lambda *_args, **_kwargs: [dict(quick)],
    )
    observed = {}

    def fake_milp(_tasks, **kwargs):
        observed["save_path"] = kwargs["save_path"]
        return []

    monkeypatch.setattr(evaluator, "evaluate_milp_parallel", fake_milp)
    monkeypatch.setattr(
        evaluator,
        "_write_metrics_jsonl",
        lambda *_args, **_kwargs: None,
    )

    evaluator.evaluate_stage2_milp(str(program))

    assert observed["save_path"] == str(
        trusted_log.with_name("evolution_codes.jsonl")
    )


def test_milp_process_binding_survives_later_environment_redirection(
    tmp_path, monkeypatch
):
    trusted_log = (tmp_path / "trusted" / "all_codes.jsonl").resolve()
    redirected_log = (
        tmp_path / "redirected" / "all_codes.jsonl"
    ).resolve()
    monkeypatch.setattr(
        evaluator,
        "_MILP_CANDIDATE_LOG_PATH_BINDING",
        None,
    )
    monkeypatch.setenv(
        evaluator.CANDIDATE_LOG_PATH_ENV,
        str(trusted_log),
    )

    first = evaluator._freeze_milp_candidate_log_path()
    monkeypatch.setenv(
        evaluator.CANDIDATE_LOG_PATH_ENV,
        str(redirected_log),
    )
    second = evaluator._freeze_milp_candidate_log_path()

    assert first == trusted_log
    assert second == trusted_log


def test_preflight_refuses_program_that_rewrites_its_source_on_import(
    tmp_path, monkeypatch
):
    program = tmp_path / "self_modifying_program.py"
    program.write_text(
        "from pathlib import Path\n"
        "Path(__file__).write_text(\n"
        "    'def generate_candidates(ell, m): return []\\n# changed\\n'\n"
        ")\n"
        "def generate_candidates(ell, m):\n"
        "    return []\n"
    )
    preflight_called = False

    def unexpected_preflight(*_args, **_kwargs):
        nonlocal preflight_called
        preflight_called = True
        return {}

    monkeypatch.setattr(
        evaluator,
        "_run_full_winner_preflight",
        unexpected_preflight,
    )

    with pytest.raises(
        evaluator.CandidateLogWriteError,
        match="changed during winner preflight",
    ):
        evaluator._preflight_program(str(program))

    assert preflight_called is False


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


def test_stage2_actual_subprocess_smoke(tmp_path, monkeypatch):
    program = tmp_path / "empty-generator.py"
    program.write_text(
        "def generate_candidates(ell, m):\n"
        "    return []\n"
    )
    monkeypatch.setenv(
        evaluator.CANDIDATE_LOG_PATH_ENV,
        str((tmp_path / "run" / "all_codes.jsonl").resolve()),
    )

    result = evaluator.evaluate_stage2(str(program))
    metrics = getattr(result, "metrics", result)

    assert metrics[evaluator.STAGE2_SUBPROCESS_FAILED_METRIC] == 0.0
    assert metrics[evaluator.STAGE2_COMPLETE_METRIC] == 1.0
    assert metrics[evaluator.STAGE2_INCOMPLETE_METRIC] == 0.0
    assert metrics[evaluator.STAGE2_LATTICES_METRIC] == float(
        len(evaluator.STAGE2_DEEP_LATTICES)
    )
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


def test_support_filter_precedes_quick_and_rank_and_keeps_full_eligible_handoff(
    tmp_path, monkeypatch
):
    monkeypatch.setattr(evaluator, "_PROJECT_ROOT", str(tmp_path))
    monkeypatch.setattr(
        evaluator,
        "_filter_static_eligible",
        lambda rows: (rows, []),
    )
    ranked = []

    def identity_dedup(rows):
        ranked.extend(rows)
        return rows, []

    monkeypatch.setattr(evaluator, "deduplicate_css_results", identity_dedup)

    def terms(count: int, offset: int) -> list[tuple[int, int]]:
        return [((offset + index) % 6, index // 6) for index in range(count)]

    eligible = [
        (terms(a_count, index), terms(b_count, index + 2))
        for index, (a_count, b_count) in enumerate(
            evaluator.CHALLENGE_SUPPORT_SPLITS
        )
    ]
    rejected = [
        (terms(1, 0), terms(2, 2)),
        (terms(2, 1), terms(1, 3)),
        (terms(4, 0), terms(3, 2)),
        (terms(7, 0), terms(2, 2)),
    ]
    batch_inputs = []

    def fake_batch(ell, m, rows, **kwargs):
        batch_inputs.append((kwargs.get("quick") is True, list(rows)))
        quick = kwargs.get("quick") is True
        return [
            {
                "ell": ell,
                "m": m,
                "A_terms": a_terms,
                "B_terms": b_terms,
                "n": 72,
                "k": 4,
                "d": 0 if quick else 8,
                "fom": 0.0 if quick else 4 * 8 * 8 / 72,
                "score": 4 / 72,
                "stage": "quick_k_only" if quick else "refined_estimate",
                "encoding_rate": 4 / 72,
            }
            for a_terms, b_terms in rows
        ]

    monkeypatch.setattr(evaluator, "evaluate_batch", fake_batch)
    metrics = evaluator._run_evaluation(
        lambda _ell, _m: [*eligible, *rejected],
        [(6, 6)],
        quick=False,
        max_distance_per_lattice=2,
        run_name="support-filter",
        sampling_salt="support-filter-program",
    )

    eligible_keys = {
        evaluator._candidate_definition_key(row, ell=6, m=6)
        for row in eligible
    }
    assert len(batch_inputs) == 2
    assert {
        evaluator._candidate_definition_key(row, ell=6, m=6)
        for row in batch_inputs[0][1]
    } == eligible_keys
    assert all(
        evaluator._definition_key(row) in eligible_keys for row in ranked
    )
    assert all(
        evaluator._candidate_definition_key(row, ell=6, m=6)
        in eligible_keys
        for _quick, rows in batch_inputs
        for row in rows
    )

    assert metrics["total_candidates"] == len(eligible) + len(rejected)
    assert metrics["unique_candidates"] == len(eligible) + len(rejected)
    assert metrics[evaluator.SUPPORT_WEIGHT_ELIGIBLE_METRIC] == len(
        eligible
    )
    assert metrics[evaluator.SUPPORT_WEIGHT_REJECTED_METRIC] == len(
        rejected
    )
    assert metrics[evaluator.SUPPORT_WEIGHT_EVALUATED_METRIC] == len(
        eligible
    )
    assert (
        metrics[evaluator.SUPPORT_WEIGHT_EVALUATION_COVERAGE_METRIC]
        == 1.0
    )
    assert metrics[evaluator.SUPPORT_WEIGHT_ELIGIBLE_FRACTION_METRIC] == (
        len(eligible) / (len(eligible) + len(rejected))
    )
    assert metrics[evaluator.SUPPORT_WEIGHT_REJECTION_FRACTION_METRIC] == (
        len(rejected) / (len(eligible) + len(rejected))
    )
    assert metrics[evaluator.SUPPORT_WEIGHT_PARTITION_COMPLETE_METRIC] == 1
    assert metrics[evaluator.SUPPORT_SPLITS_COVERED_METRIC] == len(
        evaluator.CHALLENGE_SUPPORT_SPLITS
    )
    assert metrics[evaluator.SUPPORT_SPLIT_COVERAGE_METRIC] == 1.0
    assert set(metrics["support_split_counts"].values()) == {1}

    path = (
        tmp_path
        / "results"
        / "evolution"
        / "support-filter"
        / "all_codes.jsonl"
    )
    full_pool = [
        json.loads(line)
        for line in path.read_text().splitlines()
        if json.loads(line).get("candidate_persistence_reason")
        == evaluator.FULL_POOL_PREFLIGHT_PERSISTENCE_REASON
    ]
    assert {
        evaluator._definition_key(row) for row in full_pool
    } == eligible_keys
    assert all(
        row[evaluator.SUPPORT_FILTER_VERSION_METRIC]
        == evaluator.CHALLENGE_SUPPORT_FILTER_VERSION
        and row[evaluator.PATTERN_CLASSIFIER_VERSION_METRIC]
        == evaluator.PATTERN_CLASSIFIER_VERSION
        for row in full_pool
    )
    assert metrics["winner_capable_quick_exploration_eligible"] == len(
        eligible
    )
    assert metrics["winner_capable_quick_exploration_persisted"] == len(
        eligible
    )
    evaluator._require_full_pool_persistence(
        metrics,
        expected_lattices=1,
        label="support-filter regression",
    )


def test_bounded_quick_fitness_reports_partial_eligible_coverage(monkeypatch):
    candidates = [
        (
            [(0, 0), (index + 1, 0)],
            [(0, 0), (0, index + 1)],
        )
        for index in range(3)
    ]
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
                "k": 0,
                "d": 0,
                "fom": 0.0,
                "score": 0.0,
                "stage": "quick_k_only",
                "encoding_rate": 0.0,
            }
            for a_terms, b_terms in rows
        ]

    monkeypatch.setattr(evaluator, "evaluate_batch", fake_batch)
    metrics = evaluator._run_evaluation(
        lambda _ell, _m: candidates,
        [(6, 6)],
        quick=True,
        candidate_limit=2,
        sampling_salt="bounded-support",
    )

    assert len(evaluated) == 2
    assert metrics[evaluator.SUPPORT_WEIGHT_ELIGIBLE_METRIC] == 3
    assert metrics[evaluator.SUPPORT_WEIGHT_EVALUATED_METRIC] == 2
    assert metrics[evaluator.SUPPORT_WEIGHT_EVALUATION_COVERAGE_METRIC] == (
        2 / 3
    )


def test_full_winner_preflight_persists_every_support_eligible_definition(
    tmp_path, monkeypatch
):
    eligible = (
        [(0, 0), (1, 0)],
        [(0, 0), (0, 1), (1, 0), (1, 1)],
    )
    rejected = (
        [(0, 0), (1, 0), (0, 1)],
        [(0, 0), (0, 1), (1, 0), (1, 1)],
    )
    observed = []

    def fake_batch(ell, m, rows, **_kwargs):
        observed.extend((ell, m, row) for row in rows)
        return [
            {
                "ell": ell,
                "m": m,
                "A_terms": a_terms,
                "B_terms": b_terms,
                "n": 2 * ell * m,
                "k": 4,
                "d": 0,
                "fom": 0.0,
                "score": 4 / (2 * ell * m),
                "stage": "quick_k_only",
                "encoding_rate": 4 / (2 * ell * m),
            }
            for a_terms, b_terms in rows
        ]

    monkeypatch.setattr(evaluator, "evaluate_batch", fake_batch)
    monkeypatch.setattr(
        evaluator,
        "_filter_static_eligible",
        lambda rows: (rows, []),
    )
    candidate_log = tmp_path / "all_codes.jsonl"
    markers = evaluator._run_full_winner_preflight(
        lambda _ell, _m: [eligible, rejected],
        sampling_salt="support-complete",
        contract_id=17,
        candidate_log_path=candidate_log,
    )

    expected = len(EVOLUTION_LATTICES)
    assert len(observed) == expected
    assert all(row == eligible for _ell, _m, row in observed)
    assert markers[evaluator.WINNER_PREFLIGHT_EVALUATED_METRIC] == float(
        expected
    )
    assert markers[evaluator.WINNER_PREFLIGHT_ELIGIBLE_METRIC] == float(
        expected
    )
    assert markers[evaluator.WINNER_PREFLIGHT_PERSISTED_METRIC] == float(
        expected
    )
    assert markers[evaluator.WINNER_PREFLIGHT_OMITTED_METRIC] == 0.0
    persisted = [
        json.loads(line) for line in candidate_log.read_text().splitlines()
    ]
    assert len(persisted) == expected
    assert all(
        (len(row["A_terms"]), len(row["B_terms"])) == (2, 4)
        for row in persisted
    )


def test_evaluator_support_splits_match_search_sampler_contract():
    assert evaluator.CHALLENGE_SUPPORT_SPLITS == DEFAULT_SPLITS


def test_multi_term_mixed_pattern_has_versioned_multi_term_niche():
    assert evaluator.PATTERN_CLASSIFIER_VERSION == 2
    assert evaluator._classify_pattern(
        [(0, 0), (1, 2), (2, 0), (0, 3)],
        [(0, 1), (1, 0), (2, 0)],
    ) == 4.0
    assert evaluator._classify_pattern(
        [(0, 0), (1, 2), (2, 0)],
        [(0, 1), (1, 0), (2, 0)],
    ) == 3.0


def test_pool_map_descriptor_is_not_owned_by_single_high_k_safety_row():
    safety = {
        "ell": 6,
        "m": 6,
        "A_terms": [[0, 0], [1, 1], [2, 0]],
        "B_terms": [[0, 1], [1, 0], [2, 2]],
        "n": 72,
        "k": 16,
    }
    evolved = [
        {
            "ell": 6,
            "m": 6,
            "A_terms": [[0, 0], [index + 1, 0]],
            "B_terms": [
                [0, 1],
                [1, index + 1],
                [index + 2, 0],
                [0, index + 2],
            ],
            "n": 72,
            "k": 0,
        }
        for index in range(3)
    ]
    rows = [safety, dict(safety), *evolved]

    descriptor = evaluator._pool_map_descriptor(
        rows,
        lattices={(6, 6)},
    )
    reversed_descriptor = evaluator._pool_map_descriptor(
        list(reversed(rows)),
        lattices={(6, 6)},
    )

    assert descriptor == reversed_descriptor
    assert descriptor[evaluator.MAP_DESCRIPTOR_VERSION_METRIC] == float(
        evaluator.MAP_DESCRIPTOR_VERSION
    )
    assert descriptor[evaluator.MAP_DESCRIPTOR_POOL_SIZE_METRIC] == 4.0
    assert descriptor["term_count"] == pytest.approx(3.75)
    assert descriptor["pattern_type"] == 4.0
    assert descriptor[
        evaluator.MAP_DESCRIPTOR_SUPPORT_SPLIT_METRIC
    ] == 3.0
    expected_entropy = -(
        0.75 * math.log(0.75) + 0.25 * math.log(0.25)
    ) / math.log(evaluator.MAP_DESCRIPTOR_PATTERN_CARDINALITY)
    assert descriptor[
        evaluator.MAP_DESCRIPTOR_STRUCTURAL_ENTROPY_METRIC
    ] == pytest.approx(expected_entropy)
    assert descriptor[
        evaluator.MAP_DESCRIPTOR_DOMINANT_SHARE_METRIC
    ] == pytest.approx(0.75)


def test_pool_map_descriptor_support_split_indices_follow_contract_order():
    for expected_index, (a_count, b_count) in enumerate(
        evaluator.CHALLENGE_SUPPORT_SPLITS
    ):
        row = {
            "ell": 12,
            "m": 6,
            "A_terms": [[index, 0] for index in range(a_count)],
            "B_terms": [[0, index] for index in range(b_count)],
        }
        descriptor = evaluator._pool_map_descriptor([row])
        assert descriptor[
            evaluator.MAP_DESCRIPTOR_SUPPORT_SPLIT_METRIC
        ] == float(expected_index)


def test_pool_map_descriptor_entropy_uses_all_six_pattern_classes():
    candidates = [
        # 0: univariate
        ([[0, 0], [0, 1]], [[0, 0], [1, 0]]),
        # 1: pure x/y-swap-like structure without a constant anchor
        ([[1, 0], [0, 1]], [[2, 0], [0, 2]]),
        # 2: self-dual
        ([[0, 0], [1, 1]], [[0, 0], [1, 1]]),
        # 3: compact mixed
        ([[0, 0], [1, 1]], [[0, 1], [2, 1]]),
        # 4: asymmetric multi-term
        (
            [[0, 0], [1, 0], [0, 1], [1, 1]],
            [[0, 0], [2, 1]],
        ),
        # 5: hybrid/non-standard pure
        ([[0, 0], [1, 0]], [[0, 1], [1, 0]]),
    ]
    rows = [
        {
            "ell": 12,
            "m": 6,
            "A_terms": a_terms,
            "B_terms": b_terms,
        }
        for a_terms, b_terms in candidates
    ]

    assert [
        evaluator._classify_pattern(
            row["A_terms"],
            row["B_terms"],
        )
        for row in rows
    ] == [float(index) for index in range(6)]
    descriptor = evaluator._pool_map_descriptor(rows)
    assert descriptor["pattern_type"] == 0.0
    assert descriptor[
        evaluator.MAP_DESCRIPTOR_STRUCTURAL_ENTROPY_METRIC
    ] == pytest.approx(1.0)
    assert descriptor == evaluator._pool_map_descriptor(
        [rows[index] for index in (5, 2, 4, 0, 3, 1)]
    )


def test_pool_map_descriptor_empty_and_error_envelopes_are_complete():
    required = {
        "term_count",
        "pattern_type",
        evaluator.MAP_DESCRIPTOR_SUPPORT_SPLIT_METRIC,
        evaluator.MAP_DESCRIPTOR_STRUCTURAL_ENTROPY_METRIC,
        evaluator.MAP_DESCRIPTOR_VERSION_METRIC,
        evaluator.MAP_DESCRIPTOR_POOL_SIZE_METRIC,
        evaluator.MAP_DESCRIPTOR_DOMINANT_SHARE_METRIC,
    }
    empty = evaluator._pool_map_descriptor([])
    failure = evaluator._error_result("synthetic failure")

    assert required <= empty.keys()
    assert required <= failure.keys()
    assert empty[evaluator.MAP_DESCRIPTOR_VERSION_METRIC] == 3.0
    assert failure[evaluator.MAP_DESCRIPTOR_VERSION_METRIC] == 3.0
    for metric in required - {evaluator.MAP_DESCRIPTOR_VERSION_METRIC}:
        assert empty[metric] == 0.0
        assert failure[metric] == 0.0


def test_final_gate_persistence_probes_do_not_change_resumed_fitness_basis(
    tmp_path, monkeypatch
):
    program = tmp_path / "program.py"
    program.write_text("def generate_candidates(ell, m): return []\n")
    critical = {
        "ell": 6,
        "m": 6,
        "A_terms": [[0, 0], [1, 0]],
        "B_terms": [[0, 0], [0, 1]],
        "n": 72,
        "k": 16,
        "d": 10,
        "fom": 16 * 10 * 10 / 72,
        "fom_upper_bound": 16 * 10 * 10 / 72,
        "distance_status": "upper_bound",
        "search_status": "unresolved",
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
        "fom_upper_bound": 12.0,
        "distance_status": "upper_bound",
        "search_status": "unresolved",
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
        "winner_capable_quick_exploration_eligible": 0,
        "winner_capable_quick_exploration_persisted": 0,
        "winner_capable_quick_exploration_omitted": 0,
        "winner_capable_unresolved_top_persisted": 0,
        "best_code": critical,
        "all_results": [critical, historical],
        "errors": [],
        "lattices_completed": len(EVOLUTION_LATTICES),
        "lattice_failures": 0,
        **_support_metrics(unique=2),
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
    monkeypatch.setattr(
        evaluator,
        "_run_resumable_stage2_deep",
        lambda *_args, **_kwargs: metrics,
    )
    monkeypatch.setattr(evaluator, "_write_metrics_jsonl", lambda _metrics: None)
    monkeypatch.setattr(evaluator, "save_code", lambda _row: None)
    monkeypatch.setattr(evaluator, "update_pareto_front", lambda _rows: None)

    evaluated = evaluator._evaluate_stage2_impl(str(program))
    result = getattr(evaluated, "metrics", evaluated)
    artifacts = getattr(evaluated, "artifacts", {})
    expected = evaluator._score_stage2_upper_bound_safe(
        [critical, historical]
    )

    assert result["best_bp_fom_upper_bound"] == critical["fom"]
    assert result["combined_score"] == pytest.approx(
        expected["combined_score"]
    )
    assert result["fitness_distance_credit"] == 0.0
    assert result["fitness_survivor_credit"] == 1.0
    assert result["screen_survivor_lattices"] == 1.0
    assert "best_fom" not in result
    assert result["term_count"] == 3
    artifact_text = "\n".join(artifacts.values())
    assert "d<=10" not in artifact_text
    assert f"{critical['fom']:.2f}" not in artifact_text
    assert "Best BP/OSD FOM upper bound" not in artifacts["summary"]
    assert (
        "BP/OSD upper-bound diagnostics retained in telemetry only."
        in artifacts["summary"]
    )
    assert "d=unresolved" in artifacts["best_screen_survivor"]


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


def test_stage2_full_preflight_persists_every_eligible_definition_in_one_batch(
    tmp_path, monkeypatch
):
    monkeypatch.setattr(evaluator, "_PROJECT_ROOT", str(tmp_path))
    monkeypatch.setattr(
        evaluator,
        "_filter_static_eligible",
        lambda rows: (rows, []),
    )
    candidates = [
        (
            [[0, 0], [0, 1], [index + 1, 0]],
            [[0, 0], [0, 2], [index + 2, 0]],
        )
        for index in range(20)
    ]

    def fake_batch(ell, m, rows, **_kwargs):
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
    real_append = evaluator._append_candidate_jsonl
    batch_sizes = []

    def track_batch(path, payload):
        batch_sizes.append(payload.count(b"\n"))
        return real_append(path, payload)

    monkeypatch.setattr(evaluator, "_append_candidate_jsonl", track_batch)
    metrics = evaluator._run_evaluation(
        lambda _ell, _m: candidates,
        [(6, 6)],
        quick=True,
        run_name="full-stage2-preflight",
        sampling_salt="program-a",
        persist_quick_exploration=True,
        persist_all_quick_exploration=True,
    )

    path = (
        tmp_path
        / "results"
        / "evolution"
        / "full-stage2-preflight"
        / "all_codes.jsonl"
    )
    persisted = [json.loads(line) for line in path.read_text().splitlines()]
    assert len(persisted) == len(candidates)
    assert len(persisted) > (
        evaluator.MAX_WINNER_CAPABLE_EXPLORATION_PER_LATTICE
    )
    assert batch_sizes == [len(candidates)]
    assert metrics["winner_capable_quick_exploration_eligible"] == len(
        candidates
    )
    assert metrics["winner_capable_quick_exploration_persisted"] == len(
        candidates
    )
    assert metrics["winner_capable_quick_exploration_omitted"] == 0
    assert all(
        row["winner_capable_parameters"] is True
        and row["candidate_persistence_reason"]
        == evaluator.FULL_POOL_PREFLIGHT_PERSISTENCE_REASON
        for row in persisted
    )


def test_full_preflight_does_not_sample_away_definition_after_5000(
    tmp_path, monkeypatch
):
    monkeypatch.setattr(evaluator, "_PROJECT_ROOT", str(tmp_path))
    monkeypatch.setattr(
        evaluator,
        "_filter_static_eligible",
        lambda rows: (rows, []),
    )
    candidates = [
        (
            [[0, 0], [0, 1], [index + 1, 0]],
            [[0, 0], [0, 2], [index + 2, 0]],
        )
        for index in range(evaluator.MAX_CANDIDATES_PER_LATTICE + 3)
    ]

    def fake_batch(ell, m, rows, **_kwargs):
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
        quick=True,
        run_name="unbounded-full-preflight",
        candidate_limit=None,
        persist_quick_exploration=True,
        persist_all_quick_exploration=True,
    )

    rows = [
        json.loads(line)
        for line in (
            tmp_path
            / "results"
            / "evolution"
            / "unbounded-full-preflight"
            / "all_codes.jsonl"
        ).read_text().splitlines()
    ]
    assert len(rows) == len(candidates)
    assert rows[-1]["A_terms"] == candidates[-1][0]
    assert metrics["evaluated_candidate_definitions"] == len(candidates)
    assert metrics["winner_capable_quick_exploration_omitted"] == 0


def test_stage1_completes_full_persistence_before_gate_score(
    tmp_path, monkeypatch
):
    order = []
    program = tmp_path / "program.py"
    program.write_text("def generate_candidates(ell, m): return []\n")
    markers = {
        evaluator.WINNER_PREFLIGHT_CONTRACT_VERSION_METRIC: float(
            evaluator.WINNER_PREFLIGHT_CONTRACT_VERSION
        ),
        evaluator.WINNER_PREFLIGHT_CONTRACT_ID_METRIC: 7.0,
        evaluator.WINNER_PREFLIGHT_COMPLETE_METRIC: 1.0,
    }
    monkeypatch.setattr(
        evaluator,
        "_load_generate_candidates",
        lambda _path: lambda _ell, _m: [],
    )
    monkeypatch.setattr(
        evaluator,
        "_current_winner_preflight_contract_id",
        lambda: 7,
    )

    def preflight(*_args, **_kwargs):
        order.append("persist")
        return dict(markers)

    def score(*_args, **_kwargs):
        order.append("gate")
        return {
            "total_candidates": 0,
            "unique_candidates": 0,
            "evaluated_candidate_definitions": 0,
            "all_results": [],
            "num_valid": 0,
            "num_high_k": 0,
            "lattices_with_high_k": 0,
            "lattices_completed": len(evaluator.STAGE1_LATTICES),
            "lattice_failures": 0,
            "winner_capable_quick_exploration_eligible": 0,
            "winner_capable_quick_exploration_persisted": 0,
            "winner_capable_quick_exploration_omitted": 0,
            **_support_metrics(),
        }

    monkeypatch.setattr(evaluator, "_run_full_winner_preflight", preflight)
    monkeypatch.setattr(evaluator, "_run_evaluation", score)
    result = evaluator._evaluate_stage1_impl(str(program))

    assert order == ["persist", "gate"]
    assert result[evaluator.WINNER_PREFLIGHT_COMPLETE_METRIC] == 1.0


def test_stage1_persists_full_winner_pool_before_scoring_gate(
    tmp_path, monkeypatch
):
    monkeypatch.setattr(evaluator, "_PROJECT_ROOT", str(tmp_path))
    monkeypatch.delenv("QCODE_RUN_NAME", raising=False)
    program = tmp_path / "stage1-program.py"
    program.write_text("def generate_candidates(ell, m): return []\n")
    candidate = (
        [[0, 0], [0, 1], [1, 0]],
        [[0, 0], [0, 2], [2, 0]],
    )
    monkeypatch.setattr(
        evaluator,
        "_load_generate_candidates",
        lambda _path: lambda _ell, _m: [candidate] * 20,
    )
    monkeypatch.setattr(
        evaluator,
        "_filter_static_eligible",
        lambda rows: (rows, []),
    )

    def fake_batch(ell, m, rows, **_kwargs):
        return [
            {
                "ell": ell,
                "m": m,
                "A_terms": a_terms,
                "B_terms": b_terms,
                "n": 2 * ell * m,
                "k": 4,
                "d": 0,
                "fom": 0.0,
                "score": 4 / (2 * ell * m),
                "stage": "quick_k_only",
                "encoding_rate": 4 / (2 * ell * m),
            }
            for a_terms, b_terms in rows
        ]

    monkeypatch.setattr(evaluator, "evaluate_batch", fake_batch)
    result = evaluator._evaluate_stage1_impl(str(program))

    assert result["num_valid"] == float(len(evaluator.STAGE1_LATTICES))
    persisted = [
        json.loads(line)
        for line in next(tmp_path.rglob("all_codes.jsonl")).read_text().splitlines()
    ]
    assert len(persisted) == (
        len(EVOLUTION_LATTICES) + len(evaluator.STAGE1_LATTICES)
    )
    assert {
        (row["ell"], row["m"]) for row in persisted
    } == set(EVOLUTION_LATTICES)
    assert result[evaluator.WINNER_PREFLIGHT_COMPLETE_METRIC] == 1.0


def test_stage1_stateful_fitness_pool_is_fully_persisted(
    tmp_path, monkeypatch
):
    monkeypatch.setattr(evaluator, "_PROJECT_ROOT", str(tmp_path))
    monkeypatch.setenv("QCODE_RUN_NAME", "stage1-stateful")
    monkeypatch.setattr(
        evaluator,
        "_filter_static_eligible",
        lambda rows: (rows, []),
    )
    program = tmp_path / "stage1-stateful.py"
    program.write_text(
        "_calls = 0\n"
        "def generate_candidates(ell, m):\n"
        "    global _calls\n"
        "    _calls += 1\n"
        f"    if _calls != {len(EVOLUTION_LATTICES) + 1}:\n"
        "        return []\n"
        "    return [(\n"
        "        [(0, 0), (0, 1), (1, 0)],\n"
        "        [(0, 0), (0, 2), (2, 0)],\n"
        "    )]\n"
    )

    def fake_batch(ell, m, rows, **kwargs):
        assert kwargs["quick"] is True
        return [
            {
                "ell": ell,
                "m": m,
                "A_terms": a_terms,
                "B_terms": b_terms,
                "n": 2 * ell * m,
                "k": 4,
                "d": 0,
                "fom": 0.0,
                "score": 4 / (2 * ell * m),
                "stage": "quick_k_only",
                "encoding_rate": 4 / (2 * ell * m),
            }
            for a_terms, b_terms in rows
        ]

    monkeypatch.setattr(evaluator, "evaluate_batch", fake_batch)

    result = evaluator._evaluate_stage1_impl(str(program))

    path = (
        tmp_path
        / "results"
        / "evolution"
        / "stage1-stateful"
        / "all_codes.jsonl"
    )
    persisted = [json.loads(line) for line in path.read_text().splitlines()]
    assert result[evaluator.WINNER_PREFLIGHT_COMPLETE_METRIC] == 1.0
    assert result["num_valid"] == 1.0
    assert len(persisted) == 1
    assert persisted[0]["candidate_persistence_reason"] == (
        evaluator.FULL_POOL_PREFLIGHT_PERSISTENCE_REASON
    )
    assert (persisted[0]["ell"], persisted[0]["m"]) == (
        evaluator.STAGE1_LATTICES[0]
    )


def test_stage1_partial_historical_persistence_cannot_keep_complete_marker(
    tmp_path, monkeypatch
):
    contract_id = 97531
    program = tmp_path / "partial-stage1.py"
    program.write_text("def generate_candidates(ell, m): return []\n")
    monkeypatch.setattr(
        evaluator,
        "_current_winner_preflight_contract_id",
        lambda: contract_id,
    )
    monkeypatch.setattr(
        evaluator,
        "_run_full_winner_preflight",
        lambda *_args, **_kwargs: _complete_preflight_metrics(contract_id),
    )
    monkeypatch.setattr(
        evaluator,
        "_run_evaluation",
        lambda *_args, **_kwargs: {
            "unique_candidates": 1,
            "evaluated_candidate_definitions": 1,
            "lattices_completed": 1,
            "lattice_failures": 1,
            "winner_capable_quick_exploration_eligible": 1,
            "winner_capable_quick_exploration_persisted": 1,
            "winner_capable_quick_exploration_omitted": 0,
            **_support_metrics(unique=1),
        },
    )

    with pytest.raises(
        evaluator.CandidateLogWriteError,
        match="Stage 1 historical fitness pass did not complete",
    ):
        evaluator._evaluate_stage1_impl(str(program))


def test_deep_stateful_pool_persists_tail_before_5000_sample(
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
    candidate_count = evaluator.MAX_CANDIDATES_PER_LATTICE + 1
    candidates = [
        (
            [[0, 0], [index + 1, 0]],
            [[0, 0], [0, 1]],
        )
        for index in range(candidate_count)
    ]
    generator_calls = 0
    deep_inputs = []
    path = (
        tmp_path
        / "results"
        / "evolution"
        / "stateful-tail"
        / "all_codes.jsonl"
    )

    def stateful_generator(_ell, _m):
        nonlocal generator_calls
        generator_calls += 1
        if generator_calls != 1:
            raise AssertionError("deep lattice called generator more than once")
        return candidates

    def fake_batch(ell, m, rows, **kwargs):
        quick = kwargs.get("quick") is True
        if not quick:
            deep_inputs.extend(rows)
        return [
            {
                "ell": ell,
                "m": m,
                "A_terms": a_terms,
                "B_terms": b_terms,
                "n": 72,
                "k": (
                    4
                    if max(x for x, _y in a_terms)
                    in {1, candidate_count}
                    else 0
                ),
                "d": 0 if quick else 8,
                "fom": 0.0 if quick else 4 * 8 * 8 / 72,
                "score": 0.0,
                "stage": "quick_k_only" if quick else "refined_estimate",
                "encoding_rate": 4 / 72,
            }
            for a_terms, b_terms in rows
        ]

    def exclude_tail_after_persistence(rows, **_kwargs):
        persisted = [json.loads(line) for line in path.read_text().splitlines()]
        assert any(
            max(x for x, _y in row["A_terms"]) == candidate_count
            for row in persisted
        )
        return rows[:-1]

    monkeypatch.setattr(evaluator, "evaluate_batch", fake_batch)
    monkeypatch.setattr(
        evaluator,
        "_bounded_candidate_sample",
        exclude_tail_after_persistence,
    )

    metrics = evaluator._run_evaluation(
        stateful_generator,
        [(6, 6)],
        quick=False,
        max_distance_per_lattice=1,
        candidate_limit=evaluator.MAX_CANDIDATES_PER_LATTICE,
        run_name="stateful-tail",
        sampling_salt="stateful-program",
    )

    full_pool = [
        json.loads(line)
        for line in path.read_text().splitlines()
        if json.loads(line).get("candidate_persistence_reason")
        == evaluator.FULL_POOL_PREFLIGHT_PERSISTENCE_REASON
    ]
    assert generator_calls == 1
    assert len(full_pool) == 2
    assert any(
        max(x for x, _y in row["A_terms"]) == candidate_count
        for row in full_pool
    )
    assert all(
        max(x for x, _y in a_terms) != candidate_count
        for a_terms, _b_terms in deep_inputs
    )
    assert metrics["winner_capable_quick_exploration_persisted"] == 2
    assert metrics["winner_capable_quick_exploration_omitted"] == 0


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
    full_pool_rows = [
        row for row in persisted
        if row.get("candidate_persistence_reason")
        == evaluator.FULL_POOL_PREFLIGHT_PERSISTENCE_REASON
    ]
    assert len(full_pool_rows) == len(candidates)
    pending_rows = [
        row for row in persisted
        if row.get("candidate_persistence_reason")
        == evaluator.DISTANCE_PENDING_PERSISTENCE_REASON
    ]
    assert len(pending_rows) == len(distance_inputs)
    assert all(
        row["d"] == 0 and row["fom"] == 0 for row in full_pool_rows
    )
    assert all(
        row["minimum_winning_distance"] == 15 for row in full_pool_rows
    )
    assert len(persisted) == (
        len(distance_inputs) + len(pending_rows) + len(full_pool_rows)
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
    assert len(persisted) == 3
    assert all(
        row["candidate_persistence_lane"]
        == evaluator.WINNER_CAPABLE_EXPLORATION_LANE
        for row in persisted
    )
    assert persisted[0]["candidate_persistence_reason"] == (
        evaluator.FULL_POOL_PREFLIGHT_PERSISTENCE_REASON
    )
    assert persisted[1]["candidate_persistence_reason"] == (
        evaluator.DISTANCE_PENDING_PERSISTENCE_REASON
    )
    assert persisted[2]["candidate_persistence_reason"] == (
        evaluator.UNRESOLVED_TOP_PERSISTENCE_REASON
    )
    assert metrics["winner_capable_distance_pending_persisted"] == 1
    assert metrics["winner_capable_unresolved_top_persisted"] == 1
    assert metrics["winner_capable_quick_exploration_persisted"] == 1


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
                == evaluator.FULL_POOL_PREFLIGHT_PERSISTENCE_REASON
                for row in preexisting
            ) == len(candidates)
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
    full_pool = [
        row for row in persisted
        if row.get("candidate_persistence_reason")
        == evaluator.FULL_POOL_PREFLIGHT_PERSISTENCE_REASON
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
    assert distance_keys.issubset(definitions(full_pool))
    assert len(pending) == len(failed) == 2
    assert len(full_pool) == len(candidates)
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
    assert (
        metrics["winner_capable_quick_exploration_persisted"]
        == len(full_pool)
    )
    assert metrics["distance_backend_error_count"] == 1
    assert metrics["errors"] == [
        "(6,6): distance backend RuntimeError: "
        "simulated distance backend failure"
    ]

    preflight_metrics = dict(metrics)
    preflight_metrics["winner_capable_quick_exploration_eligible"] = len(
        full_pool
    )
    preflight_metrics["winner_capable_quick_exploration_omitted"] = 0
    preflight_metrics["lattices_completed"] = len(EVOLUTION_LATTICES)
    preflight_metrics["lattice_failures"] = 0
    monkeypatch.setattr(
        evaluator,
        "_load_generate_candidates",
        lambda _path: lambda _ell, _m: [],
    )
    monkeypatch.setattr(
        evaluator,
        "_run_evaluation",
        lambda *_args, **kwargs: (
            preflight_metrics if kwargs.get("quick") is True else metrics
        ),
    )
    monkeypatch.setattr(
        evaluator,
        "_run_resumable_stage2_deep",
        lambda *_args, **_kwargs: metrics,
    )
    monkeypatch.setattr(evaluator, "_write_metrics_jsonl", lambda _metrics: None)
    program = tmp_path / "program.py"
    program.write_text("def generate_candidates(ell, m): return []\n")
    evaluated = evaluator._evaluate_stage2_impl(str(program))
    result = getattr(evaluated, "metrics", evaluated)
    artifacts = getattr(evaluated, "artifacts", {})
    assert result["distance_backend_error_count"] == 1.0
    assert artifacts["errors"] == metrics["errors"][0]
    assert "Distance backend failures: 1." in artifacts["summary"]


def test_write_ahead_log_failure_aborts_before_distance_backend(
    tmp_path, monkeypatch
):
    monkeypatch.setattr(evaluator, "_PROJECT_ROOT", str(tmp_path))
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
    full_pool = [
        row for row in persisted
        if row.get("candidate_persistence_reason")
        == evaluator.FULL_POOL_PREFLIGHT_PERSISTENCE_REASON
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
    assert len(full_pool) == len(candidates)
    assert metrics["winner_capable_unresolved_top_persisted"] == 2
    assert (
        metrics["winner_capable_quick_exploration_persisted"]
        == len(full_pool)
    )


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
    monkeypatch.setattr(evaluator, "_PROJECT_ROOT", str(tmp_path))
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

    result = evaluator._evaluate_stage1_impl(str(program))

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

    def fake_run(_generate, lattices, **_kwargs):
        if tuple(lattices) == EVOLUTION_LATTICES:
            return {
                "lattices_completed": len(EVOLUTION_LATTICES),
                "lattice_failures": 0,
                "winner_capable_quick_exploration_eligible": 0,
                "winner_capable_quick_exploration_persisted": 0,
                "winner_capable_quick_exploration_omitted": 0,
                "evaluated_candidate_definitions": 0,
                "unique_candidates": 0,
                **_support_metrics(),
            }
        return {
            **metrics,
            "lattices_completed": len(evaluator.STAGE1_LATTICES),
            "lattice_failures": 0,
            "winner_capable_quick_exploration_eligible": 1,
            "winner_capable_quick_exploration_persisted": 1,
            "winner_capable_quick_exploration_omitted": 0,
            "unique_candidates": 1,
            "evaluated_candidate_definitions": 1,
            **_support_metrics(unique=1),
        }

    monkeypatch.setattr(evaluator, "_run_evaluation", fake_run)

    monkeypatch.setattr(
        evaluator,
        "_stage1_specialist_exploration_pass",
        lambda _path: False,
    )
    ordinary = evaluator._evaluate_stage1_impl(str(program))
    monkeypatch.setattr(
        evaluator,
        "_stage1_specialist_exploration_pass",
        lambda _path: True,
    )
    sampled = evaluator._evaluate_stage1_impl(str(program))

    assert ordinary["combined_score"] == 0.001
    assert ordinary["specialist_exploration"] == 0.0
    assert sampled["combined_score"] == 0.02
    assert sampled["specialist_exploration"] == 1.0
