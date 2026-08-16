"""Tests for the independent Stage 2 exactification sidecar."""

from __future__ import annotations

import copy
import json
from pathlib import Path
from typing import Any

import numpy as np
import pytest

from humanize import exactification_queue as eq


DIGEST = "a" * 64
INPUT_SHA256 = "b" * 64


def _queue_item(digest: str = DIGEST) -> dict[str, Any]:
    return {
        "canonical_digest": digest,
        "input_sha256": INPUT_SHA256,
        "candidate": {"canonical_digest": digest, "n": 3, "k": 2},
        "artifact_path": "/fixture/xor.json",
        "artifact_sha256": "c" * 64,
        "translation_symmetry": {"verified": True},
        "cache_binding": {"binding_sha256": "d" * 64},
        "selection_ack": {
            "sequence": 0,
            "ack_sha256": "e" * 64,
            "page_sha256": "f" * 64,
        },
        "initial_upper_bound": 5,
        "initial_upper_witness": {"objective": 5, "sector": "X"},
        "n": 3,
        "k": 2,
        "score": {"numerator": 50, "denominator": 3, "decimal": 50 / 3},
    }


def _install_queue(
    tmp_path: Path,
    config: eq.QueueConfig | None = None,
) -> tuple[eq.QueuePaths, dict[str, Any]]:
    config = eq.QueueConfig() if config is None else config
    paths = eq.queue_paths(tmp_path)
    eq._ensure_paths(paths)
    job = eq._new_job(_queue_item(), rank=1, now=0.0)
    queue = eq._seal_queue({
        "schema_version": eq.QUEUE_SCHEMA_VERSION,
        "gate": eq.QUEUE_GATE,
        "revision": 0,
        "created_at": 0.0,
        "updated_at": 0.0,
        "producer": {"source_sha256": "1" * 64},
        "source": {},
        "config": config.as_dict(),
        "jobs": [job],
    })
    eq._atomic_write_json(paths.queue, queue)
    return paths, job


def _claimed_queue(
    tmp_path: Path,
    config: eq.QueueConfig | None = None,
) -> tuple[eq.QueuePaths, dict[str, Any]]:
    paths, _ = _install_queue(tmp_path, config)
    claimed = eq.claim_next_job(
        paths, worker_id="worker-1", config=config or eq.QueueConfig(), now=0.0,
    )
    assert claimed is not None
    return paths, claimed


def _seal_evidence(values: dict[str, Any]) -> dict[str, Any]:
    evidence = dict(values)
    evidence["evidence_sha256"] = eq.canonical_sha256(evidence)
    return evidence


def _terminal_evidence(
    args: tuple[Any, ...],
    kwargs: dict[str, Any],
    *,
    outcome: str,
    objective: int | None = None,
) -> dict[str, Any]:
    from evaluation import distance_sat

    checks, logicals = args[:2]
    sector = kwargs["sector"]
    cutoff = kwargs["max_weight"]
    partition = kwargs["partition_index"]
    encoding = kwargs["cardinality_encoding"]
    identity = kwargs["checkpoint_identity"]
    instance = distance_sat._instance_binding(
        checks,
        logicals,
        max_weight=cutoff,
        sector=sector,
        encoding=encoding,
        solver_name="fixture-solver",
        checkpoint_identity=identity,
        partition_index=partition,
        anchor_indices=(),
    )
    instance["native_thread_environment"] = (
        distance_sat.enforce_sat_native_thread_budget()
    )
    instance["binding_sha256"] = eq.canonical_sha256({
        key: value for key, value in instance.items() if key != "binding_sha256"
    })
    sat = outcome == "sat"
    evidence = {
        "schema_version": distance_sat.SAT_EVIDENCE_SCHEMA_VERSION,
        "evidence_kind": distance_sat.SAT_EVIDENCE_KIND,
        "formulation": distance_sat.SAT_FORMULATION,
        "instance": instance,
        "sector": sector,
        "max_weight": cutoff,
        "cardinality_encoding": encoding,
        "backend": instance["backend"],
        "partition_index": partition,
        "anchor_indices": [],
        "zero_anchor_indices": [],
        "one_anchor_index": None,
        "anchor_cube_sha256": None,
        "outcome": outcome,
        "decision_complete": True,
        "threshold_infeasible": not sat,
        "success": sat,
        "operator": {"fixture": True} if sat else None,
        "objective": objective if sat else None,
    }
    return _seal_evidence(evidence)


def _timeout() -> dict[str, Any]:
    return _seal_evidence({
        "outcome": "hard_timeout",
        "decision_complete": False,
        "threshold_infeasible": False,
        "success": False,
        "operator": None,
        "objective": None,
    })


def _mock_exactification_input(monkeypatch: pytest.MonkeyPatch) -> None:
    hx = np.zeros((1, 3), dtype=np.uint8)
    hz = np.zeros((1, 3), dtype=np.uint8)
    lx = np.asarray([[1, 0, 0], [0, 1, 0]], dtype=np.uint8)
    lz = np.asarray([[0, 1, 0], [0, 0, 1]], dtype=np.uint8)
    monkeypatch.setattr(
        eq,
        "_load_job_input",
        lambda job, replay_loader: (
            {"canonical_digest": job["job_id"]},
            (hx, hz, lx, lz),
            5,
            {"kind": "fixture-upper", "objective": 5},
        ),
    )
    import evaluation.distance_sat as distance_sat

    monkeypatch.setattr(
        distance_sat,
        "verify_css_threshold_sat_witness",
        lambda evidence, checks, logicals: [],
    )


def test_queue_tampering_and_nested_config_fail_closed(tmp_path: Path) -> None:
    paths, _ = _install_queue(tmp_path)
    valid = eq.validate_queue(paths.queue)
    tampered = copy.deepcopy(valid)
    tampered["jobs"][0]["state"] = eq.EXACT_DISTANCE_PROVEN
    with pytest.raises(ValueError, match="queue seal"):
        eq.validate_queue(tampered)

    tampered = copy.deepcopy(valid)
    tampered["jobs"][0]["state"] = eq.EXACT_DISTANCE_PROVEN
    tampered = eq._seal_queue(tampered)
    with pytest.raises(ValueError, match="job seal"):
        eq.validate_queue(tampered)

    config = eq.QueueConfig.from_json({
        "kind": "fixture",
        "queue": {"top_k": 7, "termination_grace_s": 17.0},
        "resources": {"slots": 2},
    })
    assert config.top_k == 7
    assert config.termination_grace_s == 17.0


def test_stale_claim_reuses_proof_identity_after_crash(tmp_path: Path) -> None:
    paths, _ = _install_queue(tmp_path)
    config = eq.QueueConfig(stale_after_s=10.0)
    first = eq.claim_next_job(
        paths, worker_id="dead-worker", config=config, now=0.0,
    )
    assert first is not None
    assert eq.claim_next_job(
        paths, worker_id="early-worker", config=config, now=9.9,
    ) is None
    recovered = eq.claim_next_job(
        paths, worker_id="replacement-worker", config=config, now=10.0,
    )
    assert recovered is not None
    assert recovered["attempts"] == 2
    assert recovered["proof_job_sha256"] == first["proof_job_sha256"]


def test_sat_tightens_then_independent_unsat_passes_prove_exact(
    tmp_path: Path,
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    config = eq.QueueConfig(
        timeout_s=11.0,
        verification_timeout_s=13.0,
        termination_grace_s=17.0,
    )
    paths, claimed = _claimed_queue(tmp_path, config)
    _mock_exactification_input(monkeypatch)
    calls: list[dict[str, Any]] = []

    def solve(*args: Any, **kwargs: Any) -> dict[str, Any]:
        calls.append(kwargs)
        if len(calls) == 1:
            return _terminal_evidence(args, kwargs, outcome="sat", objective=3)
        return _terminal_evidence(args, kwargs, outcome="unsat")

    result = eq.exactify_job(
        claimed, paths=paths, config=config, solve_fn=solve, now=100.0,
    )
    assert result["status"] == eq.EXACT_DISTANCE_PROVEN
    assert result["exact_distance"] == 3
    assert result["bounds"] == {"lower": 3, "upper": 3}
    assert len(calls) == 9
    assert calls[0]["max_weight"] == 4
    assert all(call["max_weight"] == 2 for call in calls[1:])
    assert {call["checkpoint_identity"]["pass"] for call in calls[1:]} == {
        "build", "verify",
    }
    assert all(call["termination_grace_s"] == 17.0 for call in calls)
    assert result["job_sha256"] == claimed["proof_job_sha256"]
    completed = eq.complete_job(
        paths,
        job_id=claimed["job_id"],
        worker_id="worker-1",
        result=result,
        now=101.0,
    )
    assert completed["jobs"][0]["state"] == eq.EXACT_DISTANCE_PROVEN



def test_all_unsat_uses_distinct_build_and_verification_instances(
    tmp_path: Path,
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    paths, claimed = _claimed_queue(tmp_path)
    _mock_exactification_input(monkeypatch)
    identities: list[dict[str, Any]] = []

    def solve(*args: Any, **kwargs: Any) -> dict[str, Any]:
        identities.append(kwargs["checkpoint_identity"])
        return _terminal_evidence(args, kwargs, outcome="unsat")

    result = eq.exactify_job(
        claimed, paths=paths, solve_fn=solve, now=100.0,
    )
    assert result["status"] == eq.EXACT_DISTANCE_PROVEN
    assert result["exact_distance"] == 5
    assert len(identities) == 8
    build = {
        (item["sector"], item["partition_index"])
        for item in identities if item["pass"] == "build"
    }
    verify = {
        (item["sector"], item["partition_index"])
        for item in identities if item["pass"] == "verify"
    }
    expected = {("X", 0), ("X", 1), ("Z", 0), ("Z", 1)}
    assert build == verify == expected
    assert all("policy_sha256" in item for item in identities)


def test_resealed_unsat_for_wrong_instance_is_error(
    tmp_path: Path,
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    paths, claimed = _claimed_queue(tmp_path)
    _mock_exactification_input(monkeypatch)

    def solve(*args: Any, **kwargs: Any) -> dict[str, Any]:
        evidence = _terminal_evidence(args, kwargs, outcome="unsat")
        evidence["instance"]["partition_index"] = 999
        evidence["evidence_sha256"] = eq.canonical_sha256({
            key: value for key, value in evidence.items()
            if key != "evidence_sha256"
        })
        return evidence

    result = eq.exactify_job(
        claimed, paths=paths, solve_fn=solve, now=100.0,
    )
    assert result["status"] == eq.ERROR
    assert "requested unit" in result["reason"]


def test_timeout_is_incomplete_and_retains_bounds(
    tmp_path: Path,
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    paths, claimed = _claimed_queue(tmp_path)
    _mock_exactification_input(monkeypatch)
    result = eq.exactify_job(
        claimed,
        paths=paths,
        solve_fn=lambda *args, **kwargs: _timeout(),
        now=100.0,
    )
    assert result["status"] == eq.INCOMPLETE
    assert result["exact_distance"] is None
    assert result["bounds"] == {"lower": 1, "upper": 5}
    assert "hard_timeout" in result["reason"]


def test_discovery_authenticates_rows_and_replays_boundary_ties_only(
    tmp_path: Path,
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    state_dir = tmp_path / "stage2"
    xor_dir = state_dir / "xor"
    xor_dir.mkdir(parents=True)
    scores = [10, 9, 9, 8]
    digests = [f"{index:064x}" for index in range(1, 5)]
    completed = {
        digest: {
            "sequence": 0,
            "ack_sha256": "a" * 64,
            "page_sha256": "b" * 64,
        }
        for digest in digests
    }
    rows: dict[str, dict[str, Any]] = {}
    for digest, score in zip(digests, scores):
        candidate = {"canonical_digest": digest, "n": 1, "k": 1}
        rows[digest] = {"candidate": candidate}
        (xor_dir / f"{digest}.json").write_text(json.dumps({
            "candidate": candidate,
            "sectors": [{"operator": {}, "objective": score}],
        }))

    fake_snapshot = object()
    monkeypatch.setattr(
        eq,
        "_validated_stage2_source",
        lambda path: (
            {"cursor": 4},
            fake_snapshot,
            {"source": {}, "completed": completed},
        ),
    )
    monkeypatch.setattr(
        eq,
        "_scan_snapshot_prefix",
        lambda snapshot, cursor, wanted: {
            digest: rows[digest] for digest in wanted
        },
    )
    helpers = (
        lambda row, digest: row["candidate"],
        None,
        None,
        lambda digest: digest,
        None,
        None,
        None,
        None,
    )
    monkeypatch.setattr(eq, "_audit_helpers", lambda: helpers)
    replayed: list[str] = []

    def replay(item: dict[str, Any], *, replay_loader: Any) -> dict[str, Any]:
        replayed.append(item["canonical_digest"])
        score = int(item["advisory_upper_bound"])
        result = _queue_item(item["canonical_digest"])
        result["selection_ack"] = item["selection_ack"]
        result["score"] = {
            "numerator": score * score,
            "denominator": 1,
            "decimal": float(score * score),
        }
        result["input_sha256"] = eq.canonical_sha256(result)
        return result

    monkeypatch.setattr(eq, "_full_replay_advisory", replay)
    source, jobs = eq._discover_jobs(
        ledger_path=tmp_path / "ledger.json",
        stage2_state_dir=state_dir,
        config=eq.QueueConfig(top_k=2),
        replay_loader=None,
    )
    assert replayed == digests[:3]
    assert [job["canonical_digest"] for job in jobs] == digests[:3]
    assert source["replay_attempts"] == 3


def test_worker_refreshes_only_after_queue_is_empty(
    tmp_path: Path,
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    paths, _ = _install_queue(tmp_path)
    events: list[str] = []
    monkeypatch.setattr(
        eq,
        "exactify_job",
        lambda job, **kwargs: events.append("run") or eq._seal_result({
            "schema_version": eq.QUEUE_SCHEMA_VERSION,
            "gate": eq.RESULT_GATE,
            "status": eq.INCOMPLETE,
            "job_id": job["job_id"],
            "canonical_digest": job["canonical_digest"],
            "input_sha256": job["input_sha256"],
            "job_sha256": job["proof_job_sha256"],
            "attempt": job["attempts"],
            "claim_worker_id": job["claimed_by"],
            "claim_token": job["claim_token"],
            "proof_policy": kwargs["config"].as_dict(),
            "policy_sha256": eq.canonical_sha256(kwargs["config"].as_dict()),
            "exactifier_source_sha256": eq._source_sha256(),
        }),
    )
    eq.worker_loop(
        paths=paths,
        once=True,
        refresh_callback=lambda: events.append("refresh"),
    )
    assert events == ["run"]



def _result_for(
    job: dict[str, Any],
    *,
    status: str = eq.INCOMPLETE,
    reason: str = "fixture",
) -> dict[str, Any]:
    policy = dict(job["proof_policy"])
    return eq._seal_result({
        "schema_version": eq.QUEUE_SCHEMA_VERSION,
        "gate": eq.RESULT_GATE,
        "status": status,
        "job_id": job["job_id"],
        "canonical_digest": job["canonical_digest"],
        "input_sha256": job["input_sha256"],
        "job_sha256": job["proof_job_sha256"],
        "attempt": job["attempts"],
        "claim_worker_id": job["claimed_by"],
        "claim_token": job["claim_token"],
        "proof_policy": policy,
        "policy_sha256": eq.canonical_sha256(policy),
        "exactifier_source_sha256": eq._source_sha256(),
        "reason": reason,
    })


def test_stale_worker_completion_cannot_replace_current_claim(
    tmp_path: Path,
) -> None:
    config = eq.QueueConfig(stale_after_s=10.0, retry_backoff_s=1.0)
    paths, _ = _install_queue(tmp_path, config)
    stale = eq.claim_next_job(
        paths, worker_id="stale-worker", config=config, now=0.0,
    )
    assert stale is not None
    current = eq.claim_next_job(
        paths, worker_id="current-worker", config=config, now=10.0,
    )
    assert current is not None
    stale_result = _result_for(stale)
    with pytest.raises(ValueError, match="lost its live claim"):
        eq.complete_job(
            paths,
            job_id=stale["job_id"],
            worker_id="stale-worker",
            result=stale_result,
            now=11.0,
        )
    live = eq.validate_queue(paths.queue)["jobs"][0]
    assert live["claimed_by"] == "current-worker"
    assert live["attempts"] == 2
    assert live["result_path"] is None
    stale_paths = list((paths.results / "stale" / DIGEST).glob("*.json"))
    assert len(stale_paths) == 1
    assert not list((paths.results / "accepted" / DIGEST).glob("*.json"))

    current_result = _result_for(current)
    completed = eq.complete_job(
        paths,
        job_id=current["job_id"],
        worker_id="current-worker",
        result=current_result,
        now=12.0,
    )
    finished = completed["jobs"][0]
    assert finished["state"] == eq.INCOMPLETE
    assert finished["next_attempt_at"] == 14.0
    assert Path(finished["result_path"]).name.endswith(".json")
    assert Path(finished["result_path"]).parent.parent.name == "accepted"


def test_claim_policy_mismatch_is_rejected(tmp_path: Path) -> None:
    first_config = eq.QueueConfig(timeout_s=11.0)
    paths, claimed = _claimed_queue(tmp_path, first_config)
    with pytest.raises(ValueError, match="claimed proof policy"):
        eq.exactify_job(
            claimed,
            paths=paths,
            config=eq.QueueConfig(timeout_s=12.0),
            solve_fn=lambda *args, **kwargs: _timeout(),
        )


def test_attempts_first_and_backoff_prevent_rank_one_starvation(
    tmp_path: Path,
) -> None:
    config = eq.QueueConfig(retry_backoff_s=10.0, retry_backoff_max_s=100.0)
    paths = eq.queue_paths(tmp_path)
    eq._ensure_paths(paths)
    first = eq._new_job(_queue_item("1" * 64), rank=1, now=0.0)
    second_item = _queue_item("2" * 64)
    second_item["input_sha256"] = "3" * 64
    second = eq._new_job(second_item, rank=2, now=0.0)
    queue = eq._seal_queue({
        "schema_version": eq.QUEUE_SCHEMA_VERSION,
        "gate": eq.QUEUE_GATE,
        "revision": 0,
        "created_at": 0.0,
        "updated_at": 0.0,
        "producer": {"source_sha256": "4" * 64},
        "source": {},
        "config": config.as_dict(),
        "jobs": [first, second],
    })
    eq._atomic_write_json(paths.queue, queue)
    claimed_first = eq.claim_next_job(
        paths, worker_id="worker-1", config=config, now=0.0,
    )
    assert claimed_first is not None and claimed_first["rank"] == 1
    eq.complete_job(
        paths,
        job_id=claimed_first["job_id"],
        worker_id="worker-1",
        result=_result_for(claimed_first),
        now=1.0,
    )
    claimed_second = eq.claim_next_job(
        paths, worker_id="worker-2", config=config, now=1.0,
    )
    assert claimed_second is not None and claimed_second["rank"] == 2


def test_refresh_reentry_and_source_rollback_are_fail_closed(
    tmp_path: Path,
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    run_root = tmp_path / "run"
    ledger = tmp_path / "ledger.json"
    stage2 = tmp_path / "stage2"
    stage2.mkdir()
    config = eq.QueueConfig()
    item = _queue_item()
    state = {"position": 1, "items": [item]}

    def discover(**kwargs: Any) -> tuple[dict[str, Any], list[dict[str, Any]]]:
        position = int(state["position"])
        source = {
            "ledger_path": str(ledger.resolve()),
            "ledger_stat": eq._stat_identity(ledger.lstat()),
            "stage2_state_dir": str(stage2.resolve()),
            "ledger_generation": 0,
            "ledger_completed_pages": position,
            "ledger_cursor": position,
            "ledger_last_ack_sha256": f"{position:064x}",
            "ledger_progress_sha256": f"{position + 10:064x}",
        }
        return source, list(state["items"])

    monkeypatch.setattr(eq, "_discover_jobs", discover)
    ledger.write_text("one")
    first = eq.refresh_queue(
        ledger_path=ledger,
        stage2_state_dir=stage2,
        run_root=run_root,
        config=config,
    )
    assert first["jobs"][0]["state"] == eq.PENDING

    state.update(position=2, items=[])
    ledger.write_text("two-two")
    retired = eq.refresh_queue(
        ledger_path=ledger,
        stage2_state_dir=stage2,
        run_root=run_root,
        config=config,
    )
    assert retired["jobs"][0]["state"] == eq.RETIRED

    state.update(position=3, items=[item])
    ledger.write_text("three-three-three")
    restored = eq.refresh_queue(
        ledger_path=ledger,
        stage2_state_dir=stage2,
        run_root=run_root,
        config=config,
    )
    assert restored["jobs"][0]["active"] is True
    assert restored["jobs"][0]["state"] == eq.PENDING
    assert eq.claim_next_job(
        eq.queue_paths(run_root), worker_id="worker", config=config,
    ) is not None

    state.update(position=2, items=[item])
    ledger.write_text("rollback-attempt")
    with pytest.raises(ValueError, match="roll Stage 2 progress back"):
        eq.refresh_queue(
            ledger_path=ledger,
            stage2_state_dir=stage2,
            run_root=run_root,
            config=config,
        )
    persisted = eq.validate_queue(eq.queue_paths(run_root).queue)
    assert persisted["source"]["ledger_completed_pages"] == 3



def test_claim_heartbeat_fences_attempt_and_token(tmp_path: Path) -> None:
    paths, claimed = _claimed_queue(tmp_path)
    for attempt, token in (
        (claimed["attempts"] + 1, claimed["claim_token"]),
        (claimed["attempts"], "0" * 64),
    ):
        with pytest.raises(ValueError, match="claim was lost"):
            eq._update_claim(
                paths,
                job_id=claimed["job_id"],
                worker_id=claimed["claimed_by"],
                attempt=attempt,
                claim_token=token,
                now=10.0,
            )
    live = eq.validate_queue(paths.queue)["jobs"][0]
    assert live["attempts"] == claimed["attempts"]
    assert live["claim_token"] == claimed["claim_token"]
    assert live["heartbeat_at"] == claimed["heartbeat_at"]


def test_verification_sat_is_a_fail_closed_contradiction(
    tmp_path: Path,
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    paths, claimed = _claimed_queue(tmp_path)
    _mock_exactification_input(monkeypatch)
    calls = 0

    def solve(*args: Any, **kwargs: Any) -> dict[str, Any]:
        nonlocal calls
        calls += 1
        if calls == 5:
            return _terminal_evidence(args, kwargs, outcome="sat", objective=4)
        return _terminal_evidence(args, kwargs, outcome="unsat")

    result = eq.exactify_job(
        claimed, paths=paths, solve_fn=solve, now=100.0,
    )
    assert result["status"] == eq.ERROR
    assert "contradicts the build UNSAT pass" in result["reason"]
    assert result["exact_distance"] is None
    assert result["iterations"][-1]["verification_contradiction"] == {
        "sector": "X",
        "partition_index": 0,
        "witness_evidence_sha256": result["iterations"][-1]["passes"]["verify"][0]["evidence_sha256"],
    }
    statuses = {
        json.loads(path.read_text())["status"]
        for path in (paths.results / "provisional" / DIGEST).glob("*.json")
    }
    assert statuses == {eq.LOWER_BOUND_PROVEN, eq.ERROR}


def test_source_change_between_units_aborts_without_result(
    tmp_path: Path,
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    paths, claimed = _claimed_queue(tmp_path)
    _mock_exactification_input(monkeypatch)
    checks = 0
    solver_calls = 0

    def guard() -> None:
        nonlocal checks
        checks += 1
        if checks > 2:
            raise RuntimeError("exactifier source changed after module import")

    def solve(*args: Any, **kwargs: Any) -> dict[str, Any]:
        nonlocal solver_calls
        solver_calls += 1
        return _terminal_evidence(args, kwargs, outcome="unsat")

    monkeypatch.setattr(eq, "_assert_source_unchanged", guard)
    with pytest.raises(RuntimeError, match="source changed"):
        eq.exactify_job(
            claimed, paths=paths, solve_fn=solve, now=100.0,
        )
    assert solver_calls == 1
    assert not list((paths.results / "provisional" / DIGEST).glob("*.json"))
