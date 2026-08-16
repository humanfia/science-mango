from __future__ import annotations

import copy
import json
from pathlib import Path

import numpy as np
import pytest

from humanize import strict_deep_queue as deep


DIGESTS = ("1" * 64, "2" * 64)


class _FakeCode:
    def __init__(self, candidate: dict[str, object]) -> None:
        self.candidate = candidate
        n, k = int(candidate["n"]), int(candidate["k"])
        self.num_qudits = n
        self.dimension = k


def _matrices(value: dict[str, object] | _FakeCode) -> tuple[np.ndarray, ...]:
    candidate = value.candidate if isinstance(value, _FakeCode) else value
    n, k = int(candidate["n"]), int(candidate["k"])
    hx = np.zeros((1, n), dtype=np.uint8)
    hz = np.zeros((1, n), dtype=np.uint8)
    lx = np.zeros((k, n), dtype=np.uint8)
    lz = np.zeros((k, n), dtype=np.uint8)
    lx[:, :k] = np.eye(k, dtype=np.uint8)
    lz[:, :k] = np.eye(k, dtype=np.uint8)
    return hx, hz, lx, lz


def _candidate(digest: str, *, n: int, required: int) -> dict[str, object]:
    return {
        "canonical_digest": digest,
        "n": n,
        "k": 8,
        "required_distance": required,
        "target_mode": "scalar-fom-strict-v1",
        "target": {
            "mode": "scalar-fom-strict-v1",
            "strict": True,
            "required_distance": required,
            "rejection_cutoff": required - 1,
            "binding_sha256": ("a" if digest == DIGESTS[0] else "b") * 64,
        },
    }


@pytest.fixture()
def initialized(tmp_path: Path, monkeypatch: pytest.MonkeyPatch):
    run_root = tmp_path / "run"
    batch = run_root / "sidecars" / "stage2-strict-discovery-v1" / "batches" / "batch-0000"
    batch.mkdir(parents=True)
    candidates = {
        DIGESTS[0]: _candidate(DIGESTS[0], n=264, required=20),
        DIGESTS[1]: _candidate(DIGESTS[1], n=288, required=21),
    }
    rows = []
    results = []
    for index, digest in enumerate(DIGESTS):
        audit_path = batch / f"audit-{index}.json"
        audit_path.write_text(json.dumps({
            "status": "UNRESOLVED",
            "sectors": [{
                "status_name": "UNKNOWN",
                "threshold_infeasible": False,
                "objective": None,
                "best_objective_bound": 0.0,
            }],
        }))
        rows.append({
            "canonical_digest": digest,
            "campaign_audit": {"status": "UNRESOLVED"},
            "distance_lower_bound_proven": True,
            "distance_lower_bound": 1,
            "distance_upper_bound": 64,
            "distance_lower_bound_status": "AUTHENTICATED_BASELINE",
            "distance_upper_bound_source": "ADVISORY_TEST_BOUND",
        })
        results.append({
            "canonical_digest": digest,
            "status": "UNRESOLVED",
            "audit_path": str(audit_path),
        })
    ranked = batch / "ranked.jsonl"
    ranked.write_text("".join(json.dumps(row) + "\n" for row in rows))
    summary = batch / "summary.json"
    summary.write_text(json.dumps({
        "gate": "qldpc-proof-oriented-candidate-pool",
        "target_mode": "scalar-fom-strict-v1",
        "certified_wins": 0,
        "results": results,
    }))

    import evaluation.distance_milp as distance_milp
    import scripts.audit_direction_pool as audit_pool
    import scripts.screen_frontier_candidate as screen_candidate

    monkeypatch.setattr(
        audit_pool,
        "candidate_from_stage2",
        lambda row, **_kwargs: copy.deepcopy(candidates[row["canonical_digest"]]),
    )
    monkeypatch.setattr(
        screen_candidate,
        "build_candidate_code",
        lambda candidate: _FakeCode(candidate),
    )
    monkeypatch.setattr(distance_milp, "get_code_matrices", _matrices)
    paths = deep.deep_paths(run_root)
    config = deep.DeepConfig()
    queue = deep.initialize_queue(
        paths,
        ranked_input=ranked,
        summary_input=summary,
        expected_digests=DIGESTS,
        config=config,
        now=10.0,
    )
    return paths, config, queue


def _seal_queue(queue: dict[str, object]) -> dict[str, object]:
    return deep._seal_queue(queue)


def _terminal_ref(*, objective: int | None = None) -> dict[str, object]:
    return {
        "path": "/immutable/evidence.json",
        "result_sha256": "e" * 64,
        "objective": objective,
        "outcome": "sat" if objective is not None else "unsat",
    }


def _mark_lane(queue: dict[str, object], candidate_index: int, lane_index: int) -> None:
    lane = queue["candidates"][candidate_index]["lanes"][lane_index]
    for unit in lane["units"]:
        unit["status"] = deep.UNSAT
        unit["evidence"] = _terminal_ref()


def _result_for_claim(claim: dict[str, object], status: str, *, objective=None, token=None):
    candidate, lane, unit = claim["candidate"], claim["lane"], claim["unit"]
    return deep._seal_result({
        "schema_version": deep.SCHEMA_VERSION,
        "gate": deep.RESULT_GATE,
        "status": status,
        "canonical_digest": candidate["canonical_digest"],
        "lane": {
            "name": lane["name"],
            "solver": lane["solver"],
            "cardinality_encoding": lane["cardinality_encoding"],
        },
        "sector": unit["sector"],
        "partition_index": unit["partition_index"],
        "cutoff": candidate["cutoff"],
        "slice_index": unit["slice_index"],
        "attempt": unit["attempt"],
        "claim_token": unit["claim_token"] if token is None else token,
        "checkpoint_identity": {},
        "solver_evidence": {"outcome": status.lower()},
        "source_sha256": deep._assert_source_unchanged(),
        "started_at": 1.0,
        "finished_at": 2.0,
        "reason": "test",
        "objective": objective,
    })


def test_initialize_has_two_candidates_four_lanes_and_sixteen_units(initialized):
    _paths, _config, queue = initialized
    assert len(queue["candidates"]) == 2
    for candidate in queue["candidates"]:
        assert len(candidate["lanes"]) == 4
        for lane in candidate["lanes"]:
            assert len(lane["units"]) == 16
            assert {(unit["sector"], unit["partition_index"]) for unit in lane["units"]} == {
                (sector, partition)
                for sector in ("X", "Z")
                for partition in range(8)
            }
    assert all(
        candidate["historical_unknown"]["completed_proof_units"] == 0
        for candidate in queue["candidates"]
    )


def test_config_rejects_duplicate_solver_even_with_enough_other_solvers():
    with pytest.raises(ValueError, match="distinct concrete solver"):
        deep.DeepConfig(
            lanes=(
                deep.LaneSpec("cadical-seq", "cadical195", "seqcounter"),
                deep.LaneSpec("cadical-total", "cadical195", "totalizer"),
                deep.LaneSpec("kissat-km", "kissat404", "kmtotalizer"),
            ),
            required_proof_lanes=2,
        ).validate()


@pytest.mark.parametrize("mutation", ["missing-unit", "single-sector"])
def test_validator_rejects_incomplete_cover(initialized, mutation):
    _paths, _config, queue = initialized
    broken = copy.deepcopy(queue)
    units = broken["candidates"][0]["lanes"][0]["units"]
    if mutation == "missing-unit":
        units.pop()
    else:
        units[:] = [unit for unit in units if unit["sector"] == "X"]
    with pytest.raises(ValueError, match="cover"):
        deep.validate_queue(_seal_queue(broken))


def test_x_from_one_lane_and_z_from_another_cannot_be_combined(initialized):
    _paths, config, queue = initialized
    mixed = copy.deepcopy(queue)
    for unit in mixed["candidates"][0]["lanes"][0]["units"]:
        if unit["sector"] == "X":
            unit["status"] = deep.UNSAT
            unit["evidence"] = _terminal_ref()
    for unit in mixed["candidates"][0]["lanes"][1]["units"]:
        if unit["sector"] == "Z":
            unit["status"] = deep.UNSAT
            unit["evidence"] = _terminal_ref()
    deep._refresh_aggregates(mixed, config)
    candidate = mixed["candidates"][0]
    assert candidate["proven_lanes"] == []
    assert candidate["bounds"]["lower"] == 1
    assert candidate["status"] != deep.PRIMARY_THRESHOLD_PROVEN
    deep.validate_queue(_seal_queue(mixed))


def test_unknown_is_incomplete_and_does_not_raise_lower_bound(initialized):
    paths, _config, _queue = initialized
    claim = deep.claim_units(paths, limit=1, worker_id="worker", now=20.0)[0]
    updated = deep.complete_unit(
        paths,
        worker_id="worker",
        result=_result_for_claim(claim, deep.INCOMPLETE),
        now=21.0,
    )
    candidate = updated["candidates"][0]
    assert candidate["bounds"]["lower"] == 1
    assert candidate["proven_lanes"] == []
    assert candidate["lanes"][0]["units"][0]["status"] == deep.INCOMPLETE


def test_one_complete_lane_is_primary_and_requires_replay(initialized):
    _paths, config, queue = initialized
    value = copy.deepcopy(queue)
    _mark_lane(value, 0, 0)
    deep._refresh_aggregates(value, config)
    candidate = value["candidates"][0]
    assert candidate["status"] == deep.PRIMARY_THRESHOLD_PROVEN
    assert candidate["bounds"]["lower"] == candidate["required_distance"]
    assert candidate["proven_lanes"] == [config.lanes[0].name]
    assert candidate["requires_independent_replay"] is True
    deep.validate_queue(_seal_queue(value))


def test_two_distinct_complete_lanes_are_strict(initialized):
    _paths, config, queue = initialized
    value = copy.deepcopy(queue)
    _mark_lane(value, 0, 0)
    _mark_lane(value, 0, 1)
    deep._refresh_aggregates(value, config)
    candidate = value["candidates"][0]
    assert candidate["status"] == deep.STRICT_THRESHOLD_PROVEN
    assert candidate["proven_lanes"] == [config.lanes[0].name, config.lanes[1].name]
    assert candidate["requires_independent_replay"] is False
    assert value["status"] == deep.STRICT_THRESHOLD_PROVEN
    deep.validate_queue(_seal_queue(value))


def test_verified_sat_witness_rejects_and_tightens_upper(initialized):
    _paths, config, queue = initialized
    value = copy.deepcopy(queue)
    unit = value["candidates"][0]["lanes"][0]["units"][0]
    unit["status"] = deep.SAT
    unit["evidence"] = _terminal_ref(objective=7)
    deep._refresh_aggregates(value, config)
    candidate = value["candidates"][0]
    assert candidate["status"] == deep.WITNESS_REJECTED
    assert candidate["bounds"]["upper"] == 7
    assert candidate["proven_lanes"] == []


def test_stale_claim_token_is_rejected_without_publication(initialized):
    paths, _config, _queue = initialized
    claim = deep.claim_units(paths, limit=1, worker_id="worker", now=20.0)[0]
    before = deep.validate_queue(paths.queue)["queue_sha256"]
    with pytest.raises(ValueError, match="stale"):
        deep.complete_unit(
            paths,
            worker_id="worker",
            result=_result_for_claim(claim, deep.INCOMPLETE, token="wrong-token"),
            now=21.0,
        )
    assert deep.validate_queue(paths.queue)["queue_sha256"] == before
    assert not list(paths.evidence.rglob("*.json"))


def test_complete_rejects_forged_unsat_without_bound_instance(initialized):
    paths, _config, _queue = initialized
    claim = deep.claim_units(paths, limit=1, worker_id="worker", now=20.0)[0]
    before = deep.validate_queue(paths.queue)["queue_sha256"]
    # A canonical result hash is only an integrity seal.  It is not a SAT
    # proof; acceptance must independently bind/replay the embedded evidence.
    forged = _result_for_claim(claim, deep.UNSAT)
    with pytest.raises(ValueError, match="evidence|instance|UNSAT"):
        deep.complete_unit(
            paths, worker_id="worker", result=forged, now=21.0,
        )
    assert deep.validate_queue(paths.queue)["queue_sha256"] == before
    assert not list(paths.evidence.rglob("*.json"))


def test_accepted_evidence_content_tamper_fails_closed(initialized):
    paths, _config, _queue = initialized
    claim = deep.claim_units(paths, limit=1, worker_id="worker", now=20.0)[0]
    queue = deep.complete_unit(
        paths,
        worker_id="worker",
        result=_result_for_claim(claim, deep.INCOMPLETE),
        now=21.0,
    )
    reference = queue["candidates"][0]["lanes"][0]["units"][0]["evidence"]
    evidence_path = Path(reference["path"])
    payload = json.loads(evidence_path.read_text())
    payload["reason"] = "tampered after acceptance"
    evidence_path.write_text(json.dumps(payload))
    with pytest.raises(ValueError, match="result|evidence|seal"):
        deep.validate_queue(paths.queue)


def test_accepted_evidence_path_escape_fails_closed(initialized):
    paths, _config, _queue = initialized
    claim = deep.claim_units(paths, limit=1, worker_id="worker", now=20.0)[0]
    queue = deep.complete_unit(
        paths,
        worker_id="worker",
        result=_result_for_claim(claim, deep.INCOMPLETE),
        now=21.0,
    )
    reference = queue["candidates"][0]["lanes"][0]["units"][0]["evidence"]
    original = Path(reference["path"])
    escaped = paths.root / "escaped-evidence.json"
    escaped.write_bytes(original.read_bytes())
    reference["path"] = str(escaped)
    deep._atomic_write_json(paths.queue, deep._seal_queue(queue))
    with pytest.raises(ValueError, match="escapes accepted root"):
        deep.validate_queue(paths.queue)


def test_crash_recovery_clears_claim_and_retries_same_slice(initialized):
    paths, _config, _queue = initialized
    claims = deep.claim_units(paths, limit=2, worker_id="dead", now=20.0)
    old_tokens = {claim["unit"]["claim_token"] for claim in claims}
    recovered = deep.recover_running_units(paths, now=21.0)
    recovered_units = recovered["candidates"][0]["lanes"][0]["units"][:2]
    assert all(unit["status"] == deep.INCOMPLETE for unit in recovered_units)
    assert all(unit["claim_token"] is None for unit in recovered_units)
    resumed = deep.claim_units(paths, limit=2, worker_id="new", now=22.0)
    assert all(claim["unit"]["slice_index"] == 0 for claim in resumed)
    assert all(claim["unit"]["retry_same_slice"] is False for claim in resumed)
    assert all(claim["unit"]["claim_token"] not in old_tokens for claim in resumed)
