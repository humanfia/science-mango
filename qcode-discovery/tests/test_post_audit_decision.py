"""Replay and fail-closed tests for the post-R4 experiment decision."""

from __future__ import annotations

import copy
import hashlib
import json
from pathlib import Path

import pytest

from humanize.audit_state import AuditOutcome
from humanize.post_audit_decision import (
    DEFAULT_BROADER_DESIGN,
    DEFAULT_LADDER_DESIGN,
    PostAuditDecisionError,
    PostAuditDecisionNotReady,
    _canonical_sha256,
    build_post_r4_decision,
    main,
)
from humanize.state import code_key


PROJECT = Path(__file__).resolve().parents[1]
SOURCE_RUN_ID = "post-r4-source-fixture"


def _json_bytes(value: object) -> bytes:
    return (json.dumps(value, ensure_ascii=False, indent=2) + "\n").encode()


def _jsonl_bytes(rows: list[dict]) -> bytes:
    return b"".join(
        (json.dumps(row, ensure_ascii=False) + "\n").encode() for row in rows
    )


def _write(path: Path, payload: bytes) -> None:
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_bytes(payload)


def _identity(payload: bytes, *, rows: int | None = None) -> dict:
    value = {
        "sha256": hashlib.sha256(payload).hexdigest(),
        "bytes": len(payload),
    }
    if rows is not None:
        value["rows"] = rows
    return value


def _candidate(tag: int, *, lower_bound: bool, upper_bound: int) -> dict:
    row = {
        "ell": 64,
        "m": 64,
        "A_terms": [[tag, 0], [tag + 1, 1]],
        "B_terms": [[0, tag + 2], [1, tag + 3]],
        "n": 128,
        "k": 16,
        "winner_capable_parameters": True,
        "_fixture_upper_bound": upper_bound,
    }
    if lower_bound:
        row.update({
            "distance_lower_bound": 5,
            "distance_lower_bound_proven": True,
            "distance_lower_bound_status": "search_oracle_proven",
        })
    else:
        row["candidate_persistence_lane"] = (
            "winner_capable_quick_exploration"
        )
    return row


def _audit(selected: dict, *, round_number: int) -> dict:
    row = copy.deepcopy(selected)
    row.update({
        "candidate_key": code_key(selected),
        "threshold_proof_distance": selected["_fixture_upper_bound"],
        "audit_attempt": {
            "schema_version": 2,
            "round": round_number,
            "evidence": {"fixture": True},
        },
        "_fixture_outcome": AuditOutcome.THRESHOLD_REJECTED.value,
    })
    return row


def _review(round_number: int) -> dict:
    return {
        "schema_version": 2,
        "verdict": "continue",
        "summary": f"Advisory review for round {round_number}.",
        "risks": [],
        "recommended_focus": ["Continue the bounded diagnostic."],
        "lessons": [],
        "search_action": {
            "schema_version": 1,
            "advisory_only": True,
            "intent": "maintain",
            "horizon_rounds": 1,
            "focus": [],
            "evidence_refs": [],
            "rationale": "The action is advisory and does not vote on the machine gate.",
        },
    }


def _copy_next_artifacts(repo: Path) -> tuple[Path, Path]:
    broader = repo / DEFAULT_BROADER_DESIGN
    ladder = repo / DEFAULT_LADDER_DESIGN
    _write(broader, (PROJECT / DEFAULT_BROADER_DESIGN).read_bytes())
    _write(ladder, (PROJECT / DEFAULT_LADDER_DESIGN).read_bytes())
    return broader, ladder


def _fake_digest(row: dict) -> str:
    return hashlib.sha256(code_key(row).encode()).hexdigest()


def _fake_lower_bound(row: dict) -> int | None:
    if row.get("distance_lower_bound_proven") is True:
        return row.get("distance_lower_bound")
    return None


def _fake_classifier(row: dict) -> AuditOutcome:
    return AuditOutcome(row["_fixture_outcome"])


def _fake_checkpoint(
    _output: Path,
    checkpoint: Path,
    expected_iteration: int | None,
) -> dict:
    assert expected_iteration is not None
    return {
        "path": str(checkpoint),
        "last_iteration": expected_iteration,
        "sha256": hashlib.sha256(str(checkpoint).encode()).hexdigest(),
        "programs": expected_iteration,
    }


def _fixture(
    tmp_path: Path,
    *,
    low_upper_bound_count: int,
) -> tuple[Path, Path, Path, Path]:
    repo = tmp_path / "repo"
    run_root = repo / "results" / "humanize" / SOURCE_RUN_ID
    evolution = repo / "results" / "evolution" / SOURCE_RUN_ID
    source_path = evolution / "all_codes.jsonl"
    source_payload = b""
    summaries: list[dict] = []
    previous_result = None
    low_remaining = low_upper_bound_count

    for round_number in range(1, 5):
        round_dir = run_root / "rounds" / f"round-{round_number:03d}"
        selected: list[dict] = []
        for offset in range(5):
            low = low_remaining > 0
            if low:
                low_remaining -= 1
            selected.append(
                _candidate(
                    round_number * 100 + offset,
                    lower_bound=True,
                    upper_bound=8 if low else 10,
                )
            )
        selected.append(
            _candidate(
                round_number * 100 + 99,
                lower_bound=False,
                upper_bound=4,
            )
        )
        audited = [
            _audit(row, round_number=round_number) for row in selected
        ]
        selected_payload = _jsonl_bytes(selected)
        milp_payload = _jsonl_bytes(audited)
        _write(round_dir / "selected.jsonl", selected_payload)
        _write(round_dir / "milp.jsonl", milp_payload)

        batch_payload = selected_payload
        start = len(source_payload)
        source_payload += batch_payload
        end = len(source_payload)
        _write(round_dir / "candidate-batch.jsonl", batch_payload)
        marker_payload = _json_bytes({"round": round_number, "status": "completed"})
        witness_payload = _json_bytes({"round": round_number, "status": "sealed"})
        marker_path = round_dir / "openevolve-completed.json"
        witness_path = round_dir / "openevolve-slice-witness.json"
        _write(marker_path, marker_payload)
        _write(witness_path, witness_payload)

        checkpoint = evolution / "checkpoints" / f"checkpoint_{round_number * 25}"
        checkpoint.mkdir(parents=True, exist_ok=True)
        result = _fake_checkpoint(
            evolution,
            checkpoint,
            round_number * 25,
        )
        transaction = {
            "schema_version": 3,
            "protocol_version": 3,
            "run_id": SOURCE_RUN_ID,
            "round": round_number,
            "mode": "openevolve",
            "status": "committed",
            "candidate_batch_policy_version": 6,
            "committed_at": f"2026-08-12T0{round_number}:00:00+00:00",
            "candidate_batch": str(round_dir / "candidate-batch.jsonl"),
            "candidate_batch_identity": _identity(batch_payload, rows=6),
            "candidate_start_offset": start,
            "candidate_end_offset": end,
            "candidate_source_sha256": hashlib.sha256(batch_payload).hexdigest(),
            "candidate_source_rows": 6,
            "candidate_log": str(source_path),
            "completion_marker": str(marker_path),
            "completion_marker_sha256": hashlib.sha256(marker_payload).hexdigest(),
            "completion_witness": str(witness_path),
            "completion_witness_sha256": hashlib.sha256(witness_payload).hexdigest(),
            "base_checkpoint": previous_result,
            "expected_result_iteration": round_number * 25,
            "result_checkpoint": result,
        }
        _write(
            round_dir / "evolution-transaction.json",
            _json_bytes(transaction),
        )
        previous_result = result

        review = _review(round_number)
        review_payload = _json_bytes(review)
        _write(round_dir / "review.json", review_payload)
        milp_identity = _identity(milp_payload, rows=6)
        summaries.append({
            "round": round_number,
            "milp_audited": 6,
            "review_verdict": review["verdict"],
            "review_summary": review["summary"],
            "review_binding": {
                "schema_version": 1,
                "artifact_sha256": hashlib.sha256(review_payload).hexdigest(),
                "artifact_bytes": len(review_payload),
                "review_schema_version": 2,
                "search_action": copy.deepcopy(review["search_action"]),
            },
            "sealed_exact_audit": {
                "schema_version": 1,
                "basis": "sealed-formal-audit-attempts",
                "source_milp_sha256": milp_identity["sha256"],
                "source_milp_bytes": milp_identity["bytes"],
                "source_milp_rows": milp_identity["rows"],
                "exact_count": 0,
                "exact_distances": [],
            },
            "failure_direction_feedback": {
                "source_milp_sha256": milp_identity["sha256"],
                "source_milp_bytes": milp_identity["bytes"],
                "source_milp_rows": milp_identity["rows"],
            },
        })

    _write(source_path, source_payload)
    state = {
        "schema_version": 1,
        "run_id": SOURCE_RUN_ID,
        "status": "running",
        "current_round": 4,
        "round_transaction_version": 3,
        "config": {
            "target_mode": "scalar-fom-strict-v1",
            "model": "gpt-5.6-sol",
            "reasoning_effort": "xhigh",
            "search_representation_id": "css-bb-twisted-torus-generator-v1",
            "milp_top": 6,
        },
        "rounds": summaries,
    }
    _write(run_root / "state.json", _json_bytes(state))
    broader, ladder = _copy_next_artifacts(repo)
    return repo, run_root, broader, ladder


def _decide(
    *,
    repo: Path,
    run_root: Path,
    broader: Path,
    ladder: Path,
) -> dict:
    return build_post_r4_decision(
        repo_dir=repo,
        run_root=run_root,
        broader_design=broader,
        ladder_design=ladder,
        classifier=_fake_classifier,
        lower_bound_replayer=_fake_lower_bound,
        digest_authority=_fake_digest,
        checkpoint_authority=_fake_checkpoint,
    )


def test_post_r4_requires_published_volume_coverage_from_low_weight_failures(
    tmp_path: Path,
):
    repo, run_root, broader, ladder = _fixture(
        tmp_path,
        low_upper_bound_count=20,
    )

    decision = _decide(
        repo=repo,
        run_root=run_root,
        broader=broader,
        ladder=ladder,
    )

    assert decision["status"] == "ready"
    assert decision["decision"]["action"] == (
        "broader_published_volume_coverage"
    )
    assert decision["decision"]["reviewer_text_votes"] is False
    assert decision["decision"]["launch_authorized"] is False
    assert decision["metrics"]["selected_audits"] == 24
    assert decision["metrics"]["distinct_candidate_keys"] == 24
    assert decision["metrics"]["distinct_canonical_digests"] == 24
    assert decision["metrics"]["unknown_audits"] == 0
    assert decision["metrics"]["trusted_upper_bound_le_8_rate"] == {
        "numerator": 20,
        "denominator": 20,
    }
    assert decision["next_experiment"]["required_representation_id"] == (
        "css-bb-twisted-torus-published-volume-generator-v2"
    )
    assert decision["next_experiment"]["implementation_status"] == (
        "required_not_installed"
    )
    unsigned = dict(decision)
    observed = unsigned.pop("decision_sha256")
    assert observed == _canonical_sha256(unsigned)


def test_post_r4_selects_only_nonlaunchable_ladder_design_for_survivors(
    tmp_path: Path,
):
    repo, run_root, broader, ladder = _fixture(
        tmp_path,
        low_upper_bound_count=15,
    )

    decision = _decide(
        repo=repo,
        run_root=run_root,
        broader=broader,
        ladder=ladder,
    )

    assert decision["decision"]["action"] == "bounded_ladder"
    assert decision["metrics"]["lb_without_trusted_upper_bound_le_8"] == 5
    assert decision["metrics"]["significant_survivors"] is True
    assert decision["decision"]["launch_authorized"] is False
    assert decision["next_experiment"]["implementation_status"] == "design_only"
    assert decision["next_experiment"]["all_pool_scan_allowed"] is False


def test_post_r4_missing_round_commit_fails_closed(tmp_path: Path):
    repo, run_root, broader, ladder = _fixture(
        tmp_path,
        low_upper_bound_count=20,
    )
    state_path = run_root / "state.json"
    state = json.loads(state_path.read_text())
    state["current_round"] = 3
    state["rounds"] = state["rounds"][:3]
    state_path.write_text(json.dumps(state) + "\n")

    with pytest.raises(PostAuditDecisionNotReady) as raised:
        _decide(
            repo=repo,
            run_root=run_root,
            broader=broader,
            ladder=ladder,
        )

    assert raised.value.code == "ROUND_4_NOT_COMMITTED"


def test_post_r4_milp_tamper_fails_closed(tmp_path: Path):
    repo, run_root, broader, ladder = _fixture(
        tmp_path,
        low_upper_bound_count=20,
    )
    milp = run_root / "rounds" / "round-003" / "milp.jsonl"
    rows = [json.loads(line) for line in milp.read_text().splitlines()]
    rows[0]["threshold_proof_distance"] = 99
    milp.write_bytes(_jsonl_bytes(rows))

    with pytest.raises(PostAuditDecisionError) as raised:
        _decide(
            repo=repo,
            run_root=run_root,
            broader=broader,
            ladder=ladder,
        )

    assert raised.value.code == "ROUND_SUMMARY"


def test_post_r4_cli_writes_nonlaunchable_not_ready_json(tmp_path: Path):
    output = tmp_path / "decision.json"
    code = main([
        "--repo-dir",
        str(PROJECT),
        "--run-root",
        str(tmp_path / "results" / "humanize" / "missing-source-run"),
        "--output",
        str(output),
    ])

    assert code == 3
    blocked = json.loads(output.read_text())
    assert blocked["status"] == "not_ready"
    assert blocked["decision"]["action"] == "none"
    assert blocked["decision"]["launch_authorized"] is False


def test_post_r4_next_experiment_designs_are_nonlaunchable_and_bounded():
    broader = json.loads((PROJECT / DEFAULT_BROADER_DESIGN).read_text())
    assert broader["implementation_status"] == "required_not_installed"
    assert broader["launchable"] is False
    assert broader["required_representation_id"] == (
        "css-bb-twisted-torus-published-volume-generator-v2"
    )
    assert broader["excluded_aliases"] == [
        "css-bb-cover-algebra-generator-v2",
        "css-bb-novel-ansatz-generator-v2",
    ]

    design = json.loads((PROJECT / DEFAULT_LADDER_DESIGN).read_text())
    assert design["implementation_status"] == "design_only"
    assert design["launchable"] is False
    assert design["all_pool_scan_allowed"] is False
    assert design["thresholds"] == [6, 8, "required_distance_minus_1"]
