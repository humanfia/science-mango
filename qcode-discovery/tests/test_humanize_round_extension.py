"""End-to-end coverage for monotonic Humanize round extensions."""

from __future__ import annotations

import json
from pathlib import Path

import pytest

from humanize.flow import FlowConfig, HumanizeFlow, UnresolvedAuditError
from humanize.reviewer import validate_review


def _candidate() -> dict:
    return {
        "ell": 6,
        "m": 6,
        "n": 72,
        "k": 8,
        "d": 6,
        "fom": 6.0,
        "score": 6.0,
        "stage": "refined_estimate",
        "A_terms": [[0, 0], [0, 1], [1, 0]],
        "B_terms": [[0, 0], [0, 2], [2, 0]],
        "pattern_type": "swap",
        "term_count": 6,
    }


class _ContinueReviewer:
    def review(self, _prompt, _round_dir):
        return validate_review({
            "verdict": "continue",
            "summary": "Continue until every MILP audit is terminal.",
            "risks": [],
            "recommended_focus": [],
            "lessons": [],
        })


class _UnresolvedThenExact:
    def __init__(self) -> None:
        self.calls: list[dict] = []

    def __call__(self, row, config, **invocation):
        checkpoint = Path(invocation["checkpoint_path"])
        self.calls.append({
            "checkpoint": str(checkpoint),
            "resume": invocation["resume"],
            "soft": config.milp_timeout_per_logical,
            "total": config.milp_total_timeout,
            "hard": invocation["hard_timeout_per_logical"],
        })
        checkpoint.write_text(
            json.dumps({"fake_attempts": len(self.calls)}) + "\n"
        )

        if len(self.calls) == 1:
            result = dict(row)
            result.update({
                "stage": "milp_timeout_no_incumbent",
                "d_is_exact": False,
                "distance_status": "unknown_no_incumbent",
                "milp_details": {
                    "exact": False,
                    "all_timeout": True,
                    "no_incumbent": True,
                    "checkpoint_path": str(checkpoint),
                },
            })
        else:
            from evaluation.evaluator import evaluate_candidate_milp
            from evaluation.final_gate import FOM_THRESHOLD

            result = evaluate_candidate_milp(
                int(row["ell"]),
                int(row["m"]),
                [tuple(term) for term in row["A_terms"]],
                [tuple(term) for term in row["B_terms"]],
                milp_timeout_per_logical=config.milp_timeout_per_logical,
                milp_total_timeout=config.milp_total_timeout,
                milp_target_fom=FOM_THRESHOLD,
                milp_checkpoint_path=checkpoint,
                milp_resume=invocation["resume"],
                milp_hard_timeout_per_logical=invocation[
                    "hard_timeout_per_logical"
                ],
            )
        return result


def test_exhausted_unresolved_run_resumes_after_monotonic_round_extension(
    tmp_path,
):
    repo = tmp_path / "repo"
    repo.mkdir()
    source = repo / "candidates.jsonl"
    source.write_text(json.dumps(_candidate()) + "\n")
    run_id = "extend-unresolved"
    evaluator = _UnresolvedThenExact()
    base = dict(
        repo_dir=repo,
        run_id=run_id,
        milp_top=1,
        candidate_file=source,
        allow_debug_audit_evaluator=True,
    )

    first = HumanizeFlow(
        FlowConfig(**base, max_rounds=1),
        reviewer=_ContinueReviewer(),
        milp_evaluator=evaluator,
    )
    with pytest.raises(UnresolvedAuditError, match="exhausted max_rounds"):
        first.run()

    state_path = first.store.state_path
    exhausted = json.loads(state_path.read_text())
    assert exhausted["status"] == "incomplete-unresolved"
    assert exhausted["current_round"] == 1
    assert exhausted["config"]["max_rounds"] == 1
    assert len(exhausted["unresolved_candidates"]) == 1

    second = HumanizeFlow(
        FlowConfig(**base, max_rounds=2),
        reviewer=_ContinueReviewer(),
        milp_evaluator=evaluator,
    )
    completed = second.run()

    assert completed["status"] == "search-complete"
    assert completed["current_round"] == 2
    assert completed["unresolved_candidates"] == {}
    assert len(evaluator.calls) == 2
    assert evaluator.calls[0]["checkpoint"] == evaluator.calls[1]["checkpoint"]
    assert evaluator.calls[0]["resume"] is True
    assert evaluator.calls[1]["resume"] is True
    assert [call["soft"] for call in evaluator.calls] == [300, 600]
    assert [call["total"] for call in evaluator.calls] == [7200, 14400]
    assert [call["hard"] for call in evaluator.calls] == [330.0, 660.0]

    evaluations = [
        json.loads(line)
        for line in second.evaluations_path.read_text().splitlines()
    ]
    assert [row["audit_attempt"]["round"] for row in evaluations] == [1, 2]
    assert [row["audit_attempt"]["attempt"] for row in evaluations] == [1, 2]
    assert [row["audit_attempt"]["multiplier"] for row in evaluations] == [1, 2]
    assert [row["audit_attempt"]["schema_version"] for row in evaluations] == [
        1,
        2,
    ]
    assert "evidence" in evaluations[1]["audit_attempt"]
    assert len({
        row["audit_attempt"]["checkpoint"] for row in evaluations
    }) == 1

    durable = json.loads(state_path.read_text())
    assert durable["config"]["max_rounds"] == 2
    assert len(durable["config_extension_events"]) == 1
    extension = durable["config_extension_events"][0]
    assert isinstance(extension["extended_at"], str)
    assert {
        key: value for key, value in extension.items() if key != "extended_at"
    } == {
        "schema_version": 1,
        "event": "max_rounds_extended",
        "sequence": 1,
        "from_max_rounds": 1,
        "to_max_rounds": 2,
        "current_round": 1,
    }
    events = [
        json.loads(line)
        for line in second.store.events_path.read_text().splitlines()
    ]
    extensions = [
        event for event in events if event["event"] == "max_rounds_extended"
    ]
    assert len(extensions) == 1
    assert extensions[0]["from_max_rounds"] == 1
    assert extensions[0]["to_max_rounds"] == 2
    assert extensions[0]["current_round"] == 1
