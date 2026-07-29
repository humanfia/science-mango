from __future__ import annotations

import json

import evaluation.final_gate as final_gate_module
import evaluation.structural_dedup as structural_dedup_module
import pytest
from humanize.audit_state import (
    AuditOutcome,
    AuditStateError,
    classify_evaluation,
)
from humanize.flow import FlowConfig, HumanizeFlow, evaluate_with_milp
from humanize.reviewer import validate_review
from humanize.state import archive_cell, code_key


def _write_jsonl(path, rows):
    path.write_text(
        "".join(json.dumps(row) + "\n" for row in rows)
    )


def _identity_structural_screen(monkeypatch):
    monkeypatch.setattr(
        structural_dedup_module,
        "deduplicate_css_results",
        lambda rows: (list(rows), []),
    )


def _map_candidate(*, distance: int, shift: int) -> dict:
    fom = 16 * distance * distance / 360
    return {
        "ell": 18,
        "m": 10,
        "n": 360,
        "k": 16,
        "d": distance,
        "fom": fom,
        "score": fom,
        "stage": "refined_estimate",
        "A_terms": [[0, 0], [0, 1 + shift], [1, 0]],
        "B_terms": [[0, 0], [0, 2 + shift], [2, 0]],
        "pattern_type": "swap",
        "term_count": 6,
    }


def _tiny_exact_candidate() -> dict:
    return {
        "ell": 2,
        "m": 2,
        "n": 8,
        "k": 4,
        "d": 4,
        "fom": 8.0,
        "score": 8.0,
        "stage": "refined_estimate",
        "A_terms": [[0, 0], [0, 1]],
        "B_terms": [[1, 0], [1, 1]],
        "pattern_type": "tiny",
        "term_count": 4,
    }


def _unresolved_candidate() -> dict:
    return {
        "ell": 6,
        "m": 6,
        "n": 72,
        "k": 8,
        "d": 6,
        "fom": 4.0,
        "score": 4.0,
        "stage": "refined_estimate",
        "A_terms": [[0, 0], [0, 1], [1, 0]],
        "B_terms": [[0, 0], [0, 2], [2, 0]],
        "pattern_type": "timeout",
        "term_count": 6,
    }


def _review_evidence(prompt: str) -> dict:
    encoded = prompt.split("Round evidence JSON:\n", 1)[1].split(
        "\n\nReturn only the JSON object", 1
    )[0]
    return json.loads(encoded)


class RecordingReviewer:
    def __init__(self, verdict: str):
        self.verdict = verdict
        self.prompts: list[str] = []

    def review(self, prompt, _round_dir):
        self.prompts.append(prompt)
        return validate_review({
            "verdict": self.verdict,
            "summary": "trusted Stage 1 handoff regression",
            "risks": [],
            "recommended_focus": [],
            "lessons": [],
        })


def test_same_cell_runner_up_is_reselected_from_bound_history(
    tmp_path,
    monkeypatch,
):
    _identity_structural_screen(monkeypatch)
    repo = tmp_path / "repo"
    repo.mkdir()
    source = repo / "candidates.jsonl"
    decoy = _map_candidate(distance=24, shift=0)
    runner_up = _map_candidate(distance=17, shift=3)
    _write_jsonl(source, [decoy, runner_up])
    flow = HumanizeFlow(
        FlowConfig(
            repo_dir=repo,
            run_id="same-cell-history",
            max_rounds=2,
            milp_top=1,
            candidate_file=source,
        ),
        reviewer=RecordingReviewer("continue"),
    )
    state = flow.store.initialize(flow.config.serializable())
    round_dir = flow.store.round_dir(1)
    assert flow._capture_round_candidates(
        state, 1, round_dir
    ) == [decoy, runner_up]

    state["current_round"] = 1
    state["audited_keys"] = [code_key(decoy)]
    state["audited_structural_digests"] = []
    state["unresolved_candidates"] = {}
    state.pop("pending_round", None)
    state.pop("round_phase", None)
    flow.store.write_state(state)

    poison = _map_candidate(distance=25, shift=5)
    flow.archive.replace([poison])
    assert archive_cell(decoy) == archive_cell(runner_up)
    assert archive_cell(decoy) == archive_cell(poison)

    selected = flow._select_audit_candidates([], state)

    assert [code_key(row) for row in selected] == [code_key(runner_up)]
    assert all(code_key(row) != code_key(poison) for row in selected)


def test_bp_patience_and_reviewer_stop_cannot_end_no_win_search(
    tmp_path,
    monkeypatch,
):
    _identity_structural_screen(monkeypatch)
    repo = tmp_path / "repo"
    repo.mkdir()
    source = repo / "candidates.jsonl"
    _write_jsonl(source, [_map_candidate(distance=24, shift=0)])
    reviewer = RecordingReviewer("stop")
    flow = HumanizeFlow(
        FlowConfig(
            repo_dir=repo,
            run_id="no-win-patience",
            max_rounds=3,
            milp_top=0,
            patience=1,
            candidate_file=source,
        ),
        reviewer=reviewer,
    )

    state = flow.run()

    assert state["status"] == "search-complete"
    assert state["current_round"] == 3
    assert state["trusted_exact_count"] == 0
    assert state["trusted_win_count"] == 0
    assert len(reviewer.prompts) == 3


def test_formal_exact_loser_is_trusted_for_review_but_cannot_stop(
    tmp_path,
    monkeypatch,
):
    _identity_structural_screen(monkeypatch)
    repo = tmp_path / "repo"
    repo.mkdir()
    source = repo / "candidates.jsonl"
    _write_jsonl(source, [_tiny_exact_candidate()])
    reviewer = RecordingReviewer("stop")
    flow = HumanizeFlow(
        FlowConfig(
            repo_dir=repo,
            run_id="exact-loser",
            max_rounds=2,
            milp_top=1,
            milp_timeout_per_logical=5,
            milp_total_timeout=30,
            candidate_file=source,
        ),
        reviewer=reviewer,
    )

    state = flow.run()

    assert state["status"] == "search-complete"
    assert state["current_round"] == 2
    assert state["trusted_exact_count"] == 1
    assert state["trusted_win_count"] == 0
    assert len(reviewer.prompts) == 2
    canonical = flow._read_jsonl(flow.evaluations_path)
    assert canonical[0]["audit_attempt"]["schema_version"] == 2
    assert classify_evaluation(canonical[0]) is AuditOutcome.EXACT
    assert final_gate_module.classify_win(8, 4, 2)["passed"] is False
    for prompt in reviewer.prompts:
        evidence = _review_evidence(prompt)
        assert evidence["trusted_exact_policy"][
            "formal_checkpoint_replay_required"
        ] is True
        assert len(evidence["trusted_exact_history"]) == 1
        assert evidence["trusted_exact_wins"] == []


def test_trusted_exact_win_hands_off_with_unrelated_unresolved(
    tmp_path,
    monkeypatch,
):
    _identity_structural_screen(monkeypatch)
    repo = tmp_path / "repo"
    repo.mkdir()
    source = repo / "candidates.jsonl"
    exact_candidate = _tiny_exact_candidate()
    unresolved_candidate = _unresolved_candidate()
    _write_jsonl(source, [exact_candidate, unresolved_candidate])

    monkeypatch.setattr(
        final_gate_module,
        "KNOWN_PARETO_REFERENCES",
        ((10, 5, 2),),
    )

    def evaluator(row, config, **invocation):
        if int(row["ell"]) == 2:
            return evaluate_with_milp(
                row, config, **invocation
            )
        result = dict(row)
        result.update({
            "d": 0,
            "fom": 0.0,
            "score": 0.0,
            "stage": "milp_timeout_no_incumbent",
            "d_is_exact": False,
            "distance_trusted": False,
            "distance_status": "unknown_no_incumbent",
            "milp_details": {
                "exact": False,
                "all_timeout": True,
                "total_logicals": 2 * int(row["k"]),
                "num_logicals_checked": 0,
                "logicals_optimal": 0,
            },
        })
        return result

    reviewer = RecordingReviewer("continue")
    flow = HumanizeFlow(
        FlowConfig(
            repo_dir=repo,
            run_id="trusted-win-handoff",
            max_rounds=3,
            milp_top=2,
            milp_timeout_per_logical=5,
            milp_total_timeout=30,
            candidate_file=source,
            allow_debug_audit_evaluator=True,
        ),
        reviewer=reviewer,
        milp_evaluator=evaluator,
    )

    state = flow.run()

    assert state["status"] == "search-complete"
    assert state["current_round"] == 1
    assert state["trusted_exact_count"] == 1
    assert state["trusted_win_count"] == 1
    assert len(state["unresolved_candidates"]) == 1
    assert len(reviewer.prompts) == 1
    evidence = _review_evidence(reviewer.prompts[0])
    assert len(evidence["trusted_exact_history"]) == 1
    assert len(evidence["trusted_exact_wins"]) == 1

    inputs = flow.pipeline_candidate_inputs
    assert inputs[-1] == flow.evaluations_path.resolve()
    assert flow.evaluations_path in inputs
    canonical_rows = flow._read_jsonl(flow.evaluations_path)
    assert len(canonical_rows) == 2
    by_key = {code_key(row): row for row in canonical_rows}
    exact_row = by_key[code_key(exact_candidate)]
    unresolved_row = by_key[code_key(unresolved_candidate)]
    assert exact_row["audit_attempt"]["schema_version"] == 2
    assert classify_evaluation(exact_row) is AuditOutcome.EXACT
    assert unresolved_row["audit_attempt"]["schema_version"] == 1
    assert (
        code_key(unresolved_candidate)
        in state["unresolved_candidates"]
    )
    events = flow._read_jsonl(flow.store.events_path)
    completed = [
        event for event in events
        if event["event"] == "search_completed"
    ]
    assert completed[-1]["unresolved_handed_off"] == 1

    canonical = flow.evaluations_path.read_bytes()
    flow.evaluations_path.write_bytes(canonical + b'{"partial":')
    with pytest.raises(AuditStateError, match="partial row"):
        _ = flow.pipeline_candidate_inputs
    flow.evaluations_path.write_bytes(canonical)

    resumed = HumanizeFlow(
        flow.config,
        reviewer=reviewer,
        milp_evaluator=evaluator,
    )
    resumed_state = resumed.run()
    assert resumed_state["status"] == "search-complete"
    assert len(resumed_state["unresolved_candidates"]) == 1
    assert len(reviewer.prompts) == 1
