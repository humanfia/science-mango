from __future__ import annotations

import json

from evaluation.bb_code import build_bb_code
import evaluation.final_gate as final_gate_module
import evaluation.structural_dedup as structural_dedup_module
from evaluation.registry import canonical_json_sha256, load_registry
from evaluation.structural_dedup import canonical_digest
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


def _write_registry(repo, entries=()):
    path = repo / "results" / "known_code_registry.json"
    path.parent.mkdir(parents=True, exist_ok=True)
    entries = list(entries)
    value = {
        "schema_version": 1,
        "registry_version": "trusted-handoff-test-v1",
        "summary": {
            "raw_entries": len(entries),
            "deduplicated_entries": len(entries),
            "css": sum(row["code_type"] == "css" for row in entries),
            "noncss": sum(row["code_type"] == "noncss" for row in entries),
        },
        "entries": entries,
    }
    value["registry_sha256"] = canonical_json_sha256(
        value,
        omit="registry_sha256",
    )
    path.write_text(json.dumps(value))
    load_registry.cache_clear()
    return path


def _known_registry_entry(candidate):
    construction = {
        name: candidate[name]
        for name in ("ell", "m", "A_terms", "B_terms")
    }
    code = build_bb_code(**construction)
    return {
        "id": "trusted-handoff-known-css",
        "family": "test",
        "code_type": "css",
        "n": int(code.num_qudits),
        "k": int(code.dimension),
        "canonical_digest": canonical_digest(code),
        "construction": construction,
        "provenance": [{"kind": "test"}],
    }


def _force_scalar_fom_win(monkeypatch):
    """Unit-test the stop gate without requiring a real challenge winner."""

    def classify_win(_n, _k, _d):
        return {
            "passed": True,
            "fom": 13.0,
            "reasons": ["fom_strictly_above_12"],
        }

    monkeypatch.setattr(final_gate_module, "classify_win", classify_win)


def _identity_structural_screen(monkeypatch):
    monkeypatch.setattr(
        structural_dedup_module,
        "screen_css_results_with_deferred_cache",
        lambda rows, **_kwargs: (list(rows), [], []),
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


def test_screen_replay_uses_unified_worker_budget_and_run_cache(
    tmp_path,
    monkeypatch,
):
    repo = tmp_path / "repo"
    repo.mkdir()
    observed = {}

    def screen(rows, *, cache_dir, max_workers):
        observed.update({
            "rows": rows,
            "cache_dir": cache_dir,
            "max_workers": max_workers,
        })
        return list(rows), [], []

    monkeypatch.setattr(
        structural_dedup_module,
        "screen_css_results_with_deferred_cache",
        screen,
    )
    flow = HumanizeFlow(
        FlowConfig(
            repo_dir=repo,
            run_id="screen-worker-budget",
            max_total_workers=6,
            candidate_file=repo / "candidates.jsonl",
        ),
        reviewer=RecordingReviewer("continue"),
    )
    monkeypatch.setattr(
        flow,
        "_validated_committed_candidate_history",
        lambda: ((), []),
    )
    candidate = _map_candidate(distance=17, shift=1)

    kept, rejected = flow._replay_screened_candidate_pool([candidate])

    assert kept == [candidate]
    assert rejected == []
    assert observed["rows"] == [candidate]
    assert observed["max_workers"] == 6
    assert observed["cache_dir"] == (
        flow.store.root / "structural-screen-cache-v1"
    )


def test_deferred_structural_timeout_does_not_reject_or_hide_raw_handoff(
    tmp_path,
    monkeypatch,
):
    repo = tmp_path / "repo"
    repo.mkdir()
    source = repo / "candidates.jsonl"
    candidate = _map_candidate(distance=17, shift=2)
    _write_jsonl(source, [candidate])
    flow = HumanizeFlow(
        FlowConfig(
            repo_dir=repo,
            run_id="screen-deferred-handoff",
            max_total_workers=2,
            candidate_file=source,
        ),
        reviewer=RecordingReviewer("continue"),
    )
    state = flow.store.initialize(flow.config.serializable())
    raw = flow._capture_round_candidates(
        state,
        1,
        flow.store.round_dir(1),
    )
    evidence = {
        "candidate_index": 0,
        "input_sha256": "a" * 64,
        "attempt_count": 1,
        "failure": {
            "kind": "hard_timeout",
            "retryable": True,
        },
    }
    monkeypatch.setattr(
        structural_dedup_module,
        "screen_css_results_with_deferred_cache",
        lambda rows, **_kwargs: ([], [], [evidence]),
    )

    kept, rejected = flow._replay_screened_candidate_pool(raw)

    assert kept == []
    assert rejected == []
    events = [
        json.loads(line) for line in flow.store.events_path.read_text().splitlines()
    ]
    assert events[-1]["event"] == "structural_screen_deferred"
    assert events[-1]["retryable"] is True

    # Stage 2 consumes transaction-bound raw batches, not the screened
    # archive. Simulate round finalization and prove the timed-out row remains
    # in the canonical handoff input.
    state = flow.store.load_state()
    state["current_round"] = 1
    flow.store.write_state(state)
    handoff_paths = flow.pipeline_candidate_inputs
    assert len(handoff_paths) == 1
    assert json.loads(handoff_paths[0].read_text().strip()) == candidate


def test_permanent_structural_timeout_does_not_block_stage1_rounds(
    tmp_path,
    monkeypatch,
):
    repo = tmp_path / "repo"
    repo.mkdir()
    source = repo / "candidates.jsonl"
    candidate = _map_candidate(distance=17, shift=4)
    _write_jsonl(source, [candidate])
    calls = 0

    def always_deferred(rows, **_kwargs):
        nonlocal calls
        calls += 1
        assert len(rows) == 1
        return [], [], [{
            "candidate_index": 0,
            "input_sha256": "b" * 64,
            "attempt_count": calls,
            "failure": {
                "kind": "hard_timeout",
                "retryable": True,
            },
        }]

    monkeypatch.setattr(
        structural_dedup_module,
        "screen_css_results_with_deferred_cache",
        always_deferred,
    )
    flow = HumanizeFlow(
        FlowConfig(
            repo_dir=repo,
            run_id="permanent-screen-timeout",
            max_rounds=2,
            milp_top=0,
            max_total_workers=2,
            candidate_file=source,
        ),
        reviewer=RecordingReviewer("continue"),
    )

    state = flow.run()

    assert state["status"] == "search-complete"
    assert state["current_round"] == 2
    assert calls == 2
    assert all(
        json.loads(
            (flow.store.round_dir(number) / "rejected-candidates.jsonl")
            .read_text() or "[]"
        ) == []
        for number in (1, 2)
    )
    raw_rows = []
    for path in flow.pipeline_candidate_inputs:
        raw_rows.extend(
            json.loads(line) for line in path.read_text().splitlines()
        )
    assert candidate in raw_rows


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
    _write_registry(repo)
    source = repo / "candidates.jsonl"
    exact_candidate = _tiny_exact_candidate()
    unresolved_candidate = _unresolved_candidate()
    _write_jsonl(source, [exact_candidate, unresolved_candidate])

    _force_scalar_fom_win(monkeypatch)

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
    gate = evidence["trusted_exact_wins"][0]["trusted_win_gate"]
    assert gate["trusted"] is True
    assert gate["registry_novelty"]["status"] == "COMPLETE"
    assert gate["registry_novelty"]["novel"] is True
    assert state["challenge_win_registry_novel_count"] == 1
    assert state["challenge_win_registry_known_count"] == 0
    assert state["challenge_win_registry_unresolved_count"] == 0

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


def test_registry_known_exact_challenge_win_does_not_stop_next_round(
    tmp_path,
    monkeypatch,
):
    _identity_structural_screen(monkeypatch)
    repo = tmp_path / "repo"
    repo.mkdir()
    exact_candidate = _tiny_exact_candidate()
    _write_registry(repo, [_known_registry_entry(exact_candidate)])
    source = repo / "candidates.jsonl"
    _write_jsonl(source, [exact_candidate])
    _force_scalar_fom_win(monkeypatch)
    reviewer = RecordingReviewer("stop")
    flow = HumanizeFlow(
        FlowConfig(
            repo_dir=repo,
            run_id="known-exact-win-keeps-searching",
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
    assert state["challenge_win_registry_novel_count"] == 0
    assert state["challenge_win_registry_known_count"] == 1
    assert state["challenge_win_registry_unresolved_count"] == 0
    assert len(reviewer.prompts) == 2
    for prompt in reviewer.prompts:
        evidence = _review_evidence(prompt)
        assert evidence["trusted_exact_wins"] == []
        gate = evidence["trusted_exact_history"][0]["trusted_win_gate"]
        assert gate["trusted"] is False
        assert gate["challenge_win"]["passed"] is True
        assert gate["challenge_win"]["fom"] > 12
        assert gate["registry_novelty"]["status"] == "COMPLETE"
        assert gate["registry_novelty"]["novel"] is False
        assert gate["registry_novelty"]["matched_entries"][0]["id"] == (
            "trusted-handoff-known-css"
        )


def test_unavailable_registry_exact_challenge_win_does_not_stop_next_round(
    tmp_path,
    monkeypatch,
):
    _identity_structural_screen(monkeypatch)
    repo = tmp_path / "repo"
    repo.mkdir()
    source = repo / "candidates.jsonl"
    _write_jsonl(source, [_tiny_exact_candidate()])
    _force_scalar_fom_win(monkeypatch)
    reviewer = RecordingReviewer("stop")
    flow = HumanizeFlow(
        FlowConfig(
            repo_dir=repo,
            run_id="missing-registry-keeps-searching",
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
    assert state["challenge_win_registry_novel_count"] == 0
    assert state["challenge_win_registry_known_count"] == 0
    assert state["challenge_win_registry_unresolved_count"] == 1
    assert len(reviewer.prompts) == 2
    for prompt in reviewer.prompts:
        evidence = _review_evidence(prompt)
        assert evidence["trusted_exact_wins"] == []
        gate = evidence["trusted_exact_history"][0]["trusted_win_gate"]
        novelty = gate["registry_novelty"]
        assert gate["trusted"] is False
        assert gate["challenge_win"]["passed"] is True
        assert gate["challenge_win"]["fom"] > 12
        assert novelty["status"] == "INCOMPLETE"
        assert novelty["novel"] is None
        assert novelty["failure"]["code"] == (
            "REGISTRY_UNAVAILABLE_OR_INVALID"
        )


def test_trusted_exact_win_survives_round_reviewer_failure(
    tmp_path,
    monkeypatch,
):
    _identity_structural_screen(monkeypatch)
    repo = tmp_path / "repo"
    repo.mkdir()
    _write_registry(repo)
    source = repo / "candidates.jsonl"
    _write_jsonl(source, [_tiny_exact_candidate()])

    _force_scalar_fom_win(monkeypatch)

    class FailingReviewer:
        @staticmethod
        def review(_prompt, round_dir):
            (round_dir / "review.json").write_text('{"partial":')
            raise RuntimeError("review backend unavailable")

    flow = HumanizeFlow(
        FlowConfig(
            repo_dir=repo,
            run_id="trusted-win-review-failure",
            max_rounds=3,
            milp_top=1,
            milp_timeout_per_logical=5,
            milp_total_timeout=30,
            candidate_file=source,
        ),
        reviewer=FailingReviewer(),
    )

    state = flow.run()

    assert state["status"] == "search-complete"
    assert state["current_round"] == 1
    assert state["trusted_exact_count"] == 1
    assert state["trusted_win_count"] == 1
    round_dir = flow.store.round_dir(1)
    review = json.loads((round_dir / "review.json").read_text())
    assert review["verdict"] == "promote"
    failure = json.loads(
        (round_dir / "review-advisory-failure.json").read_text()
    )
    assert failure["classification"] == "RuntimeError"
    assert failure["trusted_win_count"] == 1
    events = flow._read_jsonl(flow.store.events_path)
    assert any(
        event["event"] == "trusted_win_review_failed_advisory"
        for event in events
    )
