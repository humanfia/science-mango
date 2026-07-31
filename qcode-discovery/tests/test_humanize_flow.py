import json

import pytest

from humanize.audit_state import (
    authoritative_candidate_digest,
    create_unresolved_entry,
)
from humanize.flow import (
    FlowConfig,
    HumanizeFlow,
    UnresolvedAuditError,
    _deduplicate,
    _milp_is_fully_exact,
    select_for_milp,
)
from humanize.reviewer import validate_review
from humanize.state import (
    EliteArchive,
    RunStore,
    archive_cell,
    candidate_structural_features,
    code_key,
    read_jsonl_since,
)


def candidate(*, ell=6, m=6, k=12, d=6, fom=6.0, shift=0):
    return {
        "ell": ell,
        "m": m,
        "n": 2 * ell * m,
        "k": k,
        "d": d,
        "fom": fom,
        "score": fom,
        "stage": "refined_estimate",
        "A_terms": [[0, 0], [0, 1 + shift], [1, 0]],
        "B_terms": [[0, 0], [0, 2 + shift], [2, 0]],
        "pattern_type": "swap",
        "term_count": 6,
    }


def test_elite_archive_replaces_cell_winner_and_selects_diverse(tmp_path):
    archive = EliteArchive(tmp_path / "archive.json")
    weak = candidate(fom=5.0)
    strong = candidate(fom=8.0, shift=1)
    other_cell = candidate(ell=12, m=6, d=8, fom=7.0, shift=2)
    archive.update([weak, strong, other_cell], 1)

    ranked = archive.ranked()
    assert len(ranked) == 2
    assert ranked[0]["fom"] == 8.0
    selected = select_for_milp(ranked, archive, set(), 2)
    assert len(selected) == 2
    assert len({row["archive_cell"] for row in selected}) == 2


def test_candidate_archive_cell_ignores_forged_structural_metadata():
    row = candidate()
    variants = []
    for pattern, term_count, version in (
        ("forged", 999, 2),
        (3.0, 1, 1),
        (None, None, None),
    ):
        variant = dict(row)
        variant["pattern_type"] = pattern
        variant["term_count"] = term_count
        variant["pattern_classifier_version"] = version
        variants.append(variant)

    assert len({archive_cell(variant) for variant in variants}) == 1
    assert candidate_structural_features(variants[0]) == {
        "pattern_type": 5.0,
        "term_count": 3.0,
        "pattern_classifier_version": 2,
    }


def test_candidate_archive_uses_v2_mixed_and_max_term_semantics():
    multi_term_mixed = {
        "A_terms": [[0, 0], [1, 0]],
        "B_terms": [[0, 1], [1, 1], [2, 0], [0, 2]],
    }
    compact_mixed = {
        "A_terms": [[0, 0], [1, 1], [2, 0]],
        "B_terms": [[0, 1], [1, 0], [2, 2]],
    }

    assert candidate_structural_features(multi_term_mixed) == {
        "pattern_type": 4.0,
        "term_count": 4.0,
        "pattern_classifier_version": 2,
    }
    assert candidate_structural_features(compact_mixed) == {
        "pattern_type": 3.0,
        "term_count": 3.0,
        "pattern_classifier_version": 2,
    }


def test_elite_archive_migrates_metadata_without_trusting_upper_fom(tmp_path):
    path = tmp_path / "archive.json"
    weak = candidate(fom=5.0)
    strong = candidate(fom=8.0)
    weak.update({"pattern_type": "weak-forgery", "term_count": 100})
    strong.update({"pattern_type": "strong-forgery", "term_count": 200})
    path.write_text(json.dumps({
        "schema_version": 1,
        "cells": {
            "legacy-cell-a": weak,
            "legacy-cell-b": strong,
        },
    }))

    archive = EliteArchive(path)

    assert len(archive.cells) == 1
    [stored] = archive.ranked()
    # Both legacy rows describe the same unresolved definition.  A larger
    # reported BP/OSD FOM is not stronger evidence and cannot replace it.
    assert stored["fom"] == 5.0
    assert stored["pattern_type"] == 5.0
    assert stored["term_count"] == 3.0
    assert stored["pattern_classifier_version"] == 2
    assert stored["archive_cell"] == archive_cell(stored)


def test_duplicate_bp_upper_bounds_keep_tightest_observation():
    loose = candidate(k=8, d=30, fom=100.0)
    tight = candidate(k=8, d=12, fom=16.0)

    [selected] = _deduplicate([loose, tight])

    assert selected["d"] == 12
    assert selected["fom"] == 16.0
    assert selected["bp_upper_bound_observations"] == {
        "count": 2,
        "minimum_distance": 12,
        "maximum_distance": 30,
        "selected_distance": 12,
        "selection_policy": "tightest_observed_upper_bound",
    }


def test_unknown_quick_duplicate_never_overwrites_positive_upper_bound():
    unknown = candidate(k=4, d=0, fom=0.0)
    unknown.update({
        "stage": "quick_k_only",
        "candidate_persistence_lane": "winner_capable_quick_exploration",
        "winner_capable_parameters": True,
        "minimum_winning_distance": 15,
        "singleton_distance_upper_bound": 35,
    })
    observed = candidate(k=4, d=18, fom=18.0)

    [selected] = _deduplicate([unknown, observed])

    assert selected["d"] == 18
    assert selected["stage"] == "refined_estimate"
    assert selected["bp_upper_bound_observations"]["count"] == 1


def test_milp_selection_reserves_one_bounded_quick_exploration_lane():
    credible = candidate(k=8, d=8, fom=7.0, shift=1)
    outlier = candidate(k=8, d=40, fom=120.0, shift=2)
    quick = candidate(k=4, d=0, fom=0.0, shift=3)
    quick.update({
        "stage": "quick_k_only",
        "candidate_persistence_lane": "winner_capable_quick_exploration",
        "winner_capable_parameters": True,
        "minimum_winning_distance": 15,
        "singleton_distance_upper_bound": 35,
    })

    selected = select_for_milp(
        [credible, outlier, quick],
        None,
        set(),
        3,
    )

    assert {code_key(row) for row in selected} == {
        code_key(credible),
        code_key(outlier),
        code_key(quick),
    }
    assert sum(
        row.get("candidate_persistence_lane")
        == "winner_capable_quick_exploration"
        for row in selected
    ) == 1


def test_milp_selection_never_takes_more_than_one_quick_exploration():
    quick_rows = []
    for shift in range(5):
        quick = candidate(k=4, d=0, fom=0.0, shift=shift)
        quick.update({
            "stage": "quick_k_only",
            "candidate_persistence_lane": "winner_capable_quick_exploration",
            "winner_capable_parameters": True,
            "minimum_winning_distance": 15,
            "singleton_distance_upper_bound": 35,
        })
        quick_rows.append(quick)

    selected = select_for_milp(quick_rows, None, set(), 3)

    assert len(selected) == 1
    assert selected[0]["candidate_persistence_lane"] == (
        "winner_capable_quick_exploration"
    )


def test_unresolved_distance_selection_precedes_arbitrary_quick_lane():
    quick = candidate(k=4, d=0, fom=0.0, shift=1)
    unresolved = candidate(k=4, d=0, fom=0.0, shift=2)
    for row in (quick, unresolved):
        row.update({
            "stage": "quick_k_only",
            "candidate_persistence_lane": (
                "winner_capable_quick_exploration"
            ),
            "winner_capable_parameters": True,
            "minimum_winning_distance": 15,
            "singleton_distance_upper_bound": 35,
        })
    quick["candidate_persistence_reason"] = "quick_distance_budget"
    unresolved["candidate_persistence_reason"] = (
        "selected_distance_unresolved"
    )

    selected = select_for_milp([quick, unresolved], None, set(), 3)

    assert selected == [unresolved]


def test_duplicate_zero_distance_rows_preserve_unresolved_provenance():
    quick = candidate(k=4, d=0, fom=0.0)
    quick.update({
        "stage": "quick_k_only",
        "candidate_persistence_lane": "winner_capable_quick_exploration",
        "candidate_persistence_reason": "quick_distance_budget",
        "winner_capable_parameters": True,
        "minimum_winning_distance": 15,
        "singleton_distance_upper_bound": 35,
    })
    unresolved = dict(quick)
    unresolved["candidate_persistence_reason"] = (
        "selected_distance_unresolved"
    )

    [selected] = _deduplicate([quick, unresolved])

    assert selected["candidate_persistence_reason"] == (
        "selected_distance_unresolved"
    )


def test_distance_error_precedes_unresolved_pending_and_quick_lanes():
    reasons = [
        "quick_distance_budget",
        "selected_distance_pending",
        "selected_distance_unresolved",
        "selected_distance_error",
    ]
    rows = []
    for shift, reason in enumerate(reasons):
        row = candidate(k=4, d=0, fom=0.0, shift=shift)
        row.update({
            "stage": reason,
            "candidate_persistence_lane": (
                "winner_capable_quick_exploration"
            ),
            "candidate_persistence_reason": reason,
            "winner_capable_parameters": True,
            "minimum_winning_distance": 15,
            "singleton_distance_upper_bound": 35,
        })
        rows.append(row)

    selected = select_for_milp(rows, None, set(), 3)

    assert len(selected) == 1
    assert selected[0]["candidate_persistence_reason"] == (
        "selected_distance_error"
    )


def test_duplicate_write_ahead_rows_keep_error_then_later_positive_evidence():
    quick = candidate(k=4, d=0, fom=0.0)
    quick.update({
        "stage": "quick_k_only",
        "candidate_persistence_lane": "winner_capable_quick_exploration",
        "candidate_persistence_reason": "quick_distance_budget",
        "winner_capable_parameters": True,
        "minimum_winning_distance": 15,
        "singleton_distance_upper_bound": 35,
    })
    pending = dict(quick)
    pending["candidate_persistence_reason"] = "selected_distance_pending"
    unresolved = dict(quick)
    unresolved["candidate_persistence_reason"] = (
        "selected_distance_unresolved"
    )
    failed = dict(quick)
    failed["candidate_persistence_reason"] = "selected_distance_error"

    [selected_without_distance] = _deduplicate(
        [quick, pending, unresolved, failed]
    )
    assert selected_without_distance["candidate_persistence_reason"] == (
        "selected_distance_error"
    )

    positive = candidate(k=4, d=16, fom=4 * 16 * 16 / 72)
    [selected_with_distance] = _deduplicate(
        [quick, pending, unresolved, failed, positive]
    )
    assert selected_with_distance["d"] == 16
    assert selected_with_distance["stage"] == "refined_estimate"


def test_milp_selection_rejects_forged_or_malformed_quick_lane_marker():
    malformed = candidate(k=4, d=0, fom=0.0)
    malformed.update({
        "stage": "quick_k_only",
        "candidate_persistence_lane": "winner_capable_quick_exploration",
        "winner_capable_parameters": True,
        "minimum_winning_distance": "15",
        "singleton_distance_upper_bound": 35,
    })

    assert select_for_milp([malformed], None, set(), 3) == []


def test_structural_digest_prevents_cross_round_reaudit(tmp_path):
    archive = EliteArchive(tmp_path / "archive.json")
    row = candidate(k=8)
    row["static_eligibility"] = {"eligible": True}
    row["structural_novelty"] = {
        "checked": True,
        "novel": True,
        "canonical_digest": "same-tanner-graph",
    }
    archive.update([row], 1)
    digest = authoritative_candidate_digest(row)
    assert select_for_milp(
        [row], archive, set(), 1, {digest}
    ) == []


def test_unresolved_queue_reserves_one_lane_for_fresh_candidate(tmp_path):
    repo = tmp_path / "qcode"
    repo.mkdir()
    source = repo / "offline.jsonl"
    source.write_text("")
    flow = HumanizeFlow(
        FlowConfig(
            repo_dir=repo,
            run_id="retry-drain",
            max_rounds=1,
            milp_top=3,
            candidate_file=source,
        ),
        reviewer=FakeReviewer(),
    )
    unresolved_rows = [
        candidate(k=8, shift=shift) for shift in range(3)
    ]
    entries = [
        create_unresolved_entry(row, round_number=1)
        for row in unresolved_rows
    ]
    state = {
        "unresolved_candidates": {
            entry["candidate_key"]: entry for entry in entries
        },
        "audited_keys": [],
        "audited_structural_digests": [],
    }

    fresh = candidate(k=8, shift=3)
    selected = flow._select_audit_candidates(
        [fresh],
        state,
        screened_history=[fresh],
    )

    selected_keys = {code_key(row) for row in selected}
    assert code_key(fresh) in selected_keys
    assert len(selected_keys & set(state["unresolved_candidates"])) == 2
    assert len(selected) == 3


def test_unresolved_queue_fills_idle_fresh_lane_with_retry(tmp_path):
    repo = tmp_path / "qcode"
    repo.mkdir()
    source = repo / "offline.jsonl"
    source.write_text("")
    flow = HumanizeFlow(
        FlowConfig(
            repo_dir=repo,
            run_id="retry-fill",
            max_rounds=1,
            milp_top=3,
            candidate_file=source,
        ),
        reviewer=FakeReviewer(),
    )
    entries = [
        create_unresolved_entry(
            candidate(k=8, shift=shift),
            round_number=1,
        )
        for shift in range(3)
    ]
    state = {
        "current_round": 1,
        "unresolved_candidates": {
            entry["candidate_key"]: entry for entry in entries
        },
        "audited_keys": [],
        "audited_structural_digests": [],
    }

    selected = flow._select_audit_candidates(
        [],
        state,
        screened_history=[],
    )

    assert {code_key(row) for row in selected} == set(
        state["unresolved_candidates"]
    )
    assert len(selected) == 3


def test_single_milp_lane_alternates_fresh_and_retry_turns(tmp_path):
    repo = tmp_path / "qcode"
    repo.mkdir()
    source = repo / "offline.jsonl"
    source.write_text("")
    flow = HumanizeFlow(
        FlowConfig(
            repo_dir=repo,
            run_id="retry-alternation",
            max_rounds=3,
            milp_top=1,
            candidate_file=source,
        ),
        reviewer=FakeReviewer(),
    )
    unresolved = create_unresolved_entry(
        candidate(k=8, shift=0),
        round_number=1,
    )
    fresh = candidate(k=8, shift=1)
    state = {
        "current_round": 1,
        "unresolved_candidates": {
            unresolved["candidate_key"]: unresolved,
        },
        "audited_keys": [],
        "audited_structural_digests": [],
    }

    fresh_turn = flow._select_audit_candidates(
        [fresh],
        state,
        screened_history=[fresh],
    )
    state["current_round"] = 2
    retry_turn = flow._select_audit_candidates(
        [fresh],
        state,
        screened_history=[fresh],
    )

    assert [code_key(row) for row in fresh_turn] == [code_key(fresh)]
    assert [code_key(row) for row in retry_turn] == [
        unresolved["candidate_key"]
    ]


def test_forged_structural_digest_cannot_hide_candidate_before_audit(tmp_path):
    archive = EliteArchive(tmp_path / "archive.json")
    row = candidate(k=8)
    row["static_eligibility"] = {"eligible": True}
    row["structural_novelty"] = {
        "checked": True,
        "novel": True,
        "canonical_digest": "forged-terminal-digest",
    }

    assert select_for_milp(
        [row],
        archive,
        set(),
        1,
        {"forged-terminal-digest"},
    ) == [row]


def test_partial_milp_never_becomes_exact():
    partial = {
        "d": 18,
        "d_is_exact": True,
        "stage": "milp_exact",
        "milp_details": {
            "exact": True,
            "total_logicals": 24,
            "num_logicals_checked": 7,
            "logicals_optimal": 7,
        },
    }
    assert not _milp_is_fully_exact(partial)
    partial["milp_details"].update(
        num_logicals_checked=24, logicals_optimal=24
    )
    assert _milp_is_fully_exact(partial)


def test_jsonl_offset_is_resumable(tmp_path):
    path = tmp_path / "codes.jsonl"
    first = candidate()
    path.write_text(json.dumps(first) + "\n")
    rows, offset = read_jsonl_since(path, 0)
    assert [code_key(row) for row in rows] == [code_key(first)]
    assert read_jsonl_since(path, offset) == ([], offset)
    second = candidate(ell=12, m=6, shift=2)
    with path.open("a") as stream:
        stream.write(json.dumps(second) + "\n")
    rows, new_offset = read_jsonl_since(path, offset)
    assert [code_key(row) for row in rows] == [code_key(second)]
    assert new_offset > offset


class FakeReviewer:
    def review(self, prompt, round_dir):
        assert "BP-OSD returns an upper bound" in prompt
        return validate_review({
            "verdict": "promote",
            "summary": "The complete MILP audit is suitable for Lean promotion.",
            "risks": [],
            "recommended_focus": ["Try a second lattice cell."],
            "lessons": [{
                "insight": "Require complete logical-direction coverage.",
                "evidence": "The exact candidate has checked=optimal=total.",
                "action": "Keep partial MILP results as upper bounds.",
            }],
        })


def fake_milp(row, _config, **_invocation):
    result = dict(row)
    result.update({
        "milp_attempted": True,
        "stage": "milp_exact",
        "d_is_exact": True,
        "distance_source": "milp_exact",
        "milp_details": {
            "exact": True,
            "total_logicals": 2 * row["k"],
            "num_logicals_checked": 2 * row["k"],
            "logicals_optimal": 2 * row["k"],
        },
    })
    return result


def test_debug_exact_results_remain_unresolved_but_persist_review_memory(
    tmp_path,
):
    repo = tmp_path / "qcode"
    repo.mkdir()
    source = repo / "offline.jsonl"
    rows = [
        candidate(k=8),
        candidate(ell=12, m=6, k=8, d=8, fom=7.0, shift=0),
    ]
    source.write_text("".join(json.dumps(row) + "\n" for row in rows))
    config = FlowConfig(
        repo_dir=repo,
        run_id="test-humanize",
        max_rounds=1,
        milp_top=2,
        candidate_file=source,
        allow_debug_audit_evaluator=True,
    )
    flow = HumanizeFlow(config, reviewer=FakeReviewer(), milp_evaluator=fake_milp)
    with pytest.raises(UnresolvedAuditError):
        flow.run()
    state = flow.store.load_state()
    assert state is not None

    assert state["status"] == "incomplete-unresolved"
    assert state["current_round"] == 1
    evaluations = (repo / "results/runs/test-humanize/evaluations.jsonl").read_text().splitlines()
    assert len(evaluations) == 2
    assert all(
        json.loads(line)["audit_attempt"]["schema_version"] == 1
        for line in evaluations
    )
    assert state["audited_keys"] == []
    assert len(state["unresolved_candidates"]) == 2
    assert state["trusted_exact_count"] == 0
    assert state["trusted_win_count"] == 0
    memory = (repo / "results/humanize/test-humanize/bitlesson.md").read_text()
    assert "Require complete logical-direction coverage" in memory

    # A resumed debug run stays unresolved and does not append duplicates.
    with pytest.raises(UnresolvedAuditError):
        flow.run()
    assert len((repo / "results/runs/test-humanize/evaluations.jsonl").read_text().splitlines()) == 2
