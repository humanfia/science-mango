"""Tests for pure Humanize unresolved/retry state helpers."""

from __future__ import annotations

import copy
from types import SimpleNamespace

import numpy as np
import pytest

from humanize.audit_state import (
    AuditOutcome,
    AuditStateError,
    classify_evaluation,
    create_unresolved_entry,
    is_fully_exact,
    rebuild_audit_state,
    retry_budget,
    select_retry_lane,
    update_unresolved_entry,
)
from humanize.state import code_key


def candidate(*, shift: int = 0, digest: str | None = None) -> dict:
    row = {
        "ell": 18,
        "m": 10,
        "n": 360,
        "k": 16,
        "d": 17,
        "fom": 16 * 17 * 17 / 360,
        "A_terms": [[0, 0], [1 + shift, 0], [0, 1]],
        "B_terms": [[0, 0], [2 + shift, 0], [0, 2]],
        "stage": "milp_incumbent",
        "d_is_exact": False,
        "distance_trusted": True,
        "milp_attempted": True,
        "milp_solver_attempted": True,
        "threshold_rejection_proven": False,
        "milp_details": {
            "exact": False,
            "total_logicals": 32,
            "num_logicals_checked": 1,
            "logicals_optimal": 0,
            "logicals_incumbent": 1,
        },
    }
    if digest is not None:
        row["structural_novelty"] = {
            "novel": True,
            "canonical_digest": digest,
        }
    row["candidate_key"] = code_key(row)
    return row


def exact(*, shift: int = 0, digest: str | None = None) -> dict:
    row = candidate(shift=shift, digest=digest)
    row.update({"d": 18, "stage": "milp_exact", "d_is_exact": True})
    row["milp_details"] = {
        "exact": True,
        "total_logicals": 32,
        "num_logicals_checked": 32,
        "logicals_optimal": 32,
    }
    return row


def threshold_rejected(
    *,
    shift: int = 0,
    digest: str | None = None,
) -> dict:
    row = candidate(shift=shift, digest=digest)
    distance = 16
    row.update(
        {
            "d": distance,
            "fom": 16 * distance * distance / 360,
            "stage": "milp_low_d",
            "fom_target": 12.0,
            "fom_target_numerator": 12,
            "fom_target_denominator": 1,
            "fom_rejection_cutoff": 16,
            "challenge_rejection_cutoff": 16,
            "minimum_passing_distance": 17,
            "milp_early_stop_objective": "challenge_final_gate",
            "milp_effective_early_stop": 16,
            "fom_target_excluded_by_upper_bound": True,
            "final_gate_excluded_by_upper_bound": True,
            "threshold_rejection_proven": True,
            "threshold_proof_lhs": 16 * distance * distance,
            "threshold_proof_rhs": 12 * 360,
            "threshold_proof_distance": distance,
            "threshold_proof_source": "milp_feasible_upper_bound",
        }
    )
    row["milp_details"].update(d_x=0, d_z=distance)
    return row


def no_incumbent(*, shift: int = 0, digest: str | None = None) -> dict:
    row = candidate(shift=shift, digest=digest)
    row.update(
        {
            "d": 0,
            "fom": 0.0,
            "stage": "milp_timeout_no_incumbent",
            "distance_status": "unknown_no_incumbent",
        }
    )
    row["milp_details"].update(all_timeout=True, no_incumbent=True)
    return row


def legacy_upper_bound(*, distance: int = 6, source: str = "milp") -> dict:
    row = candidate()
    row.update(
        {
            "ell": 12,
            "m": 12,
            "n": 288,
            "k": 12,
            "d": distance,
            "fom": 12 * distance * distance / 288,
        }
    )
    row.pop("threshold_rejection_proven")
    row["candidate_key"] = code_key(row)
    if source == "symplectic":
        row.update(
            {
                "stage": "symplectic_low_d",
                "d_symplectic": distance,
                "milp_solver_attempted": False,
            }
        )
    elif source == "bp":
        row.update(
            {
                "stage": "bp_osd_after_milp",
                "distance_source": "bp_osd",
            }
        )
    else:
        row.update(
            {
                "stage": "milp_incumbent",
                "distance_source": "milp_incumbent",
            }
        )
        row["milp_details"].update(
            d_x=distance,
            d_z=24,
            logicals_incumbent=1,
            logicals_optimal=0,
        )
    return row


def test_classification_accepts_only_exact_or_replayed_threshold_proof():
    # Legacy schema-0 rows retain scheduling information but cannot become
    # terminal without immutable schema-2 checkpoint evidence.
    assert (
        classify_evaluation(exact())
        is AuditOutcome.UNRESOLVED_WINNER_NOT_EXCLUDED
    )
    assert (
        classify_evaluation(threshold_rejected())
        is AuditOutcome.UNRESOLVED_WINNER_NOT_EXCLUDED
    )
    assert (
        classify_evaluation(candidate())
        is AuditOutcome.UNRESOLVED_WINNER_NOT_EXCLUDED
    )
    assert (
        classify_evaluation(no_incumbent())
        is AuditOutcome.UNRESOLVED_NO_INCUMBENT
    )
    assert AuditOutcome.EXACT.terminal
    assert not AuditOutcome.UNRESOLVED_NO_INCUMBENT.terminal


def test_legacy_trusted_milp_upper_bound_is_downgraded_for_retry():
    row = legacy_upper_bound(distance=6)

    assert (
        classify_evaluation(row)
        is AuditOutcome.UNRESOLVED_WINNER_NOT_EXCLUDED
    )
    rebuilt = rebuild_audit_state([row])
    assert rebuilt.terminal_keys == set()
    assert set(rebuilt.unresolved) == {row["candidate_key"]}


def test_legacy_upper_bound_above_current_cutoff_remains_unresolved():
    row = legacy_upper_bound(distance=17)

    assert (
        classify_evaluation(row)
        is AuditOutcome.UNRESOLVED_WINNER_NOT_EXCLUDED
    )
    rebuilt = rebuild_audit_state([row])
    assert rebuilt.terminal_keys == set()
    assert set(rebuilt.unresolved) == {row["candidate_key"]}


def test_legacy_fallback_rejects_bp_and_forged_provenance():
    bp_only = legacy_upper_bound(source="bp")
    assert (
        classify_evaluation(bp_only)
        is AuditOutcome.UNRESOLVED_WINNER_NOT_EXCLUDED
    )

    forged_milp = legacy_upper_bound()
    forged_milp["milp_details"]["d_x"] = 8
    assert (
        classify_evaluation(forged_milp)
        is AuditOutcome.UNRESOLVED_WINNER_NOT_EXCLUDED
    )

    symplectic = legacy_upper_bound(source="symplectic")
    assert (
        classify_evaluation(symplectic)
        is AuditOutcome.UNRESOLVED_WINNER_NOT_EXCLUDED
    )
    symplectic["d_symplectic"] = 8
    assert (
        classify_evaluation(symplectic)
        is AuditOutcome.UNRESOLVED_WINNER_NOT_EXCLUDED
    )


def test_explicit_false_never_uses_legacy_fallback():
    row = legacy_upper_bound()
    row["threshold_rejection_proven"] = False

    assert (
        classify_evaluation(row)
        is AuditOutcome.UNRESOLVED_WINNER_NOT_EXCLUDED
    )


@pytest.mark.parametrize(
    ("field", "value"),
    [
        ("threshold_proof_distance", 17),
        ("threshold_proof_lhs", 1),
        ("challenge_rejection_cutoff", 17),
        ("final_gate_excluded_by_upper_bound", False),
        ("threshold_proof_source", "bp_osd"),
        ("distance_trusted", False),
    ],
)
def test_threshold_true_is_revalidated_fail_closed(field, value):
    row = threshold_rejected()
    row[field] = value
    assert (
        classify_evaluation(row)
        is AuditOutcome.UNRESOLVED_WINNER_NOT_EXCLUDED
    )


def test_fully_exact_callback_must_return_a_boolean():
    row = candidate()
    assert (
        classify_evaluation(row, fully_exact=lambda _row: True)
        is AuditOutcome.UNRESOLVED_WINNER_NOT_EXCLUDED
    )
    with pytest.raises(AuditStateError, match="must return a boolean"):
        classify_evaluation(row, fully_exact=lambda _row: 1)


def test_threshold_source_must_match_its_machine_evidence():
    feasible = threshold_rejected()
    feasible["milp_details"]["logicals_incumbent"] = 0
    assert (
        classify_evaluation(feasible)
        is AuditOutcome.UNRESOLVED_WINNER_NOT_EXCLUDED
    )

    mislabeled_exact = threshold_rejected()
    mislabeled_exact["threshold_proof_source"] = "milp_exact"
    assert (
        classify_evaluation(mislabeled_exact)
        is AuditOutcome.UNRESOLVED_WINNER_NOT_EXCLUDED
    )

    valid_exact = threshold_rejected()
    valid_exact.update({"stage": "milp_exact", "d_is_exact": True})
    valid_exact["milp_details"] = {
        "exact": True,
        "total_logicals": 32,
        "num_logicals_checked": 32,
        "logicals_optimal": 32,
        "logicals_incumbent": 0,
    }
    valid_exact["threshold_proof_source"] = "milp_exact"
    assert (
        classify_evaluation(valid_exact)
        is AuditOutcome.UNRESOLVED_WINNER_NOT_EXCLUDED
    )

    symplectic = threshold_rejected()
    symplectic.update(
        {
            "threshold_proof_source": "symplectic_upper_bound",
            "d_symplectic": 16,
            "milp_solver_attempted": False,
        }
    )
    assert (
        classify_evaluation(symplectic)
        is AuditOutcome.UNRESOLVED_WINNER_NOT_EXCLUDED
    )
    symplectic["d_symplectic"] = 17
    assert (
        classify_evaluation(symplectic)
        is AuditOutcome.UNRESOLVED_WINNER_NOT_EXCLUDED
    )


def test_bp_distance_trust_is_separate_from_milp_threshold_proof_trust():
    from main import merge_bp_milp_result

    milp = threshold_rejected()
    bp = candidate()
    bp.update({"d": 15, "distance_trusted": False})

    merged = merge_bp_milp_result(bp, milp)

    assert merged["distance_source"] == "bp_osd"
    assert merged["distance_trusted"] is False
    assert merged["threshold_proof_trusted"] is True
    assert (
        classify_evaluation(merged)
        is AuditOutcome.UNRESOLVED_WINNER_NOT_EXCLUDED
    )


@pytest.mark.parametrize("value", [False, "true", 1])
def test_explicit_untrusted_threshold_proof_fails_closed(value):
    row = threshold_rejected()
    row["threshold_proof_trusted"] = value

    assert (
        classify_evaluation(row)
        is AuditOutcome.UNRESOLVED_WINNER_NOT_EXCLUDED
    )


def test_unresolved_entry_creation_and_2x_updates_are_immutable():
    first_row = candidate()
    original = copy.deepcopy(first_row)
    first = create_unresolved_entry(
        first_row,
        round_number=1,
        checkpoint_path="/proof/candidate.json",
    )
    assert first_row == original
    assert first["attempts_completed"] == 1
    assert first["last_budget_multiplier"] == 1
    assert first["next_budget_multiplier"] == 2

    second_row = candidate()
    second = update_unresolved_entry(
        first,
        second_row,
        round_number=2,
        budget_multiplier=2,
        checkpoint_path="/proof/candidate.json",
    )
    assert first["attempts_completed"] == 1
    assert second["attempts_completed"] == 2
    assert second["last_budget_multiplier"] == 2
    assert second["next_budget_multiplier"] == 4

    third = update_unresolved_entry(
        second,
        candidate(),
        round_number=3,
        budget_multiplier=4,
    )
    assert third["last_budget_multiplier"] == 4
    assert third["next_budget_multiplier"] == 4
    fourth = update_unresolved_entry(
        third,
        candidate(),
        round_number=4,
        budget_multiplier=4,
    )
    assert fourth["attempts_completed"] == 4
    assert fourth["next_budget_multiplier"] == 4

    with pytest.raises(AuditStateError, match="1x, 2x, or 4x"):
        update_unresolved_entry(
            fourth,
            candidate(),
            round_number=5,
            budget_multiplier=8,
        )
    legacy_exact = update_unresolved_entry(
        fourth,
        exact(),
        round_number=5,
        budget_multiplier=4,
    )
    assert legacy_exact["reason"] == (
        AuditOutcome.UNRESOLVED_WINNER_NOT_EXCLUDED.value
    )


def test_retry_budget_is_base_then_2x_then_4x():
    budgets = [
        retry_budget(
            timeout_per_logical=300,
            total_timeout=7200,
            completed_attempts=attempt,
            hard_timeout_per_logical=330,
        )
        for attempt in (0, 1, 2, 3, 99)
    ]
    assert [budget.multiplier for budget in budgets] == [1, 2, 4, 4, 4]
    assert [budget.timeout_per_logical for budget in budgets] == [
        300,
        600,
        1200,
        1200,
        1200,
    ]
    assert [budget.total_timeout for budget in budgets] == [
        7200,
        14400,
        28800,
        28800,
        28800,
    ]
    assert [budget.hard_timeout_per_logical for budget in budgets] == [
        330.0,
        660.0,
        1320.0,
        1320.0,
        1320.0,
    ]

    with pytest.raises(AuditStateError):
        retry_budget(
            timeout_per_logical=300,
            total_timeout=7200,
            completed_attempts=True,
        )


def test_retry_lane_is_least_recent_then_deterministic():
    oldest = create_unresolved_entry(candidate(shift=1), round_number=1)
    tied_a = create_unresolved_entry(candidate(shift=2), round_number=2)
    tied_b = create_unresolved_entry(candidate(shift=3), round_number=2)
    queue = {
        tied_b["candidate_key"]: tied_b,
        oldest["candidate_key"]: oldest,
        tied_a["candidate_key"]: tied_a,
    }

    selected = select_retry_lane(queue, limit=2)

    expected_tie = min(tied_a["candidate_key"], tied_b["candidate_key"])
    assert [entry["candidate_key"] for entry in selected] == [
        oldest["candidate_key"],
        expected_tie,
    ]
    assert select_retry_lane(queue, limit=0) == []


def test_legacy_rebuild_downgrades_all_unsealed_terminal_claims():
    exact_row = exact(shift=1, digest="exact-digest")
    rejected_row = threshold_rejected(shift=2, digest="rejected-digest")
    partial_first = candidate(shift=3, digest="partial-digest")
    partial_second = candidate(shift=3, digest="partial-digest")
    timeout_row = no_incumbent(shift=4, digest="timeout-digest")
    rows = [
        partial_first,
        exact_row,
        timeout_row,
        rejected_row,
        partial_second,
    ]

    rebuilt = rebuild_audit_state(
        rows,
        checkpoint_path_for=lambda key: f"/checkpoints/{key}.json",
    )

    assert rebuilt.evaluations_seen == 5
    assert rebuilt.terminal_keys == set()
    assert rebuilt.terminal_digests == set()
    assert set(rebuilt.unresolved) == {
        exact_row["candidate_key"],
        rejected_row["candidate_key"],
        partial_first["candidate_key"],
        timeout_row["candidate_key"],
    }
    partial = rebuilt.unresolved[partial_first["candidate_key"]]
    assert partial["attempts_completed"] == 2
    assert partial["next_budget_multiplier"] == 4
    assert partial["checkpoint_path"].endswith(
        f"{partial_first['candidate_key']}.json"
    )
    fields = rebuilt.as_state_fields()
    assert fields["audit_state_version"] == 1
    assert fields["audited_keys"] == sorted(rebuilt.terminal_keys)


def test_legacy_exact_digest_is_only_an_unresolved_representative():
    unresolved = candidate(shift=1, digest="same-structure")
    terminal = exact(shift=2, digest="same-structure")

    rebuilt = rebuild_audit_state([unresolved, terminal])

    assert list(rebuilt.unresolved) == [unresolved["candidate_key"]]
    assert rebuilt.terminal_digests == set()


def with_attempt(
    row: dict,
    attempt: int,
    *,
    round_number: int | None = None,
    checkpoint: str = "/proof/candidate.json",
) -> dict:
    value = copy.deepcopy(row)
    multiplier = min(1 << min(attempt - 1, 2), 4)
    value["audit_attempt"] = {
        "schema_version": 1,
        "round": attempt if round_number is None else round_number,
        "kind": "new" if attempt == 1 else "retry",
        "attempt": attempt,
        "multiplier": multiplier,
        "soft": 300 * multiplier,
        "total": 7200 * multiplier,
        "hard": 330.0 * multiplier,
        "checkpoint": checkpoint,
    }
    return value


def test_explicit_attempt_history_replays_one_two_four_four():
    rows = [with_attempt(candidate(), attempt) for attempt in range(1, 5)]

    rebuilt = rebuild_audit_state(
        rows,
        checkpoint_path_for=lambda _key: "/proof/candidate.json",
    )

    entry = next(iter(rebuilt.unresolved.values()))
    assert entry["attempts_completed"] == 4
    assert entry["last_budget_multiplier"] == 4
    assert entry["next_budget_multiplier"] == 4
    assert entry["checkpoint_path"] == "/proof/candidate.json"


@pytest.mark.parametrize("row_factory", (exact, threshold_rejected))
def test_schema1_terminal_claims_are_safely_downgraded(row_factory):
    row = with_attempt(row_factory(), 1)
    assert (
        classify_evaluation(row)
        is AuditOutcome.UNRESOLVED_WINNER_NOT_EXCLUDED
    )
    rebuilt = rebuild_audit_state([row])
    assert rebuilt.terminal_keys == set()
    assert set(rebuilt.unresolved) == {row["candidate_key"]}


def test_explicit_attempt_rounds_strictly_increase():
    first = with_attempt(candidate(), 1, round_number=1)
    second = with_attempt(candidate(), 2, round_number=1)

    with pytest.raises(AuditStateError, match="strictly increase"):
        rebuild_audit_state([first, second])


@pytest.mark.parametrize(
    "mutation",
    [
        lambda row: row["audit_attempt"].__setitem__("multiplier", 1),
        lambda row: row["audit_attempt"].__setitem__("checkpoint", "relative.json"),
        lambda row: row["audit_attempt"].__setitem__("soft", 601),
        lambda row: row["audit_attempt"].__setitem__("schema_version", 2),
        lambda row: row["audit_attempt"].__setitem__("unexpected", True),
        lambda row: row["audit_attempt"].pop("hard"),
    ],
)
def test_explicit_attempt_metadata_is_revalidated_fail_closed(mutation):
    first = with_attempt(candidate(), 1)
    second = with_attempt(candidate(), 2)
    mutation(second)

    with pytest.raises(AuditStateError, match="audit_attempt|budget"):
        rebuild_audit_state([first, second])


def test_unresolved_digest_keeps_one_stable_representative():
    first = candidate(shift=1, digest="same-unresolved-structure")
    second = candidate(shift=2, digest="same-unresolved-structure")

    rebuilt = rebuild_audit_state([first, second])

    assert list(rebuilt.unresolved) == [first["candidate_key"]]
    assert rebuilt.unresolved[first["candidate_key"]]["canonical_digest"] == (
        "same-unresolved-structure"
    )


def test_current_three_row_legacy_shape_migrates_as_unresolved():
    symplectic = legacy_upper_bound(distance=4, source="symplectic")
    symplectic["structural_novelty"] = {
        "canonical_digest": "legacy-symplectic"
    }
    incumbent = legacy_upper_bound(distance=6)
    incumbent["A_terms"] = [[0, 0], [1, 5], [7, 0]]
    incumbent["B_terms"] = [[0, 0], [5, 1], [0, 7]]
    incumbent["candidate_key"] = code_key(incumbent)
    incumbent["structural_novelty"] = {
        "canonical_digest": "legacy-incumbent"
    }
    dynamic_threshold = threshold_rejected(
        shift=3,
        digest="dynamic-threshold",
    )

    rebuilt = rebuild_audit_state(
        [symplectic, incumbent, dynamic_threshold]
    )

    assert rebuilt.evaluations_seen == 3
    assert len(rebuilt.terminal_keys) == 0
    assert rebuilt.terminal_digests == set()
    assert len(rebuilt.unresolved) == 3


def test_legacy_rebuild_rejects_malformed_or_inconsistent_rows():
    malformed = candidate()
    malformed["candidate_key"] = "forged"
    with pytest.raises(AuditStateError, match=r"evaluation\[0\]"):
        rebuild_audit_state([malformed])

    first = candidate(digest="one")
    second = candidate(digest="two")
    with pytest.raises(AuditStateError, match="canonical_digest changed"):
        rebuild_audit_state([first, second])
