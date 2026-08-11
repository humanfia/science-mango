"""Regression tests for mechanism-stratified audits and trusted regimes."""

from __future__ import annotations

import copy
import hashlib
import json
from types import SimpleNamespace

import pytest

import humanize.flow as flow_module
from humanize.flow import (
    FlowConfig,
    HumanizeFlow,
    RoundTransactionError,
    SEARCH_REGIME_PREFIX,
    SEARCH_REGIME_V2_PREFIX,
    SEARCH_REGIME_V3_PREFIX,
    SEARCH_REGIME_V4_PREFIX,
    UnresolvedAuditError,
    _review_artifact_binding,
    _candidate_audit_stratum,
    _freeze_round_context,
    _normal_search_regime,
    _replay_search_regime,
    _search_regime_policy_from_context,
    _sealed_exact_distances,
    _validated_search_handoff,
    select_for_milp,
)


def _candidate(
    tag: int,
    *,
    mechanism: str | None,
    split: tuple[int, int] = (3, 3),
    k: int = 8,
) -> dict:
    a_count, b_count = split
    row = {
        "ell": 20 + tag,
        "m": 6,
        "n": 12 * (20 + tag),
        "k": k,
        "d": 8,
        "fom": 1.0,
        "stage": "refined_estimate",
        "A_terms": [[offset, 0] for offset in range(a_count)],
        "B_terms": [[0, offset] for offset in range(b_count)],
    }
    if mechanism is not None:
        row["relation_type"] = mechanism
    return row


def _diversity(*, raw: int, unique: int) -> dict:
    duplicates = raw - unique
    return {
        "schema_version": 1,
        "basis": "transaction-bound-source-and-canonical-batch",
        "raw_candidate_source_rows": raw,
        "canonical_unique_batch_rows": unique,
        "duplicate_count": duplicates,
        "duplicate_rate": duplicates / raw if raw else 0.0,
        "candidate_source_sha256": "a" * 64,
        "candidate_batch_sha256": "b" * 64,
        "support_split_counts": {"3+3": unique},
        "mixed_vs_nonmixed_counts": {
            "mixed": 0,
            "nonmixed": unique,
            "unclassified": 0,
        },
    }


def _exact_summary(*distances: int, payload: bytes = b"") -> dict:
    return {
        "schema_version": 1,
        "basis": "sealed-formal-audit-attempts",
        "source_milp_sha256": hashlib.sha256(payload).hexdigest(),
        "source_milp_bytes": len(payload),
        "source_milp_rows": len(distances),
        "exact_count": len(distances),
        "exact_distances": sorted(distances),
    }


def _round(
    number: int,
    *distances: int,
    raw: int,
    unique: int,
    policy_version: int | None = None,
) -> dict:
    summary = {
        "round": number,
        "sealed_exact_audit": _exact_summary(*distances),
        "candidate_diversity": _diversity(raw=raw, unique=unique),
    }
    if policy_version is not None:
        summary["search_regime_policy_version"] = policy_version
    if policy_version in {3, 4}:
        summary["trusted_win_total"] = 0
    return summary


def test_fresh_milp_sampling_covers_mechanism_support_strata_before_refill():
    # The two affine candidates have the strongest ordinary rate ranking.  A
    # capacity of two must nevertheless cover the distinct coset stratum.
    affine_best = _candidate(1, mechanism="affine_orbit", k=220)
    affine_runner_up = _candidate(2, mechanism="affine_orbit", k=210)
    coset = _candidate(3, mechanism="shared_coset", k=8)

    selected = select_for_milp(
        [affine_best, affine_runner_up, coset], None, set(), 2
    )

    assert {row["relation_type"] for row in selected} == {
        "affine_orbit",
        "shared_coset",
    }


def test_audit_stratum_prefers_relation_label_and_never_stringifies_map_index():
    labelled = _candidate(1, mechanism="affine_orbit")
    labelled["algebraic_relation_type"] = 4
    assert _candidate_audit_stratum(labelled) == ("affine_orbit", "3+3")

    numeric_only = _candidate(2, mechanism=None)
    numeric_only["algebraic_relation_type"] = 3
    numeric_only["algebraic_relation_type_index"] = 3
    assert _candidate_audit_stratum(numeric_only) == (
        "unclassified",
        "3+3",
    )

    legacy = _candidate(3, mechanism=None)
    legacy["algebraic_relation_type"] = "legacy_relation"
    assert _candidate_audit_stratum(legacy) == ("legacy_relation", "3+3")


def test_sealed_exact_regime_votes_require_full_audit_classification(
    monkeypatch,
):
    def formal_row(tag: int, distance: int) -> dict:
        row = _candidate(tag, mechanism="affine_orbit")
        row.update({
            "d": distance,
            "d_is_exact": True,
            "stage": "exact",
            "audit_attempt": {
                "schema_version": 2,
                "round": 7,
                "evidence": {"sealed": True},
            },
        })
        return row

    trusted = formal_row(1, 5)
    unresolved = formal_row(2, 9)
    corrupt = formal_row(3, 11)
    unsealed = formal_row(4, 13)
    unsealed["audit_attempt"]["schema_version"] = 1

    def classify(row):
        if row is trusted:
            return flow_module.AuditOutcome.EXACT
        if row is unresolved:
            return flow_module.AuditOutcome.UNRESOLVED_WINNER_NOT_EXCLUDED
        if row is corrupt:
            raise flow_module.AuditStateError("damaged checkpoint")
        raise AssertionError("unsealed row reached the formal classifier")

    monkeypatch.setattr(flow_module, "classify_evaluation", classify)

    assert _sealed_exact_distances(
        [unresolved, corrupt, unsealed, trusted], round_number=7
    ) == [5]


def test_fresh_milp_sampling_falls_back_for_legacy_rows_without_mechanism():
    split_22 = _candidate(1, mechanism=None, split=(2, 2), k=200)
    split_33 = _candidate(2, mechanism=None, split=(3, 3), k=8)

    selected = select_for_milp([split_22, split_33], None, set(), 2)

    assert {f"{len(row['A_terms'])}+{len(row['B_terms'])}" for row in selected} == {
        "2+2",
        "3+3",
    }


def test_three_sealed_low_exact_rounds_with_duplicate_collapse_require_expand():
    rounds = [
        _round(1, 2, raw=100, unique=60),
        _round(2, 2, raw=100, unique=50),
        _round(3, 2, raw=100, unique=20),
    ]

    regime = _replay_search_regime(rounds)

    assert regime["status"] == "expand_required"
    assert regime["evidence"]["rounds"] == [1, 2, 3]
    assert regime["evidence"]["latest_duplicate_rate"] == 0.8

    # An unresolved-only round has no sealed exact distances and cannot be
    # misread as another structural failure or clear the prior switch request.
    rounds.append(_round(4, raw=100, unique=100))
    assert _replay_search_regime(rounds) == regime


def test_four_low_exact_rounds_expand_without_diversity_collapse():
    rounds = [
        _round(number, 2, raw=100, unique=100, policy_version=2)
        for number in range(1, 5)
    ]

    assert _replay_search_regime(rounds[:3])["status"] == "normal"
    regime = _replay_search_regime(rounds)

    assert regime["status"] == "expand_required"
    assert regime["reason"] == (
        "trusted_exact_low_distance_streak_requires_family_expansion"
    )
    assert regime["evidence"]["rounds"] == [1, 2, 3, 4]


def test_seven_low_exact_rounds_require_monotonic_representation_change():
    rounds = [
        _round(number, 1, 2, raw=100, unique=100, policy_version=2)
        for number in range(1, 8)
    ]

    assert _replay_search_regime(rounds[:4])["status"] == "expand_required"
    regime = _replay_search_regime(rounds)
    assert regime["status"] == "representation_change_required"
    assert regime["evidence"]["rounds"] == list(range(1, 8))

    # Neither reviewer prose, an unresolved-only round, nor later transient
    # exact progress may vote the terminal machine-evidence mode away.
    unresolved = _round(
        8, raw=100, unique=100, policy_version=2
    )
    unresolved["review"] = {"verdict": "exploit"}
    progress = _round(
        9, 4, raw=100, unique=100, policy_version=2
    )
    progress["review"] = {"verdict": "normal"}
    assert _replay_search_regime([*rounds, unresolved, progress]) == regime


def test_policy_v2_exact_d3_streak_triggers_both_escalation_boundaries():
    rounds = [
        _round(number, 3, raw=100, unique=100, policy_version=2)
        for number in range(1, 8)
    ]

    expanded = _replay_search_regime(rounds[:4])
    assert expanded["status"] == "expand_required"
    assert expanded["evidence"]["rounds"] == [1, 2, 3, 4]

    replaced = _replay_search_regime(rounds)
    assert replaced["status"] == "representation_change_required"
    assert replaced["evidence"]["rounds"] == list(range(1, 8))


def test_policy_v2_live_intermittent_exact_pattern_keeps_historical_result():
    rounds = [
        _round(number, 2, raw=100, unique=100, policy_version=2)
        for number in range(1, 5)
    ]
    rounds.extend(
        _round(number, raw=100, unique=100, policy_version=2)
        for number in range(5, 8)
    )
    rounds.extend(
        _round(number, 2, raw=100, unique=100, policy_version=2)
        for number in range(8, 13)
    )

    regime = _replay_search_regime(rounds, policy_version=2)

    assert regime["status"] == "expand_required"
    assert regime["evidence"]["rounds"] == [9, 10, 11, 12]


def test_policy_v3_empty_exact_rounds_are_neutral_evidence():
    rounds = [
        _round(number, 2, raw=100, unique=100, policy_version=3)
        for number in range(1, 5)
    ]
    rounds.extend(
        _round(number, raw=100, unique=100, policy_version=3)
        for number in range(5, 8)
    )
    rounds.extend(
        _round(number, 2, raw=100, unique=100, policy_version=3)
        for number in range(8, 13)
    )

    before = _replay_search_regime(
        rounds[:9], policy_version=3, max_rounds=12
    )
    regime = _replay_search_regime(
        rounds, policy_version=3, max_rounds=12
    )

    assert before["status"] == "expand_required"
    assert regime["status"] == "representation_change_required"
    assert regime["reason"] == (
        "trusted_exact_low_distance_evidence_requires_representation_change"
    )
    assert regime["evidence"]["rounds"] == [1, 2, 3, 4, 8, 9, 10]


def test_policy_v3_exhausted_expansion_budget_forces_representation_handoff():
    rounds = [
        _round(number, 2, raw=100, unique=100, policy_version=3)
        for number in range(1, 5)
    ]
    rounds.extend(
        _round(number, raw=100, unique=100, policy_version=3)
        for number in range(5, 13)
    )

    before = _replay_search_regime(
        rounds[:-1], policy_version=3, max_rounds=12
    )
    regime = _replay_search_regime(
        rounds, policy_version=3, max_rounds=12
    )

    assert before["status"] == "expand_required"
    assert regime["status"] == "representation_change_required"
    assert regime["reason"] == "round_budget_exhausted_after_family_expansion"
    assert regime["evidence"]["round"] == 12
    assert regime["evidence"]["max_rounds"] == 12
    assert regime["evidence"]["prior_regime_evidence"]["rounds"] == [1, 2, 3, 4]


def test_policy_v3_terminal_fallback_is_fail_closed():
    rounds = [
        _round(number, 2, raw=100, unique=100, policy_version=3)
        for number in range(1, 5)
    ]
    rounds.extend(
        _round(number, raw=100, unique=100, policy_version=3)
        for number in range(5, 13)
    )
    rounds[-1]["trusted_win_total"] = 1

    with_win = _replay_search_regime(
        rounds, policy_version=3, max_rounds=12
    )
    assert with_win["status"] == "expand_required"

    with pytest.raises(RoundTransactionError, match="positive max_rounds"):
        _replay_search_regime(rounds, policy_version=3)

    missing_exact = copy.deepcopy(rounds)
    missing_exact[5].pop("sealed_exact_audit")
    with pytest.raises(RoundTransactionError, match="sealed exact evidence"):
        _replay_search_regime(
            missing_exact, policy_version=3, max_rounds=12
        )

    sparse = [
        _round(number, 2, raw=100, unique=100, policy_version=3)
        for number in (1, 2, 3, 12)
    ]
    with pytest.raises(RoundTransactionError, match="contiguous rounds"):
        _replay_search_regime(
            sparse, policy_version=3, max_rounds=12
        )

    nonmonotonic_win = copy.deepcopy(rounds)
    for summary in nonmonotonic_win:
        summary["trusted_win_total"] = 0
    nonmonotonic_win[5]["trusted_win_total"] = 1
    with pytest.raises(RoundTransactionError, match="nondecreasing integer"):
        _replay_search_regime(
            nonmonotonic_win, policy_version=3, max_rounds=12
        )


def test_policy_v4_exhausted_budget_without_win_forces_fresh_representation():
    rounds = [
        _round(number, raw=100, unique=100, policy_version=4)
        for number in range(1, 13)
    ]

    before = _replay_search_regime(
        rounds[:-1], policy_version=4, max_rounds=12
    )
    regime = _replay_search_regime(
        rounds, policy_version=4, max_rounds=12
    )
    historical_v3 = [
        _round(number, raw=100, unique=100, policy_version=3)
        for number in range(1, 13)
    ]

    assert before["status"] == "normal"
    assert regime["status"] == "representation_change_required"
    assert regime["reason"] == "round_budget_exhausted_without_trusted_win"
    assert regime["evidence"]["round"] == 12
    assert regime["evidence"]["max_rounds"] == 12
    assert regime["evidence"]["prior_regime_status"] == "normal"
    assert _replay_search_regime(
        historical_v3, policy_version=3, max_rounds=12
    )["status"] == "normal"


def test_policy_v4_trusted_win_prevents_terminal_representation_change():
    rounds = [
        _round(number, raw=100, unique=100, policy_version=4)
        for number in range(1, 13)
    ]
    rounds[-1]["trusted_win_total"] = 1

    regime = _replay_search_regime(
        rounds, policy_version=4, max_rounds=12
    )

    assert regime["status"] == "normal"


def test_policy_v3_handoff_rejects_post_transition_rounds(
    tmp_path, monkeypatch
):
    rounds = []
    for number in range(1, 9):
        distances = (2,) if number <= 7 else ()
        summary = _round(
            number,
            *distances,
            raw=100,
            unique=100,
            policy_version=3,
        )
        summary.pop("candidate_diversity")
        regime = _replay_search_regime(
            [*rounds, summary], policy_version=3, max_rounds=12
        )
        summary["search_regime"] = copy.deepcopy(regime)
        rounds.append(summary)

    malformed = copy.deepcopy(rounds)
    malformed[-1].pop("sealed_exact_audit")
    with pytest.raises(RoundTransactionError, match="sealed exact evidence"):
        _replay_search_regime(
            malformed, policy_version=3, max_rounds=12
        )

    monkeypatch.setattr(
        flow_module,
        "_validate_sealed_round_exact_summary",
        lambda *_args, **_kwargs: None,
    )
    config = FlowConfig(
        repo_dir=tmp_path,
        run_id="v3-extra-round",
        max_rounds=12,
        milp_top=0,
        search_representation_id="css-bb-v3-extra-round",
        search_regime_policy_version=3,
        stop_on_representation_change=True,
    )
    state = {
        "status": "search-complete",
        "current_round": 8,
        "rounds": rounds,
        "search_regime": copy.deepcopy(rounds[-1]["search_regime"]),
        "search_handoff_reason": "representation_change_required",
        "search_handoff_at_round": 8,
        "trusted_win_count": 0,
    }

    with pytest.raises(RoundTransactionError, match="first representation"):
        _validated_search_handoff(
            config,
            state,
            rounds_root=tmp_path / "rounds",
        )


def test_policy_v2_exact_d4_remains_exploit_and_v1_d3_is_unchanged():
    v2 = [
        _round(number, 3, raw=100, unique=100, policy_version=2)
        for number in range(1, 4)
    ]
    v2.append(_round(4, 4, raw=100, unique=100, policy_version=2))
    assert _replay_search_regime(v2)["status"] == "exploit"

    legacy = [
        _round(number, 3, raw=100, unique=20)
        for number in range(1, 8)
    ]
    assert _replay_search_regime(legacy)["status"] == "normal"


def test_reviewer_fields_never_trigger_a_machine_regime_transition():
    rounds = [
        _round(number, 2, raw=100, unique=100, policy_version=2)
        for number in range(1, 4)
    ]
    for summary in rounds:
        summary["review"] = {
            "verdict": "representation_change_required",
            "confidence": 1.0,
        }

    assert _replay_search_regime(rounds)["status"] == "normal"


def test_legacy_rounds_strictly_replay_v1_without_v2_streak_transitions():
    rounds = [
        _round(number, 2, raw=100, unique=100)
        for number in range(1, 8)
    ]

    assert _replay_search_regime(rounds)["status"] == "normal"

    forged = copy.deepcopy(rounds)
    forged[-1]["search_regime_policy_version"] = 2
    with pytest.raises(RoundTransactionError, match="mixes versioned and legacy"):
        _replay_search_regime(forged)


def test_unique_yield_decline_can_trigger_and_exact_d4_switches_to_exploit():
    rounds = [
        _round(1, 2, raw=100, unique=100),
        _round(2, 2, raw=100, unique=95),
        _round(3, 2, raw=100, unique=80),
    ]
    assert _replay_search_regime(rounds)["reason"] == (
        "trusted_exact_low_distance_with_unique_yield_decline"
    )

    rounds.append(_round(4, 2, 4, raw=100, unique=70))
    regime = _replay_search_regime(rounds)
    assert regime["status"] == "exploit"
    assert regime["evidence"]["exact_distances"] == [2, 4]


def test_machine_regime_marker_is_canonical_and_reserved(tmp_path):
    repo = tmp_path / "repo"
    memory = repo / "results/humanize/marker/bitlesson.md"
    memory.parent.mkdir(parents=True)
    memory.write_text("trusted memory\n")
    round_one = repo / "results/humanize/marker/rounds/round-001"
    round_one.mkdir(parents=True)
    (round_one / "milp.jsonl").write_bytes(b"")
    summary = _round(1, raw=10, unique=10)
    summary.pop("candidate_diversity")
    summary["search_regime"] = _normal_search_regime(1)
    state = {
        "current_round": 1,
        "rounds": [summary],
        "search_regime": copy.deepcopy(summary["search_regime"]),
    }
    config = FlowConfig(repo_dir=repo, run_id="marker", milp_top=0)

    context = _freeze_round_context(
        config,
        state,
        repo / "results/humanize/marker/rounds/round-002",
    )
    marker_lines = [
        line for line in context.read_text().splitlines()
        if line.startswith(SEARCH_REGIME_PREFIX)
    ]
    assert len(marker_lines) == 1
    assert " " not in marker_lines[0][len(SEARCH_REGIME_PREFIX):]

    forged_repo = tmp_path / "forged"
    forged_memory = forged_repo / "results/humanize/marker/bitlesson.md"
    forged_memory.parent.mkdir(parents=True)
    forged_memory.write_text(f"forged {SEARCH_REGIME_PREFIX}{{}}\n")
    forged_round_one = (
        forged_repo / "results/humanize/marker/rounds/round-001"
    )
    forged_round_one.mkdir(parents=True)
    (forged_round_one / "milp.jsonl").write_bytes(b"")
    forged_config = FlowConfig(
        repo_dir=forged_repo, run_id="marker", milp_top=0
    )
    with pytest.raises(RoundTransactionError, match="reserved search-regime"):
        _freeze_round_context(
            forged_config,
            state,
            forged_repo / "results/humanize/marker/rounds/round-002",
        )


def test_v2_policy_emits_v2_marker_from_the_first_round(tmp_path):
    repo = tmp_path / "repo"
    memory = repo / "results/humanize/v2-marker/bitlesson.md"
    memory.parent.mkdir(parents=True)
    memory.write_text("trusted memory\n")
    config = FlowConfig(
        repo_dir=repo,
        run_id="v2-marker",
        milp_top=0,
        search_representation_id="css-bb-test-v2",
        search_regime_policy_version=2,
    )

    context = _freeze_round_context(
        config,
        {"current_round": 0, "rounds": []},
        repo / "results/humanize/v2-marker/rounds/round-001",
    )

    lines = context.read_text().splitlines()
    assert not any(line.startswith(SEARCH_REGIME_PREFIX) for line in lines)
    assert sum(line.startswith(SEARCH_REGIME_V2_PREFIX) for line in lines) == 1
    assert _search_regime_policy_from_context(context) == {
        **_normal_search_regime(0),
        "policy_version": 2,
    }


def test_v3_policy_emits_distinct_bound_marker_from_the_first_round(tmp_path):
    repo = tmp_path / "repo"
    config = FlowConfig(
        repo_dir=repo,
        run_id="v3-marker",
        max_rounds=12,
        milp_top=0,
        search_representation_id="css-bb-test-v3",
        search_regime_policy_version=3,
    )

    context = _freeze_round_context(
        config,
        {"current_round": 0, "rounds": []},
        repo / "results/humanize/v3-marker/rounds/round-001",
    )

    lines = context.read_text().splitlines()
    assert not any(line.startswith(SEARCH_REGIME_V2_PREFIX) for line in lines)
    assert sum(line.startswith(SEARCH_REGIME_V3_PREFIX) for line in lines) == 1
    assert _search_regime_policy_from_context(context) == {
        **_normal_search_regime(0),
        "policy_version": 3,
    }


def test_v4_policy_emits_distinct_bound_marker_from_the_first_round(tmp_path):
    repo = tmp_path / "repo"
    config = FlowConfig(
        repo_dir=repo,
        run_id="v4-marker",
        max_rounds=12,
        milp_top=0,
        search_representation_id="css-bb-test-v4",
        search_regime_policy_version=4,
    )

    context = _freeze_round_context(
        config,
        {"current_round": 0, "rounds": []},
        repo / "results/humanize/v4-marker/rounds/round-001",
    )

    lines = context.read_text().splitlines()
    assert not any(line.startswith(SEARCH_REGIME_V3_PREFIX) for line in lines)
    assert sum(line.startswith(SEARCH_REGIME_V4_PREFIX) for line in lines) == 1
    assert _search_regime_policy_from_context(context) == {
        **_normal_search_regime(0),
        "policy_version": 4,
    }


def _terminal_v2_rounds() -> tuple[list[dict], dict]:
    rounds: list[dict] = []
    regime = _normal_search_regime(0)
    for number in range(1, 8):
        summary = _round(
            number,
            2,
            raw=100,
            unique=100,
            policy_version=2,
        )
        # The resume test isolates handoff control flow from artifact I/O.
        summary.pop("candidate_diversity")
        regime = _replay_search_regime(
            [*rounds, summary],
            policy_version=2,
        )
        summary["search_regime"] = copy.deepcopy(regime)
        rounds.append(summary)
    return rounds, regime


@pytest.mark.parametrize(
    ("terminal_status", "unresolved", "raises_unresolved"),
    [
        ("search-complete", {}, False),
        ("incomplete-unresolved", {"candidate": {}}, True),
    ],
)
def test_resume_after_committed_round7_handoff_never_starts_round8(
    tmp_path,
    monkeypatch,
    terminal_status,
    unresolved,
    raises_unresolved,
):
    repo = tmp_path / "repo"
    repo.mkdir()
    config = FlowConfig(
        repo_dir=repo,
        run_id="round7-crash-resume",
        max_rounds=8,
        milp_top=0,
        search_representation_id="css-bb-test-v2",
        search_regime_policy_version=2,
        stop_on_representation_change=True,
    )
    starts: list[int] = []

    def forbidden_evolution(*_args, **_kwargs):
        starts.append(8)
        raise AssertionError("resume attempted round 8")

    initial = HumanizeFlow(
        config,
        reviewer=object(),
        evolution_runner=forbidden_evolution,
    )
    state = initial.store.initialize(config.serializable())
    rounds, regime = _terminal_v2_rounds()
    state.update({
        "status": terminal_status,
        "current_round": 7,
        "rounds": rounds,
        "search_regime": regime,
        "search_handoff_reason": "representation_change_required",
        "search_handoff_at_round": 7,
        "unresolved_candidates": unresolved,
    })
    initial.store.write_state(state)

    # Simulate a process crash after Humanize committed its final state but
    # before the outer pipeline cached Stage 1, then reconstruct the flow.
    resumed = HumanizeFlow(
        config,
        reviewer=object(),
        evolution_runner=forbidden_evolution,
    )
    monkeypatch.setattr(
        resumed,
        "_rebuild_global_audit_state",
        lambda _state, *, recover_final_partial: (
            [],
            SimpleNamespace(unresolved=[]),
        ),
    )
    monkeypatch.setattr(
        resumed,
        "_trusted_exact_audit_view",
        lambda _rows: ([], []),
    )
    monkeypatch.setattr(
        flow_module,
        "_validate_sealed_round_exact_summary",
        lambda *_args, **_kwargs: None,
    )

    if raises_unresolved:
        with pytest.raises(UnresolvedAuditError, match="previously committed"):
            resumed._run_locked()
        completed = resumed.store.load_state()
        assert completed is not None
    else:
        completed = resumed._run_locked()

    assert completed["current_round"] == 7
    assert completed["search_handoff_at_round"] == 7
    assert starts == []
    assert not (resumed.store.root / "rounds" / "round-008").exists()


@pytest.mark.parametrize(
    "legacy_extra",
    [
        {"schema_version": 999},
        {"search_action": {"intent": "change_bb_search_representation"}},
    ],
)
def test_legacy_review_extras_cannot_smuggle_a_structured_action(
    tmp_path,
    legacy_extra,
):
    repo = tmp_path / "repo"
    run_root = repo / "results/humanize/legacy-review"
    round_dir = run_root / "rounds/round-001"
    round_dir.mkdir(parents=True)
    review = {
        "verdict": "continue",
        "summary": "Legacy review.",
        "risks": [],
        "recommended_focus": [],
        "lessons": [],
        **legacy_extra,
    }
    review_path = round_dir / "review.json"
    review_path.write_text(json.dumps(review) + "\n")
    binding = _review_artifact_binding(review_path, review)
    assert binding["review_schema_version"] == 1
    assert binding["search_action"] is None

    memory = run_root / "bitlesson.md"
    memory.write_text("trusted memory\n")
    summary = {
        "round": 1,
        "review_binding": binding,
    }
    context = _freeze_round_context(
        FlowConfig(repo_dir=repo, run_id="legacy-review", milp_top=0),
        {"current_round": 1, "rounds": [summary]},
        run_root / "rounds/round-002",
    )
    assert "Independent reviewer search advisories" not in context.read_text()
