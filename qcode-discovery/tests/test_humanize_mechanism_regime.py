"""Regression tests for mechanism-stratified audits and trusted regimes."""

from __future__ import annotations

import copy
import hashlib

import pytest

import humanize.flow as flow_module
from humanize.flow import (
    FlowConfig,
    RoundTransactionError,
    SEARCH_REGIME_PREFIX,
    _candidate_audit_stratum,
    _freeze_round_context,
    _normal_search_regime,
    _replay_search_regime,
    _sealed_exact_distances,
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


def _round(number: int, *distances: int, raw: int, unique: int) -> dict:
    return {
        "round": number,
        "sealed_exact_audit": _exact_summary(*distances),
        "candidate_diversity": _diversity(raw=raw, unique=unique),
    }


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
