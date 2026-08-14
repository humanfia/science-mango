from __future__ import annotations

import hashlib
import json

import pytest

from humanize import scientific_selector as selector
from humanize.audit_state import AuditOutcome


REPRESENTATION_ID = "test-css-bb-representation"


def _sha256(value):
    return hashlib.sha256(json.dumps(
        value,
        sort_keys=True,
        separators=(",", ":"),
        ensure_ascii=False,
        allow_nan=False,
    ).encode()).hexdigest()


def _candidate(
    tag: int,
    *,
    side: str = "X",
    weight: int = 5,
    ell: int = 2,
    m: int = 2,
    k: int = 1,
    outcome: str = "threshold_rejected",
):
    n = 2 * ell * m
    bits = [0] * n
    for index in range(weight):
        bits[index % n] = 1
    # Tests keep weight <= n.  The assertion makes accidental duplicate bit
    # positions explicit instead of creating a malformed fixture.
    assert sum(bits) == weight
    return {
        "ell": ell,
        "m": m,
        "n": n,
        "k": k,
        "d": weight,
        "A_terms": [[0, 0], [1 % ell, tag % m]],
        "B_terms": [[0, 1 % m], [1 % ell, (tag + 1) % m]],
        "audit_attempt": {
            "schema_version": 2,
            "evidence": {"sha256": "a" * 64},
        },
        "milp_details": {
            "minimum_direction_witness": {
                "side": side,
                "index": 0,
                "weight": weight,
                "bits": bits,
            }
        },
        "mock_outcome": outcome,
        "search_representation_id": REPRESENTATION_ID,
        # Deliberately absurd values: neither field is allowed into a feature
        # or priority key.
        "bp_osd_distance": 999999,
        "fom": 999999.0,
        "score": 999999.0,
    }


def _build(rows, **kwargs):
    return selector.build_negative_witness_risk_index(
        rows,
        representation_id=kwargs.pop("representation_id", REPRESENTATION_ID),
        **kwargs,
    )


@pytest.fixture
def replay_stubs(monkeypatch):
    monkeypatch.setattr(
        selector,
        "classify_evaluation",
        lambda row: AuditOutcome(row["mock_outcome"]),
    )
    monkeypatch.setattr(
        selector,
        "_canonical_witness_support",
        lambda row, *, side, support: (
            tuple(sorted(support)),
            {"verified": True, "report_sha256": "b" * 64},
        ),
    )


def test_context_is_closed_self_hashed_and_negative_only(replay_stubs):
    row = _candidate(0)
    index = _build([row])

    context = index.context()
    assert set(context) == {
        "context_sha256",
        "source_rows_sha256",
        "source_rows",
        "target_mode",
        "representation_id",
        "risk_index_sha256",
        "unknown_semantics",
        "bp_osd_positive_credit",
        "sector_canonicalization",
    }
    unsigned = dict(context)
    claimed = unsigned.pop("context_sha256")
    assert claimed == _sha256(unsigned)
    assert context["unknown_semantics"] == "fail-open-no-vote"
    assert context["bp_osd_positive_credit"] is False
    assert context["target_mode"] == index.target_mode
    assert context["representation_id"] == REPRESENTATION_ID
    assert context["risk_index_sha256"] == index.risk_index_sha256()
    assert context["sector_canonicalization"] == (
        "bb-xz-inversion-block-swap-rowspace-v1"
    )


def test_priority_penalizes_replayed_motifs_and_larger_is_better(replay_stubs):
    bad_motif = _candidate(0)
    index = _build([bad_motif])
    unrelated = _candidate(0, ell=2, m=3, weight=5)

    penalized = index.priority_key(bad_motif)
    neutral = index.priority_key(unrelated)

    assert len(penalized) == 12
    assert all(value <= 0 for value in penalized)
    assert any(value < 0 for value in penalized)
    assert neutral > penalized
    diagnostic = index.diagnostics(bad_motif)
    assert diagnostic["priority_key"] == list(penalized)
    assert diagnostic["semantics"] == (
        "negative-only-no-distance-or-promotion-credit"
    )


def test_unknown_and_unsealed_rows_fail_open_without_a_vote(monkeypatch):
    calls = []

    def classify(row):
        calls.append(row)
        return AuditOutcome.UNRESOLVED_NO_INCUMBENT

    monkeypatch.setattr(selector, "classify_evaluation", classify)
    monkeypatch.setattr(
        selector,
        "_canonical_witness_support",
        lambda *args, **kwargs: pytest.fail("UNKNOWN must not replay a sector"),
    )
    unknown = _candidate(0, outcome="unresolved_no_incumbent")
    unsealed = {**_candidate(1), "audit_attempt": {"schema_version": 1}}

    index = _build([unknown, unsealed])

    assert calls == [unknown]
    assert index.priority_key(unknown) == (0,) * 12
    assert index.observations == ()
    assert index.exclusion_counts == {
        "not_sealed_formal_checkpoint": 1,
        "unknown_no_vote": 1,
    }


def test_bp_osd_and_reported_scores_do_not_change_priority(replay_stubs):
    source = _candidate(0)
    candidate = _candidate(1, ell=2, m=3)
    index = _build([source])
    baseline = index.priority_key(candidate)
    poisoned = {
        **candidate,
        "bp_osd_distance": -10**30,
        "bp_distance": 10**30,
        "osd_distance": -10**30,
        "fom": -10**30,
        "score": 10**30,
    }

    assert index.priority_key(poisoned) == baseline


def test_each_candidate_votes_once_and_lowest_weight_wins(replay_stubs):
    weight_seven = _candidate(0, weight=7, side="Z")
    weight_five = _candidate(0, weight=5, side="X")

    index = _build(
        [weight_seven, weight_five]
    )

    assert len(index.observations) == 1
    assert index.observations[0]["weight"] == 5
    key = index.priority_key(weight_five)
    # One candidate, not two rows, votes in every matching w<=6 bucket.
    assert key[0] == -1
    assert index.exclusion_counts["duplicate_candidate_replaced"] == 1


def test_exact_target_winner_does_not_cast_negative_vote(replay_stubs):
    # For n=k=8 the selected target requires d=4, so exact d=4 is not a
    # target-negative result even though the row contains a witness.
    exact_winner = _candidate(
        0,
        weight=4,
        ell=2,
        m=2,
        k=8,
        outcome="exact",
    )

    index = _build([exact_winner])

    assert index.observations == ()
    assert index.exclusion_counts == {"exact_target_nonnegative_no_vote": 1}


def test_representation_filter_prevents_cross_family_votes(replay_stubs):
    row = {
        **_candidate(0),
        "search_representation_id": "different-family",
    }

    index = _build(
        [row],
        representation_id="current-family",
    )

    assert index.observations == ()
    assert index.exclusion_counts == {
        "incompatible_representation_no_vote": 1
    }


def test_z_support_is_mapped_to_canonical_x_after_verified_isometry(monkeypatch):
    row = _candidate(0, weight=2)
    monkeypatch.setattr(
        selector,
        "_rebuild_bb_matrices",
        lambda _row: ("HX", "HZ"),
    )
    calls = []

    def verify(hx, hz, *, ell, m, geometry):
        calls.append((hx, hz, ell, m, geometry))
        return {"verified": True, "report_sha256": "c" * 64}

    monkeypatch.setattr(selector, "verify_bb_xz_sector_isometry", verify)
    # Involution that swaps the two length-four BB blocks.
    monkeypatch.setattr(
        selector,
        "bb_xz_inversion_block_swap_permutation",
        lambda ell, m, *, geometry: [4, 5, 6, 7, 0, 1, 2, 3],
    )

    z_support, report = selector._canonical_witness_support(
        row,
        side="Z",
        support=(0, 3),
    )
    x_support, _ = selector._canonical_witness_support(
        row,
        side="X",
        support=(0, 3),
    )

    assert z_support == (4, 7)
    assert x_support == (0, 3)
    assert report["verified"] is True
    assert len(calls) == 2


def test_failed_isometry_is_fail_open_no_vote(monkeypatch):
    row = _candidate(0)
    monkeypatch.setattr(
        selector,
        "classify_evaluation",
        lambda _row: AuditOutcome.THRESHOLD_REJECTED,
    )
    monkeypatch.setattr(
        selector,
        "_canonical_witness_support",
        lambda *args, **kwargs: (_ for _ in ()).throw(
            ValueError("unverified isometry")
        ),
    )

    index = _build([row])

    assert index.observations == ()
    assert index.exclusion_counts == {
        "witness_or_isometry_replay_failed_no_vote": 1
    }


def test_risk_index_artifact_is_self_hashed(replay_stubs):
    index = _build([_candidate(0)])

    artifact = index.as_dict()
    claimed = artifact["risk_index_sha256"]
    payload = {
        key: value
        for key, value in artifact.items()
        if key not in {"risk_index_sha256", "context"}
    }

    assert artifact["policy_id"] == selector.NEGATIVE_WITNESS_POLICY_ID
    assert claimed == _sha256(payload)
    assert artifact["context"]["risk_index_sha256"] == claimed
    assert artifact["diagnostics"]["raw_sector_counts_available"] is False


def test_context_binds_target_representation_and_derived_risk(replay_stubs):
    row = _candidate(0)
    gist = _build([row])
    scalar = _build([row], target_mode="scalar-fom-strict-v1")
    other_rep = _build([], representation_id="other-css-bb-representation")

    assert gist.context()["context_sha256"] != scalar.context()["context_sha256"]
    assert gist.context()["context_sha256"] != other_rep.context()["context_sha256"]

    before = gist.context()
    [entry] = gist.risks["full"].values()
    entry["counts"]["target_excluding"] += 1
    after = gist.context()

    assert before["source_rows_sha256"] == after["source_rows_sha256"]
    assert before["risk_index_sha256"] != after["risk_index_sha256"]
    assert before["context_sha256"] != after["context_sha256"]
