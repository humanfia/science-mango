"""Search-cascade integration for proof-safe low-weight evidence."""

from __future__ import annotations

import copy

import pytest

import evaluation.evaluator as candidate_evaluator
import evolve.openevolve_evaluator as search_evaluator


GROSS_A = [(3, 0), (0, 1), (0, 2)]
GROSS_B = [(0, 3), (1, 0), (2, 0)]
D2_A = [(0, 3), (6, 0)]
D2_B = [(1, 1), (2, 0), (6, 0), (9, 1)]


def _hide_symplectic_shortcuts(monkeypatch):
    monkeypatch.setattr(
        candidate_evaluator,
        "symplectic_weight_bound",
        lambda code: (code.num_qudits, code.num_qudits, code.num_qudits),
    )


def test_replayed_d2_oracle_witness_rejects_before_bp(monkeypatch):
    _hide_symplectic_shortcuts(monkeypatch)

    def forbidden_bp(*_args, **_kwargs):
        raise AssertionError("BP must not run after a low-weight witness")

    monkeypatch.setattr(candidate_evaluator, "estimate_distance", forbidden_bp)
    row = candidate_evaluator.evaluate_candidate(
        12,
        6,
        D2_A,
        D2_B,
        skip_exact=True,
        skip_osd_cs=True,
        challenge_target_fom=12.0,
        low_weight_oracle_max_weight=4,
    )

    assert (row["n"], row["k"]) == (144, 28)
    assert row["stage"] == "low_weight_oracle_rejected"
    assert row["search_status"] == "terminal_negative"
    assert row["threshold_proof_source"] == "low_weight_oracle"
    assert row["threshold_proof_distance"] == 2
    assert row["threshold_proof_witness"]["side"] == "X"
    assert sum(row["threshold_proof_witness"]["bits"]) == 2
    assert row["low_weight_oracle"]["outcome"] == "SAT"
    persisted = search_evaluator._candidate_jsonl_record(row)
    assert persisted is not None
    assert persisted["low_weight_oracle"]["witness"]["support"] == row[
        "low_weight_oracle"
    ]["witness"]["support"]
    assert persisted["threshold_proof_witness"]["bits"] == row[
        "threshold_proof_witness"
    ]["bits"]


def test_two_sector_unsat_survives_bp_and_earns_bounded_lower_signal(
    monkeypatch,
):
    monkeypatch.setattr(
        search_evaluator,
        "ACTIVE_GEOMETRY_CONTRACT",
        search_evaluator.PUBLISHED_VOLUME_ANSATZ_V3_GEOMETRY_CONTRACT,
    )
    _hide_symplectic_shortcuts(monkeypatch)
    monkeypatch.setattr(candidate_evaluator, "estimate_distance", lambda *_a, **_k: 6)
    row = candidate_evaluator.evaluate_candidate(
        12,
        6,
        GROSS_A,
        GROSS_B,
        skip_exact=True,
        skip_osd_cs=True,
        challenge_target_fom=12.0,
        low_weight_oracle_max_weight=4,
    )

    assert (row["n"], row["k"]) == (144, 12)
    assert row["low_weight_oracle"]["outcome"] == "UNSAT"
    assert row["distance_lower_bound"] == 5
    assert row["distance_lower_bound_proven"] is True
    assert row["fom_lower_bound"] == pytest.approx(12 * 25 / 144)
    assert row["distance_status"] == "upper_bound"
    assert row["search_status"] == "certified_lower_bound"
    persisted = search_evaluator._candidate_jsonl_record(row)
    assert persisted is not None
    assert persisted["distance_lower_bound"] == 5
    assert persisted["low_weight_oracle"]["outcome"] == "UNSAT"

    scored = search_evaluator._score_stage2_upper_bound_safe([row])
    unresolved = copy.deepcopy(row)
    for field in (
        "distance_lower_bound",
        "distance_lower_bound_proven",
        "distance_lower_bound_status",
        "fom_lower_bound",
        "low_weight_oracle_threshold",
        "low_weight_oracle",
    ):
        unresolved.pop(field, None)
    unresolved["search_status"] = "unresolved"
    baseline = search_evaluator._score_stage2_upper_bound_safe([unresolved])

    assert scored["fitness_lower_bound_credit"] == pytest.approx(12 * 25 / 144)
    assert baseline["fitness_distance_credit"] == 0.0
    assert baseline["fitness_survivor_credit"] == 0.0
    assert baseline["combined_score"] == 0.0
    assert scored["combined_score"] > baseline["combined_score"]

    tampered = copy.deepcopy(row)
    tampered["A_terms"] = [(0, 0), (0, 1)]
    assert search_evaluator._normalized_stage2_lower_bound_row(tampered) is None
    assert search_evaluator._score_stage2_upper_bound_safe([tampered])[
        "fitness_lower_bound_credit"
    ] == 0.0

    forged_sat_unsat = copy.deepcopy(row)
    forged_sat_unsat.update({
        "low_weight_oracle_threshold": 5,
        "distance_lower_bound": 6,
        "fom_lower_bound": 12 * 36 / 144,
    })
    forged_sat_unsat["low_weight_oracle"]["max_weight"] = 5
    forged_sat_unsat["low_weight_oracle"]["distance_lower_bound"] = 6
    for sector in ("X", "Z"):
        forged_sat_unsat["low_weight_oracle"]["sectors"][sector][
            "max_weight"
        ] = 5
        forged_sat_unsat["low_weight_oracle"]["sectors"][sector][
            "binding"
        ]["engine"] = "css-global-threshold-sat-v1"
    assert (
        search_evaluator._normalized_stage2_lower_bound_row(
            forged_sat_unsat
        )
        is None
    )
    assert search_evaluator._score_stage2_upper_bound_safe([
        forged_sat_unsat
    ])["fitness_lower_bound_credit"] == 0.0


def test_decoder_bound_below_oracle_lower_bound_fails_closed(monkeypatch):
    _hide_symplectic_shortcuts(monkeypatch)
    monkeypatch.setattr(candidate_evaluator, "estimate_distance", lambda *_a, **_k: 2)
    row = candidate_evaluator.evaluate_candidate(
        12,
        6,
        GROSS_A,
        GROSS_B,
        skip_exact=True,
        skip_osd_cs=True,
        challenge_target_fom=12.0,
        low_weight_oracle_max_weight=4,
    )

    assert row["distance_lower_bound"] == 5
    assert row["search_status"] == "retry"
    assert row["distance_retry_required"] is True
    assert row["distance_evidence_conflict"]["upper_bound"] == 2
    scored = search_evaluator._score_stage2_upper_bound_safe([row])
    assert scored["combined_score"] == 0.0
    assert scored["fitness_lower_bound_credit"] == 0.0


def test_oracle_unknown_is_retryable_and_never_reaches_bp(monkeypatch):
    _hide_symplectic_shortcuts(monkeypatch)
    monkeypatch.setattr(
        candidate_evaluator,
        "evaluate_css_low_weight_oracle",
        lambda *_a, **_k: {
            "schema_version": 1,
            "kind": "qcode-css-low-weight-oracle",
            "outcome": "UNKNOWN",
            "decision_complete": False,
            "retryable": True,
            "distance_lower_bound": None,
        },
    )
    monkeypatch.setattr(
        candidate_evaluator,
        "verify_css_low_weight_oracle",
        lambda *_a, **_k: [],
    )

    def forbidden_bp(*_args, **_kwargs):
        raise AssertionError("BP must not launder UNKNOWN into survivor credit")

    monkeypatch.setattr(candidate_evaluator, "estimate_distance", forbidden_bp)
    row = candidate_evaluator.evaluate_candidate(
        12,
        6,
        GROSS_A,
        GROSS_B,
        skip_exact=True,
        skip_osd_cs=True,
        challenge_target_fom=12.0,
        low_weight_oracle_max_weight=4,
    )

    assert row["search_status"] == "retry"
    assert row["distance_retry_required"] is True
    assert row["fitness_distance_credit"] == 0.0
    assert row["low_weight_oracle"]["outcome"] == "UNKNOWN"
    assert search_evaluator._score_stage2_upper_bound_safe([row])[
        "combined_score"
    ] == 0.0
