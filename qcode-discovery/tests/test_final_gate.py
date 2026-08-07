"""Tests for the fail-closed qLDPC challenge acceptance gate."""

import hashlib
import json

import pytest

from evaluation.final_gate import (
    TARGET_MODE_GIST,
    TARGET_MODE_SCALAR,
    classify_target_win,
    classify_win,
    minimum_target_distance,
    minimum_winning_distance,
    evaluate_final_gate,
    target_binding,
    validate_target_binding,
    validate_known_answer_artifact,
)
from evaluation.structural_dedup import check_css_structural_novelty


def _baseline_artifact():
    rows = []
    for label, n, k, d in (
        ("[[72,12,6]]", 72, 12, 6),
        ("[[90,8,10]]", 90, 8, 10),
        ("[[144,12,12]]", 144, 12, 12),
    ):
        total = 2 * k
        rows.append({
            "label": label,
            "status": "passed",
            "observed": {"n": n, "k": k, "d": d},
            "checks": {"valid": True, "distance": True},
            "milp": {
                "exact": True,
                "total_logicals": total,
                "num_logicals_checked": total,
                "logicals_optimal": total,
                "logicals_incumbent": 0,
            },
        })
    return {
        "schema_version": 1,
        "gate": "qldpc-known-answer-baselines",
        "passed": True,
        "summary": {"passed": 3, "total": 3},
        "baselines": rows,
    }


def _candidate():
    # A connected, structurally novel test candidate.  The distance evidence is
    # synthetic because this test exercises gate composition, not the MILP.
    ell, m = 6, 6
    a = [[0, 0], [1, 0], [0, 1]]
    b = [[0, 0], [2, 0], [0, 2]]
    novelty = check_css_structural_novelty(ell, m, a, b)
    return {
        "ell": ell,
        "m": m,
        "A_terms": a,
        "B_terms": b,
        "n": 72,
        "k": 8,
        "d": 12,
        "fom": 16.0,
        "d_is_exact": True,
        "milp_attempted": True,
        "milp_details": {
            "exact": True,
            "total_logicals": 16,
            "num_logicals_checked": 16,
            "logicals_optimal": 16,
            "logicals_incumbent": 0,
        },
        "structural_novelty": novelty,
    }


def test_known_answer_gate_fails_closed_on_missing_file(tmp_path):
    result = validate_known_answer_artifact(tmp_path / "missing.json")
    assert result["passed"] is False
    assert result["failures"]


def test_known_answer_gate_rejects_top_level_pass_with_partial_milp(tmp_path):
    artifact = _baseline_artifact()
    artifact["baselines"][0]["milp"]["logicals_optimal"] = 23
    path = tmp_path / "known.json"
    path.write_text(json.dumps(artifact))
    result = validate_known_answer_artifact(path)
    assert result["passed"] is False


def test_scalar_and_pareto_win_rules():
    assert classify_win(72, 8, 12)["passed"] is True
    assert classify_win(144, 13, 12)["passed"] is True
    assert classify_win(144, 12, 12)["passed"] is False


def test_minimum_winning_distance_includes_pareto_fronts():
    assert minimum_winning_distance(72, 12) == 7
    assert minimum_winning_distance(90, 8) == 11
    assert minimum_winning_distance(108, 8) == 11
    assert minimum_winning_distance(144, 12) == 13
    assert minimum_winning_distance(288, 12) == 17


def test_explicit_scalar_target_uses_strict_integer_boundary():
    # The gist admits d=7 by its fixed-(n,k) Pareto rule; the scalar target
    # requires the exact integer inequality 12*d^2 > 12*72.
    assert classify_target_win(72, 12, 7, TARGET_MODE_GIST)["passed"] is True
    assert classify_target_win(72, 12, 8, TARGET_MODE_SCALAR)["passed"] is False
    assert classify_target_win(72, 12, 9, TARGET_MODE_SCALAR)["passed"] is True
    assert minimum_target_distance(72, 12, TARGET_MODE_GIST) == 7
    assert minimum_target_distance(72, 12, TARGET_MODE_SCALAR) == 9


def test_target_binding_is_self_hashed_and_semantically_recomputed():
    binding = target_binding(72, 12, TARGET_MODE_SCALAR)
    assert binding["required_distance"] == 9
    assert binding["rejection_cutoff"] == 8
    assert validate_target_binding(binding, n=72, k=12) == binding

    forged = dict(binding)
    forged["required_distance"] = 8
    unsigned = dict(forged)
    unsigned.pop("binding_sha256")
    forged["binding_sha256"] = hashlib.sha256(
        json.dumps(
            unsigned,
            sort_keys=True,
            separators=(",", ":"),
            ensure_ascii=False,
            allow_nan=False,
        ).encode()
    ).hexdigest()
    with pytest.raises(ValueError, match="recomputed parameters"):
        validate_target_binding(forged, n=72, k=12)


def test_explicit_target_can_describe_an_unattainable_small_code():
    binding = target_binding(4, 1, TARGET_MODE_GIST)
    assert binding["required_distance"] == 7
    assert binding["rejection_cutoff"] == 6
    with pytest.raises(ValueError, match="no winning distance"):
        minimum_winning_distance(4, 1)


def test_final_gate_rejects_missing_structural_audit(tmp_path):
    path = tmp_path / "known.json"
    path.write_text(json.dumps(_baseline_artifact()))
    candidate = _candidate()
    candidate.pop("structural_novelty")
    result = evaluate_final_gate(candidate, known_answer_artifact=path)
    assert result["accepted"] is False
    assert result["checks"]["structural_audit_present"] is False


def test_final_gate_rejects_partial_milp(tmp_path):
    path = tmp_path / "known.json"
    path.write_text(json.dumps(_baseline_artifact()))
    candidate = _candidate()
    candidate["milp_details"]["logicals_optimal"] = 15
    result = evaluate_final_gate(candidate, known_answer_artifact=path)
    assert result["accepted"] is False
    assert result["checks"]["all_2k_milp_directions_optimal"] is False
