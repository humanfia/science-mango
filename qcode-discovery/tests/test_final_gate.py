"""Tests for the fail-closed qLDPC challenge acceptance gate."""

import json

from evaluation.final_gate import (
    classify_win,
    evaluate_final_gate,
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
