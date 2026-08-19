"""Tests for the fail-closed qLDPC challenge acceptance gate."""

import hashlib
import json

import pytest
from evaluation.admissibility_policy import (
    css_w6_admissibility_binding,
)

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
from evaluation.target_policy import (
    TARGET_MODE_SCALAR_13_INCLUSIVE,
    TARGET_MODE_SCALAR_INCLUSIVE,
)


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


def test_explicit_inclusive_target_preserves_fom_12_boundary():
    binding = target_binding(144, 12, TARGET_MODE_SCALAR_INCLUSIVE)

    assert classify_target_win(
        144, 12, 11, TARGET_MODE_SCALAR_INCLUSIVE,
    )["passed"] is False
    assert classify_target_win(
        144, 12, 12, TARGET_MODE_SCALAR_INCLUSIVE,
    )["passed"] is True
    assert minimum_target_distance(
        144, 12, TARGET_MODE_SCALAR_INCLUSIVE,
    ) == 12
    assert binding["strict"] is False
    assert binding["rejection_cutoff"] == 11
    assert validate_target_binding(
        binding,
        n=144,
        k=12,
        mode=TARGET_MODE_SCALAR_INCLUSIVE,
    ) == binding


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


def test_targetless_final_gate_keeps_legacy_check_shape(tmp_path, monkeypatch):
    path = tmp_path / "known.json"
    path.write_text(json.dumps(_baseline_artifact()))
    candidate = _candidate()
    candidate["structural_novelty"]["registry_sha256"] = "fixture-registry"
    monkeypatch.setattr(
        "evaluation.final_gate.check_code_novelty",
        lambda _code, *, code_type: {
            "novel": True,
            "registry_sha256": "fixture-registry",
        },
    )
    result = evaluate_final_gate(candidate, known_answer_artifact=path)

    assert result["accepted"] is True
    assert "target" not in result
    assert set(result["checks"]) == {
        "known_answer_gate",
        "candidate_rebuild",
        "css_commutation",
        "weight_and_degree_at_most_6",
        "connected_tanner_graph",
        "reported_n_matches",
        "reported_k_matches",
        "qldpc_k_crosscheck",
        "positive_reported_distance",
        "all_2k_milp_directions_optimal",
        "structural_audit_present",
        "structural_audit_reproduced",
        "expanded_registry_novel",
        "challenge_win",
        "reported_fom_matches",
    }


def test_explicit_fom12_target_keeps_legacy_result_shape(tmp_path):
    path = tmp_path / "known.json"
    path.write_text(json.dumps(_baseline_artifact()))
    legacy = evaluate_final_gate(_candidate(), known_answer_artifact=path)
    candidate = _candidate()
    candidate.update({
        "target_mode": TARGET_MODE_SCALAR_INCLUSIVE,
        "target": target_binding(72, 8, TARGET_MODE_SCALAR_INCLUSIVE),
    })

    replayed = evaluate_final_gate(candidate, known_answer_artifact=path)

    assert replayed["accepted"] == legacy["accepted"]
    assert replayed["checks"] == legacy["checks"]
    assert replayed["win"] == legacy["win"]
    assert "target" not in replayed
    assert "target_css_w6_admissibility" not in replayed["checks"]


def test_fom13_final_gate_uses_selected_mode_not_legacy_classifier(
    tmp_path,
    monkeypatch,
):
    path = tmp_path / "known.json"
    path.write_text(json.dumps(_baseline_artifact()))
    candidate = _candidate()
    candidate.update({
        "d": 10,
        "fom": 8 * 10 * 10 / 72,
        "target_mode": TARGET_MODE_SCALAR_13_INCLUSIVE,
        "target": target_binding(
            72,
            8,
            TARGET_MODE_SCALAR_13_INCLUSIVE,
        ),
        "admissibility": css_w6_admissibility_binding(),
    })
    assert classify_target_win(
        72,
        8,
        10,
        TARGET_MODE_SCALAR_13_INCLUSIVE,
    )["passed"] is False

    legacy_calls = []

    def synthetic_legacy_win(n, k, d):
        legacy_calls.append((n, k, d))
        return {
            "passed": True,
            "fom": k * d * d / n,
            "reasons": ["synthetic_legacy_win"],
        }

    monkeypatch.setattr(
        "evaluation.final_gate.classify_win",
        synthetic_legacy_win,
    )
    result = evaluate_final_gate(candidate, known_answer_artifact=path)

    assert legacy_calls == []
    assert result["accepted"] is False
    assert result["checks"]["challenge_win"] is False
    assert result["checks"]["reported_fom_matches"] is True
    assert result["checks"]["target_css_w6_admissibility"] is True
    assert result["target"] == candidate["target"]


def test_final_gate_requires_fom13_css_w6_policy_binding(
    tmp_path,
    monkeypatch,
):
    path = tmp_path / "known.json"
    path.write_text(json.dumps(_baseline_artifact()))
    candidate = _candidate()
    candidate.update({
        "target_mode": TARGET_MODE_SCALAR_13_INCLUSIVE,
        "target": target_binding(
            72,
            8,
            TARGET_MODE_SCALAR_13_INCLUSIVE,
        ),
    })
    candidate["structural_novelty"]["registry_sha256"] = "fixture-registry"
    monkeypatch.setattr(
        "evaluation.final_gate.check_code_novelty",
        lambda _code, *, code_type: {
            "novel": True,
            "registry_sha256": "fixture-registry",
        },
    )

    missing = evaluate_final_gate(candidate, known_answer_artifact=path)
    assert missing["accepted"] is False
    assert missing["checks"]["target_css_w6_admissibility"] is False

    candidate["admissibility"] = css_w6_admissibility_binding()
    replayed = evaluate_final_gate(candidate, known_answer_artifact=path)
    assert replayed["checks"]["target_css_w6_admissibility"] is True
    assert replayed["candidate"]["admissibility"] == (
        css_w6_admissibility_binding()
    )
    assert replayed["candidate"]["admissibility_report"]["passed"] is True
    assert (
        replayed["candidate"]["admissibility_report"]
        ["max_check_row_weight"] <= 6
    )

    target_only = dict(candidate)
    target_only.pop("target_mode")
    replayed_target_only = evaluate_final_gate(
        target_only,
        known_answer_artifact=path,
    )
    assert (
        replayed_target_only["checks"]["target_css_w6_admissibility"]
        is True
    )
    assert replayed_target_only["accepted"] is True
    assert replayed_target_only["target"] == candidate["target"]

    conflicting = dict(candidate)
    conflicting["target_mode"] = TARGET_MODE_SCALAR_INCLUSIVE
    rejected = evaluate_final_gate(conflicting, known_answer_artifact=path)
    assert rejected["accepted"] is False
    assert rejected["checks"]["challenge_win"] is False
    assert rejected["checks"]["target_css_w6_admissibility"] is False

    orphaned_hash = _candidate()
    orphaned_hash["target_binding_sha256"] = candidate["target"][
        "binding_sha256"
    ]
    rejected_orphan = evaluate_final_gate(
        orphaned_hash,
        known_answer_artifact=path,
    )
    assert rejected_orphan["accepted"] is False
    assert rejected_orphan["checks"]["challenge_win"] is False
