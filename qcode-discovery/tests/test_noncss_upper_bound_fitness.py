"""Regression tests for proof-safe Non-CSS OpenEvolve fitness."""

from __future__ import annotations

import math

import pytest

from evaluation import results as result_store
from evolve import openevolve_evaluator_noncss as evaluator


def _row(
    *,
    distance: int,
    exact: bool = False,
    upper: bool = True,
) -> dict:
    n = 144
    k = 12
    return {
        "ell": 12,
        "m": 6,
        "n": n,
        "k": k,
        "d": distance,
        "fom": k * distance * distance / n,
        "d_is_exact": exact,
        "d_is_upper_bound": upper,
        "distance_status": "exact" if exact else "upper_bound",
        "trust_level": "TRUSTED",
        "encoding_rate": k / n,
        "A_terms": [[0, 0], [0, 1], [1, 0]],
        "B_terms": [[0, 0], [0, 2], [2, 0]],
        "C_terms": [[0, 0]],
        "D_terms": [[1, 1]],
    }


def _metrics(row: dict) -> dict:
    return {
        "all_results": [row],
        "errors": [],
        "total_candidates": 1,
        "num_valid": 1,
        "num_high_k": 1,
        "lattices_with_high_k": 1,
        "best_encoding_rate": row["k"] / row["n"],
        "best_fom": row["fom"],
        "mean_fom": row["fom"],
    }


def _evaluate_with_row(tmp_path, monkeypatch, row):
    monkeypatch.setattr(
        evaluator,
        "_load_generate_candidates",
        lambda _path: lambda _ell, _m: [],
    )
    monkeypatch.setattr(
        evaluator,
        "_run_evaluation",
        lambda *_args, **_kwargs: _metrics(row),
    )
    saved = []
    pareto = []
    logged = {}
    monkeypatch.setattr(result_store, "save_code", saved.append)
    monkeypatch.setattr(result_store, "update_pareto_front", pareto.extend)
    monkeypatch.setattr(
        evaluator,
        "_write_metrics_jsonl",
        lambda metrics: logged.update(metrics),
    )
    result = evaluator.evaluate_stage2(str(tmp_path / "program.py"))
    return (
        getattr(result, "metrics", result),
        getattr(result, "artifacts", {}),
        saved,
        pareto,
        logged,
    )


def test_bp_upper_bound_magnitude_never_changes_positive_fitness():
    low = _row(distance=13)
    high = _row(distance=80)

    low_score = evaluator._score_upper_bound_safe([low])
    high_score = evaluator._score_upper_bound_safe([high])

    assert evaluator._upper_bound_fom(low) < evaluator._upper_bound_fom(high)
    assert low_score["fitness_distance_credit"] == 0.0
    assert high_score["fitness_distance_credit"] == 0.0
    assert low_score["fitness_survivor_credit"] == 1.0
    assert low_score["combined_score"] == high_score["combined_score"]


def test_scalar_only_small_upper_bound_remains_unresolved():
    row = _row(distance=10)

    safe = evaluator._safe_result_semantics(row)
    score = evaluator._score_upper_bound_safe([row])

    assert safe["fom_upper_bound"] == pytest.approx(100 / 12)
    assert safe["search_status"] == "unresolved"
    assert safe["search_final_gate_excluded_by_upper_bound"] is False
    assert score["fitness_distance_credit"] == 0.0
    assert score["fitness_survivor_credit"] == 1.0
    assert score["terminal_negative_count"] == 0


def test_upper_bound_equal_to_minimum_winning_distance_survives():
    row = _row(distance=13)

    safe = evaluator._safe_result_semantics(row)

    assert safe["minimum_winning_distance"] == 13
    assert safe["search_status"] == "unresolved"
    assert safe["search_final_gate_excluded_by_upper_bound"] is False


def test_unverified_trust_label_does_not_create_distance_credit():
    row = _row(distance=40)
    row["d_is_upper_bound"] = False
    row["distance_status"] = "partial"
    row["trust_level"] = "EXACT"

    assert evaluator._trust_level_for_result(row) == "UNRESOLVED"
    assert evaluator._scored_fom(row) == 0.0
    assert evaluator._score_upper_bound_safe([row])["combined_score"] == 0.0


@pytest.mark.parametrize("value", [5.5, math.nan, math.inf, "5", True])
def test_distance_evidence_requires_a_strict_positive_integer(value):
    row = _row(distance=14)
    row["d"] = value

    assert evaluator._positive_int(value) is None
    assert evaluator._proven_distance_evidence(row) is None


def test_explicit_none_exact_distance_falls_back_to_d():
    row = _row(distance=14, exact=True, upper=False)
    row["exact_distance"] = None

    assert evaluator._proven_distance_evidence(row) == ("exact", 14)
    assert evaluator._scored_fom(row) == pytest.approx(49 / 3)


def test_only_exact_distance_is_positive_without_a_certificate_validator():
    exact = _row(distance=14, exact=True, upper=False)
    lower = _row(distance=80)
    lower.update({
        "distance_lower_bound": 14,
        "distance_lower_bound_status": "certified",
    })

    exact_score = evaluator._score_upper_bound_safe([exact])
    lower_score = evaluator._score_upper_bound_safe([lower])

    assert evaluator._scored_fom(exact) == pytest.approx(49 / 3)
    assert evaluator._scored_fom(lower) == 0.0
    assert exact_score["fitness_distance_credit"] == 12.0
    assert lower_score["fitness_distance_credit"] == 0.0
    assert exact_score["fitness_survivor_credit"] == 0.0
    assert lower_score["fitness_survivor_credit"] == 1.0


def test_self_declared_lower_bound_never_creates_positive_credit():
    row = _row(distance=5)
    row.update({
        "distance_lower_bound": 1000,
        "distance_lower_bound_status": "certified",
        "distance_lower_bound_proven": True,
    })

    safe = evaluator._safe_result_semantics(row)

    assert evaluator._scored_fom(row) == 0.0
    assert safe["search_status"] == "unresolved"
    assert safe["distance_upper_bound"] == 5


def test_upper_bound_stage2_is_diagnostic_only_and_never_persisted(
    tmp_path, monkeypatch
):
    upper = _row(distance=80)

    metrics, artifacts, saved, pareto, logged = _evaluate_with_row(
        tmp_path, monkeypatch, upper
    )

    assert metrics["best_fom"] == 0.0
    assert metrics["fitness_distance_credit"] == 0.0
    assert metrics["fitness_survivor_credit"] == 1.0
    assert metrics["best_fom_upper_bound"] == pytest.approx(upper["fom"])
    assert metrics["combined_score"] < 1.1
    assert "best_code" not in artifacts
    assert "upper-bound magnitude withheld" in artifacts[
        "best_upper_bound_survivor"
    ]
    assert "no achieved FOM or win claim" in artifacts[
        "best_upper_bound_survivor"
    ]
    assert "<=80" not in artifacts["best_upper_bound_survivor"]
    assert str(upper["fom"]) not in artifacts["best_upper_bound_survivor"]
    assert saved == []
    assert pareto == []
    assert logged["best_fom"] == 0.0


def test_self_declared_lower_bound_is_not_persisted(
    tmp_path, monkeypatch
):
    lower = _row(distance=80)
    lower.update({
        "distance_lower_bound": 14,
        "distance_lower_bound_status": "certified",
    })

    metrics, artifacts, saved, pareto, _logged = _evaluate_with_row(
        tmp_path, monkeypatch, lower
    )

    assert metrics["best_fom"] == 0.0
    assert "best_code" not in artifacts
    assert saved == []
    assert pareto == []
