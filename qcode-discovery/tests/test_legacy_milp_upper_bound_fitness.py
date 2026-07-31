"""Regression tests for upper-bound-safe legacy MILP Stage 2 scoring."""

from __future__ import annotations

import pytest

from evolve import openevolve_evaluator as evaluator


_A = [[0, 0], [0, 1], [1, 0]]
_B = [[0, 0], [0, 2], [2, 0]]


def _row(
    *,
    distance: int,
    exact: bool,
    stage: str,
    distance_status: str,
) -> dict:
    n = 144
    k = 12
    return {
        "ell": 12,
        "m": 6,
        "A_terms": _A,
        "B_terms": _B,
        "n": n,
        "k": k,
        "d": distance,
        "d_is_exact": exact,
        "distance_trusted": exact or distance_status == "upper_bound",
        "distance_status": distance_status,
        "fom": k * distance * distance / n if distance > 0 else 0.0,
        "encoding_rate": k / n,
        "score": k * distance * distance / n if distance > 0 else 0.0,
        "stage": stage,
        "milp_solver_attempted": True,
        "milp_details": {
            "exact": exact,
            "num_logicals_checked": 8,
            "logicals_optimal": 5,
            "total_logicals": 24,
        },
    }


def _run_legacy_stage2(tmp_path, monkeypatch, milp_row):
    program = tmp_path / "program.py"
    program.write_text("def generate_candidates(ell, m): return []\n")
    candidate_log = (tmp_path / "run" / "all_codes.jsonl").resolve()
    monkeypatch.setenv(evaluator.CANDIDATE_LOG_PATH_ENV, str(candidate_log))
    monkeypatch.setattr(
        evaluator,
        "_MILP_CANDIDATE_LOG_PATH_BINDING",
        None,
    )
    monkeypatch.setattr(evaluator, "STAGE2_LATTICES_MILP", [(12, 6)])
    monkeypatch.setattr(
        evaluator,
        "_load_generate_candidates",
        lambda _path: lambda _ell, _m: [(_A, _B)],
    )
    quick = _row(
        distance=0,
        exact=False,
        stage="quick_k_only",
        distance_status="unknown",
    )
    quick["d_symplectic"] = 8
    monkeypatch.setattr(
        evaluator,
        "evaluate_batch_milp_parallel",
        lambda *_args, **_kwargs: [quick],
    )
    monkeypatch.setattr(
        evaluator,
        "evaluate_milp_parallel",
        lambda *_args, **_kwargs: [milp_row],
    )
    logged = {}
    saved = []
    pareto = []
    monkeypatch.setattr(
        evaluator,
        "_write_metrics_jsonl",
        lambda metrics: logged.update(metrics),
    )
    monkeypatch.setattr(evaluator, "save_code", saved.append)
    monkeypatch.setattr(evaluator, "update_pareto_front", pareto.extend)

    result = evaluator.evaluate_stage2_milp(str(program))
    return (
        getattr(result, "metrics", result),
        getattr(result, "artifacts", {}),
        logged,
        saved,
        pareto,
    )


def test_legacy_milp_incumbent_gets_no_distance_fitness_or_positive_store(
    tmp_path, monkeypatch
):
    incumbent = _row(
        distance=40,
        exact=False,
        stage="milp_incumbent",
        distance_status="upper_bound",
    )

    metrics, artifacts, logged, saved, pareto = _run_legacy_stage2(
        tmp_path, monkeypatch, incumbent
    )

    assert metrics["best_fom"] == 0.0
    assert metrics["fitness_distance_credit"] == 0.0
    assert metrics["fitness_survivor_credit"] == 1.0
    assert metrics["best_milp_fom_upper_bound"] == pytest.approx(
        incumbent["fom"]
    )
    assert metrics["combined_score"] < 1.1
    assert "best_code" not in artifacts
    artifact_text = "\n".join(artifacts.values())
    assert "BEATS BRAVYI" not in artifact_text
    assert "d<=40" not in artifact_text
    assert f"{incumbent['fom']:.2f}" not in artifact_text
    assert "Best MILP FOM upper bound" not in artifacts["summary"]
    assert (
        "MILP upper-bound diagnostics retained in telemetry only."
        in artifacts["summary"]
    )
    assert "d=unresolved" in artifacts["best_milp_survivor"]
    assert "no achieved FOM or win claim" in artifacts["best_milp_survivor"]
    assert logged["num_above_12"] == 0
    assert logged["num_milp_upper_bounds_above_12"] == 1
    assert saved == []
    assert pareto == []


def test_legacy_milp_upper_bound_magnitude_does_not_change_fitness():
    low = _row(
        distance=6,
        exact=False,
        stage="milp_incumbent",
        distance_status="upper_bound",
    )
    high = _row(
        distance=80,
        exact=False,
        stage="milp_incumbent",
        distance_status="upper_bound",
    )

    low_score = evaluator._score_stage2_upper_bound_safe(
        evaluator._legacy_milp_upper_bound_safe_rows([low])
    )
    high_score = evaluator._score_stage2_upper_bound_safe(
        evaluator._legacy_milp_upper_bound_safe_rows([high])
    )

    assert low["fom"] < high["fom"]
    assert low_score["fitness_distance_credit"] == 0.0
    assert high_score["fitness_distance_credit"] == 0.0
    assert low_score["combined_score"] == high_score["combined_score"]


def test_legacy_milp_timeout_without_incumbent_is_bounded_survivor_only(
    tmp_path, monkeypatch
):
    timeout = _row(
        distance=0,
        exact=False,
        stage="milp_timeout_no_incumbent",
        distance_status="unknown_no_incumbent",
    )

    metrics, artifacts, _logged, saved, pareto = _run_legacy_stage2(
        tmp_path, monkeypatch, timeout
    )

    assert metrics["combined_score"] < 1.1
    assert metrics["fitness_survivor_credit"] == 1.0
    assert metrics["fitness_distance_credit"] == 0.0
    assert metrics["best_fom"] == 0.0
    assert metrics["best_milp_fom_upper_bound"] == 0.0
    assert "d=unresolved" in artifacts["best_milp_survivor"]
    assert saved == []
    assert pareto == []


def test_legacy_milp_exact_distance_can_receive_credit_and_persist(
    tmp_path, monkeypatch
):
    exact = _row(
        distance=14,
        exact=True,
        stage="milp_exact",
        distance_status="exact",
    )
    exact["fom"] = 999_999.0
    exact["score"] = 999_999.0

    metrics, artifacts, _logged, saved, pareto = _run_legacy_stage2(
        tmp_path, monkeypatch, exact
    )

    recomputed_fom = 12 * 14 * 14 / 144
    assert metrics["best_fom"] == pytest.approx(recomputed_fom)
    assert metrics["fitness_distance_credit"] == 12.0
    assert metrics["fitness_survivor_credit"] == 0.0
    assert metrics["best_milp_fom_upper_bound"] == 0.0
    assert "[[144,12,14]]" in artifacts["best_code"]
    assert f"FOM={recomputed_fom:.2f}" in artifacts["best_code"]
    assert "999999" not in "\n".join(artifacts.values())
    assert len(saved) == 1
    assert saved[0]["d"] == saved[0]["exact_distance"] == 14
    assert saved[0]["fom"] == saved[0]["exact_fom"] == pytest.approx(
        recomputed_fom
    )
    assert saved[0]["fitness_distance_credit"] == pytest.approx(
        recomputed_fom
    )
    assert pareto == saved
