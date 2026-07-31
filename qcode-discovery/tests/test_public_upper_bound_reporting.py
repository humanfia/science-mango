"""Regression tests for proof-safe public evaluator/reporting semantics."""

from types import SimpleNamespace

import numpy as np
import pytest

from evaluation import evaluator
from evaluation.tracking import RunTracker
from main import (
    _certified_fom,
    _is_exact_distance_result,
    merge_bp_milp_result,
)


_A = [(0, 0), (1, 0), (0, 1)]
_B = [(0, 0), (2, 0), (0, 2)]


def _row(*, exact: bool, score: float, distance: int) -> dict:
    n, k = 72, 12
    fom = k * distance * distance / n
    return {
        "ell": 6,
        "m": 6,
        "A_terms": _A,
        "B_terms": _B,
        "n": n,
        "k": k,
        "d": distance,
        "d_is_exact": exact,
        "distance_status": "exact" if exact else "upper_bound",
        "exact_distance": distance if exact else None,
        "fom": fom,
        "fom_upper_bound": fom,
        "exact_fom": fom if exact else None,
        "score": score,
        "stage": "exact" if exact else "quick_estimate",
    }


def test_scalar_bp_bound_below_cutoff_is_never_terminal():
    result = {
        "challenge_rejection_cutoff": 16,
        "threshold_rejection_proven": False,
    }

    stopped = evaluator._record_distance_upper_bound(
        result,
        n=360,
        k=16,
        distance=3,
        source="bp_osd_0",
        stage="quick_estimate",
    )

    assert stopped is False
    assert result["search_status"] == "unresolved"
    assert result["score"] == 0.0
    assert result["fitness_distance_credit"] == 0.0
    assert result["fom_upper_bound"] == pytest.approx(0.4)
    assert result["threshold_rejection_proven"] is False
    assert "search_final_gate_excluded_by_upper_bound" not in result


def test_bp_candidate_keeps_upper_diagnostic_but_no_positive_score(monkeypatch):
    code = SimpleNamespace(num_qudits=360, dimension=16)
    monkeypatch.setattr(
        evaluator,
        "_validate_and_build",
        lambda *_args, **_kwargs: (code, 360, 16),
    )
    monkeypatch.setattr(
        evaluator,
        "symplectic_weight_bound",
        lambda _code: (20, 20, 20),
    )
    monkeypatch.setattr(
        evaluator,
        "estimate_distance",
        lambda *_args, **_kwargs: 3,
    )

    result = evaluator.evaluate_candidate(
        2,
        1,
        _A,
        _B,
        challenge_target_fom=12.0,
        fom_threshold_refine=float("inf"),
        fom_threshold_osd_cs=float("inf"),
        skip_exact=True,
    )

    assert result["distance_status"] == "upper_bound"
    assert result["distance_upper_bound"] == 3
    assert result["fom_upper_bound"] == pytest.approx(0.4)
    assert result["score"] == 0.0
    assert result["search_status"] == "unresolved"
    assert result["threshold_rejection_proven"] is False


def test_batch_ranking_neutralizes_legacy_positive_upper_score(monkeypatch):
    upper = _row(exact=False, score=999.0, distance=20)
    exact = _row(exact=True, score=1.0, distance=2)
    rows = iter((upper, exact))
    monkeypatch.setattr(
        evaluator,
        "evaluate_candidate",
        lambda *_args, **_kwargs: next(rows),
    )

    results = evaluator.evaluate_batch(
        6,
        6,
        [(_A, _B), (_A, _B)],
    )

    assert results[0]["d_is_exact"] is True
    assert results[1]["distance_status"] == "upper_bound"


def test_lattice_and_milp_batch_ranking_are_upper_bound_neutral(monkeypatch):
    upper = _row(exact=False, score=999.0, distance=20)
    exact = _row(exact=True, score=1.0, distance=2)
    monkeypatch.setattr(
        evaluator,
        "evaluate_batch",
        lambda *_args, **_kwargs: [upper, exact],
    )

    lattice_results = evaluator.evaluate_lattices(
        [(6, 6)],
        lambda *_args: [(_A, _B)],
    )
    assert lattice_results[0]["d_is_exact"] is True

    rows = iter((upper, exact))
    monkeypatch.setattr(
        evaluator,
        "evaluate_candidate_milp",
        lambda *_args, **_kwargs: next(rows),
    )
    milp_results = evaluator.evaluate_batch_milp(
        6,
        6,
        [(_A, _B), (_A, _B)],
    )
    assert milp_results[0]["d_is_exact"] is True


def test_parallel_milp_cache_sort_is_upper_bound_neutral(monkeypatch):
    b2 = [(0, 0), (3, 0), (0, 3)]
    tasks = [(6, 6, _A, _B), (6, 6, _A, b2)]
    upper = {
        **_row(exact=False, score=999.0, distance=20),
        "B_terms": _B,
    }
    exact = {
        **_row(exact=True, score=1.0, distance=2),
        "B_terms": b2,
    }
    cache = {
        evaluator._milp_cache_key(6, 6, _A, _B): upper,
        evaluator._milp_cache_key(6, 6, _A, b2): exact,
    }
    monkeypatch.setattr(
        evaluator,
        "_load_milp_cache",
        lambda *_args, **_kwargs: cache,
    )

    results = evaluator.evaluate_milp_parallel(tasks)

    assert results[0]["d_is_exact"] is True
    assert results[1]["distance_status"] == "upper_bound"


def test_milp_incumbent_is_upper_diagnostic_with_zero_score(monkeypatch):
    code = SimpleNamespace(num_qudits=12, dimension=2)
    hx = np.zeros((1, 12), dtype=int)
    hz = np.zeros((1, 12), dtype=int)
    lx = np.zeros((1, 12), dtype=int)
    lx[0, 0] = 1
    lz = np.zeros((1, 12), dtype=int)
    monkeypatch.setattr(
        evaluator,
        "_validate_and_build",
        lambda *_args, **_kwargs: (code, 12, 2),
    )
    monkeypatch.setattr(
        evaluator,
        "get_code_matrices",
        lambda _code: (hx, hz, lx, lz),
    )
    monkeypatch.setattr(
        evaluator,
        "symplectic_weight_bound",
        lambda _code: (12, 12, 12),
    )
    monkeypatch.setattr(
        evaluator,
        "compute_distance_milp",
        lambda *_args, **_kwargs: (
            3,
            {
                "exact": False,
                "all_timeout": False,
                "d_x": 0,
                "d_z": 3,
                "minimum_direction_witness": {
                    "side": "Z",
                    "index": 0,
                    "weight": 3,
                    "bits": [1, 1, 1] + [0] * 9,
                },
            },
        ),
    )

    result = evaluator.evaluate_candidate_milp(
        2,
        1,
        _A,
        _B,
        milp_early_stop=None,
    )

    assert result["stage"] == "milp_incumbent"
    assert result["distance_status"] == "upper_bound"
    assert result["fom_upper_bound"] == pytest.approx(1.5)
    assert result["score"] == 0.0
    assert result["fitness_distance_credit"] == 0.0


def test_tracker_counts_only_exact_fom_as_achieved(tmp_path):
    tracker = RunTracker(base_dir=tmp_path)
    tracker.start_run(run_id="proof-safe")
    upper = _row(exact=False, score=999.0, distance=20)
    exact = _row(exact=True, score=1.0, distance=2)

    tracker.start_generation(0)
    tracker.log_evaluation(upper)
    tracker.log_evaluation(exact)
    summary = tracker.end_generation(0, [upper, exact])
    meta = tracker.end_run()

    assert summary["codes_with_exact_fom"] == 1
    assert summary["best_fom"] == exact["fom"]
    assert summary["best_fom_upper_bound"] == upper["fom_upper_bound"]
    assert meta["best_fom"] == exact["fom"]
    assert meta["best_code"]["d_is_exact"] is True


def test_forged_exact_fom_is_recomputed_and_mismatched_distance_rejected(
    tmp_path,
):
    forged = _row(exact=True, score=10**9, distance=2)
    forged["fom"] = 10**9
    forged["exact_fom"] = 10**9
    expected = forged["k"] * forged["d"] ** 2 / forged["n"]

    assert _certified_fom(forged) == expected

    tracker = RunTracker(base_dir=tmp_path)
    tracker.start_run(run_id="forged-exact")
    tracker.log_evaluation(forged)
    summary = tracker.end_generation(0, [forged])
    meta = tracker.end_run()
    assert summary["best_fom"] == expected
    assert meta["best_fom"] == expected

    forged["exact_distance"] = forged["d"] + 1
    assert _is_exact_distance_result(forged) is False
    assert _certified_fom(forged) == 0.0


def test_main_merge_and_discovery_helpers_reject_upper_bound_credit():
    bp = _row(exact=False, score=100.0, distance=8)
    milp = {
        **_row(exact=False, score=50.0, distance=6),
        "stage": "milp_incumbent",
        "milp_details": {
            "exact": False,
            "total_logicals": 24,
            "num_logicals_checked": 2,
            "logicals_optimal": 1,
        },
    }

    merged = merge_bp_milp_result(bp, milp)

    assert merged["distance_status"] == "upper_bound"
    assert merged["fom_upper_bound"] > 0
    assert merged["score"] == 0.0
    assert merged["fitness_distance_credit"] == 0.0
    assert _is_exact_distance_result(merged) is False
    assert _certified_fom(merged) == 0.0
