from types import SimpleNamespace

import numpy as np
from scipy.sparse import issparse

from evaluation import distance_milp, evaluator


class DummyCssCode:
    num_qudits = 4
    dimension = 1


class DummySymplecticCode:
    num_qudits = 4
    dimension = 1
    matrix = np.zeros((1, 8), dtype=int)


def test_css_timeout_without_incumbent_has_no_lower_bound(monkeypatch):
    hx = np.zeros((1, 4), dtype=int)
    hz = np.zeros((1, 4), dtype=int)
    lx = np.array([[1, 0, 0, 0]], dtype=int)
    lz = np.array([[0, 1, 0, 0]], dtype=int)
    monkeypatch.setattr(
        distance_milp, "get_code_matrices", lambda _code: (hx, hz, lx, lz)
    )
    monkeypatch.setattr(
        distance_milp, "ilp_min_weight", lambda *_args, **_kwargs: (None, False)
    )

    distance, details = distance_milp.compute_distance_milp(
        DummyCssCode(), early_stop=4, timeout_per_logical=1, total_timeout=10
    )

    assert distance == DummyCssCode.num_qudits
    assert details["all_timeout"] is True
    assert details["no_incumbent"] is True
    assert details["distance_status"] == "unknown"
    assert details["d_is_lower_bound"] is False


def test_symplectic_timeout_and_early_exit_are_never_exact(monkeypatch):
    from evaluation import pbb_code

    logicals = np.zeros((2, 8), dtype=int)
    monkeypatch.setattr(pbb_code, "get_symplectic_logicals", lambda _code: logicals)
    monkeypatch.setattr(
        distance_milp,
        "ilp_min_weight_symplectic",
        lambda *_args, **_kwargs: (None, False),
    )
    distance, details = distance_milp.compute_distance_milp_symplectic(
        DummySymplecticCode(), early_stop=4,
        timeout_per_logical=1, total_timeout=10,
    )
    assert distance == DummySymplecticCode.num_qudits
    assert details["distance_status"] == "unknown"
    assert details["d_is_lower_bound"] is False

    calls = iter([(2, True), (3, True)])
    monkeypatch.setattr(
        distance_milp,
        "ilp_min_weight_symplectic",
        lambda *_args, **_kwargs: next(calls),
    )
    distance, details = distance_milp.compute_distance_milp_symplectic(
        DummySymplecticCode(), early_stop=2,
        timeout_per_logical=1, total_timeout=10,
    )
    assert distance == 2
    assert details["num_logicals_checked"] == 1
    assert details["exact"] is False


def test_evaluator_accepts_none_and_timeout_is_fail_closed(monkeypatch):
    dummy = DummyCssCode()
    monkeypatch.setattr(
        evaluator, "_validate_and_build",
        lambda *_args, **_kwargs: (dummy, dummy.num_qudits, dummy.dimension),
    )
    monkeypatch.setattr(
        evaluator, "symplectic_weight_bound", lambda _code: (3, 3, 3)
    )
    monkeypatch.setattr(
        evaluator, "compute_distance_milp",
        lambda *_args, **_kwargs: (
            dummy.num_qudits,
            {"exact": False, "all_timeout": True, "total_logicals": 2},
        ),
    )

    result = evaluator.evaluate_candidate_milp(
        2, 1, [(0, 0), (1, 0)], [(0, 0), (1, 0)],
        milp_early_stop=None,
    )
    assert result["d"] == 0
    assert result["score"] == 0.0
    assert result["stage"] == "milp_timeout_no_incumbent"
    assert "d_lower_bound" not in result


def test_none_with_incumbent_remains_an_upper_bound(monkeypatch):
    dummy = DummyCssCode()
    monkeypatch.setattr(
        evaluator, "_validate_and_build",
        lambda *_args, **_kwargs: (dummy, dummy.num_qudits, dummy.dimension),
    )
    monkeypatch.setattr(
        evaluator, "symplectic_weight_bound", lambda _code: (3, 3, 3)
    )
    monkeypatch.setattr(
        evaluator, "compute_distance_milp",
        lambda *_args, **_kwargs: (
            3,
            {"exact": False, "total_logicals": 2, "num_logicals_checked": 1},
        ),
    )
    result = evaluator.evaluate_candidate_milp(
        2, 1, [(0, 0), (1, 0)], [(0, 0), (1, 0)],
        milp_early_stop=None,
    )
    assert result["d"] == 3
    assert result["d_is_exact"] is False
    assert result["stage"] == "milp_incumbent"


def test_ilp_constraint_matrices_are_sparse(monkeypatch):
    observed = []

    def fake_milp(*, constraints, **_kwargs):
        observed.append(constraints.A)
        return SimpleNamespace(x=np.zeros(constraints.A.shape[1]), fun=1, success=True)

    monkeypatch.setattr(distance_milp, "milp", fake_milp)
    assert distance_milp.ilp_min_weight(
        np.array([[1, 1]], dtype=int), np.array([1, 0], dtype=int)
    ) == (1, True)
    assert distance_milp.ilp_min_weight_symplectic(
        np.array([[1, 0, 0, 1]], dtype=int),
        np.array([1, 0, 0, 0], dtype=int),
    ) == (1, True)
    assert len(observed) == 2
    assert all(issparse(matrix) for matrix in observed)
