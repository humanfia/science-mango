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


def test_dynamic_fom_cutoff_uses_exact_integer_boundaries():
    assert evaluator.compute_fom_rejection_cutoff(360, 16, 12.0) == 16
    assert evaluator.compute_fom_rejection_cutoff(288, 12, 12.0) == 16
    assert evaluator.compute_fom_rejection_cutoff(144, 12, 12.0) == 12


def test_challenge_cutoff_preserves_equal_fom_pareto_winner():
    assert evaluator.compute_fom_rejection_cutoff(36, 12, 12.0) == 6
    assert evaluator.compute_challenge_rejection_cutoff(36, 12, 12.0) == 5


def test_dynamic_cutoff_handles_parameter_sets_with_no_possible_winner():
    assert evaluator.compute_challenge_rejection_cutoff(4, 1, 12.0) == 4


def test_css_incumbent_at_cutoff_stops_after_first_direction(monkeypatch):
    hx = np.zeros((1, 4), dtype=int)
    hz = np.zeros((1, 4), dtype=int)
    lx = np.array([[1, 0, 0, 0]], dtype=int)
    lz = np.array([[0, 1, 0, 0]], dtype=int)
    monkeypatch.setattr(
        distance_milp, "get_code_matrices", lambda _code: (hx, hz, lx, lz)
    )
    calls = []

    def incumbent(*_args, **_kwargs):
        calls.append(1)
        return 3, False

    monkeypatch.setattr(distance_milp, "ilp_min_weight", incumbent)
    distance, details = distance_milp.compute_distance_milp(
        DummyCssCode(), early_stop=3, timeout_per_logical=1, total_timeout=10
    )

    assert distance == 3
    assert len(calls) == 1
    assert details["num_logicals_checked"] == 1
    assert details["logicals_incumbent"] == 1
    assert details["d_x_computed"] is False
    assert details["exact"] is False


def test_dynamic_cutoff_uses_rebuilt_n_k_and_stops_at_boundary(monkeypatch):
    dummy = SimpleNamespace(num_qudits=360, dimension=16)
    observed = {}
    monkeypatch.setattr(
        evaluator,
        "_validate_and_build",
        lambda *_args, **_kwargs: (dummy, 360, 16),
    )
    monkeypatch.setattr(
        evaluator, "symplectic_weight_bound", lambda _code: (58, 58, 58)
    )

    def fake_distance(*_args, **kwargs):
        observed.update(kwargs)
        return 16, {
            "exact": False,
            "all_timeout": False,
            "total_logicals": 32,
            "num_logicals_checked": 1,
        }

    monkeypatch.setattr(evaluator, "compute_distance_milp", fake_distance)
    result = evaluator.evaluate_candidate_milp(
        2,
        1,
        [(0, 0), (1, 0)],
        [(0, 0), (1, 0)],
        milp_early_stop=4,
        milp_target_fom=12.0,
    )

    assert observed["early_stop"] == 16
    assert result["milp_effective_early_stop"] == 16
    assert result["d"] == 16
    assert result["d_is_exact"] is False
    assert result["stage"] == "milp_low_d"
    assert result["fom_target_excluded_by_upper_bound"] is True
    assert result["final_gate_excluded_by_upper_bound"] is True
    assert result["threshold_rejection_proven"] is True
    assert result["threshold_proof_lhs"] <= result["threshold_proof_rhs"]
    assert result["threshold_proof_distance"] == 16
    assert result["threshold_proof_source"] == "milp_feasible_upper_bound"


def test_dynamic_cutoff_does_not_reject_above_boundary(monkeypatch):
    dummy = SimpleNamespace(num_qudits=360, dimension=16)
    monkeypatch.setattr(
        evaluator,
        "_validate_and_build",
        lambda *_args, **_kwargs: (dummy, 360, 16),
    )
    monkeypatch.setattr(
        evaluator, "symplectic_weight_bound", lambda _code: (58, 58, 58)
    )
    monkeypatch.setattr(
        evaluator,
        "compute_distance_milp",
        lambda *_args, **_kwargs: (
            17,
            {
                "exact": False,
                "all_timeout": False,
                "total_logicals": 32,
                "num_logicals_checked": 1,
            },
        ),
    )

    result = evaluator.evaluate_candidate_milp(
        2,
        1,
        [(0, 0), (1, 0)],
        [(0, 0), (1, 0)],
        milp_target_fom=12.0,
    )

    assert result["d"] == 17
    assert result["stage"] == "milp_incumbent"
    assert result["fom_target_excluded_by_upper_bound"] is False
    assert result["final_gate_excluded_by_upper_bound"] is False
    assert result["threshold_rejection_proven"] is False


def test_dynamic_cutoff_can_skip_milp_from_symplectic_upper_bound(monkeypatch):
    dummy = SimpleNamespace(num_qudits=360, dimension=16)
    monkeypatch.setattr(
        evaluator,
        "_validate_and_build",
        lambda *_args, **_kwargs: (dummy, 360, 16),
    )
    monkeypatch.setattr(
        evaluator, "symplectic_weight_bound", lambda _code: (16, 16, 16)
    )

    def unexpected_milp(*_args, **_kwargs):
        raise AssertionError("MILP must not run once the upper bound excludes a win")

    monkeypatch.setattr(evaluator, "compute_distance_milp", unexpected_milp)
    result = evaluator.evaluate_candidate_milp(
        2,
        1,
        [(0, 0), (1, 0)],
        [(0, 0), (1, 0)],
        milp_target_fom=12.0,
    )

    assert result["stage"] == "symplectic_low_d"
    assert result["d"] == 16
    assert result["d_is_exact"] is False
    assert result["milp_solver_attempted"] is False
    assert result["final_gate_excluded_by_upper_bound"] is True
    assert result["threshold_proof_distance"] == 16
    assert result["threshold_proof_source"] == "symplectic_upper_bound"


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
