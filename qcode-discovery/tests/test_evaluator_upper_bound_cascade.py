"""Focused tests for the evaluator's upper-bound evidence cascade."""

from types import SimpleNamespace

import numpy as np
import pytest

from evaluation import evaluator


_A = [(0, 0), (1, 0), (0, 1)]
_B = [(0, 0), (2, 0), (0, 2)]


def _install_dummy_code(monkeypatch, *, n=360, k=16):
    code = SimpleNamespace(num_qudits=n, dimension=k)
    monkeypatch.setattr(
        evaluator,
        "_validate_and_build",
        lambda *_args, **_kwargs: (code, n, k),
    )
    return code


def _valid_witness_matrices(n, distance):
    bits = np.zeros(n, dtype=int)
    bits[:distance] = 1
    dual = np.zeros(n, dtype=int)
    dual[0] = 1
    checks = np.zeros((1, n), dtype=int)
    witness = {
        "side": "X",
        "index": 0,
        "dual_side": "Z",
        "dual_index": 0,
        "weight": distance,
        "bits": bits.tolist(),
    }
    return (checks, checks, bits.reshape(1, -1), dual.reshape(1, -1)), witness


def test_challenge_prefilter_replays_witness_before_formal_rejection(
    monkeypatch,
):
    _install_dummy_code(monkeypatch)
    matrices, witness = _valid_witness_matrices(360, 16)
    monkeypatch.setattr(
        evaluator, "symplectic_weight_bound", lambda _code: (16, 16, 20)
    )
    monkeypatch.setattr(
        evaluator,
        "symplectic_weight_witness",
        lambda _code, _distance: witness,
    )
    monkeypatch.setattr(
        evaluator, "get_code_matrices", lambda _code: matrices
    )
    monkeypatch.setattr(
        evaluator,
        "estimate_distance",
        lambda *_args, **_kwargs: pytest.fail("BP must be short-circuited"),
    )

    result = evaluator.evaluate_candidate(
        2,
        1,
        _A,
        _B,
        challenge_target_fom=12.0,
    )

    assert result["challenge_rejection_cutoff"] == 16
    assert result["stage"] == "challenge_symplectic_rejected"
    assert result["search_status"] == "terminal_negative"
    assert result["threshold_rejection_proven"] is True
    assert result["threshold_proof_witness"] == witness
    assert result["distance_status"] == "upper_bound"
    assert result["distance_trusted"] is False
    assert result["fitness_distance_credit"] == 0.0


def test_malformed_symplectic_witness_never_claims_formal_rejection(
    monkeypatch,
):
    _install_dummy_code(monkeypatch)
    monkeypatch.setattr(
        evaluator, "symplectic_weight_bound", lambda _code: (16, 16, 20)
    )
    monkeypatch.setattr(
        evaluator,
        "symplectic_weight_witness",
        lambda _code, _distance: {
            "side": "X",
            "index": 0,
            "dual_side": "Z",
            "dual_index": 0,
            "weight": 16,
            "bits": [1, 0],
        },
    )
    bp_calls = []

    def bp(*_args, **_kwargs):
        bp_calls.append(True)
        return 20

    monkeypatch.setattr(evaluator, "estimate_distance", bp)

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

    assert bp_calls == [True]
    assert result["search_status"] == "unresolved"
    assert result["distance_upper_bound"] == 20
    assert result["distance_upper_bound_source"] == "bp_osd_0"
    assert result["threshold_rejection_proven"] is False
    assert "d_symplectic" not in result
    assert "threshold_proof_witness" not in result


@pytest.mark.parametrize("invalid_bound", [0, float("nan")])
def test_invalid_symplectic_bound_requires_retry_before_bp(
    monkeypatch, invalid_bound
):
    _install_dummy_code(monkeypatch)
    monkeypatch.setattr(
        evaluator,
        "symplectic_weight_bound",
        lambda _code: (invalid_bound, invalid_bound, invalid_bound),
    )
    monkeypatch.setattr(
        evaluator,
        "estimate_distance",
        lambda *_args, **_kwargs: pytest.fail("BP must not hide the error"),
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

    _assert_retry_without_upper_bound(result, "symplectic_upper_bound")
    assert "d_symplectic" not in result


def test_symplectic_backend_exception_requires_retry(monkeypatch):
    _install_dummy_code(monkeypatch)

    def fail(_code):
        raise RuntimeError("symplectic exploded")

    monkeypatch.setattr(evaluator, "symplectic_weight_bound", fail)
    monkeypatch.setattr(
        evaluator,
        "estimate_distance",
        lambda *_args, **_kwargs: pytest.fail("BP must not hide the error"),
    )

    result = evaluator.evaluate_candidate(
        2,
        1,
        _A,
        _B,
        challenge_target_fom=12.0,
        skip_exact=True,
    )

    _assert_retry_without_upper_bound(result, "symplectic_upper_bound")


def test_symplectic_witness_exception_discards_bound_before_bp(monkeypatch):
    _install_dummy_code(monkeypatch)
    monkeypatch.setattr(
        evaluator, "symplectic_weight_bound", lambda _code: (16, 16, 20)
    )

    def fail(*_args, **_kwargs):
        raise RuntimeError("witness exploded")

    monkeypatch.setattr(evaluator, "symplectic_weight_witness", fail)
    monkeypatch.setattr(
        evaluator, "estimate_distance", lambda *_args, **_kwargs: 20
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

    assert result["search_status"] == "unresolved"
    assert result["distance_status"] == "upper_bound"
    assert result["distance_upper_bound"] == 20
    assert result["distance_upper_bound_source"] == "bp_osd_0"
    assert result["threshold_rejection_proven"] is False
    assert "d_symplectic" not in result


def _assert_retry_without_upper_bound(result, source):
    assert result["search_status"] == "retry"
    assert result["distance_status"] == "unknown_backend_error"
    assert result["distance_retry_required"] is True
    assert result["distance_upper_bound"] is None
    assert result["fom_upper_bound"] is None
    assert result["d"] == 0
    assert result["threshold_rejection_proven"] is False
    assert result["final_gate_excluded_by_upper_bound"] is False
    assert result["distance_backend_error"]["source"] == source
    assert "distance_upper_bound_source" not in result
    assert "search_final_gate_excluded_by_upper_bound" not in result


@pytest.mark.parametrize("invalid_bound", [0, -1, float("nan")])
def test_upper_bound_recorder_rejects_invalid_values(invalid_bound):
    with pytest.raises(ValueError, match="finite positive integers"):
        evaluator._record_distance_upper_bound(
            {},
            n=72,
            k=12,
            distance=invalid_bound,
            source="test",
            stage="test",
        )


@pytest.mark.parametrize("invalid_bound", [0, float("nan")])
def test_invalid_bp_bound_requires_retry(monkeypatch, invalid_bound):
    _install_dummy_code(monkeypatch)
    monkeypatch.setattr(
        evaluator,
        "symplectic_weight_bound",
        lambda _code: (20, 20, 24),
    )
    monkeypatch.setattr(
        evaluator,
        "estimate_distance",
        lambda *_args, **_kwargs: invalid_bound,
    )

    result = evaluator.evaluate_candidate(
        2,
        1,
        _A,
        _B,
        challenge_target_fom=12.0,
        skip_exact=True,
    )

    _assert_retry_without_upper_bound(result, "bp_osd_0")
    assert "d_symplectic" not in result


@pytest.mark.parametrize("invalid_bound", [0, float("nan")])
def test_invalid_refined_bound_clears_provisional_bp_bound(
    monkeypatch, invalid_bound
):
    _install_dummy_code(monkeypatch)
    calls = 0

    def estimate(*_args, **_kwargs):
        nonlocal calls
        calls += 1
        return 20 if calls == 1 else invalid_bound

    monkeypatch.setattr(evaluator, "estimate_distance", estimate)

    result = evaluator.evaluate_candidate(
        2,
        1,
        _A,
        _B,
        fom_threshold_refine=0.0,
        fom_threshold_osd_cs=float("inf"),
        skip_exact=True,
    )

    assert calls == 2
    _assert_retry_without_upper_bound(result, "bp_osd_0_refined")
    assert "bp_distance_upper_bound" not in result


@pytest.mark.parametrize("invalid_bound", [0, float("nan")])
def test_invalid_osd_cs_bound_clears_provisional_bp_bound(
    monkeypatch, invalid_bound
):
    _install_dummy_code(monkeypatch)
    monkeypatch.setattr(
        evaluator, "estimate_distance", lambda *_args, **_kwargs: 20
    )
    monkeypatch.setattr(
        evaluator,
        "estimate_distance_osd_cs",
        lambda *_args, **_kwargs: invalid_bound,
    )

    result = evaluator.evaluate_candidate(
        2,
        1,
        _A,
        _B,
        fom_threshold_refine=float("inf"),
        fom_threshold_osd_cs=0.0,
        fom_threshold_exact=float("inf"),
        skip_exact=True,
    )

    _assert_retry_without_upper_bound(result, "bp_osd_cs")
    assert "bp_distance_upper_bound" not in result
    assert "osd_cs_distance_upper_bound" not in result


@pytest.mark.parametrize(
    ("backend", "source"),
    [
        ("bp", "bp_osd_0"),
        ("refined", "bp_osd_0_refined"),
        ("osd_cs", "bp_osd_cs"),
    ],
)
def test_distance_backend_exceptions_require_retry(
    monkeypatch, backend, source
):
    _install_dummy_code(monkeypatch)
    calls = 0

    def estimate(*_args, **_kwargs):
        nonlocal calls
        calls += 1
        if backend == "bp" or (backend == "refined" and calls > 1):
            raise RuntimeError(f"{backend} exploded")
        return 20

    def osd(*_args, **_kwargs):
        if backend == "osd_cs":
            raise RuntimeError("osd exploded")
        return 20

    monkeypatch.setattr(evaluator, "estimate_distance", estimate)
    monkeypatch.setattr(evaluator, "estimate_distance_osd_cs", osd)

    result = evaluator.evaluate_candidate(
        2,
        1,
        _A,
        _B,
        fom_threshold_refine=(
            0.0 if backend == "refined" else float("inf")
        ),
        fom_threshold_osd_cs=(
            0.0 if backend == "osd_cs" else float("inf")
        ),
        fom_threshold_exact=float("inf"),
        skip_exact=True,
    )

    _assert_retry_without_upper_bound(result, source)


def test_challenge_survivor_uses_tightest_symplectic_bp_and_osd_bound(
    monkeypatch,
):
    _install_dummy_code(monkeypatch)
    monkeypatch.setattr(
        evaluator, "symplectic_weight_bound", lambda _code: (20, 20, 24)
    )
    monkeypatch.setattr(
        evaluator, "estimate_distance", lambda *_args, **_kwargs: 24
    )
    osd_calls = []

    def osd(*_args, **_kwargs):
        osd_calls.append(True)
        return 18

    monkeypatch.setattr(evaluator, "estimate_distance_osd_cs", osd)

    result = evaluator.evaluate_candidate(
        2,
        1,
        _A,
        _B,
        challenge_target_fom=12.0,
        fom_threshold_refine=float("inf"),
        fom_threshold_osd_cs=0.0,
        fom_threshold_exact=float("inf"),
        skip_exact=True,
    )

    assert osd_calls == [True]
    assert result["search_status"] == "unresolved"
    assert result["distance_status"] == "upper_bound"
    assert result["distance_upper_bound"] == 18
    assert result["distance_upper_bound_source"] == "bp_osd_cs"
    assert result["fom_upper_bound"] == pytest.approx(16 * 18**2 / 360)
    assert result["fitness_distance_credit"] == 0.0


def test_challenge_survivor_keeps_tighter_symplectic_bound(monkeypatch):
    _install_dummy_code(monkeypatch)
    monkeypatch.setattr(
        evaluator, "symplectic_weight_bound", lambda _code: (17, 17, 24)
    )
    monkeypatch.setattr(
        evaluator, "estimate_distance", lambda *_args, **_kwargs: 24
    )
    monkeypatch.setattr(
        evaluator, "estimate_distance_osd_cs", lambda *_args, **_kwargs: 19
    )

    result = evaluator.evaluate_candidate(
        2,
        1,
        _A,
        _B,
        challenge_target_fom=12.0,
        fom_threshold_refine=float("inf"),
        fom_threshold_osd_cs=0.0,
        fom_threshold_exact=float("inf"),
        skip_exact=True,
    )

    assert result["search_status"] == "unresolved"
    assert result["distance_upper_bound"] == 17
    assert result["distance_upper_bound_source"] == "symplectic_upper_bound"


def test_exact_result_has_separate_exact_evidence_fields(monkeypatch):
    _install_dummy_code(monkeypatch, n=100, k=10)
    monkeypatch.setattr(
        evaluator, "estimate_distance", lambda *_args, **_kwargs: 10
    )
    monkeypatch.setattr(
        evaluator, "compute_distance_exact", lambda *_args, **_kwargs: 4
    )

    result = evaluator.evaluate_candidate(
        2,
        1,
        _A,
        _B,
        fom_threshold_refine=float("inf"),
        fom_threshold_exact=0.0,
        skip_osd_cs=True,
    )

    assert result["distance_status"] == "exact"
    assert result["d_is_exact"] is True
    assert result["distance_trusted"] is True
    assert result["exact_distance"] == 4
    assert result["exact_fom"] == pytest.approx(1.6)
    assert result["fitness_distance_credit"] == result["exact_fom"]
    assert result["search_status"] == "exact"
