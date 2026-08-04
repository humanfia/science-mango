"""Exact semantics for the search-time CSS low-weight oracle."""

from __future__ import annotations

import copy
import itertools

import numpy as np
import pytest

import evaluation.low_weight_oracle as oracle


def _valid_d2_css_matrices():
    checks = np.array([[1, 1, 1, 1]], dtype=np.uint8)
    lx = np.array([[1, 1, 0, 0], [1, 0, 1, 0]], dtype=np.uint8)
    lz = np.array([[0, 1, 0, 1], [0, 0, 1, 1]], dtype=np.uint8)
    return checks, checks.copy(), lx, lz


def _brute_sector(checks: np.ndarray, logicals: np.ndarray, threshold: int):
    n = checks.shape[1]
    for weight in range(1, threshold + 1):
        for support in itertools.combinations(range(n), weight):
            vector = np.zeros(n, dtype=np.uint8)
            vector[list(support)] = 1
            if not np.any((checks @ vector) & 1) and np.any(
                (logicals @ vector) & 1
            ):
                return vector
    return None


def test_mitm_sat_witness_is_replayed_and_tamper_is_rejected():
    hx, hz, lx, lz = _valid_d2_css_matrices()
    evidence = oracle.evaluate_css_low_weight_oracle(
        hx,
        hz,
        lx,
        lz,
        max_weight=2,
    )

    assert evidence["outcome"] == "SAT"
    assert evidence["witness"]["side"] == "X"
    assert evidence["witness"]["weight"] == 2
    assert oracle.verify_css_low_weight_oracle(
        evidence, hx, hz, lx, lz
    ) == []

    tampered = copy.deepcopy(evidence)
    tampered["witness"]["bits"][0] ^= 1
    assert "oracle evidence self-hash mismatch" in (
        oracle.verify_css_low_weight_oracle(
            tampered, hx, hz, lx, lz
        )
    )


def test_two_complete_unsat_sectors_are_required_for_lower_bound():
    hx, hz, lx, lz = _valid_d2_css_matrices()
    evidence = oracle.evaluate_css_low_weight_oracle(
        hx,
        hz,
        lx,
        lz,
        max_weight=1,
    )

    assert evidence["outcome"] == "UNSAT"
    assert evidence["distance_lower_bound"] == 2
    assert set(evidence["sectors"]) == {"X", "Z"}
    assert all(
        evidence["sectors"][side]["outcome"] == "UNSAT"
        for side in ("X", "Z")
    )
    assert oracle.verify_css_low_weight_oracle(
        evidence, hx, hz, lx, lz
    ) == []

    inconsistent = copy.deepcopy(evidence)
    inconsistent["sectors"]["X"]["decision_complete"] = False
    oracle._seal_sector_evidence(inconsistent["sectors"]["X"])
    oracle._seal_oracle_evidence(inconsistent)
    assert any(
        "terminal/retry semantics" in failure
        for failure in oracle.verify_css_low_weight_oracle(
            inconsistent, hx, hz, lx, lz
        )
    )


def test_historical_source_relaxation_rejects_unsat_lower_bound(monkeypatch):
    hx, hz, lx, lz = _valid_d2_css_matrices()
    evidence = oracle.evaluate_css_low_weight_oracle(
        hx,
        hz,
        lx,
        lz,
        max_weight=1,
    )
    assert evidence["outcome"] == "UNSAT"
    historical_source = evidence["source_sha256"]
    replacement_source = (
        "f" * 64 if historical_source != "f" * 64 else "e" * 64
    )
    monkeypatch.setattr(oracle, "_SOURCE_SHA256", replacement_source)

    strict = oracle.verify_css_low_weight_oracle(
        evidence, hx, hz, lx, lz
    )
    relaxed = oracle.verify_css_low_weight_oracle(
        evidence,
        hx,
        hz,
        lx,
        lz,
        require_current_source=False,
    )
    assert "oracle evidence source binding mismatch" in strict
    assert any(
        "restricted to SAT upper-bound witnesses" in failure
        for failure in relaxed
    )


@pytest.mark.parametrize("threshold", range(5))
def test_mitm_matches_bruteforce_on_small_random_sector_problems(threshold):
    rng = np.random.default_rng(90210 + threshold)
    for _ in range(20):
        hx = rng.integers(0, 2, size=(3, 8), dtype=np.uint8)
        hz = rng.integers(0, 2, size=(3, 8), dtype=np.uint8)
        lx = rng.integers(0, 2, size=(2, 8), dtype=np.uint8)
        lz = rng.integers(0, 2, size=(2, 8), dtype=np.uint8)
        evidence = oracle._solve_sector_mitm(
            hx,
            lx,
            max_weight=threshold,
            sector="Z",
        )
        brute_z = _brute_sector(hx, lx, threshold)
        expected_sat = brute_z is not None
        assert evidence["outcome"] == ("SAT" if expected_sat else "UNSAT")


def test_missing_optional_sat_backend_is_unknown_and_retryable(monkeypatch):
    def unavailable(*_args, **kwargs):
        return {
            "outcome": "backend_unavailable",
            "decision_complete": False,
            "retryable": True,
            "message": "python-sat unavailable",
            "max_weight": kwargs["max_weight"],
        }

    monkeypatch.setattr(oracle, "solve_css_threshold_sat", unavailable)
    hx, hz, lx, lz = _valid_d2_css_matrices()
    evidence = oracle.evaluate_css_low_weight_oracle(
        hx,
        hz,
        lx,
        lz,
        max_weight=5,
        hard_timeout_s=0.1,
    )

    assert evidence["outcome"] == "UNKNOWN"
    assert evidence["decision_complete"] is False
    assert evidence["retryable"] is True
    assert evidence["distance_lower_bound"] is None
    assert set(evidence["sectors"]) == {"X", "Z"}
    assert oracle.verify_css_low_weight_oracle(
        evidence, hx, hz, lx, lz
    ) == []


def test_incomplete_sat_backend_unsat_is_unknown_not_a_lower_bound(monkeypatch):
    monkeypatch.setattr(
        oracle,
        "solve_css_threshold_sat",
        lambda *_args, **_kwargs: {
            "outcome": "unsat",
            "decision_complete": False,
            "threshold_infeasible": False,
            "retryable": True,
        },
    )
    hx, hz, lx, lz = _valid_d2_css_matrices()
    evidence = oracle.evaluate_css_low_weight_oracle(
        hx, hz, lx, lz, max_weight=5, hard_timeout_s=0.1
    )

    assert evidence["outcome"] == "UNKNOWN"
    assert evidence["distance_lower_bound"] is None
    assert evidence["retryable"] is True


def test_invalid_logical_detectors_can_never_produce_unsat_credit():
    empty_checks = np.zeros((0, 1), dtype=np.uint8)
    broken_logical = np.zeros((1, 1), dtype=np.uint8)
    evidence = oracle.evaluate_css_low_weight_oracle(
        empty_checks,
        empty_checks,
        broken_logical,
        broken_logical,
        max_weight=1,
    )

    assert evidence["outcome"] == "UNKNOWN"
    assert evidence["distance_lower_bound"] is None
    assert evidence["logical_detector"]["verified"] is False
    assert oracle.verify_css_low_weight_oracle(
        evidence,
        empty_checks,
        empty_checks,
        broken_logical,
        broken_logical,
    ) == []
