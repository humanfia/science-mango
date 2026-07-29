from pathlib import Path

import pytest

import evaluation.matrix_certificate as matrix_certificate_module
import evaluation.noncss_certificate as noncss_certificate_module
from evaluation.matrix_certificate import (
    build_matrix_css_certificate,
    verify_matrix_css_certificate,
)
from evaluation.noncss_certificate import (
    build_noncss_certificate,
    verify_noncss_certificate,
)


KNOWN_ANSWER = Path(__file__).resolve().parent.parent / "results" / "known_answer_gate.json"


def _generic_css_claim():
    return {
        "source": "test [[4,1,2]]",
        "H_X": ["1111"],
        "H_Z": ["1100", "0011"],
    }


def _five_qubit_claim():
    # Standard cyclic [[5,1,3]] stabilizers: XZZXI and shifts.
    paulies = ["XZZXI", "IXZZX", "XIXZZ", "ZXIXZ"]
    rows = []
    for pauli in paulies:
        x = [int(item in "XY") for item in pauli]
        z = [int(item in "ZY") for item in pauli]
        rows.append(x + z)
    return {
        "source": "test [[5,1,3]]",
        "symplectic_stabilizer": rows,
    }


def _contradictory_result(status: int) -> dict:
    return {
        "success": False,
        "status": status,
        "message": "contradicts stored feasible optimum",
        "objective": None,
        "mip_dual_bound": None,
        "mip_gap": None,
        "mip_node_count": 0,
        "elapsed_s": 0.0,
        "operator": None,
    }


def test_generic_css_certificate_exports_all_2k_directions():
    certificate = build_matrix_css_certificate(
        _generic_css_claim(),
        known_answer_artifact=KNOWN_ANSWER,
        timeout_per_logical=10,
        total_timeout=30,
    )
    assert certificate["claim"]["n"] == 4
    assert certificate["claim"]["k"] == 1
    assert certificate["milp"]["exact"] is True
    assert certificate["milp"]["completed_directions"] == 2
    assert certificate["milp"]["distance"] == 2
    assert certificate["upper_witness"]["weight"] == 2
    # It is a complete exact certificate, but intentionally not a challenge win.
    assert certificate["passed"] is False
    assert "challenge_win" in certificate["final_gate"]["failures"]


def test_generic_noncss_five_qubit_certificate_exports_symplectic_witness():
    certificate = build_noncss_certificate(
        _five_qubit_claim(),
        known_answer_artifact=KNOWN_ANSWER,
        timeout_per_logical=10,
        total_timeout=30,
    )
    assert certificate["claim"]["n"] == 5
    assert certificate["claim"]["k"] == 1
    assert certificate["milp"]["exact"] is True
    assert certificate["milp"]["completed_directions"] == 2
    assert certificate["milp"]["distance"] == 3
    assert certificate["upper_witness"]["weight"] == 3
    assert certificate["passed"] is False


@pytest.mark.parametrize("solver_status", [2, 3])
def test_generic_css_verifier_retries_contradictory_terminal_status(
    monkeypatch, solver_status,
):
    certificate = build_matrix_css_certificate(
        _generic_css_claim(),
        known_answer_artifact=KNOWN_ANSWER,
        timeout_per_logical=10,
        total_timeout=30,
    )
    monkeypatch.setattr(
        matrix_certificate_module,
        "solve_css_direction",
        lambda *_args, **_kwargs: _contradictory_result(solver_status),
    )

    result = verify_matrix_css_certificate(
        certificate,
        known_answer_artifact=KNOWN_ANSWER,
        timeout_per_logical=10,
        total_timeout=30,
    )

    assert result["passed"] is False
    assert result["replay_complete"] is False


@pytest.mark.parametrize("solver_status", [2, 3])
def test_noncss_verifier_retries_contradictory_terminal_status(
    monkeypatch, solver_status,
):
    certificate = build_noncss_certificate(
        _five_qubit_claim(),
        known_answer_artifact=KNOWN_ANSWER,
        timeout_per_logical=10,
        total_timeout=30,
    )
    monkeypatch.setattr(
        noncss_certificate_module,
        "solve_symplectic_direction",
        lambda *_args, **_kwargs: _contradictory_result(solver_status),
    )

    result = verify_noncss_certificate(
        certificate,
        known_answer_artifact=KNOWN_ANSWER,
        timeout_per_logical=10,
        total_timeout=30,
    )

    assert result["passed"] is False
    assert result["replay_complete"] is False
