from pathlib import Path

from evaluation.matrix_certificate import build_matrix_css_certificate
from evaluation.noncss_certificate import build_noncss_certificate


KNOWN_ANSWER = Path(__file__).resolve().parent.parent / "results" / "known_answer_gate.json"


def test_generic_css_certificate_exports_all_2k_directions():
    certificate = build_matrix_css_certificate(
        {
            "source": "test [[4,1,2]]",
            "H_X": ["1111"],
            "H_Z": ["1100", "0011"],
        },
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
    # Standard cyclic [[5,1,3]] stabilizers: XZZXI and shifts.
    paulies = ["XZZXI", "IXZZX", "XIXZZ", "ZXIXZ"]
    rows = []
    for pauli in paulies:
        x = [int(item in "XY") for item in pauli]
        z = [int(item in "ZY") for item in pauli]
        rows.append(x + z)
    certificate = build_noncss_certificate(
        {
            "source": "test [[5,1,3]]",
            "symplectic_stabilizer": rows,
        },
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
