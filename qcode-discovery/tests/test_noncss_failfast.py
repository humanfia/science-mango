from pathlib import Path

from evaluation.noncss_certificate import build_noncss_certificate


KNOWN_ANSWER = Path(__file__).resolve().parent.parent / "results" / "known_answer_gate.json"


def test_disconnected_noncss_claim_skips_milp():
    # Two independent XX components, so the support graph is disconnected.
    certificate = build_noncss_certificate(
        {
            "symplectic_stabilizer": [
                [1, 1, 0, 0, 0, 0, 0, 0],
                [0, 0, 1, 1, 0, 0, 0, 0],
            ],
        },
        known_answer_artifact=KNOWN_ANSWER,
        timeout_per_logical=10,
        total_timeout=30,
    )
    assert certificate["milp"]["completed_directions"] == 0
    assert certificate["final_gate"]["checks"]["connected_tanner_graph"] is False
    assert certificate["passed"] is False
