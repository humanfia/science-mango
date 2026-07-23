"""Tests for the public terminal challenge gate."""

from evaluation.challenge_gate import evaluate_challenge_gate


def test_noncss_claim_fails_closed_before_css_projection(tmp_path):
    result = evaluate_challenge_gate(
        {
            "ell": 6,
            "m": 6,
            "A_terms": [[0, 0]],
            "B_terms": [[0, 0]],
            "C_terms": [[1, 0]],
            "D_terms": [[0, 1]],
        },
        known_answer_artifact=tmp_path / "not-used.json",
    )
    assert result["accepted"] is False
    assert result["checks"]["css_bb_candidate"] is False
