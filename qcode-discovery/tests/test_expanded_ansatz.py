import numpy as np
import pytest

from evaluation.bb_code import build_bb_code
from evaluation.certificate import solve_css_direction, verify_css_witness
from evaluation.distance_milp import get_code_matrices
from scripts.search_expanded_ansatz import (
    candidate_key,
    parse_shapes,
    parse_term_splits,
    sample_css_claim,
)


def test_expanded_sampler_covers_weight_four_to_six():
    rng = np.random.default_rng(9)
    splits = parse_term_splits("2+2,2+3,3+3,4+2")
    weights = set()
    for trial in range(100):
        claim = sample_css_claim(
            rng, ((6, 6),), splits, seed=9, trial=trial,
        )
        weights.add(len(claim["A_terms"]) + len(claim["B_terms"]))
        assert len(set(map(tuple, claim["A_terms"]))) == len(claim["A_terms"])
        assert len(set(map(tuple, claim["B_terms"]))) == len(claim["B_terms"])
        code = build_bb_code(
            claim["ell"], claim["m"], claim["A_terms"], claim["B_terms"],
        )
        hx, hz, _, _ = get_code_matrices(code)
        assert max(np.asarray(hx).sum(axis=1)) <= 6
        assert max(np.asarray(hz).sum(axis=1)) <= 6
    assert weights == {4, 5, 6}


def test_expanded_key_ignores_term_order_but_binds_shape():
    claim = {
        "ell": 6, "m": 6,
        "A_terms": [[0, 0], [1, 0]],
        "B_terms": [[0, 1], [2, 0]],
    }
    reordered = {**claim, "A_terms": list(reversed(claim["A_terms"]))}
    reshaped = {**claim, "ell": 9}
    assert candidate_key(claim) == candidate_key(reordered)
    assert candidate_key(claim) != candidate_key(reshaped)


def test_expanded_parser_rejects_overweight_checks():
    assert parse_shapes("6x6,12x6") == ((6, 6), (12, 6))
    with pytest.raises(Exception):
        parse_term_splits("3+4")


def test_css_solver_objective_matches_saved_incumbent_weight():
    checks = np.zeros((0, 3), dtype=np.uint8)
    target = np.asarray([1, 0, 0], dtype=np.uint8)
    result = solve_css_direction(checks, target, timeout=10)
    assert result["success"] is True
    assert result["objective"] == result["operator"]["weight"] == 1
    assert verify_css_witness(result, checks, target) == []
