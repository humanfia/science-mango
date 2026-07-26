import numpy as np

from scripts.search_real_win import _candidate_key, _subset


def test_targeted_perturbations_stay_inside_base_support():
    rng = np.random.default_rng(7)
    base = [[0, 0], [1, 2], [3, 4]]
    for _ in range(20):
        selected = _subset(rng, base)
        assert 1 <= len(selected) < len(base)
        assert set(map(tuple, selected)) < set(map(tuple, base))


def test_candidate_key_ignores_term_order():
    left = {
        "A_terms": [[0, 0], [1, 0]],
        "B_terms": [[0, 1]],
        "C_terms": [[1, 0]],
        "D_terms": [[0, 1]],
    }
    right = {**left, "A_terms": list(reversed(left["A_terms"]))}
    assert _candidate_key(left) == _candidate_key(right)
