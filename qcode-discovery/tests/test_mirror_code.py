"""Tests for mirror code construction (arXiv:2603.05496)."""

import numpy as np
import pytest
from qldpc.codes import QuditCode

from evaluation.mirror_code import (
    build_mirror_code,
    get_mirror_params,
    _element_to_index,
    _group_add,
    _group_inv,
    _enumerate_group,
)


class TestGroupOperations:
    """Test basic group operations."""

    def test_element_to_index(self):
        """Index mapping for Z3 × Z4."""
        orders = (3, 4)
        assert _element_to_index((0, 0), orders) == 0
        assert _element_to_index((0, 1), orders) == 1
        assert _element_to_index((1, 0), orders) == 4
        assert _element_to_index((2, 3), orders) == 11

    def test_group_add(self):
        """Componentwise addition mod orders."""
        assert _group_add((2, 3), (1, 2), (3, 5)) == (0, 0)
        assert _group_add((1, 1), (1, 1), (3, 3)) == (2, 2)

    def test_group_inv(self):
        """Group inverse."""
        assert _group_inv((0, 0), (5, 6)) == (0, 0)
        assert _group_inv((1, 2), (5, 6)) == (4, 4)
        # a + inv(a) should equal identity
        a = (2, 3)
        orders = (5, 7)
        assert _group_add(a, _group_inv(a, orders), orders) == (0, 0)

    def test_enumerate_group(self):
        """Enumerate all elements of Z3 × Z2."""
        elements = _enumerate_group((3, 2))
        assert len(elements) == 6
        assert (0, 0) in elements
        assert (2, 1) in elements


class TestMirrorConstruction:
    """Test mirror code construction."""

    def test_basic_construction(self):
        """Build a mirror code and check dimensions."""
        code = build_mirror_code(
            (3, 3),
            [(0, 0), (1, 0), (2, 0)],
            [(0, 0), (0, 1), (0, 2)],
        )
        n, k = get_mirror_params(code)
        assert n == 9
        assert k > 0
        assert isinstance(code, QuditCode)

    def test_stabilizer_weight(self):
        """Check weight = |A| + |B|."""
        A = [(0, 0), (1, 0), (0, 1)]
        B = [(0, 0), (2, 0), (0, 2)]
        code = build_mirror_code((5, 5), A, B)
        stab = np.array(code.matrix, dtype=int) % 2
        # Each row should have exactly |A| + |B| = 6 nonzero entries
        weights = np.sum(stab, axis=1)
        assert np.all(weights == 6), f"Weights: {np.unique(weights)}"

    def test_n_equals_group_order(self):
        """n should equal product of group orders."""
        for orders in [(3, 4), (5, 6), (6, 12)]:
            expected_n = orders[0] * orders[1]
            code = build_mirror_code(
                orders,
                [(0, 0), (1, 0), (0, 1)],
                [(0, 0), (1, 0), (0, 1)],
            )
            assert code.num_qudits == expected_n

    def test_validation_errors(self):
        """Invalid inputs should raise ValueError."""
        with pytest.raises(ValueError, match="nonempty"):
            build_mirror_code((3, 3), [], [(0, 0)])

        with pytest.raises(ValueError, match="wrong dimension"):
            build_mirror_code((3, 3), [(0, 0, 0)], [(0, 0)])

        with pytest.raises(ValueError, match="out of range"):
            build_mirror_code((3, 3), [(5, 0), (0, 0), (1, 0)], [(0, 0)])

    def test_known_code_z9(self):
        """Z3×Z3 should produce valid codes with k > 0."""
        # From our search: A=[(0,0),(1,0),(2,0)], B=[(0,0),(0,1),(0,2)]
        code = build_mirror_code(
            (3, 3),
            [(0, 0), (1, 0), (2, 0)],
            [(0, 0), (0, 1), (0, 2)],
        )
        n, k = get_mirror_params(code)
        assert n == 9
        assert k == 4  # Known from search

    def test_known_code_z30(self):
        """Z5×Z6 should produce [[30,4,4]] or better."""
        code = build_mirror_code(
            (5, 6),
            [(0, 0), (0, 1), (0, 2)],
            [(0, 0), (1, 0), (3, 1)],
        )
        n, k = get_mirror_params(code)
        assert n == 30
        assert k == 4


class TestMirrorWithDistance:
    """Test mirror codes with distance estimation."""

    def test_small_code_milp(self):
        """MILP distance on a small mirror code."""
        from evaluation.distance_milp import compute_distance_milp_symplectic

        code = build_mirror_code(
            (3, 3),
            [(0, 0), (1, 0), (2, 0)],
            [(0, 0), (0, 1), (0, 2)],
        )
        d, details = compute_distance_milp_symplectic(
            code, timeout_per_logical=10, total_timeout=30, early_stop=2,
        )
        assert d >= 1
        assert details["k"] > 0
        print(f"Mirror Z3×Z3: [[{code.num_qudits},{code.dimension},{d}]]")

    def test_bposd_on_mirror_code(self):
        """BP-OSD should give a reasonable bound on a mirror code."""
        from evaluation.distance_bposd_noncss import estimate_distance_noncss

        code = build_mirror_code(
            (5, 6),
            [(0, 0), (0, 1), (0, 2)],
            [(0, 0), (1, 0), (3, 1)],
        )
        n, k = get_mirror_params(code)
        d = estimate_distance_noncss(code, num_trials=300, seed=42)
        assert 2 <= d <= n // 2, f"Expected 2 <= d <= {n//2}, got d={d}"
        print(f"Mirror Z5×Z6: [[{n},{k},{d}]]")
