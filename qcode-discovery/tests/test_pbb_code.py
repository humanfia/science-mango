"""Tests for perturbed bivariate bicycle (PBB) code construction and symplectic MILP."""

import numpy as np
import pytest
from qldpc.codes import QuditCode

from evaluation.pbb_code import (
    build_pbb_code,
    check_commutativity,
    get_pbb_params_fast,
    symplectic_weight,
    symplectic_weight_bound_pbb,
    validate_pbb_terms,
    _poly_to_matrix,
)
from evaluation.bb_code import build_bb_code, get_code_params_fast
from evaluation.distance_milp import (
    compute_distance_milp,
    compute_distance_milp_symplectic,
)


# --- Known BB codes for CSS baseline ---

# Gross code: [[72, 12, 6]] at (6,6)
GROSS_A = [(3, 0), (0, 1), (0, 2)]
GROSS_B = [(0, 3), (1, 0), (2, 0)]

# Code at (6,3) with k=4: [[36, 4, ?]]
SMALL_A = [(0, 0), (0, 1), (0, 2)]
SMALL_B = [(1, 0), (0, 0), (0, 1)]


class TestCSSEquivalence:
    """Verify that PBB with C=D=None matches BBCode exactly."""

    def test_gross_code_css_params(self):
        """CSS PBB code should have same (n, k) as BBCode."""
        bb = build_bb_code(6, 6, GROSS_A, GROSS_B)
        ptb = build_pbb_code(6, 6, GROSS_A, GROSS_B)

        bb_n, bb_k = get_code_params_fast(bb)
        ptb_n, ptb_k = get_pbb_params_fast(ptb)

        assert bb_n == ptb_n == 72
        assert bb_k == ptb_k == 12

    def test_small_code_css_params(self):
        """CSS PBB code at (6,3) should match BBCode."""
        bb = build_bb_code(6, 3, SMALL_A, SMALL_B)
        ptb = build_pbb_code(6, 3, SMALL_A, SMALL_B)

        bb_n, bb_k = get_code_params_fast(bb)
        ptb_n, ptb_k = get_pbb_params_fast(ptb)

        assert bb_n == ptb_n
        assert bb_k == ptb_k

    def test_css_returns_bbcode_type(self):
        """CSS case should return a BBCode, not QuditCode."""
        from qldpc.codes import BBCode
        code = build_pbb_code(6, 6, GROSS_A, GROSS_B)
        assert isinstance(code, BBCode)

    def test_css_with_empty_lists(self):
        """Empty C_terms/D_terms should also give CSS."""
        from qldpc.codes import BBCode
        code = build_pbb_code(6, 6, GROSS_A, GROSS_B, C_terms=[], D_terms=[])
        assert isinstance(code, BBCode)

    def test_css_distance_milp(self):
        """CSS BB code distance via standard MILP should work."""
        code = build_pbb_code(6, 6, GROSS_A, GROSS_B)
        d, details = compute_distance_milp(code, timeout_per_logical=10,
                                            total_timeout=60, early_stop=2)
        assert d >= 2
        assert details["k"] == 12


class TestNonCSSConstruction:
    """Test non-CSS PBB code construction."""

    def _find_valid_perturbation(self, ell, m, A_terms, B_terms, rng=None):
        """Find a valid (C, D) perturbation by random search."""
        if rng is None:
            rng = np.random.default_rng(42)

        from evaluation.bb_code import terms_to_poly
        from sympy.abc import x, y
        from qldpc import codes

        poly_a = terms_to_poly(A_terms)
        poly_b = terms_to_poly(B_terms)
        bb = codes.BBCode({x: ell, y: m}, poly_a, poly_b)

        mat_A = _poly_to_matrix(bb, A_terms)
        mat_B = _poly_to_matrix(bb, B_terms)

        ell * m
        for _ in range(10000):
            # Random multi-term C and D (2-4 terms each)
            num_c = rng.integers(2, 5)
            num_d = rng.integers(2, 5)
            c_exps = set()
            while len(c_exps) < num_c:
                c_exps.add((int(rng.integers(0, ell)), int(rng.integers(0, m))))
            d_exps = set()
            while len(d_exps) < num_d:
                d_exps.add((int(rng.integers(0, ell)), int(rng.integers(0, m))))

            C_terms = list(c_exps)
            D_terms = list(d_exps)

            mat_C = _poly_to_matrix(bb, C_terms)
            mat_D = _poly_to_matrix(bb, D_terms)

            if check_commutativity(mat_A, mat_B, mat_C, mat_D):
                return C_terms, D_terms

        pytest.skip("Could not find valid perturbation in 10000 trials")

    def test_non_css_construction_63(self):
        """Non-CSS PBB code at (6,3) should be constructible."""
        C_terms, D_terms = self._find_valid_perturbation(6, 3, SMALL_A, SMALL_B)
        code = build_pbb_code(6, 3, SMALL_A, SMALL_B, C_terms, D_terms)

        assert isinstance(code, QuditCode)
        n, k = get_pbb_params_fast(code)
        assert n == 36
        assert k > 0

    def test_non_css_different_k(self):
        """Non-CSS codes should be able to access different k values."""
        np.random.default_rng(123)
        k_values = set()
        for seed in range(5):
            rng_i = np.random.default_rng(seed * 100)
            try:
                C_terms, D_terms = self._find_valid_perturbation(
                    6, 3, SMALL_A, SMALL_B, rng=rng_i
                )
                code = build_pbb_code(6, 3, SMALL_A, SMALL_B, C_terms, D_terms)
                _, k = get_pbb_params_fast(code)
                k_values.add(k)
            except (ValueError, np.linalg.LinAlgError):
                continue

        # Should find at least 2 distinct k values
        assert len(k_values) >= 2, f"Expected >=2 distinct k values, got: {k_values}"

    def test_commutativity_violation_raises(self):
        """Invalid (C, D) should raise ValueError."""
        # Use a single monomial for C and D -- very likely to violate
        # commutativity (0% acceptance for monomials at (6,6))
        C_terms = [(1, 0)]
        D_terms = [(0, 1)]
        with pytest.raises(ValueError, match="Commutativity violated"):
            build_pbb_code(6, 6, GROSS_A, GROSS_B, C_terms, D_terms)

    def test_validate_pbb_terms_errors(self):
        """Validation should catch bad terms."""
        with pytest.raises(ValueError, match="at least 1 term"):
            validate_pbb_terms(6, 3, [])

        with pytest.raises(ValueError, match="x-exponent"):
            validate_pbb_terms(6, 3, [(7, 0)])

        with pytest.raises(ValueError, match="duplicate"):
            validate_pbb_terms(6, 3, [(1, 0), (1, 0)])

    def test_symplectic_weight(self):
        """Symplectic weight computation."""
        # [1,0,0 | 0,0,1] -> qubit 0 has X, qubit 2 has Z -> weight 2
        vec = np.array([1, 0, 0, 0, 0, 1])
        assert symplectic_weight(vec) == 2

        # [1,1,0 | 1,0,0] -> qubit 0 has Y (both), qubit 1 has X -> weight 2
        vec = np.array([1, 1, 0, 1, 0, 0])
        assert symplectic_weight(vec) == 2

        # Zero vector -> weight 0
        vec = np.array([0, 0, 0, 0, 0, 0])
        assert symplectic_weight(vec) == 0


class TestSymplecticMILP:
    """Test symplectic MILP distance computation."""

    def test_symplectic_milp_on_css_code(self):
        """Symplectic MILP on a CSS code should agree with CSS MILP."""
        bb = build_bb_code(6, 6, GROSS_A, GROSS_B)
        n, k = get_code_params_fast(bb)
        assert k == 12

        # CSS MILP
        d_css, details_css = compute_distance_milp(
            bb, timeout_per_logical=15, total_timeout=60, early_stop=2
        )

        # Now build the same code as a general stabilizer code for symplectic MILP
        stab_matrix = np.array(bb.matrix, dtype=int) % 2
        stab_code = QuditCode(stab_matrix)

        d_symp, details_symp = compute_distance_milp_symplectic(
            stab_code, timeout_per_logical=15, total_timeout=60, early_stop=2
        )

        # Both should find the same distance
        assert d_css == d_symp, (
            f"CSS MILP d={d_css} != symplectic MILP d={d_symp}"
        )

    def test_symplectic_milp_on_noncss(self):
        """Symplectic MILP should work on a non-CSS PBB code."""
        # Find a valid perturbation
        rng = np.random.default_rng(42)
        from evaluation.bb_code import terms_to_poly
        from sympy.abc import x, y
        from qldpc import codes

        ell, m = 6, 3
        poly_a = terms_to_poly(SMALL_A)
        poly_b = terms_to_poly(SMALL_B)
        bb = codes.BBCode({x: ell, y: m}, poly_a, poly_b)

        mat_A = _poly_to_matrix(bb, SMALL_A)
        mat_B = _poly_to_matrix(bb, SMALL_B)

        found = False
        for _ in range(10000):
            num_c = int(rng.integers(2, 5))
            num_d = int(rng.integers(2, 5))
            c_exps = set()
            while len(c_exps) < num_c:
                c_exps.add((int(rng.integers(0, ell)), int(rng.integers(0, m))))
            d_exps = set()
            while len(d_exps) < num_d:
                d_exps.add((int(rng.integers(0, ell)), int(rng.integers(0, m))))

            C_terms = list(c_exps)
            D_terms = list(d_exps)

            mat_C = _poly_to_matrix(bb, C_terms)
            mat_D = _poly_to_matrix(bb, D_terms)

            if check_commutativity(mat_A, mat_B, mat_C, mat_D):
                code = build_pbb_code(ell, m, SMALL_A, SMALL_B, C_terms, D_terms)
                _, k = get_pbb_params_fast(code)
                if k > 0:
                    found = True
                    break

        if not found:
            pytest.skip("Could not find valid non-CSS code with k>0")

        d, details = compute_distance_milp_symplectic(
            code, timeout_per_logical=15, total_timeout=60, early_stop=2
        )
        assert d >= 1
        assert details["k"] > 0
        assert details["num_logicals_checked"] > 0
        print(f"Non-CSS PBB code: [[{code.num_qudits}, {k}, {d}]]")
        print(f"  C_terms={C_terms}, D_terms={D_terms}")
        print(f"  Details: {details}")

    def test_symplectic_weight_bound(self):
        """symplectic_weight_bound_pbb should give a valid upper bound."""
        rng = np.random.default_rng(42)
        # Find a non-CSS code
        from evaluation.bb_code import terms_to_poly
        from sympy.abc import x, y
        from qldpc import codes

        ell, m = 6, 3
        poly_a = terms_to_poly(SMALL_A)
        poly_b = terms_to_poly(SMALL_B)
        bb = codes.BBCode({x: ell, y: m}, poly_a, poly_b)
        mat_A = _poly_to_matrix(bb, SMALL_A)
        mat_B = _poly_to_matrix(bb, SMALL_B)

        for _ in range(10000):
            num_c = int(rng.integers(2, 5))
            num_d = int(rng.integers(2, 5))
            c_exps = set()
            while len(c_exps) < num_c:
                c_exps.add((int(rng.integers(0, ell)), int(rng.integers(0, m))))
            d_exps = set()
            while len(d_exps) < num_d:
                d_exps.add((int(rng.integers(0, ell)), int(rng.integers(0, m))))

            C_terms = list(c_exps)
            D_terms = list(d_exps)
            mat_C = _poly_to_matrix(bb, C_terms)
            mat_D = _poly_to_matrix(bb, D_terms)

            if check_commutativity(mat_A, mat_B, mat_C, mat_D):
                code = build_pbb_code(ell, m, SMALL_A, SMALL_B, C_terms, D_terms)
                if code.dimension > 0:
                    ub = symplectic_weight_bound_pbb(code)
                    assert ub >= 1
                    assert ub <= code.num_qudits
                    return

        pytest.skip("Could not find valid non-CSS code")
