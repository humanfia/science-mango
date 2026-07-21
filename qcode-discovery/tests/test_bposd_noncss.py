"""Tests for non-CSS BP-OSD distance estimation."""

import numpy as np
import pytest
from qldpc.codes import QuditCode

from evaluation.distance_bposd_noncss import (
    estimate_distance_noncss,
    estimate_distance_noncss_osdcs,
    _symplectic_syndrome_matrix,
)
from evaluation.pbb_code import (
    build_pbb_code,
    check_commutativity,
    _poly_to_matrix,
)
from evaluation.bb_code import build_bb_code, get_code_params_fast


# --- Known codes ---

GROSS_A = [(3, 0), (0, 1), (0, 2)]
GROSS_B = [(0, 3), (1, 0), (2, 0)]

SMALL_A = [(0, 0), (0, 1), (0, 2)]
SMALL_B = [(1, 0), (0, 0), (0, 1)]


def test_symplectic_syndrome_matrix_swaps_xz_blocks():
    """Full symplectic BP-OSD must decode symplectic, not ordinary, syndrome."""
    stabilizer_x = np.array([[1, 0]], dtype=np.uint8)  # single-qubit X row
    effective = _symplectic_syndrome_matrix(stabilizer_x)

    x_error = np.array([1, 0], dtype=np.uint8)
    z_error = np.array([0, 1], dtype=np.uint8)

    # An X stabilizer commutes with X and anticommutes with Z.
    assert int((effective @ x_error % 2)[0]) == 0
    assert int((effective @ z_error % 2)[0]) == 1

    # The raw dot product has the opposite behavior and is not a valid
    # symplectic syndrome map.
    assert int((stabilizer_x @ x_error % 2)[0]) == 1
    assert int((stabilizer_x @ z_error % 2)[0]) == 0


class TestBpOsdOnCSSCode:
    """Validate BP-OSD non-CSS estimator on CSS codes with known distances."""

    def test_gross_code_as_stabilizer(self):
        """Gross [[72,12,6]] through non-CSS BP-OSD should give d <= 6."""
        bb = build_bb_code(6, 6, GROSS_A, GROSS_B)
        stab = np.array(bb.matrix, dtype=int) % 2
        code = QuditCode(stab)

        assert code.num_qudits == 72
        assert code.dimension == 12

        d = estimate_distance_noncss(code, num_trials=2000, seed=42)
        assert 4 <= d <= 6, f"Expected 4 <= d <= 6 for Gross [[72,12,6]] code, got d={d}"

    def test_small_css_code(self):
        """Small CSS code at (6,3) through non-CSS BP-OSD."""
        bb = build_bb_code(6, 3, SMALL_A, SMALL_B)
        n, k = get_code_params_fast(bb)
        if k == 0:
            pytest.skip("Code has k=0")

        stab = np.array(bb.matrix, dtype=int) % 2
        code = QuditCode(stab)

        d_bposd = estimate_distance_noncss(code, num_trials=300, seed=42)
        assert d_bposd >= 1
        assert d_bposd <= n, f"BP-OSD returned n={n}, decoder likely failing"


class TestBpOsdOnNonCSSCode:
    """Test BP-OSD on genuine non-CSS PBB codes."""

    def _find_valid_ptb(self, ell, m, A_terms, B_terms, rng_seed=42):
        """Find a valid non-CSS PBB code with k > 0."""
        from evaluation.bb_code import terms_to_poly
        from sympy.abc import x, y
        from qldpc import codes

        rng = np.random.default_rng(rng_seed)
        poly_a = terms_to_poly(A_terms)
        poly_b = terms_to_poly(B_terms)
        bb = codes.BBCode({x: ell, y: m}, poly_a, poly_b)
        mat_A = _poly_to_matrix(bb, A_terms)
        mat_B = _poly_to_matrix(bb, B_terms)

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
                code = build_pbb_code(ell, m, A_terms, B_terms, C_terms, D_terms)
                if code.dimension > 0:
                    return code, C_terms, D_terms

        pytest.skip("Could not find valid non-CSS code")

    def test_ptb_63_distance(self):
        """Non-CSS PBB code at (6,3) -- BP-OSD should give a finite bound."""
        code, C, D = self._find_valid_ptb(6, 3, SMALL_A, SMALL_B)
        n = code.num_qudits
        k = code.dimension

        d = estimate_distance_noncss(code, num_trials=300, seed=42)
        assert 1 <= d <= n
        print(f"PBB [[{n},{k},{d}]] C={C} D={D}")

    def test_ptb_63_milp_crosscheck(self):
        """Cross-check BP-OSD against MILP on a non-CSS code at (6,3)."""
        from evaluation.distance_milp import compute_distance_milp_symplectic

        code, C, D = self._find_valid_ptb(6, 3, SMALL_A, SMALL_B)
        n = code.num_qudits

        # MILP exact distance (feasible at n=36)
        d_milp, details = compute_distance_milp_symplectic(
            code, timeout_per_logical=15, total_timeout=60, early_stop=2
        )

        # BP-OSD upper bound
        d_bposd = estimate_distance_noncss(code, num_trials=500, seed=42)

        assert d_bposd >= 1
        assert d_bposd <= n
        # Both are upper bounds; MILP is generally tighter
        if d_milp > 0:
            assert d_bposd >= d_milp, (
                f"BP-OSD d={d_bposd} < MILP d={d_milp}: "
                f"BP-OSD should not undercut a valid MILP upper bound"
            )
        print(f"PBB [[{n},{code.dimension}]]: MILP d={d_milp}, BP-OSD d<={d_bposd}")

    @pytest.mark.skip(reason="OSD-CS segfaults in ldpc BpOsdDecoder on mixed-channel matrices")
    def test_osdcs_tighter_than_osd0(self):
        """OSD-CS should give bounds at least as tight as OSD_0."""
        code, _, _ = self._find_valid_ptb(6, 3, SMALL_A, SMALL_B, rng_seed=123)

        d_osd0 = estimate_distance_noncss(code, num_trials=200, seed=42)
        d_osdcs = estimate_distance_noncss_osdcs(code, num_trials=200, seed=42)

        # OSD-CS should be <= OSD_0 (tighter or equal)
        # Due to randomness, allow OSD-CS to be slightly worse
        assert d_osdcs <= d_osd0 + 2, (
            f"OSD-CS d={d_osdcs} much worse than OSD_0 d={d_osd0}"
        )
