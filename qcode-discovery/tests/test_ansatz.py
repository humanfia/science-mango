"""Tests for Direction 1 (mixed-monomial ansatz exploration) infrastructure.

Covers:
- _classify_pattern() labels known code families correctly
- Self-dual hard gate returns d=2 for A=B, does NOT fire for A!=B
- Mixed-monomial trinomials produce valid BBCodes with correct n, k
- 4-term and 5-term polynomials produce valid BBCodes
- _structural_feedback() generates non-empty output
"""

from evaluation.bb_code import build_bb_code, validate_terms, get_code_params_fast
from evaluation.evaluator import evaluate_candidate, evaluate_candidate_milp


class TestClassifyPattern:
    """Test _classify_pattern labels known code families correctly."""

    def setup_method(self):
        from evolve.openevolve_evaluator import _classify_pattern
        self.classify = _classify_pattern

    def test_univariate(self):
        # A=f(y), B=g(x) -- univariate
        assert self.classify(
            [(0, 1), (0, 2), (0, 3)],
            [(1, 0), (2, 0), (3, 0)],
        ) == 0.0

    def test_xy_swap(self):
        # A = x^3 + y + y^2, B = y^3 + x + x^2 -- x/y-swap (pure terms, not univariate)
        assert self.classify(
            [(3, 0), (0, 1), (0, 2)],
            [(0, 3), (1, 0), (2, 0)],
        ) == 1.0

    def test_self_dual(self):
        # A = B -- self-dual
        assert self.classify(
            [(3, 0), (0, 1), (0, 2)],
            [(3, 0), (0, 1), (0, 2)],
        ) == 2.0

    def test_novel_mixed(self):
        # A has mixed monomial x^1*y^2
        assert self.classify(
            [(0, 0), (1, 2), (3, 0)],
            [(0, 3), (1, 0), (2, 0)],
        ) == 3.0

    def test_both_mixed(self):
        # Both A and B have mixed monomials (distinct sorted terms → not self-dual)
        assert self.classify(
            [(0, 0), (1, 2), (2, 1)],
            [(0, 0), (3, 1), (1, 3)],
        ) == 3.0

    def test_constant_monomial(self):
        # A = 1+y+y^2, B = 1+x^5+x^10 -- constant-monomial is structurally univariate
        assert self.classify(
            [(0, 0), (0, 1), (0, 2)],
            [(0, 0), (5, 0), (10, 0)],
        ) == 0.0


class TestSelfDualGate:
    """Self-dual gate returns d=2 for A=B, does NOT fire for A!=B."""

    def test_self_dual_returns_d2(self):
        # A = B = x^3 + y + y^2 at (6,6) -- self-dual, should get d=2
        A = [(3, 0), (0, 1), (0, 2)]
        result = evaluate_candidate(6, 6, A, A, quick=False,
                                     fom_threshold_refine=100, fom_threshold_exact=100)
        assert result["d"] == 2
        assert result["d_is_exact"] is True
        assert result["stage"] == "self_dual_d2"

    def test_non_self_dual_not_gated(self):
        # A != B -- should NOT hit self_dual gate
        result = evaluate_candidate(
            12, 6, [(3, 0), (0, 1), (0, 2)], [(0, 3), (1, 0), (2, 0)],
            quick=True,
        )
        assert result["stage"] != "self_dual_d2"
        assert result["k"] == 12

    def test_self_dual_milp_returns_d2(self):
        # Self-dual gate in MILP evaluator
        A = [(3, 0), (0, 1), (0, 2)]
        result = evaluate_candidate_milp(6, 6, A, A, quick=False)
        assert result["d"] == 2
        assert result["stage"] == "self_dual_d2"

    def test_self_dual_quick_mode(self):
        # In quick mode, self-dual gate fires BEFORE the quick return
        A = [(3, 0), (0, 1), (0, 2)]
        result = evaluate_candidate(6, 6, A, A, quick=True)
        assert result["stage"] == "self_dual_d2"
        assert result["d"] == 2


class TestMixedMonomialCodes:
    """Mixed-monomial trinomials produce valid BBCodes with correct n."""

    def test_mixed_trinomial_construction(self):
        # A = 1 + x*y + x^2*y^3, B = 1 + x^2*y + x*y^2
        A = [(0, 0), (1, 1), (2, 3)]
        B = [(0, 0), (2, 1), (1, 2)]
        validate_terms(6, 6, A, "A")
        validate_terms(6, 6, B, "B")
        code = build_bb_code(6, 6, A, B)
        n, k = get_code_params_fast(code)
        assert n == 72
        # k may be 0 -- that's fine, the construction should work

    def test_mixed_trinomial_at_12_6(self):
        # A = 1 + x*y^2 + x^3*y, B = 1 + x^2*y + x*y^3
        A = [(0, 0), (1, 2), (3, 1)]
        B = [(0, 0), (2, 1), (1, 3)]
        validate_terms(12, 6, A, "A")
        validate_terms(12, 6, B, "B")
        code = build_bb_code(12, 6, A, B)
        n, k = get_code_params_fast(code)
        assert n == 144

    def test_mixed_evaluator_accepts(self):
        # Mixed-monomial code should pass validation in evaluator
        A = [(0, 0), (1, 1), (2, 3)]
        B = [(0, 0), (2, 1), (1, 2)]
        result = evaluate_candidate(6, 6, A, B, quick=True)
        assert result["stage"] != "invalid"
        assert result["n"] == 72


class TestMultiTermCodes:
    """4-term and 5-term polynomials produce valid BBCodes."""

    def test_4term_construction(self):
        # A = x^3 + y + y^2 + x*y (4 terms)
        A = [(3, 0), (0, 1), (0, 2), (1, 1)]
        B = [(0, 3), (1, 0), (2, 0)]
        validate_terms(12, 6, A, "A")
        validate_terms(12, 6, B, "B")
        code = build_bb_code(12, 6, A, B)
        n, k = get_code_params_fast(code)
        assert n == 144

    def test_5term_construction(self):
        # A = 1 + x + y + x*y + x^2*y^2 (5 terms)
        A = [(0, 0), (1, 0), (0, 1), (1, 1), (2, 2)]
        B = [(0, 3), (1, 0), (2, 0)]
        validate_terms(12, 6, A, "A")
        validate_terms(12, 6, B, "B")
        code = build_bb_code(12, 6, A, B)
        n, k = get_code_params_fast(code)
        assert n == 144

    def test_4term_evaluator(self):
        # 4-term polynomial should pass evaluator
        A = [(3, 0), (0, 1), (0, 2), (1, 1)]
        B = [(0, 3), (1, 0), (2, 0)]
        result = evaluate_candidate(12, 6, A, B, quick=True)
        assert result["stage"] != "invalid"
        assert result["n"] == 144


class TestStructuralFeedback:
    """_structural_feedback generates meaningful output."""

    def setup_method(self):
        from evolve.openevolve_evaluator import _structural_feedback
        self.feedback = _structural_feedback

    def test_pure_code_feedback(self):
        result = {
            "A_terms": [(3, 0), (0, 1), (0, 2)],
            "B_terms": [(0, 3), (1, 0), (2, 0)],
        }
        fb = self.feedback(result)
        assert "pure-x" in fb
        assert "pure-y" in fb
        assert "Axis coupling: none" in fb

    def test_mixed_code_feedback(self):
        result = {
            "A_terms": [(0, 0), (1, 2), (3, 1)],
            "B_terms": [(0, 0), (2, 1), (1, 3)],
        }
        fb = self.feedback(result)
        assert "mixed" in fb
        assert "both A and B have mixed terms" in fb


class TestAnsatzSeed:
    """Test the ansatz seed solution produces valid codes."""

    def setup_method(self):
        from evolve.seed_solution_ansatz import generate_candidates, _safety_net_codes
        self.generate = generate_candidates
        self.safety_net = _safety_net_codes

    def test_generates_candidates_at_6_6(self):
        cands = self.generate(6, 6)
        assert isinstance(cands, list)
        assert len(cands) > 0

    def test_generates_candidates_at_12_6(self):
        cands = self.generate(12, 6)
        assert isinstance(cands, list)
        assert len(cands) > 0

    def test_safety_net_at_stage1_lattices(self):
        """Safety net produces codes at both stage 1 lattices."""
        for ell, m in [(6, 6), (12, 6)]:
            codes = self.safety_net(ell, m)
            assert len(codes) > 0, f"No safety net codes at ({ell},{m})"

    def test_safety_net_produces_k_gt_0(self):
        """Safety net codes have k > 0 at stage 1 lattices."""
        for ell, m in [(6, 6), (12, 6)]:
            codes = self.safety_net(ell, m)
            for A, B in codes:
                code = build_bb_code(ell, m, A, B)
                n, k = get_code_params_fast(code)
                assert k > 0, f"Safety net code has k=0 at ({ell},{m}): A={A}, B={B}"

    def test_seed_produces_k_gt_0_at_stage1(self):
        """Seed must produce at least one k > 0 code at both stage 1 lattices."""
        for ell, m in [(6, 6), (12, 6)]:
            cands = self.generate(ell, m)
            found_k_gt_0 = False
            for A, B in cands[:100]:  # check first 100 to be fast
                code = build_bb_code(ell, m, A, B)
                _, k = get_code_params_fast(code)
                if k > 0:
                    found_k_gt_0 = True
                    break
            assert found_k_gt_0, f"No k>0 code at ({ell},{m}) in first 100 candidates"

    def test_has_mixed_monomial_candidates(self):
        """Seed generates candidates with mixed monomials (both x,y > 0)."""
        cands = self.generate(6, 6)
        has_mixed = False
        for A, B in cands:
            for x, y in A + B:
                if x > 0 and y > 0:
                    has_mixed = True
                    break
            if has_mixed:
                break
        assert has_mixed, "No mixed-monomial candidates generated"

    def test_no_self_dual_in_candidates(self):
        """No candidate should have A = B (self-dual, always d=2)."""
        cands = self.generate(6, 6)
        for A, B in cands:
            assert sorted(map(tuple, A)) != sorted(map(tuple, B)), \
                f"Self-dual candidate: A=B={A}"

    def test_empty_lattice_produces_candidates(self):
        """Lattice not in REFERENCE_CODES still produces Strategy 1 candidates."""
        cands = self.generate(10, 10)
        assert len(cands) > 0

    def test_go_no_go_mixed_k_rate(self):
        """Go/no-go diagnostic: Strategy 1 mixed-monomial k > 0 rate.

        This is a diagnostic, not a hard assertion -- reports the rate.
        We need SOME mixed-monomial codes with k > 0 for the LLM to learn from.
        """
        total = 0
        k_gt_0 = 0
        for ell, m in [(6, 6), (12, 6)]:
            cands = self.generate(ell, m)
            for A, B in cands:
                # Check if this is a mixed-monomial candidate (not safety net)
                a_mixed = any(x > 0 and y > 0 for x, y in A)
                b_mixed = any(x > 0 and y > 0 for x, y in B)
                if a_mixed or b_mixed:
                    total += 1
                    code = build_bb_code(ell, m, A, B)
                    _, k = get_code_params_fast(code)
                    if k > 0:
                        k_gt_0 += 1
                    if total >= 200:  # sample 200 per lattice
                        break
        rate = k_gt_0 / total if total > 0 else 0
        print(f"\nGo/no-go diagnostic: {k_gt_0}/{total} mixed-monomial codes have k>0 "
              f"({rate:.1%})")
        # Soft assertion: we want > 0% but don't hard-fail the test
        # since k=0 for all mixed monomials is itself informative
        assert total > 0, "No mixed-monomial candidates to test"
