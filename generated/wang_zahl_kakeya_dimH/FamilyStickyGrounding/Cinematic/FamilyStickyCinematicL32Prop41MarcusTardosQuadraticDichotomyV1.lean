import Mathlib

set_option autoImplicit false

namespace FamilyStickyCinematicL32Prop41MarcusTardosQuadraticDichotomyV1

/-!
# Constant-explicit quadratic dichotomy in Marcus--Tardos Theorem 1

After Lemmas 3--5, the paper reaches one quadratic inequality.  The next
line splits it into two alternatives with the constant `8`.  This module
formalizes only that algebraic step; none of the combinatorial estimates is
assumed as a final theorem premise.
-/

/-- The exact constant-8 alternative on page 7 of Marcus--Tardos. -/
theorem quadratic_dichotomy_eight
    {p m d weightSum weightedDepth reciprocalSum : Real}
    (hp : 0 ≤ p) (hm : 0 < m)
    (hreciprocal : 0 < reciprocalSum)
    (hmain : -m * d ^ 2 * weightedDepth ≤
      p * weightSum - p ^ 2 /
        (4 * m ^ 2 * reciprocalSum)) :
    p ≤ 8 * m ^ 2 * weightSum * reciprocalSum ∨
      p ^ 2 ≤
        8 * d ^ 2 * m ^ 3 * weightedDepth * reciprocalSum := by
  have hden : 0 < 4 * m ^ 2 * reciprocalSum := by positivity
  have hcleared : p ^ 2 ≤
      (4 * m ^ 2 * reciprocalSum) *
        (p * weightSum + m * d ^ 2 * weightedDepth) := by
    have hdiv : p ^ 2 / (4 * m ^ 2 * reciprocalSum) ≤
        p * weightSum + m * d ^ 2 * weightedDepth := by
      linarith
    have hmul := (div_le_iff₀ hden).mp hdiv
    nlinarith
  by_cases hfirst : p ≤ 8 * m ^ 2 * weightSum * reciprocalSum
  · exact Or.inl hfirst
  · right
    have hpLarge : 8 * m ^ 2 * weightSum * reciprocalSum < p :=
      lt_of_not_ge hfirst
    nlinarith

#print axioms quadratic_dichotomy_eight

end FamilyStickyCinematicL32Prop41MarcusTardosQuadraticDichotomyV1
