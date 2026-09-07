import Mathlib.Tactic

/-!
# The same-assembly middle/third product cannot be projected to a middle bound

The contracted-John endpoint bounds a retained average by a fixed factor
times `frozenCoarseAverage * middleFactor`.  Positivity of the retained
average does not remove the frozen-coarse factor.  This file records both
the exact valid regrouping and a scalar counterexample to the invalid
standalone-middle inference.
-/

set_option autoImplicit false
set_option warningAsError true

open scoped ENNReal

namespace Family8SameAssemblyMiddleThirdProjectionNoGoV1

/-- The honest consequence keeps the fixed factor and the same-assembly
third average together. -/
theorem le_combinedThird_mul_middle
    {retained frozenCoarse middle : ENNReal}
    (h : retained <= 4 * (frozenCoarse * middle)) :
    retained <= (4 * frozenCoarse) * middle := by
  simpa only [mul_assoc] using h

/-- If a later producer controls the exact same frozen-coarse factor, the
bound can be transported with that explicit loss. -/
theorem le_thirdLoss_mul_middle
    {retained frozenCoarse middle thirdLoss : ENNReal}
    (h : retained <= 4 * (frozenCoarse * middle))
    (hthird : 4 * frozenCoarse <= thirdLoss) :
    retained <= thirdLoss * middle := by
  exact (le_combinedThird_mul_middle h).trans
    (mul_le_mul' hthird le_rfl)

/-- Even adding `1 <= retained` does not imply the standalone middle bound;
the missing upper control on the same frozen-coarse factor is logical, not
an elaboration artifact. -/
theorem not_standaloneMiddle_of_positive_and_product :
    ¬ (forall retained frozenCoarse middle : ENNReal,
      1 <= retained ->
      retained <= 4 * (frozenCoarse * middle) ->
      retained <= middle) := by
  intro h
  have hfalse := h 2 2 1 (by norm_num) (by norm_num)
  norm_num at hfalse

#print axioms le_combinedThird_mul_middle
#print axioms le_thirdLoss_mul_middle
#print axioms not_standaloneMiddle_of_positive_and_product

end Family8SameAssemblyMiddleThirdProjectionNoGoV1
