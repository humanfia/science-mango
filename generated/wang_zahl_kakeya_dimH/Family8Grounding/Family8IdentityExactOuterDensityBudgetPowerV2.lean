import Mathlib.Tactic

/-!
# Identity exact-outer density-budget power algebra, V2

This clean successor fixes the unavailable namespaced nonzero API in V1.
The statement and scalar argument are otherwise unchanged.
-/

set_option autoImplicit false
set_option warningAsError true

open scoped ENNReal

namespace Family8IdentityExactOuterDensityBudgetPowerV2

/-- Replacing the actual finite assembly loss by a power upper bound and the
actual density square by a source power lower bound is monotone in the
required direction. -/
theorem target_le_density_div_actualLoss_mul_768
    {target actualLoss lossUpper densityFloor density : ENNReal}
    (hactual0 : actualLoss ≠ 0)
    (hactualTop : actualLoss ≠ ∞)
    (hactual : actualLoss ≤ lossUpper)
    (hdensity : densityFloor ≤ density)
    (hpower : target * (lossUpper * 768) ≤ densityFloor) :
    target ≤ density / (actualLoss * 768) := by
  have hden0 : actualLoss * 768 ≠ 0 :=
    mul_ne_zero hactual0 (by norm_num)
  have hdenTop : actualLoss * 768 ≠ ∞ :=
    ENNReal.mul_ne_top hactualTop (by norm_num)
  apply (ENNReal.le_div_iff_mul_le
    (Or.inl hden0) (Or.inl hdenTop)).2
  calc
    target * (actualLoss * 768) ≤
        target * (lossUpper * 768) := by
      gcongr
    _ ≤ densityFloor := hpower
    _ ≤ density := hdensity

#print axioms target_le_density_div_actualLoss_mul_768

end Family8IdentityExactOuterDensityBudgetPowerV2
