import Mathlib.Data.ENNReal.Real
import Mathlib.Tactic

set_option autoImplicit false

open scoped ENNReal

namespace FamilyStickyCinematicL32PyzWeightedThreeHalfAbsorptionV1

/-!
# Denominator-free three-halves absorption

If a weighted source multiplicity is at most a loss factor times a retained
multiplicity, its three-halves power combines monotonically with any retained
moment bound. This is the algebraic form needed to transport the exact
two-stage cardinality inequality into the low-multiplicity E2 estimate.
-/

theorem weighted_threeHalf_absorption
    {a b d E M : ENNReal}
    (hab : a ≤ b * d)
    (hmoment : d ^ (3 / 2 : Real) * E ≤ M) :
    a ^ (3 / 2 : Real) * E ≤ b ^ (3 / 2 : Real) * M := by
  calc
    a ^ (3 / 2 : Real) * E ≤ (b * d) ^ (3 / 2 : Real) * E := by
      gcongr
    _ = b ^ (3 / 2 : Real) * (d ^ (3 / 2 : Real) * E) := by
      rw [ENNReal.mul_rpow_of_nonneg _ _ (by norm_num : (0 : Real) ≤ 3 / 2)]
      ac_rfl
    _ ≤ b ^ (3 / 2 : Real) * M := by gcongr

end FamilyStickyCinematicL32PyzWeightedThreeHalfAbsorptionV1
