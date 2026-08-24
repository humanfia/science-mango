import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Tactic

set_option autoImplicit false

namespace FamilyStickyCinematicL32PyzDyadicNegativeRpowComparisonV1

/-!
# A dyadic half-bin comparison for negative real powers

This is the exact scale arithmetic behind the first- and second-stage PYZ
dyadic selections.  It keeps the factor `2 ^ exponent` visible for the final
small-parameter absorption.
-/

theorem rpow_neg_le_two_rpow_mul_of_half_lt
    {selected upper exponent : Real}
    (hupper : 0 < upper) (hexponent : 0 ≤ exponent)
    (hbin : upper / 2 < selected) :
    selected ^ (-exponent) ≤
      2 ^ exponent * upper ^ (-exponent) := by
  calc
    selected ^ (-exponent) ≤ (upper / 2) ^ (-exponent) := by
      exact Real.rpow_le_rpow_of_nonpos (div_pos hupper (by norm_num))
        hbin.le (neg_nonpos.mpr hexponent)
    _ = upper ^ (-exponent) / 2 ^ (-exponent) := by
      rw [Real.div_rpow hupper.le (by norm_num)]
    _ = 2 ^ exponent * upper ^ (-exponent) := by
      rw [Real.rpow_neg (by norm_num : (0 : Real) ≤ 2)]
      simp only [div_eq_mul_inv, inv_inv]
      ac_rfl

#print axioms rpow_neg_le_two_rpow_mul_of_half_lt

end FamilyStickyCinematicL32PyzDyadicNegativeRpowComparisonV1
