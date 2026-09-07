import Mathlib.Tactic

/-!
# Pure scalar absorption for the FirstCrossing middle factor, V2

This ADD-only clean successor uses Lean's native inequality notation.  The
geometric middle consumer naturally splits its final coefficient into an
outer loss, a fixed proxy coefficient, and a relative-scale power.  The
theorem below combines independent source-delta power bounds for those three
factors and is independent of every geometric certificate or selection.
-/

set_option autoImplicit false
set_option warningAsError true

open scoped ENNReal NNReal

namespace Family8FirstCrossingMiddleScalarAbsorptionV2

noncomputable section

/-- Three source-delta power bounds and the numerical exponent budget imply
the exact absorption shape required by the FirstCrossing strict-middle
consumer. -/
theorem outer_mul_coefficient_mul_ratio_le_globalTenEta
    {delta : NNReal} {outer coefficient ratio : ENNReal}
    {aOuter aCoefficient aRatio eta : Real}
    (hdelta : 0 < delta) (hdeltaOne : delta ≤ 1)
    (hOuter : outer ≤ (delta : ENNReal) ^ aOuter)
    (hCoefficient : coefficient ≤
      (delta : ENNReal) ^ (-aCoefficient))
    (hRatio : ratio ≤ (delta : ENNReal) ^ aRatio)
    (hExponentBudget :
      10 * eta ≤ aOuter - aCoefficient + aRatio) :
    outer * (coefficient * ratio) ≤
      (delta : ENNReal) ^ (10 * eta) := by
  have hdelta0 : (delta : ENNReal) ≠ 0 :=
    ENNReal.coe_ne_zero.mpr hdelta.ne'
  have hdeltaTop : (delta : ENNReal) ≠ ∞ := ENNReal.coe_ne_top
  have hdeltaOneENN : (delta : ENNReal) ≤ 1 := by
    exact_mod_cast hdeltaOne
  calc
    outer * (coefficient * ratio) ≤
        (delta : ENNReal) ^ aOuter *
          ((delta : ENNReal) ^ (-aCoefficient) *
            (delta : ENNReal) ^ aRatio) :=
      mul_le_mul' hOuter (mul_le_mul' hCoefficient hRatio)
    _ = ((delta : ENNReal) ^ aOuter *
          (delta : ENNReal) ^ (-aCoefficient)) *
        (delta : ENNReal) ^ aRatio := by
      ac_rfl
    _ = (delta : ENNReal) ^ (aOuter + (-aCoefficient)) *
        (delta : ENNReal) ^ aRatio := by
      rw [ENNReal.rpow_add aOuter (-aCoefficient) hdelta0 hdeltaTop]
    _ = (delta : ENNReal) ^
        ((aOuter + (-aCoefficient)) + aRatio) := by
      rw [ENNReal.rpow_add
        (aOuter + (-aCoefficient)) aRatio hdelta0 hdeltaTop]
    _ = (delta : ENNReal) ^
        (aOuter - aCoefficient + aRatio) := by
      congr 1
    _ ≤ (delta : ENNReal) ^ (10 * eta) := by
      exact ENNReal.rpow_le_rpow_of_exponent_ge
        hdeltaOneENN hExponentBudget

#print axioms outer_mul_coefficient_mul_ratio_le_globalTenEta

end
end Family8FirstCrossingMiddleScalarAbsorptionV2
