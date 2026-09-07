import Family8Grounding.Family8WeightedCanonicalCriticalScaleDominatesV1
import Mathlib.Tactic

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 1200000

open scoped BigOperators ENNReal

namespace Family8WeightedCanonicalBallMassRatioV1

open Family8Family7NativeHighWeightedCriticalBallV1
open Family8WeightedCanonicalCriticalScaleDominatesV1

noncomputable section

universe u

/-- Ratio-form weighted nonconcentration for the literal critical ball. -/
theorem weightedBallMass_le_ratio_rpow_mul_criticalBallMass
    {alpha : Type u} (D : WeightedCanonicalNormBallData alpha)
    {radius : Real} (hradiusLower : D.delta ≤ radius)
    (hradiusUpper : radius ≤ D.ceiling)
    (testCenter : alpha) (htestCenter : testCenter ∈ D.family) :
    finiteWeightedBallMass D.family D.distance D.weight radius testCenter ≤
      ((ENNReal.ofReal radius) /
          (ENNReal.ofReal D.criticalScale)) ^ D.exponent *
        ∑ i ∈ D.criticalBall, D.weight i := by
  have hradiusPos : 0 < radius := D.delta_pos.trans_le hradiusLower
  have hcriticalPos : 0 < D.criticalScale :=
    D.delta_pos.trans_le D.criticalScale_bounds.1
  have hweighted := weightedCriticalMaximizer_dominates_on_Icc D
    hradiusLower hradiusUpper testCenter htestCenter
  rw [finiteWeightedTwoEndsScore,
    finiteWeightedTwoEndsScore,
    D.finiteWeightedBallMass_criticalScale] at hweighted
  let R : ENNReal := ENNReal.ofReal radius
  let T : ENNReal := ENNReal.ofReal D.criticalScale
  have hR0 : R ≠ 0 := ne_of_gt (ENNReal.ofReal_pos.mpr hradiusPos)
  have hRTop : R ≠ ∞ := ENNReal.ofReal_ne_top
  have hT0 : T ≠ 0 := ne_of_gt (ENNReal.ofReal_pos.mpr hcriticalPos)
  have hTTop : T ≠ ∞ := ENNReal.ofReal_ne_top
  calc
    finiteWeightedBallMass D.family D.distance D.weight radius testCenter =
        (finiteWeightedBallMass D.family D.distance D.weight radius
          testCenter * R ^ (-D.exponent)) * R ^ D.exponent := by
      rw [mul_assoc, ← ENNReal.rpow_add _ _ hR0 hRTop]
      simp [R]
    _ ≤ ((∑ i ∈ D.criticalBall, D.weight i) * T ^ (-D.exponent)) *
          R ^ D.exponent := by
      exact mul_le_mul' (by simpa only [R, T] using hweighted) le_rfl
    _ = (R / T) ^ D.exponent *
          ∑ i ∈ D.criticalBall, D.weight i := by
      rw [ENNReal.div_rpow_of_nonneg R T D.exponent_nonneg,
        div_eq_mul_inv, ENNReal.rpow_neg]
      ac_rfl

end

end Family8WeightedCanonicalBallMassRatioV1
