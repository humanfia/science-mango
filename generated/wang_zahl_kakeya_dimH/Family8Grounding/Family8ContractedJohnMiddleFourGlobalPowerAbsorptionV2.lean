import Family8Grounding.Family8ContractedJohnMiddleGlobalPowerAbsorptionV3
import Mathlib.Tactic

/-!
# Global power absorption including the same-assembly factor four, V2

V1 asked `change` to reassociate a non-definitional product.  This corrected successor explicitly proves that reassociation.  The strict middle factor contains the literal coefficient `4`.  This module
absorbs it together with the existing actual-volume coefficient instead of
leaving a separate final scalar callback.
-/

set_option autoImplicit false
set_option warningAsError true

open scoped ENNReal NNReal

namespace Family8ContractedJohnMiddleFourGlobalPowerAbsorptionV2

open Family8ContractedJohnMiddleActualVolumeEnvelopeV3
open Family8ContractedJohnMiddleGlobalPowerAbsorptionV3
open Family8ContractedJohnMiddleRelativeScaleEnvelopeV3
open FamilyStickyScaleChainSmallDeltaExponentBudgetProducerV1

noncomputable section

def contractedJohnMiddleFourActualPowerThreshold
    (K : ENNReal) (epsilon beta gamma lossExp absorbExp : Real) : NNReal :=
  finiteConstantSmallDeltaThreshold
    (4 * contractedJohnMiddleActualFixedCoefficient
      K epsilon beta gamma lossExp) absorbExp

theorem contractedJohnMiddleFourActualPowerThreshold_pos
    (K : ENNReal) (epsilon beta gamma lossExp absorbExp : Real) :
    0 < contractedJohnMiddleFourActualPowerThreshold
      K epsilon beta gamma lossExp absorbExp :=
  finiteConstantSmallDeltaThreshold_pos _ _

/-- The relative long-interval gain absorbs both the actual-volume constant
and the literal same-assembly factor `4`. -/
theorem four_mul_fixed_mul_ratioGain_le_globalTenEta
    {delta q : NNReal} {K : ENNReal}
    {stoppingEpsilon beta gamma lossExp kappa absorbExp eta : Real}
    (hdeltaOne : delta ≤ 1) (hq : 0 < q)
    (hK0 : K ≠ 0) (hKTop : K ≠ ∞)
    (habsorb : 0 < absorbExp)
    (hqSmall : q ≤ contractedJohnMiddleFourActualPowerThreshold
      K stoppingEpsilon beta gamma lossExp absorbExp)
    (hqDelta : (q : ENNReal) ≤
      (delta : ENNReal) ^ (stoppingEpsilon ^ 2))
    (hnet : 0 ≤
      contractedJohnMiddleRatioGain
        stoppingEpsilon beta gamma lossExp kappa - absorbExp)
    (hbudget : 10 * eta ≤
      stoppingEpsilon ^ 2 *
        (contractedJohnMiddleRatioGain
          stoppingEpsilon beta gamma lossExp kappa - absorbExp)) :
    4 *
        (contractedJohnMiddleActualFixedCoefficient
            K stoppingEpsilon beta gamma lossExp *
          (q : ENNReal) ^
            contractedJohnMiddleRatioGain
              stoppingEpsilon beta gamma lossExp kappa) ≤
      (delta : ENNReal) ^ (10 * eta) := by
  let coefficient : ENNReal :=
    4 * contractedJohnMiddleActualFixedCoefficient
      K stoppingEpsilon beta gamma lossExp
  let gain := contractedJohnMiddleRatioGain
    stoppingEpsilon beta gamma lossExp kappa
  have hcoefficientTop : coefficient ≠ ∞ := by
    dsimp only [coefficient]
    exact ENNReal.mul_ne_top (by norm_num)
      (contractedJohnMiddleActualFixedCoefficient_ne_top
        hK0 hKTop stoppingEpsilon beta gamma lossExp)
  have hcoefficient : coefficient ≤ (q : ENNReal) ^ (-absorbExp) :=
    finiteConstant_le_delta_negativePower
      hcoefficientTop habsorb hq hqSmall
  have hq0 : (q : ENNReal) ≠ 0 := ENNReal.coe_ne_zero.mpr hq.ne'
  have hqTop : (q : ENNReal) ≠ ∞ := ENNReal.coe_ne_top
  have hdeltaOneENN : (delta : ENNReal) ≤ 1 := by
    exact_mod_cast hdeltaOne
  have hqCombined :
      (q : ENNReal) ^ (-absorbExp) * (q : ENNReal) ^ gain =
        (q : ENNReal) ^ (gain - absorbExp) := by
    rw [← ENNReal.rpow_add (-absorbExp) gain hq0 hqTop]
    congr 1
    ring
  have hratioPower :
      (q : ENNReal) ^ (gain - absorbExp) ≤
        (delta : ENNReal) ^
          (stoppingEpsilon ^ 2 * (gain - absorbExp)) := by
    calc
      (q : ENNReal) ^ (gain - absorbExp) ≤
          ((delta : ENNReal) ^ (stoppingEpsilon ^ 2)) ^
            (gain - absorbExp) :=
        ENNReal.rpow_le_rpow hqDelta (by simpa only [gain] using hnet)
      _ = (delta : ENNReal) ^
          (stoppingEpsilon ^ 2 * (gain - absorbExp)) := by
        rw [← ENNReal.rpow_mul]
  have hglobal :
      (delta : ENNReal) ^
          (stoppingEpsilon ^ 2 * (gain - absorbExp)) ≤
        (delta : ENNReal) ^ (10 * eta) := by
    apply ENNReal.rpow_le_rpow_of_exponent_ge hdeltaOneENN
    simpa only [gain] using hbudget
  calc
    4 *
        (contractedJohnMiddleActualFixedCoefficient
            K stoppingEpsilon beta gamma lossExp *
          (q : ENNReal) ^
            contractedJohnMiddleRatioGain
              stoppingEpsilon beta gamma lossExp kappa) =
        coefficient * (q : ENNReal) ^ gain := by
      dsimp only [coefficient, gain]
      ac_rfl
    _ ≤ (q : ENNReal) ^ (-absorbExp) * (q : ENNReal) ^ gain :=
      mul_le_mul' hcoefficient le_rfl
    _ = (q : ENNReal) ^ (gain - absorbExp) := hqCombined
    _ ≤ (delta : ENNReal) ^
        (stoppingEpsilon ^ 2 * (gain - absorbExp)) := hratioPower
    _ ≤ (delta : ENNReal) ^ (10 * eta) := hglobal

#print axioms contractedJohnMiddleFourActualPowerThreshold
#print axioms contractedJohnMiddleFourActualPowerThreshold_pos
#print axioms four_mul_fixed_mul_ratioGain_le_globalTenEta

end
end Family8ContractedJohnMiddleFourGlobalPowerAbsorptionV2
