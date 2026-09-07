import Family8Grounding.Family8ContractedJohnMiddleActualVolumeEnvelopeV3
import FamilyStickyGrounding.FamilyStickyScaleChainSmallDeltaExponentBudgetProducerV1
import Mathlib.Tactic

/-!
# Global power absorption for the contracted-John middle factor, V3

V1 had an unused premise and V2 did not expose finiteness of the literal
`3/64` coefficient; neither is imported.  This successor converts the
relative long-interval gain into the requested global power.
-/

set_option autoImplicit false
set_option warningAsError true

open scoped ENNReal NNReal

namespace Family8ContractedJohnMiddleGlobalPowerAbsorptionV3

open Family8ContractedJohnMiddleActualVolumeEnvelopeV3
open Family8ContractedJohnMiddleRelativeScaleEnvelopeV3
open FamilyStickyScaleChainSmallDeltaExponentBudgetProducerV1

noncomputable section

def contractedJohnMiddleActualPowerThreshold
    (K : ENNReal) (epsilon beta gamma lossExp absorbExp : Real) : NNReal :=
  finiteConstantSmallDeltaThreshold
    (contractedJohnMiddleActualFixedCoefficient
      K epsilon beta gamma lossExp) absorbExp

theorem contractedJohnMiddleActualPowerThreshold_pos
    (K : ENNReal) (epsilon beta gamma lossExp absorbExp : Real) :
    0 < contractedJohnMiddleActualPowerThreshold
      K epsilon beta gamma lossExp absorbExp :=
  finiteConstantSmallDeltaThreshold_pos _ _

theorem contractedJohnMiddleActualFixedCoefficient_ne_top
    {K : ENNReal} (hK0 : K ≠ 0) (hKTop : K ≠ ∞)
    (epsilon beta gamma lossExp : Real) :
    contractedJohnMiddleActualFixedCoefficient
      K epsilon beta gamma lossExp ≠ ∞ := by
  have hc0 : (3 / 64 : ENNReal) ≠ 0 := by norm_num
  have hcTop : (3 / 64 : ENNReal) ≠ ∞ := by
    exact ENNReal.div_ne_top (by norm_num) (by norm_num)
  unfold contractedJohnMiddleActualFixedCoefficient
    contractedJohnMiddleFixedCoefficient
  apply ENNReal.mul_ne_top
  · exact ENNReal.rpow_ne_top_of_ne_zero (by norm_num) (by norm_num)
  apply ENNReal.mul_ne_top
  · exact ENNReal.rpow_ne_top_of_ne_zero hK0 hKTop
  · exact ENNReal.rpow_ne_top_of_ne_zero hc0 hcTop

theorem fixed_mul_ratioGain_le_globalTenEta
    {delta q : NNReal} {K : ENNReal}
    {stoppingEpsilon beta gamma lossExp kappa absorbExp eta : Real}
    (hdeltaOne : delta <= 1) (hq : 0 < q)
    (hK0 : K ≠ 0) (hKTop : K ≠ ∞)
    (habsorb : 0 < absorbExp)
    (hqSmall : q <= contractedJohnMiddleActualPowerThreshold
      K stoppingEpsilon beta gamma lossExp absorbExp)
    (hqDelta : (q : ENNReal) <=
      (delta : ENNReal) ^ (stoppingEpsilon ^ 2))
    (hnet : 0 <=
      contractedJohnMiddleRatioGain
        stoppingEpsilon beta gamma lossExp kappa - absorbExp)
    (hbudget : 10 * eta <=
      stoppingEpsilon ^ 2 *
        (contractedJohnMiddleRatioGain
          stoppingEpsilon beta gamma lossExp kappa - absorbExp)) :
    contractedJohnMiddleActualFixedCoefficient
        K stoppingEpsilon beta gamma lossExp *
      (q : ENNReal) ^
        contractedJohnMiddleRatioGain
          stoppingEpsilon beta gamma lossExp kappa <=
      (delta : ENNReal) ^ (10 * eta) := by
  let coefficient := contractedJohnMiddleActualFixedCoefficient
    K stoppingEpsilon beta gamma lossExp
  let gain := contractedJohnMiddleRatioGain
    stoppingEpsilon beta gamma lossExp kappa
  have hcoefficient : coefficient <=
      (q : ENNReal) ^ (-absorbExp) := by
    exact finiteConstant_le_delta_negativePower
      (contractedJohnMiddleActualFixedCoefficient_ne_top
        hK0 hKTop stoppingEpsilon beta gamma lossExp)
      habsorb hq hqSmall
  have hq0 : (q : ENNReal) ≠ 0 := ENNReal.coe_ne_zero.mpr hq.ne'
  have hqTop : (q : ENNReal) ≠ ∞ := ENNReal.coe_ne_top
  have hdeltaOneENN : (delta : ENNReal) <= 1 := by
    exact_mod_cast hdeltaOne
  have hqCombined :
      (q : ENNReal) ^ (-absorbExp) * (q : ENNReal) ^ gain =
        (q : ENNReal) ^ (gain - absorbExp) := by
    rw [← ENNReal.rpow_add (-absorbExp) gain hq0 hqTop]
    congr 1
    ring
  have hratioPower :
      (q : ENNReal) ^ (gain - absorbExp) <=
        (delta : ENNReal) ^
          (stoppingEpsilon ^ 2 * (gain - absorbExp)) := by
    calc
      (q : ENNReal) ^ (gain - absorbExp) <=
          ((delta : ENNReal) ^ (stoppingEpsilon ^ 2)) ^
            (gain - absorbExp) :=
        ENNReal.rpow_le_rpow hqDelta (by simpa only [gain] using hnet)
      _ = (delta : ENNReal) ^
          (stoppingEpsilon ^ 2 * (gain - absorbExp)) := by
        rw [← ENNReal.rpow_mul]
  have hglobal :
      (delta : ENNReal) ^
          (stoppingEpsilon ^ 2 * (gain - absorbExp)) <=
        (delta : ENNReal) ^ (10 * eta) := by
    apply ENNReal.rpow_le_rpow_of_exponent_ge hdeltaOneENN
    simpa only [gain] using hbudget
  calc
    coefficient * (q : ENNReal) ^ gain <=
        (q : ENNReal) ^ (-absorbExp) * (q : ENNReal) ^ gain :=
      mul_le_mul' hcoefficient le_rfl
    _ = (q : ENNReal) ^ (gain - absorbExp) := hqCombined
    _ <= (delta : ENNReal) ^
        (stoppingEpsilon ^ 2 * (gain - absorbExp)) := hratioPower
    _ <= (delta : ENNReal) ^ (10 * eta) := hglobal

#print axioms contractedJohnMiddleActualPowerThreshold
#print axioms contractedJohnMiddleActualPowerThreshold_pos
#print axioms contractedJohnMiddleActualFixedCoefficient_ne_top
#print axioms fixed_mul_ratioGain_le_globalTenEta

end
end Family8ContractedJohnMiddleGlobalPowerAbsorptionV3
