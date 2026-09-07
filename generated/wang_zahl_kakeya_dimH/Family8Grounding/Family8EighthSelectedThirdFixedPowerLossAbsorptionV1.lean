import Family8Grounding.Family8EighthSelectedThirdFactorLossAbsorptionV2
import Mathlib.Tactic

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 3000000

open scoped ENNReal NNReal

namespace Family8EighthSelectedThirdFixedPowerLossAbsorptionV1

open Family8ThreeScaleFrostmanFactorAlgebraV2
open Family8EighthNormalizedSelectedFrostmanThirdFactorV3
open Family8EighthSelectedThirdFactorLossAbsorptionV2
open FamilyStickyScaleChainSmallDeltaExponentBudgetProducerV1

noncomputable section

/-!
# Uniform power absorption of the canonical third-factor loss

The conflict loss varies with the input family and therefore cannot occur
inside a datum-dependent small-scale threshold in a uniform property.  This
module separates it from the fixed eighth-normalization constant.  A genuine
power cap on the conflict loss is then combined with one fixed threshold that
depends only on the exponents.

The failed V1 and V2 drafts are intentionally not imported here.
-/

/-- The finite normalization cost after removing both the variable conflict
loss and the intermediate-radius power. -/
def eighthSelectedThirdNormalizationLoss
    (epsilon gamma : Real) : ENNReal :=
  (((8 : ENNReal) ^ epsilon) *
      (8 : ENNReal) ^ (1 - gamma / 2)) *
    sectionEightScaleCountFrostmanFactor (1 / 8) 1 1 gamma

/-- The fixed loss factors as the variable conflict loss times a normalization
constant independent of the datum. -/
theorem eighthSelectedThirdFixedLoss_eq_loss_mul_normalization
    (loss : ENNReal) (epsilon gamma : Real) :
    eighthSelectedThirdFixedLoss loss epsilon gamma =
      loss * eighthSelectedThirdNormalizationLoss epsilon gamma := by
  unfold eighthSelectedThirdFixedLoss eighthSelectedThirdNormalizationLoss
  ac_rfl

theorem eighthSelectedThirdNormalizationLoss_ne_top
    (epsilon gamma : Real) :
    eighthSelectedThirdNormalizationLoss epsilon gamma ≠ ∞ := by
  unfold eighthSelectedThirdNormalizationLoss
  apply ENNReal.mul_ne_top
  · exact ENNReal.mul_ne_top
      (ENNReal.rpow_ne_top_of_ne_zero (by norm_num) (by norm_num))
      (ENNReal.rpow_ne_top_of_ne_zero (by norm_num) (by norm_num))
  · unfold sectionEightScaleCountFrostmanFactor
    apply ENNReal.mul_ne_top
    · exact ENNReal.rpow_ne_top_of_ne_zero (by norm_num) (by norm_num)
    · exact ENNReal.rpow_ne_top_of_ne_zero (by norm_num) (by norm_num)

/-- A power-sized conflict loss and the fixed eighth-normalization constant
give a uniform source-scale power bound.  Unlike the fixed-loss endpoint, the
small-scale threshold is independent of `loss`, hence independent of the input
family and its cardinality. -/
theorem eighthSelectedThirdFactorLoss_le_delta_negativePower_of_lossPower
    {delta rho : NNReal} {loss : ENNReal}
    {epsilon gamma lossExponent absorbExponent : Real}
    (hdelta : 0 < delta) (hrho : 0 < rho)
    (hdeltaRho : delta ≤ rho) (hepsilon : 0 ≤ epsilon)
    (hloss : loss ≤ (delta : ENNReal) ^ (-lossExponent))
    (habsorb : 0 < absorbExponent)
    (hsmall : delta ≤ finiteConstantSmallDeltaThreshold
      (eighthSelectedThirdNormalizationLoss epsilon gamma) absorbExponent) :
    eighthSelectedThirdFactorLoss rho loss epsilon gamma ≤
      (delta : ENNReal) ^
        (-(lossExponent + epsilon + absorbExponent)) := by
  have hnormalization :
      eighthSelectedThirdNormalizationLoss epsilon gamma ≤
        (delta : ENNReal) ^ (-absorbExponent) :=
    finiteConstant_le_delta_negativePower
      (eighthSelectedThirdNormalizationLoss_ne_top epsilon gamma)
      habsorb hdelta hsmall
  have hthird :=
    eighthSelectedThirdFactorLoss_le_fixed_mul_delta_rpow
      (loss := loss) (epsilon := epsilon) (gamma := gamma)
      hdelta hrho hdeltaRho hepsilon
  rw [eighthSelectedThirdFixedLoss_eq_loss_mul_normalization] at hthird
  have hd0 : (delta : ENNReal) ≠ 0 :=
    ENNReal.coe_ne_zero.mpr hdelta.ne'
  have hdTop : (delta : ENNReal) ≠ ∞ := ENNReal.coe_ne_top
  calc
    eighthSelectedThirdFactorLoss rho loss epsilon gamma ≤
        (loss * eighthSelectedThirdNormalizationLoss epsilon gamma) *
          (delta : ENNReal) ^ (-epsilon) := hthird
    _ ≤ (((delta : ENNReal) ^ (-lossExponent)) *
          ((delta : ENNReal) ^ (-absorbExponent))) *
          (delta : ENNReal) ^ (-epsilon) := by
      exact mul_le_mul'
        (mul_le_mul' hloss hnormalization) le_rfl
    _ = (delta : ENNReal) ^
          (-(lossExponent + epsilon + absorbExponent)) := by
      rw [← ENNReal.rpow_add _ _ hd0 hdTop,
        ← ENNReal.rpow_add _ _ hd0 hdTop]
      congr 1
      ring

/-- A power-sized variable loss and the finite normalization constant bound the fixed loss, with no intermediate-radius epsilon charged to the exponent. -/
theorem eighthSelectedThirdFixedLoss_le_delta_negativePower_of_lossPower
    {delta : NNReal} {loss : ENNReal}
    {epsilon gamma lossExponent absorbExponent : Real}
    (hdelta : 0 < delta)
    (hloss : loss ≤ (delta : ENNReal) ^ (-lossExponent))
    (habsorb : 0 < absorbExponent)
    (hsmall : delta ≤ finiteConstantSmallDeltaThreshold
      (eighthSelectedThirdNormalizationLoss epsilon gamma) absorbExponent) :
    eighthSelectedThirdFixedLoss loss epsilon gamma ≤
      (delta : ENNReal) ^ (-(lossExponent + absorbExponent)) := by
  have hnormalization :
      eighthSelectedThirdNormalizationLoss epsilon gamma ≤
        (delta : ENNReal) ^ (-absorbExponent) :=
    finiteConstant_le_delta_negativePower
      (eighthSelectedThirdNormalizationLoss_ne_top epsilon gamma)
      habsorb hdelta hsmall
  have hd0 : (delta : ENNReal) ≠ 0 :=
    ENNReal.coe_ne_zero.mpr (ne_of_gt hdelta)
  have hdTop : (delta : ENNReal) ≠ ∞ := ENNReal.coe_ne_top
  rw [eighthSelectedThirdFixedLoss_eq_loss_mul_normalization]
  calc
    loss * eighthSelectedThirdNormalizationLoss epsilon gamma ≤
        (delta : ENNReal) ^ (-lossExponent) *
          (delta : ENNReal) ^ (-absorbExponent) :=
      mul_le_mul' hloss hnormalization
    _ = (delta : ENNReal) ^ (-(lossExponent + absorbExponent)) := by
      rw [← ENNReal.rpow_add _ _ hd0 hdTop]
      congr 1
      ring

#print axioms eighthSelectedThirdFixedLoss_le_delta_negativePower_of_lossPower
#print axioms eighthSelectedThirdNormalizationLoss
#print axioms eighthSelectedThirdFixedLoss_eq_loss_mul_normalization
#print axioms eighthSelectedThirdNormalizationLoss_ne_top
#print axioms
  eighthSelectedThirdFactorLoss_le_delta_negativePower_of_lossPower

end
end Family8EighthSelectedThirdFixedPowerLossAbsorptionV1
