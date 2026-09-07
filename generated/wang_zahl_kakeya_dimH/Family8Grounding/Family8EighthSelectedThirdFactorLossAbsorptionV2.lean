import Family8Grounding.Family8EighthNormalizedSelectedFrostmanThirdFactorV3
import FamilyStickyGrounding.FamilyStickyScaleChainSmallDeltaExponentBudgetProducerV1
import Family8Grounding.Family8FrostmanRHSScaleVolumeAlgebraV3
import Mathlib.Tactic

open scoped ENNReal NNReal

namespace Family8EighthSelectedThirdFactorLossAbsorptionV2

open Family8ThreeScaleFrostmanFactorAlgebraV2
open Family8EighthNormalizedSelectedFrostmanThirdFactorV3
open Family8FrostmanRHSScaleVolumeAlgebraV3
open FamilyStickyScaleChainSmallDeltaExponentBudgetProducerV1

noncomputable section

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 3000000

/-!
# Small-scale absorption of the canonical third-factor loss

After the actual B2/Frostman estimate is converted to the official third
factor, its only scale-dependent loss is `rho ^ (-epsilon)`.  The apparent
factor from `rho / 8` to `rho` is a fixed ratio.  This module makes that fact
literal and absorbs every remaining uniformly finite constant below an
explicit source-scale threshold.

V1 was an ENNReal normalization draft and is intentionally not imported.
-/

/-- The part of the eighth-normalization loss that is independent of the
intermediate radius. -/
def eighthSelectedThirdFixedLoss
    (loss : ENNReal) (epsilon gamma : Real) : ENNReal :=
  ((loss * (8 : ENNReal) ^ epsilon) *
      (8 : ENNReal) ^ (1 - gamma / 2)) *
    sectionEightScaleCountFrostmanFactor (1 / 8) 1 1 gamma

/-- The scale-count factor across the fixed ratio `(rho / 8) / rho` is
independent of the positive radius `rho`. -/
theorem eighth_ratio_scaleCountFactor_eq_constant
    (rho : NNReal) (gamma : Real) (hrho : 0 < rho) :
    sectionEightScaleCountFrostmanFactor (rho / 8) rho 1 gamma =
      sectionEightScaleCountFrostmanFactor (1 / 8) 1 1 gamma := by
  have hrhoENN0 : (rho : ENNReal) ≠ 0 :=
    ENNReal.coe_ne_zero.mpr hrho.ne'
  have hrhoENNTop : (rho : ENNReal) ≠ ∞ := ENNReal.coe_ne_top
  have hratio :
      (((rho / 8 : NNReal) : ENNReal) / (rho : ENNReal)) =
        (((1 / 8 : NNReal) : ENNReal) / (1 : ENNReal)) := by
    rw [ENNReal.coe_div (by norm_num : (8 : NNReal) ≠ 0)]
    rw [div_eq_mul_inv, div_eq_mul_inv]
    have hcancel : (rho : ENNReal) * (rho : ENNReal)⁻¹ = 1 :=
      ENNReal.mul_inv_cancel hrhoENN0 hrhoENNTop
    calc
      (rho : ENNReal) * (8 : ENNReal)⁻¹ * (rho : ENNReal)⁻¹ =
          ((rho : ENNReal) * (rho : ENNReal)⁻¹) *
            (8 : ENNReal)⁻¹ := by ac_rfl
      _ = (8 : ENNReal)⁻¹ := by rw [hcancel, one_mul]
      _ = (((1 / 8 : NNReal) : ENNReal) / (1 : ENNReal)) := by norm_num
  unfold sectionEightScaleCountFrostmanFactor
  rw [hratio]
  norm_num

/-- Exact separation of the radius-dependent negative epsilon power from
the fixed eighth-normalization loss. -/
theorem eighthSelectedThirdFactorLoss_eq_fixed_mul_rpow
    (rho : NNReal) (loss : ENNReal) (epsilon gamma : Real)
    (hrho : 0 < rho) :
    eighthSelectedThirdFactorLoss rho loss epsilon gamma =
      eighthSelectedThirdFixedLoss loss epsilon gamma *
        (rho : ENNReal) ^ (-epsilon) := by
  rw [eighthSelectedThirdFactorLoss]
  rw [coe_div_eight_rpow rho (-epsilon)]
  rw [eighth_ratio_scaleCountFactor_eq_constant rho gamma hrho]
  unfold eighthSelectedThirdFixedLoss
  ring_nf

theorem eighthSelectedThirdFixedLoss_ne_top
    {loss : ENNReal} {epsilon gamma : Real}
    (hloss : loss ≠ ∞) :
    eighthSelectedThirdFixedLoss loss epsilon gamma ≠ ∞ := by
  unfold eighthSelectedThirdFixedLoss
  apply ENNReal.mul_ne_top
  · apply ENNReal.mul_ne_top
    · exact ENNReal.mul_ne_top hloss
        (ENNReal.rpow_ne_top_of_ne_zero (by norm_num) (by norm_num))
    · exact ENNReal.rpow_ne_top_of_ne_zero (by norm_num) (by norm_num)
  · unfold sectionEightScaleCountFrostmanFactor
    apply ENNReal.mul_ne_top
    · exact ENNReal.rpow_ne_top_of_ne_zero (by norm_num) (by norm_num)
    · exact ENNReal.rpow_ne_top_of_ne_zero (by norm_num) (by norm_num)

/-- The intermediate-radius power is bounded by the source-radius power
whenever `delta <= rho` and the loss exponent is nonnegative. -/
theorem eighthSelectedThirdFactorLoss_le_fixed_mul_delta_rpow
    {delta rho : NNReal} {loss : ENNReal} {epsilon gamma : Real}
    (hdelta : 0 < delta) (hrho : 0 < rho)
    (hdeltaRho : delta <= rho) (hepsilon : 0 <= epsilon) :
    eighthSelectedThirdFactorLoss rho loss epsilon gamma <=
      eighthSelectedThirdFixedLoss loss epsilon gamma *
        (delta : ENNReal) ^ (-epsilon) := by
  rw [eighthSelectedThirdFactorLoss_eq_fixed_mul_rpow
    rho loss epsilon gamma hrho]
  apply mul_le_mul' le_rfl
  rw [← ENNReal.coe_rpow_of_ne_zero hrho.ne' (-epsilon),
    ← ENNReal.coe_rpow_of_ne_zero hdelta.ne' (-epsilon)]
  exact ENNReal.coe_le_coe.mpr
    (NNReal.rpow_le_rpow_of_nonpos hdelta hdeltaRho
      (neg_nonpos.mpr hepsilon))

/-- Below the explicit finite-constant threshold, the full canonical third
loss is absorbed into `delta ^ (-(epsilon + absorbExponent))`.

The `loss` supplied here must be uniform in the datum.  A datum-dependent
conflict bound should first be dominated by a source-scale power and then
combined with this fixed-ratio calculation. -/
theorem eighthSelectedThirdFactorLoss_le_delta_negativePower
    {delta rho : NNReal} {loss : ENNReal}
    {epsilon gamma absorbExponent : Real}
    (hdelta : 0 < delta) (hrho : 0 < rho)
    (hdeltaRho : delta <= rho) (hepsilon : 0 <= epsilon)
    (hloss : loss ≠ ∞) (habsorb : 0 < absorbExponent)
    (hsmall : delta <= finiteConstantSmallDeltaThreshold
      (eighthSelectedThirdFixedLoss loss epsilon gamma) absorbExponent) :
    eighthSelectedThirdFactorLoss rho loss epsilon gamma <=
      (delta : ENNReal) ^ (-(epsilon + absorbExponent)) := by
  have hfixed : eighthSelectedThirdFixedLoss loss epsilon gamma <=
      (delta : ENNReal) ^ (-absorbExponent) :=
    finiteConstant_le_delta_negativePower
      (eighthSelectedThirdFixedLoss_ne_top hloss)
      habsorb hdelta hsmall
  have hd0 : (delta : ENNReal) ≠ 0 :=
    ENNReal.coe_ne_zero.mpr hdelta.ne'
  have hdTop : (delta : ENNReal) ≠ ∞ := ENNReal.coe_ne_top
  calc
    eighthSelectedThirdFactorLoss rho loss epsilon gamma <=
        eighthSelectedThirdFixedLoss loss epsilon gamma *
          (delta : ENNReal) ^ (-epsilon) :=
      eighthSelectedThirdFactorLoss_le_fixed_mul_delta_rpow
        hdelta hrho hdeltaRho hepsilon
    _ <= (delta : ENNReal) ^ (-absorbExponent) *
        (delta : ENNReal) ^ (-epsilon) :=
      mul_le_mul' hfixed le_rfl
    _ = (delta : ENNReal) ^ (-(epsilon + absorbExponent)) := by
      rw [← ENNReal.rpow_add _ _ hd0 hdTop]
      congr 1
      ring

#print axioms eighthSelectedThirdFixedLoss
#print axioms eighth_ratio_scaleCountFactor_eq_constant
#print axioms eighthSelectedThirdFactorLoss_eq_fixed_mul_rpow
#print axioms eighthSelectedThirdFixedLoss_ne_top
#print axioms eighthSelectedThirdFactorLoss_le_fixed_mul_delta_rpow
#print axioms eighthSelectedThirdFactorLoss_le_delta_negativePower

end
end Family8EighthSelectedThirdFactorLossAbsorptionV2
