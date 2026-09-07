import Family8Grounding.Family8IdentityRadiusSourceKatzTaoTransportV1
import FamilyStickyGrounding.FamilyStickyScaleChainSmallDeltaExponentBudgetProducerV1
import Mathlib.Tactic

/-!
# Power envelope for the identity-radius Katz--Tao loss

The identity-radius transport costs the literal tube-volume ratio
`8 * rho^2 / (delta^2 / 2)`.  The canonical long-scale geometry already
provides a power envelope for `rho^2 / (delta^2 / 2)`.  This file combines
that envelope with the source Katz--Tao power and absorbs only the fixed
factor sixteen.
-/

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 1400000

open scoped ENNReal NNReal

namespace Family8IdentityRadiusKatzTaoPowerEnvelopeV1

open Family8IdentityRadiusSourceKatzTaoTransportV1
open FamilyStickyScaleChainSmallDeltaExponentBudgetProducerV1

noncomputable section

def identityRadiusKatzTaoPowerThreshold
    (absorbExponent : Real) : NNReal :=
  finiteConstantSmallDeltaThreshold 16 absorbExponent

theorem identityRadiusKatzTaoPowerThreshold_pos
    (absorbExponent : Real) :
    0 < identityRadiusKatzTaoPowerThreshold absorbExponent :=
  finiteConstantSmallDeltaThreshold_pos _ _

/-- The exact identity-radius Katz--Tao coefficient inherits the sum of the
source exponent, twice the radius-loss exponent, and one fixed absorption. -/
theorem identityRadiusKatzTaoVolumeRatio_mul_sourcePower_le_delta_negativePower
    {delta rho : NNReal} {etaKT scaleLoss absorbExponent : Real}
    (hdelta : 0 < delta)
    (hscaleRatio :
      (rho : ENNReal) ^ 2 / ((delta : ENNReal) ^ 2 / 2) ≤
        2 * (delta : ENNReal) ^ (-2 * scaleLoss))
    (habsorbExponent : 0 < absorbExponent)
    (hsmall : delta ≤
      identityRadiusKatzTaoPowerThreshold absorbExponent) :
    identityRadiusKatzTaoVolumeRatio delta rho *
        (delta : ENNReal) ^ (-etaKT) ≤
      (delta : ENNReal) ^
        (-(etaKT + 2 * scaleLoss + absorbExponent)) := by
  have hconstant : (16 : ENNReal) ≤
      (delta : ENNReal) ^ (-absorbExponent) :=
    finiteConstant_le_delta_negativePower (by norm_num)
      habsorbExponent hdelta hsmall
  have hd0 : (delta : ENNReal) ≠ 0 :=
    ENNReal.coe_ne_zero.mpr hdelta.ne'
  calc
    identityRadiusKatzTaoVolumeRatio delta rho *
        (delta : ENNReal) ^ (-etaKT) =
      (8 * ((rho : ENNReal) ^ 2 /
        ((delta : ENNReal) ^ 2 / 2))) *
          (delta : ENNReal) ^ (-etaKT) := by
        unfold identityRadiusKatzTaoVolumeRatio
        rw [mul_div_assoc]
    _ ≤ (16 * (delta : ENNReal) ^ (-2 * scaleLoss)) *
          (delta : ENNReal) ^ (-etaKT) := by
      apply mul_le_mul' _ le_rfl
      calc
        8 * ((rho : ENNReal) ^ 2 /
            ((delta : ENNReal) ^ 2 / 2)) ≤
          8 * (2 * (delta : ENNReal) ^ (-2 * scaleLoss)) :=
            mul_le_mul' le_rfl hscaleRatio
        _ = 16 * (delta : ENNReal) ^ (-2 * scaleLoss) := by ring
    _ ≤ ((delta : ENNReal) ^ (-absorbExponent) *
          (delta : ENNReal) ^ (-2 * scaleLoss)) *
            (delta : ENNReal) ^ (-etaKT) := by
      gcongr
    _ = (delta : ENNReal) ^
        (-(etaKT + 2 * scaleLoss + absorbExponent)) := by
      rw [← ENNReal.rpow_add _ _ hd0 ENNReal.coe_ne_top,
        ← ENNReal.rpow_add _ _ hd0 ENNReal.coe_ne_top]
      congr 1
      ring

#print axioms identityRadiusKatzTaoPowerThreshold_pos
#print axioms
  identityRadiusKatzTaoVolumeRatio_mul_sourcePower_le_delta_negativePower

end
end Family8IdentityRadiusKatzTaoPowerEnvelopeV1
