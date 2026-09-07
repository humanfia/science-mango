import Family8Grounding.Family8ContractedJohnMiddleCardScaleAlgebraV3
import Mathlib.Tactic

/-!
# Relative-scale envelope for the contracted-John middle factor, V3

V1 had a delimiter corruption and V2 left two finite-product rewrites
unfinished; neither is imported.  This successor exposes the exact net
`tau/b` gain while keeping the dependent sticky objects out of the theorem.
-/

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 1500000

open scoped ENNReal NNReal

namespace Family8ContractedJohnMiddleRelativeScaleEnvelopeV3

open Family8ContractedJohnMiddleCardScaleAlgebraV3
open Family8KatzTaoFrostmanPropertiesV1
open Family8Prop66AFrostmanAspectGainAlgebraV1
open Family8ThreeScaleFrostmanFactorAlgebraV2

noncomputable section

def contractedJohnMiddleFixedCoefficient
    (K : ENNReal) (epsilon beta gamma lossExp : Real) : ENNReal :=
  K ^ ((gamma - beta) / 2) *
    (3 / 64 : ENNReal) ^ (2 - 3 * beta - epsilon - lossExp)

def contractedJohnMiddleRatioGain
    (epsilon beta gamma lossExp kappa : Real) : Real :=
  2 * (gamma - beta) - epsilon - lossExp -
    kappa * ((gamma - beta) / 2)

theorem loss_mul_cardScaleRHS_le_fixed_mul_ratioGain_mul_sectionEight
    {fine coarse scale : NNReal} {tubeCount : Nat}
    {loss K : ENNReal} {epsilon beta gamma lossExp kappa : Real}
    (hfine : 0 < fine) (hcoarse : 0 < coarse) (hscale : 0 < scale)
    (htubeCount : 0 < tubeCount)
    (hbetaTwo : beta <= 2) (hgammaTwo : gamma <= 2)
    (hgap : 0 <= gamma - beta)
    (hscaleEq : (scale : ENNReal) =
      (3 / 64 : ENNReal) *
        ((fine : ENNReal) / (coarse : ENNReal)))
    (hloss : loss <= (scale : ENNReal) ^ (-lossExp))
    (hcount : (tubeCount : ENNReal) <=
      K * (((fine : ENNReal) / (coarse : ENNReal)) ^
        (-(2 + kappa)))) :
    loss * frostmanMultiplicityRHS scale
        (proposition66ACardScaleVolume scale tubeCount) epsilon beta <=
      contractedJohnMiddleFixedCoefficient K epsilon beta gamma lossExp *
        (((fine : ENNReal) / (coarse : ENNReal)) ^
          contractedJohnMiddleRatioGain epsilon beta gamma lossExp kappa) *
        sectionEightScaleCountFrostmanFactor
          fine coarse tubeCount gamma := by
  let q : ENNReal := (fine : ENNReal) / (coarse : ENNReal)
  let c : ENNReal := 3 / 64
  let gapHalf : Real := (gamma - beta) / 2
  let scaleExp : Real := 2 - 3 * beta - epsilon - lossExp
  let countExp : Real := (2 + kappa) * gapHalf
  let gain : Real := 2 * (gamma - beta) - epsilon - lossExp -
    kappa * gapHalf
  let targetExp : Real := 2 - 3 * gamma
  have hq0 : q ≠ 0 := by
    dsimp only [q]
    apply ENNReal.div_ne_zero.mpr
    constructor
    · exact ENNReal.coe_ne_zero.mpr hfine.ne'
    · exact ENNReal.coe_ne_top
  have hqTop : q ≠ ∞ := by
    dsimp only [q]
    exact ENNReal.div_ne_top ENNReal.coe_ne_top
      (ENNReal.coe_ne_zero.mpr hcoarse.ne')
  have hcTop : c ≠ ∞ := by
    dsimp only [c]
    exact ENNReal.div_ne_top (by norm_num) (by norm_num)
  have hcountPower :
      (tubeCount : ENNReal) ^ (1 - beta / 2) <=
        K ^ gapHalf * q ^ (-countExp) *
          (tubeCount : ENNReal) ^ (1 - gamma / 2) := by
    simpa only [q, gapHalf, countExp] using
      count_power_beta_le_envelope_mul_gamma
        htubeCount hgap hcount
  have hscalePower :
      (scale : ENNReal) ^ (-lossExp) *
          (scale : ENNReal) ^ (2 - 3 * beta - epsilon) =
        (scale : ENNReal) ^ scaleExp := by
    rw [← ENNReal.rpow_add (-lossExp)
      (2 - 3 * beta - epsilon)
      (ENNReal.coe_ne_zero.mpr hscale.ne') ENNReal.coe_ne_top]
    congr 1
    dsimp only [scaleExp]
    ring
  have hqPower : q ^ scaleExp * q ^ (-countExp) =
      q ^ gain * q ^ targetExp := by
    rw [← ENNReal.rpow_add scaleExp (-countExp) hq0 hqTop,
      ← ENNReal.rpow_add gain targetExp hq0 hqTop]
    congr 1
    dsimp only [scaleExp, countExp, gain, targetExp, gapHalf]
    ring
  rw [frostmanMultiplicityRHS_cardScale_eq hscale hbetaTwo,
    sectionEightScaleCountFrostmanFactor_eq_ratio_count
      hfine hcoarse hgammaTwo]
  change loss *
      ((scale : ENNReal) ^ (2 - 3 * beta - epsilon) *
        (tubeCount : ENNReal) ^ (1 - beta / 2)) <=
    (K ^ gapHalf * c ^ scaleExp) * q ^ gain *
      (q ^ targetExp *
        (tubeCount : ENNReal) ^ (1 - gamma / 2))
  calc
    loss * ((scale : ENNReal) ^ (2 - 3 * beta - epsilon) *
          (tubeCount : ENNReal) ^ (1 - beta / 2)) <=
        ((scale : ENNReal) ^ (-lossExp)) *
          ((scale : ENNReal) ^ (2 - 3 * beta - epsilon) *
            (tubeCount : ENNReal) ^ (1 - beta / 2)) :=
      mul_le_mul' hloss le_rfl
    _ = (scale : ENNReal) ^ scaleExp *
          (tubeCount : ENNReal) ^ (1 - beta / 2) := by
      rw [← mul_assoc, hscalePower]
    _ <= (scale : ENNReal) ^ scaleExp *
          (K ^ gapHalf * q ^ (-countExp) *
            (tubeCount : ENNReal) ^ (1 - gamma / 2)) :=
      mul_le_mul' le_rfl hcountPower
    _ = c ^ scaleExp * q ^ scaleExp *
          (K ^ gapHalf * q ^ (-countExp) *
            (tubeCount : ENNReal) ^ (1 - gamma / 2)) := by
      rw [hscaleEq, ENNReal.mul_rpow_of_ne_top hcTop hqTop]
    _ = (K ^ gapHalf * c ^ scaleExp) *
          (q ^ scaleExp * q ^ (-countExp)) *
            (tubeCount : ENNReal) ^ (1 - gamma / 2) := by
      ac_rfl
    _ = (K ^ gapHalf * c ^ scaleExp) * q ^ gain *
          (q ^ targetExp *
            (tubeCount : ENNReal) ^ (1 - gamma / 2)) := by
      rw [hqPower]
      ac_rfl

#print axioms contractedJohnMiddleFixedCoefficient
#print axioms contractedJohnMiddleRatioGain
#print axioms
  loss_mul_cardScaleRHS_le_fixed_mul_ratioGain_mul_sectionEight

end
end Family8ContractedJohnMiddleRelativeScaleEnvelopeV3
