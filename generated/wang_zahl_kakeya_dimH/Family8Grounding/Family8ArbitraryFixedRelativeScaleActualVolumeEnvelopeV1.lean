import Family8Grounding.Family8ContractedJohnMiddleActualVolumeEnvelopeV4
import Mathlib.Tactic

/-!
# Relative-scale Frostman envelope with an arbitrary fixed proxy coefficient

The existing contracted-John envelope specializes the normalized proxy scale
to `(3/64) * (fine/coarse)`.  The full-coefficient critical-scale proxy has
the equally explicit scale `2 * (fine/coarse)`.  This module proves the same
Section 8 algebra with the fixed coefficient kept as a parameter.
-/

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 1900000

open scoped ENNReal NNReal

namespace Family8ArbitraryFixedRelativeScaleActualVolumeEnvelopeV1

open Family8ContractedJohnMiddleActualVolumeEnvelopeV4
open Family8ContractedJohnMiddleCardScaleAlgebraV3
open Family8ContractedJohnMiddleRelativeScaleEnvelopeV3
open Family8KatzTaoFrostmanPropertiesV1
open Family8Prop66AActualFamilyVolumeTransportV1
open Family8Prop66AFrostmanAspectGainAlgebraV1
open Family8ThreeScaleFrostmanFactorAlgebraV2

noncomputable section

/-- Fixed coefficient in the card-scale relative Frostman envelope. -/
def arbitraryFixedMiddleCoefficient
    (fixed K : ENNReal)
    (epsilon beta gamma lossExp : Real) : ENNReal :=
  K ^ ((gamma - beta) / 2) *
    fixed ^ (2 - 3 * beta - epsilon - lossExp)

/-- The corresponding coefficient for actual tube volume. -/
def arbitraryFixedMiddleActualCoefficient
    (fixed K : ENNReal)
    (epsilon beta gamma lossExp : Real) : ENNReal :=
  (8 : ENNReal) ^ (1 - beta / 2) *
    arbitraryFixedMiddleCoefficient
      fixed K epsilon beta gamma lossExp

/-- Card-scale form of the arbitrary-fixed relative envelope. -/
theorem loss_mul_cardScaleRHS_le_arbitraryFixed_mul_ratioGain_mul_sectionEight
    {fine coarse scale : NNReal} {tubeCount : Nat}
    {loss fixed K : ENNReal} {epsilon beta gamma lossExp kappa : Real}
    (hfine : 0 < fine) (hcoarse : 0 < coarse) (hscale : 0 < scale)
    (htubeCount : 0 < tubeCount)
    (hbetaTwo : beta ≤ 2) (hgammaTwo : gamma ≤ 2)
    (hgap : 0 ≤ gamma - beta)
    (hfixedTop : fixed ≠ ∞)
    (hscaleEq : (scale : ENNReal) = fixed *
      ((fine : ENNReal) / (coarse : ENNReal)))
    (hloss : loss ≤ (scale : ENNReal) ^ (-lossExp))
    (hcount : (tubeCount : ENNReal) ≤
      K * (((fine : ENNReal) / (coarse : ENNReal)) ^
        (-(2 + kappa)))) :
    loss * frostmanMultiplicityRHS scale
        (proposition66ACardScaleVolume scale tubeCount) epsilon beta ≤
      arbitraryFixedMiddleCoefficient
          fixed K epsilon beta gamma lossExp *
        (((fine : ENNReal) / (coarse : ENNReal)) ^
          contractedJohnMiddleRatioGain
            epsilon beta gamma lossExp kappa) *
        sectionEightScaleCountFrostmanFactor
          fine coarse tubeCount gamma := by
  let q : ENNReal := (fine : ENNReal) / (coarse : ENNReal)
  let gapHalf : Real := (gamma - beta) / 2
  let scaleExp : Real := 2 - 3 * beta - epsilon - lossExp
  let countExp : Real := (2 + kappa) * gapHalf
  let gain : Real := 2 * (gamma - beta) - epsilon - lossExp -
    kappa * gapHalf
  let targetExp : Real := 2 - 3 * gamma
  have hq0 : q ≠ 0 := by
    dsimp only [q]
    apply ENNReal.div_ne_zero.mpr
    exact ⟨ENNReal.coe_ne_zero.mpr hfine.ne', ENNReal.coe_ne_top⟩
  have hqTop : q ≠ ∞ := by
    dsimp only [q]
    exact ENNReal.div_ne_top ENNReal.coe_ne_top
      (ENNReal.coe_ne_zero.mpr hcoarse.ne')
  have hcountPower :
      (tubeCount : ENNReal) ^ (1 - beta / 2) ≤
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
        (tubeCount : ENNReal) ^ (1 - beta / 2)) ≤
    (K ^ gapHalf * fixed ^ scaleExp) * q ^ gain *
      (q ^ targetExp *
        (tubeCount : ENNReal) ^ (1 - gamma / 2))
  calc
    loss * ((scale : ENNReal) ^ (2 - 3 * beta - epsilon) *
          (tubeCount : ENNReal) ^ (1 - beta / 2)) ≤
        (scale : ENNReal) ^ (-lossExp) *
          ((scale : ENNReal) ^ (2 - 3 * beta - epsilon) *
            (tubeCount : ENNReal) ^ (1 - beta / 2)) :=
      mul_le_mul' hloss le_rfl
    _ = (scale : ENNReal) ^ scaleExp *
          (tubeCount : ENNReal) ^ (1 - beta / 2) := by
      rw [← mul_assoc, hscalePower]
    _ ≤ (scale : ENNReal) ^ scaleExp *
          (K ^ gapHalf * q ^ (-countExp) *
            (tubeCount : ENNReal) ^ (1 - gamma / 2)) :=
      mul_le_mul' le_rfl hcountPower
    _ = fixed ^ scaleExp * q ^ scaleExp *
          (K ^ gapHalf * q ^ (-countExp) *
            (tubeCount : ENNReal) ^ (1 - gamma / 2)) := by
      rw [hscaleEq, ENNReal.mul_rpow_of_ne_top hfixedTop hqTop]
    _ = (K ^ gapHalf * fixed ^ scaleExp) *
          (q ^ scaleExp * q ^ (-countExp)) *
            (tubeCount : ENNReal) ^ (1 - gamma / 2) := by
      ac_rfl
    _ = (K ^ gapHalf * fixed ^ scaleExp) * q ^ gain *
          (q ^ targetExp *
            (tubeCount : ENNReal) ^ (1 - gamma / 2)) := by
      rw [hqPower]
      ac_rfl

/-- Actual-volume form, including the exact standard tube-volume factor. -/
theorem loss_mul_actualRHS_le_arbitraryFixed_mul_ratioGain_mul_sectionEight
    {fine coarse scale : NNReal} {iota : Type}
    [Fintype iota] [DecidableEq iota]
    (D : ActualTubeDatum scale iota)
    {loss fixed K : ENNReal} {epsilon beta gamma lossExp kappa : Real}
    (hfine : 0 < fine) (hcoarse : 0 < coarse)
    (hscale : 0 < scale) (hscaleHalf : scale ≤ (2 : NNReal)⁻¹)
    (hbetaTwo : beta ≤ 2) (hgammaTwo : gamma ≤ 2)
    (hgap : 0 ≤ gamma - beta)
    (hfixedTop : fixed ≠ ∞)
    (hscaleEq : (scale : ENNReal) = fixed *
      ((fine : ENNReal) / (coarse : ENNReal)))
    (hloss : loss ≤ (scale : ENNReal) ^ (-lossExp))
    (hcountPos : 0 < Fintype.card iota)
    (hcount : (Fintype.card iota : ENNReal) ≤
      K * (((fine : ENNReal) / (coarse : ENNReal)) ^
        (-(2 + kappa)))) :
    loss * frostmanMultiplicityRHS
        scale D.actualFamilyVolume epsilon beta ≤
      arbitraryFixedMiddleActualCoefficient
          fixed K epsilon beta gamma lossExp *
        (((fine : ENNReal) / (coarse : ENNReal)) ^
          contractedJohnMiddleRatioGain
            epsilon beta gamma lossExp kappa) *
        sectionEightScaleCountFrostmanFactor
          fine coarse (Fintype.card iota) gamma := by
  have hcard :=
    frostmanMultiplicityRHS_actual_le_cardScale_mul_eight_rpow
      (epsilon := epsilon) (beta := beta) D hscaleHalf hbetaTwo
  have hrelative :=
    loss_mul_cardScaleRHS_le_arbitraryFixed_mul_ratioGain_mul_sectionEight
      (loss := loss) (fixed := fixed) (K := K)
      (epsilon := epsilon) (beta := beta) (gamma := gamma)
      (lossExp := lossExp) (kappa := kappa)
      hfine hcoarse hscale hcountPos hbetaTwo hgammaTwo hgap
        hfixedTop hscaleEq hloss hcount
  calc
    loss * frostmanMultiplicityRHS
          scale D.actualFamilyVolume epsilon beta ≤
        loss *
          (frostmanMultiplicityRHS scale
              (proposition66ACardScaleVolume scale (Fintype.card iota))
              epsilon beta *
            (8 : ENNReal) ^ (1 - beta / 2)) :=
      mul_le_mul' le_rfl hcard
    _ = (8 : ENNReal) ^ (1 - beta / 2) *
          (loss * frostmanMultiplicityRHS scale
            (proposition66ACardScaleVolume scale (Fintype.card iota))
              epsilon beta) := by
      ac_rfl
    _ ≤ (8 : ENNReal) ^ (1 - beta / 2) *
          (arbitraryFixedMiddleCoefficient
              fixed K epsilon beta gamma lossExp *
            (((fine : ENNReal) / (coarse : ENNReal)) ^
              contractedJohnMiddleRatioGain
                epsilon beta gamma lossExp kappa) *
            sectionEightScaleCountFrostmanFactor
              fine coarse (Fintype.card iota) gamma) :=
      mul_le_mul' le_rfl hrelative
    _ = arbitraryFixedMiddleActualCoefficient
          fixed K epsilon beta gamma lossExp *
        (((fine : ENNReal) / (coarse : ENNReal)) ^
          contractedJohnMiddleRatioGain
            epsilon beta gamma lossExp kappa) *
        sectionEightScaleCountFrostmanFactor
          fine coarse (Fintype.card iota) gamma := by
      unfold arbitraryFixedMiddleActualCoefficient
      ac_rfl

#print axioms arbitraryFixedMiddleCoefficient
#print axioms arbitraryFixedMiddleActualCoefficient
#print axioms
  loss_mul_cardScaleRHS_le_arbitraryFixed_mul_ratioGain_mul_sectionEight
#print axioms
  loss_mul_actualRHS_le_arbitraryFixed_mul_ratioGain_mul_sectionEight

end
end Family8ArbitraryFixedRelativeScaleActualVolumeEnvelopeV1
