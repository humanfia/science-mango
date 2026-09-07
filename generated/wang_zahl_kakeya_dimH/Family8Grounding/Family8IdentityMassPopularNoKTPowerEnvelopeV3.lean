import Mathlib.Tactic

/-!
# Identity mass-popular power envelopes without Katz--Tao, V2

V1--V2 are frozen.  This clean successor removes two unused area side lemmas,
normalizes the exact half-square identity before reassociating products, and
uses a single-source-exponent power core directly.
-/

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 3000000

open scoped ENNReal NNReal

namespace Family8IdentityMassPopularNoKTPowerEnvelopeV3

noncomputable section

def identityMassPopularDensityFixedConstant : ENNReal :=
  16 * 93312 * 128

def identityMassPopularBaseFixedConstant (eta p a : Real) : ENNReal :=
  32 * (3 / 64 : ENNReal) ^ (eta - (2 * p + a) - 2)

/-- Exact payment of the mass-popular `card * tau^2` coefficient by the
source card-area density lower bound. -/
theorem identityCardArea_massPopular_scalar_cancellation
    {tau : ENNReal} {card loss densityTarget baseTarget baseScale baseUnit
      densityFloor sourceMass : ENNReal}
    (_htau0 : tau ≠ 0) (_htauTop : tau ≠ ∞)
    (hsource : densityFloor * (card * (tau ^ 2 / 2)) ≤ sourceMass)
    (hdensity :
      16 * loss * ((densityTarget * 93312) * 128) ≤ densityFloor)
    (hbase :
      16 * loss * baseTarget ≤ baseScale * baseUnit * densityFloor) :
    (((loss * card) * (1 * (8 * tau ^ 2))) *
          ((densityTarget * 93312) * 128) ≤ sourceMass) ∧
      (((loss * card) * (8 * tau ^ 2)) * baseTarget ≤
        (baseScale * baseUnit) * sourceMass) := by
  have hhalfSixteen : (tau ^ 2 / 2) * 16 = 8 * tau ^ 2 := by
    calc
      (tau ^ 2 / 2) * 16 = ((tau ^ 2 / 2) * 2) * 8 := by ring
      _ = tau ^ 2 * 8 := by
        rw [ENNReal.div_mul_cancel (by norm_num) (by norm_num)]
      _ = 8 * tau ^ 2 := by ac_rfl
  constructor
  · calc
      ((loss * card) * (1 * (8 * tau ^ 2))) *
          ((densityTarget * 93312) * 128) =
        loss * ((densityTarget * 93312) * 128) * card *
          (8 * tau ^ 2) := by ac_rfl
      _ = loss * ((densityTarget * 93312) * 128) * card *
          ((tau ^ 2 / 2) * 16) := by rw [hhalfSixteen]
      _ = (16 * loss * ((densityTarget * 93312) * 128)) *
          (card * (tau ^ 2 / 2)) := by ac_rfl
      _ ≤ densityFloor * (card * (tau ^ 2 / 2)) :=
        mul_le_mul' hdensity le_rfl
      _ ≤ sourceMass := hsource
  · calc
      ((loss * card) * (8 * tau ^ 2)) * baseTarget =
        loss * baseTarget * card * (8 * tau ^ 2) := by ac_rfl
      _ = loss * baseTarget * card * ((tau ^ 2 / 2) * 16) := by
        rw [hhalfSixteen]
      _ = (16 * loss * baseTarget) *
          (card * (tau ^ 2 / 2)) := by ac_rfl
      _ ≤ (baseScale * baseUnit * densityFloor) *
          (card * (tau ^ 2 / 2)) := mul_le_mul' hbase le_rfl
      _ = (baseScale * baseUnit) *
          (densityFloor * (card * (tau ^ 2 / 2))) := by ac_rfl
      _ ≤ (baseScale * baseUnit) * sourceMass :=
        mul_le_mul' le_rfl hsource

/-- A single-source-exponent power product core. -/
theorem fixedPowerCoreSingle_le_source
    {delta : NNReal} {lossBound XUpper q source K : ENNReal}
    {lossExp xExp absorbExp scaleExp gain etaSource : Real}
    (hdelta : 0 < delta) (hdeltaOne : delta ≤ 1)
    (hloss : lossBound ≤ (delta : ENNReal) ^ (-lossExp))
    (hX : XUpper ≤ (delta : ENNReal) ^ (-xExp))
    (hK : K ≤ (delta : ENNReal) ^ (-absorbExp))
    (hq : q ≤ (delta : ENNReal) ^ scaleExp)
    (hgain : 0 ≤ gain)
    (hbudget : etaSource + lossExp + xExp + absorbExp ≤
      scaleExp * gain)
    (hsource : (delta : ENNReal) ^ etaSource ≤ source) :
    K * (lossBound * XUpper * q ^ gain) ≤ source := by
  have hd0 : (delta : ENNReal) ≠ 0 :=
    ENNReal.coe_ne_zero.mpr hdelta.ne'
  have hdTop : (delta : ENNReal) ≠ ∞ := ENNReal.coe_ne_top
  have hdOne : (delta : ENNReal) ≤ 1 := by exact_mod_cast hdeltaOne
  have hqPower : q ^ gain ≤
      (delta : ENNReal) ^ (scaleExp * gain) := by
    calc
      q ^ gain ≤ ((delta : ENNReal) ^ scaleExp) ^ gain :=
        ENNReal.rpow_le_rpow hq hgain
      _ = (delta : ENNReal) ^ (scaleExp * gain) := by
        rw [ENNReal.rpow_mul]
  have hproduct :
      K * (lossBound * XUpper * q ^ gain) ≤
        (delta : ENNReal) ^
          (-absorbExp + (-lossExp) + (-xExp) + scaleExp * gain) := by
    calc
      K * (lossBound * XUpper * q ^ gain) ≤
          (delta : ENNReal) ^ (-absorbExp) *
            ((delta : ENNReal) ^ (-lossExp) *
              (delta : ENNReal) ^ (-xExp) *
                (delta : ENNReal) ^ (scaleExp * gain)) := by
        exact mul_le_mul' hK
          (mul_le_mul' (mul_le_mul' hloss hX) hqPower)
      _ = (delta : ENNReal) ^
          (-absorbExp + (-lossExp) + (-xExp) + scaleExp * gain) := by
        rw [ENNReal.rpow_add _ _ hd0 hdTop,
          ENNReal.rpow_add _ _ hd0 hdTop,
          ENNReal.rpow_add _ _ hd0 hdTop]
        ring
  have hpower :
      (delta : ENNReal) ^
          (-absorbExp + (-lossExp) + (-xExp) + scaleExp * gain) ≤
        (delta : ENNReal) ^ etaSource := by
    apply ENNReal.rpow_le_rpow_of_exponent_ge hdOne
    linarith
  exact hproduct.trans (hpower.trans hsource)

/-- The density budget after exact identity-card cancellation. -/
theorem densityEnvelope_of_powerCaps_noKT
    {delta : NNReal} {lossBound q densityFloor : ENNReal}
    {eta p a etaSource lossExp absorbExp scaleExp : Real}
    (hdelta : 0 < delta) (hdeltaOne : delta ≤ 1)
    (hloss : lossBound ≤ (delta : ENNReal) ^ (-lossExp))
    (hconstant : identityMassPopularDensityFixedConstant ≤
      (delta : ENNReal) ^ (-absorbExp))
    (hq : q ≤ (delta : ENNReal) ^ scaleExp)
    (hgain : 0 ≤ eta - (p + a))
    (hbudget : etaSource + lossExp + absorbExp ≤
      scaleExp * (eta - (p + a)))
    (hsource : (delta : ENNReal) ^ etaSource ≤ densityFloor) :
    identityMassPopularDensityFixedConstant *
        (lossBound * q ^ (eta - (p + a))) ≤ densityFloor := by
  have hcore := fixedPowerCoreSingle_le_source
    (lossBound := lossBound) (XUpper := 1) (q := q)
    (source := densityFloor) (K := identityMassPopularDensityFixedConstant)
    (lossExp := lossExp) (xExp := 0) (absorbExp := absorbExp)
    (scaleExp := scaleExp) (gain := eta - (p + a))
    (etaSource := etaSource)
    hdelta hdeltaOne hloss (by simp) hconstant hq hgain
      (by linarith) hsource
  simpa only [mul_one] using hcore

/-- The base-scale budget after exact identity-card cancellation. -/
theorem baseEnvelope_of_powerCaps_noKT
    {delta : NNReal} {lossBound q densityFloor : ENNReal}
    {eta p a etaSource lossExp absorbExp scaleExp : Real}
    (hdelta : 0 < delta) (hdeltaOne : delta ≤ 1)
    (hloss : lossBound ≤ (delta : ENNReal) ^ (-lossExp))
    (hconstant : identityMassPopularBaseFixedConstant eta p a ≤
      (delta : ENNReal) ^ (-absorbExp))
    (hq : q ≤ (delta : ENNReal) ^ scaleExp)
    (hgain : 0 ≤ eta - (2 * p + a) - 2)
    (hbudget : etaSource + lossExp + absorbExp ≤
      scaleExp * (eta - (2 * p + a) - 2))
    (hsource : (delta : ENNReal) ^ etaSource ≤ densityFloor) :
    identityMassPopularBaseFixedConstant eta p a *
        (lossBound * q ^ (eta - (2 * p + a) - 2)) ≤ densityFloor := by
  have hcore := fixedPowerCoreSingle_le_source
    (lossBound := lossBound) (XUpper := 1) (q := q)
    (source := densityFloor)
    (K := identityMassPopularBaseFixedConstant eta p a)
    (lossExp := lossExp) (xExp := 0) (absorbExp := absorbExp)
    (scaleExp := scaleExp) (gain := eta - (2 * p + a) - 2)
    (etaSource := etaSource)
    hdelta hdeltaOne hloss (by simp) hconstant hq hgain
      (by linarith) hsource
  simpa only [mul_one] using hcore

#print axioms identityMassPopularDensityFixedConstant
#print axioms identityMassPopularBaseFixedConstant
#print axioms identityCardArea_massPopular_scalar_cancellation
#print axioms fixedPowerCoreSingle_le_source
#print axioms densityEnvelope_of_powerCaps_noKT
#print axioms baseEnvelope_of_powerCaps_noKT

end
end Family8IdentityMassPopularNoKTPowerEnvelopeV3
