import Family8Grounding.Family8B2NormalizedConflictKatzTaoCapV6
import Family8Grounding.Family8UnitBallBodyVolumeUpperV1
import FamilyStickyGrounding.FamilyStickyScaleChainSmallDeltaExponentBudgetProducerV1
import Mathlib.Tactic

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 3000000

open Set MeasureTheory
open scoped ENNReal NNReal

namespace Family8FrozenOuterThirdKatzTaoBasePowerEnvelopeV4

open LeanEval.Analysis.WangZahlKakeya
open Family8KatzTaoFrostmanPropertiesV1
open Family8B2NormalizedConflictKatzTaoCapV6
open Family8UnitBallBodyVolumeUpperV1
open FamilyStickyScaleChainSmallDeltaExponentBudgetProducerV1

noncomputable section

/-!
# Long-scale power envelope for the frozen outer base scalar

This performance successor isolates the pure numerical core.  The fixed
normalized-conflict loss and the native Katz--Tao factor cost two copies of
`CKT`, while the correlated quantity
`(rho / 8)^(-etaF) * tau^baseExponent` is retained exactly.

V1--V3 are failed import/rewrite/specialization drafts and are intentionally
not imported.
-/

def frozenOuterThirdKatzTaoBaseFixedConstant : ENNReal :=
  128 * ((480000 * 128 + 2) * 128 * 8)

def frozenOuterThirdKatzTaoBaseSmallDeltaThreshold
    (absorbEta : Real) : NNReal :=
  finiteConstantSmallDeltaThreshold
    frozenOuterThirdKatzTaoBaseFixedConstant absorbEta

theorem frozenOuterThirdKatzTaoBaseFixedConstant_ne_top :
    frozenOuterThirdKatzTaoBaseFixedConstant ≠ ∞ := by
  norm_num [frozenOuterThirdKatzTaoBaseFixedConstant]

theorem longBufferedScale_negativePower_le_baseGain
    {delta tau rho : NNReal}
    {epsilon etaF baseExponent : Real}
    (hdelta : 0 < delta) (htau : 0 < tau) (hrho : 0 < rho)
    (htauDelta : tau ≤ delta ^ epsilon)
    (hrhoTau : rho ≤ tau ^ (1 - epsilon))
    (hetaF : 0 ≤ etaF)
    (hgain : 0 ≤ (1 - epsilon) * etaF - baseExponent) :
    (delta : ENNReal) ^
        (-(epsilon * ((1 - epsilon) * etaF - baseExponent))) ≤
      (((rho / 8 : NNReal) : ENNReal) ^ (-etaF)) *
        (((tau ^ baseExponent : NNReal) : ENNReal)) := by
  let gain : Real := (1 - epsilon) * etaF - baseExponent
  have hgain' : 0 ≤ gain := by simpa only [gain] using hgain
  have hrhoEightPos : 0 < rho / 8 := div_pos hrho (by norm_num)
  have hrhoEight : rho / 8 ≤ rho := by
    exact div_le_self (show 0 ≤ rho from bot_le) (by norm_num)
  have hpowEight : rho ^ (-etaF) ≤ (rho / 8) ^ (-etaF) :=
    NNReal.rpow_le_rpow_of_nonpos hrhoEightPos hrhoEight
      (neg_nonpos.mpr hetaF)
  have hpowRho : (tau ^ (1 - epsilon)) ^ (-etaF) ≤
      rho ^ (-etaF) :=
    NNReal.rpow_le_rpow_of_nonpos hrho hrhoTau
      (neg_nonpos.mpr hetaF)
  have hpowTau : (delta ^ epsilon) ^ (-gain) ≤ tau ^ (-gain) :=
    NNReal.rpow_le_rpow_of_nonpos htau htauDelta
      (neg_nonpos.mpr hgain')
  have hcore : delta ^ (-(epsilon * gain)) ≤
      (rho / 8) ^ (-etaF) * tau ^ baseExponent := by
    calc
      delta ^ (-(epsilon * gain)) = delta ^ (epsilon * (-gain)) := by
        congr 1
        ring
      _ = (delta ^ epsilon) ^ (-gain) :=
        NNReal.rpow_mul delta epsilon (-gain)
      _ ≤ tau ^ (-gain) := hpowTau
      _ = tau ^ (((1 - epsilon) * (-etaF)) + baseExponent) := by
        congr 1
        dsimp only [gain]
        ring
      _ = tau ^ ((1 - epsilon) * (-etaF)) * tau ^ baseExponent :=
        NNReal.rpow_add htau.ne' _ _
      _ = (tau ^ (1 - epsilon)) ^ (-etaF) *
          tau ^ baseExponent := by
        rw [NNReal.rpow_mul]
      _ ≤ rho ^ (-etaF) * tau ^ baseExponent :=
        mul_le_mul_of_nonneg_right hpowRho (by positivity)
      _ ≤ (rho / 8) ^ (-etaF) * tau ^ baseExponent :=
        mul_le_mul_of_nonneg_right hpowEight (by positivity)
  rw [← ENNReal.coe_rpow_of_ne_zero hdelta.ne'
      (-(epsilon * ((1 - epsilon) * etaF - baseExponent))),
    ← ENNReal.coe_rpow_of_ne_zero hrhoEightPos.ne' (-etaF),
    ← ENNReal.coe_mul]
  exact ENNReal.coe_le_coe.mpr hcore

theorem fixedConflict_baseScalar_mul_128_le_delta_negativePower
    {delta : NNReal} {CKT : ENNReal} {etaKT absorbEta : Real}
    (hdelta : 0 < delta)
    (hCKTfinite : CKT ≠ ∞) (hCKTone : 1 ≤ CKT)
    (hCKT : CKT ≤ (delta : ENNReal) ^ (-etaKT))
    (habsorbEta : 0 < absorbEta)
    (hsmall : delta ≤
      frozenOuterThirdKatzTaoBaseSmallDeltaThreshold absorbEta) :
    128 *
        ((((Nat.ceil ((480000 * (128 * CKT) : ENNReal).toReal) + 1 : Nat) :
              ENNReal) *
          ((128 * CKT) * volume (unitBallBody : Set Space)))) ≤
      (delta : ENNReal) ^ (-(2 * etaKT + absorbEta)) := by
  have hscaledFinite : (128 : ENNReal) * CKT ≠ ∞ :=
    ENNReal.mul_ne_top (by norm_num) hCKTfinite
  have hclosed :
      ((Nat.ceil ((480000 * (128 * CKT) : ENNReal).toReal) + 1 : Nat) :
          ENNReal) ≤
        480000 * (128 * CKT) + 2 :=
    fixedKatzTaoClosedLoss_coe_le_add_two hscaledFinite
  have htwo : (2 : ENNReal) ≤ 2 * CKT := by
    simpa only [mul_one] using
      (mul_le_mul' (show (2 : ENNReal) ≤ 2 from le_rfl) hCKTone)
  have hlinear :
      480000 * (128 * CKT) + 2 ≤ (480000 * 128 + 2) * CKT := by
    calc
      480000 * (128 * CKT) + 2 ≤
          480000 * (128 * CKT) + 2 * CKT := add_le_add le_rfl htwo
      _ = (480000 * 128 + 2) * CKT := by ring
  have hfixed :
      128 *
          ((((Nat.ceil ((480000 * (128 * CKT) : ENNReal).toReal) + 1 : Nat) :
                ENNReal) *
            ((128 * CKT) * volume (unitBallBody : Set Space)))) ≤
        frozenOuterThirdKatzTaoBaseFixedConstant * CKT ^ (2 : Nat) := by
    calc
      128 *
          ((((Nat.ceil ((480000 * (128 * CKT) : ENNReal).toReal) + 1 : Nat) :
                ENNReal) *
            ((128 * CKT) * volume (unitBallBody : Set Space)))) ≤
          128 * (((480000 * 128 + 2) * CKT) *
            ((128 * CKT) * 8)) := by
        exact mul_le_mul' le_rfl
          (mul_le_mul' (hclosed.trans hlinear)
            (mul_le_mul' le_rfl volume_unitBallBody_le_eight))
      _ = frozenOuterThirdKatzTaoBaseFixedConstant * CKT ^ (2 : Nat) := by
        unfold frozenOuterThirdKatzTaoBaseFixedConstant
        ring
  have hsq : CKT ^ (2 : Nat) ≤
      ((delta : ENNReal) ^ (-etaKT)) ^ (2 : Nat) :=
    pow_le_pow_left' hCKT 2
  have hd0 : (delta : ENNReal) ≠ 0 :=
    ENNReal.coe_ne_zero.mpr hdelta.ne'
  have hdTop : (delta : ENNReal) ≠ ∞ := ENNReal.coe_ne_top
  have hpower : CKT ^ (2 : Nat) ≤
      (delta : ENNReal) ^ (-(2 * etaKT)) := by
    calc
      CKT ^ (2 : Nat) ≤ ((delta : ENNReal) ^ (-etaKT)) ^ (2 : Nat) := hsq
      _ = (delta : ENNReal) ^ ((-etaKT) * 2) := by
        rw [← ENNReal.rpow_natCast, ENNReal.rpow_mul]
        norm_num
      _ = (delta : ENNReal) ^ (-(2 * etaKT)) := by
        congr 1
        ring
  have hconstant : frozenOuterThirdKatzTaoBaseFixedConstant ≤
      (delta : ENNReal) ^ (-absorbEta) :=
    finiteConstant_le_delta_negativePower
      frozenOuterThirdKatzTaoBaseFixedConstant_ne_top
        habsorbEta hdelta hsmall
  calc
    128 *
        ((((Nat.ceil ((480000 * (128 * CKT) : ENNReal).toReal) + 1 : Nat) :
              ENNReal) *
          ((128 * CKT) * volume (unitBallBody : Set Space)))) ≤
        frozenOuterThirdKatzTaoBaseFixedConstant * CKT ^ (2 : Nat) := hfixed
    _ ≤ (delta : ENNReal) ^ (-absorbEta) *
        (delta : ENNReal) ^ (-(2 * etaKT)) :=
      mul_le_mul' hconstant hpower
    _ = (delta : ENNReal) ^
        ((-absorbEta) + (-(2 * etaKT))) := by
      rw [ENNReal.rpow_add _ _ hd0 hdTop]
    _ = (delta : ENNReal) ^ (-(2 * etaKT + absorbEta)) := by
      congr 1
      ring

theorem fixedConflict_baseScalar_le_of_longBufferedScale
    {delta tau rho : NNReal} {CKT : ENNReal}
    {epsilon etaF baseExponent etaKT absorbEta : Real}
    (hdelta : 0 < delta) (hdeltaOne : delta ≤ 1)
    (htau : 0 < tau) (hrho : 0 < rho)
    (htauDelta : tau ≤ delta ^ epsilon)
    (hrhoTau : rho ≤ tau ^ (1 - epsilon))
    (hetaF : 0 ≤ etaF)
    (hscaleGain : 0 ≤ (1 - epsilon) * etaF - baseExponent)
    (hCKTfinite : CKT ≠ ∞) (hCKTone : 1 ≤ CKT)
    (hCKT : CKT ≤ (delta : ENNReal) ^ (-etaKT))
    (habsorbEta : 0 < absorbEta)
    (hsmall : delta ≤
      frozenOuterThirdKatzTaoBaseSmallDeltaThreshold absorbEta)
    (hbudget : 2 * etaKT + absorbEta ≤
      epsilon * ((1 - epsilon) * etaF - baseExponent)) :
    ((Nat.ceil ((480000 * (128 * CKT) : ENNReal).toReal) + 1 : Nat) :
          ENNReal) *
        ((128 * CKT) * volume (unitBallBody : Set Space)) ≤
      (((rho / 8 : NNReal) : ENNReal) ^ (-etaF)) *
        ((((tau ^ baseExponent : NNReal) : ENNReal) / 128)) := by
  let lhs : ENNReal :=
    ((Nat.ceil ((480000 * (128 * CKT) : ENNReal).toReal) + 1 : Nat) :
        ENNReal) * ((128 * CKT) * volume (unitBallBody : Set Space))
  let gain : Real := epsilon * ((1 - epsilon) * etaF - baseExponent)
  have hscaled : 128 * lhs ≤
      (delta : ENNReal) ^ (-(2 * etaKT + absorbEta)) := by
    dsimp only [lhs]
    exact fixedConflict_baseScalar_mul_128_le_delta_negativePower
      hdelta hCKTfinite hCKTone hCKT habsorbEta hsmall
  have hdOneENN : (delta : ENNReal) ≤ 1 := by exact_mod_cast hdeltaOne
  have hpower : (delta : ENNReal) ^ (-(2 * etaKT + absorbEta)) ≤
      (delta : ENNReal) ^ (-gain) := by
    apply ENNReal.rpow_le_rpow_of_exponent_ge hdOneENN
    dsimp only [gain]
    linarith
  have hscale : (delta : ENNReal) ^ (-gain) ≤
      (((rho / 8 : NNReal) : ENNReal) ^ (-etaF)) *
        (((tau ^ baseExponent : NNReal) : ENNReal)) := by
    dsimp only [gain]
    exact longBufferedScale_negativePower_le_baseGain
      hdelta htau hrho htauDelta hrhoTau hetaF hscaleGain
  have hmul : lhs * 128 ≤
      (((rho / 8 : NNReal) : ENNReal) ^ (-etaF)) *
        (((tau ^ baseExponent : NNReal) : ENNReal)) := by
    calc
      lhs * 128 = 128 * lhs := mul_comm _ _
      _ ≤ (delta : ENNReal) ^ (-(2 * etaKT + absorbEta)) := hscaled
      _ ≤ (delta : ENNReal) ^ (-gain) := hpower
      _ ≤ (((rho / 8 : NNReal) : ENNReal) ^ (-etaF)) *
          (((tau ^ baseExponent : NNReal) : ENNReal)) := hscale
  change lhs ≤ _
  rw [show
    (((rho / 8 : NNReal) : ENNReal) ^ (-etaF)) *
        (((tau ^ baseExponent : NNReal) : ENNReal) / 128) =
      ((((rho / 8 : NNReal) : ENNReal) ^ (-etaF)) *
        (((tau ^ baseExponent : NNReal) : ENNReal))) / 128 by
      simp only [div_eq_mul_inv]
      ac_rfl]
  exact (ENNReal.le_div_iff_mul_le
    (Or.inl (by norm_num : (128 : ENNReal) ≠ 0))
    (Or.inl (by norm_num : (128 : ENNReal) ≠ ∞))).2 hmul

#print axioms frozenOuterThirdKatzTaoBaseFixedConstant_ne_top
#print axioms longBufferedScale_negativePower_le_baseGain
#print axioms fixedConflict_baseScalar_mul_128_le_delta_negativePower
#print axioms fixedConflict_baseScalar_le_of_longBufferedScale

end
end Family8FrozenOuterThirdKatzTaoBasePowerEnvelopeV4
