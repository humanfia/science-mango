import FamilyStickyGrounding.FamilyStickyScaleChainSmallDeltaExponentBudgetProducerV1
import Mathlib.Tactic

/-!
# Power absorption for the buffered canonical outer/thick envelope

The honest buffered common-scale datum has comparison constant `16`, so its
isotropic unique-owner thickening coefficient is `27 * 16^3 = 110592`.
This scalar successor absorbs that fixed coefficient together with finite
cardinality and Frostman power envelopes.  No conclusion-valued hypothesis is
introduced.
-/

open scoped ENNReal NNReal

namespace Family8BufferedCanonicalOuterThickNEnvelopePowerAlgebraV1

open FamilyStickyScaleChainSmallDeltaExponentBudgetProducerV1

noncomputable section

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 1000000

/-- Smallness threshold which pays exactly for the buffered comparison
constant `27 * 16^3 = 110592`. -/
def bufferedCanonicalOuterThickFixedThreshold
    (beta absorbExponent : Real) : NNReal :=
  finiteConstantSmallDeltaThreshold
    ((110592 : ENNReal) ^ (beta / 2)) absorbExponent

theorem bufferedCanonicalOuterThickFixedThreshold_pos
    (beta absorbExponent : Real) :
    0 < bufferedCanonicalOuterThickFixedThreshold beta absorbExponent :=
  finiteConstantSmallDeltaThreshold_pos _ _

/-- Independent negative-power bounds for the active-cardinality and
Frostman factors absorb the complete buffered outer/thick envelope. -/
theorem bufferedCanonicalOuterThickNEnvelope_le_delta_negativePower
    {delta : NNReal} {N C : ENNReal}
    {cardExponent frostmanExponent beta absorbExponent : Real}
    (hdelta : 0 < delta) (hdeltaOne : delta ≤ 1)
    (hcardExponent : 0 ≤ cardExponent)
    (hfrostmanExponent : 0 ≤ frostmanExponent)
    (hbeta : 0 ≤ beta) (habsorbExponent : 0 < absorbExponent)
    (hsmall : delta ≤
      bufferedCanonicalOuterThickFixedThreshold beta absorbExponent)
    (hN : N ≤ (delta : ENNReal) ^ (-cardExponent))
    (hC : C ≤ (delta : ENNReal) ^ (-frostmanExponent)) :
    ((N * N) * N) *
        (max 1 ((110592 : ENNReal) * C * N)) ^ (beta / 2) ≤
      (delta : ENNReal) ^
        (-(3 * cardExponent +
          (frostmanExponent + cardExponent) * (beta / 2) +
          absorbExponent)) := by
  have hd0 : (delta : ENNReal) ≠ 0 :=
    ENNReal.coe_ne_zero.mpr hdelta.ne'
  have hdTop : (delta : ENNReal) ≠ ∞ := ENNReal.coe_ne_top
  have hdOne : (delta : ENNReal) ≤ 1 := by
    exact_mod_cast hdeltaOne
  have hcardOne : 1 ≤ (delta : ENNReal) ^ (-cardExponent) := by
    have hpow : (delta : ENNReal) ^ cardExponent ≤ 1 ^ cardExponent :=
      ENNReal.rpow_le_rpow hdOne hcardExponent
    simpa only [ENNReal.rpow_neg, one_div, ENNReal.one_rpow, inv_one] using
      ENNReal.inv_le_inv' hpow
  have hfrostmanOne : 1 ≤ (delta : ENNReal) ^ (-frostmanExponent) := by
    have hpow : (delta : ENNReal) ^ frostmanExponent ≤
        1 ^ frostmanExponent :=
      ENNReal.rpow_le_rpow hdOne hfrostmanExponent
    simpa only [ENNReal.rpow_neg, one_div, ENNReal.one_rpow, inv_one] using
      ENNReal.inv_le_inv' hpow
  have hinside :
      max 1 ((110592 : ENNReal) * C * N) ≤
        (110592 : ENNReal) *
          (delta : ENNReal) ^ (-frostmanExponent) *
          (delta : ENNReal) ^ (-cardExponent) := by
    apply max_le
    · calc
        1 ≤ (110592 : ENNReal) := by norm_num
        _ ≤ (110592 : ENNReal) *
            (delta : ENNReal) ^ (-frostmanExponent) := by
          simpa [mul_comm] using mul_le_mul_left hfrostmanOne
            (110592 : ENNReal)
        _ ≤ (110592 : ENNReal) *
            (delta : ENNReal) ^ (-frostmanExponent) *
            (delta : ENNReal) ^ (-cardExponent) := by
          simpa [mul_comm] using mul_le_mul_left hcardOne
            ((110592 : ENNReal) *
              (delta : ENNReal) ^ (-frostmanExponent))
    · exact mul_le_mul' (mul_le_mul' le_rfl hC) hN
  have hhalf : 0 ≤ beta / 2 := by linarith
  have hconstant : (110592 : ENNReal) ^ (beta / 2) ≤
      (delta : ENNReal) ^ (-absorbExponent) := by
    exact finiteConstant_le_delta_negativePower (by finiteness)
      habsorbExponent hdelta hsmall
  calc
    ((N * N) * N) *
        (max 1 ((110592 : ENNReal) * C * N)) ^ (beta / 2) ≤
      ((((delta : ENNReal) ^ (-cardExponent) *
          (delta : ENNReal) ^ (-cardExponent)) *
        (delta : ENNReal) ^ (-cardExponent)) *
        (((110592 : ENNReal) *
          (delta : ENNReal) ^ (-frostmanExponent) *
          (delta : ENNReal) ^ (-cardExponent)) ^ (beta / 2))) := by
      exact mul_le_mul'
        (mul_le_mul' (mul_le_mul' hN hN) hN)
        (ENNReal.rpow_le_rpow hinside hhalf)
    _ = (((delta : ENNReal) ^ (-cardExponent) *
          (delta : ENNReal) ^ (-cardExponent)) *
        (delta : ENNReal) ^ (-cardExponent)) *
        (((110592 : ENNReal) ^ (beta / 2) *
          ((delta : ENNReal) ^ (-frostmanExponent)) ^ (beta / 2)) *
          ((delta : ENNReal) ^ (-cardExponent)) ^ (beta / 2)) := by
      rw [ENNReal.mul_rpow_of_nonneg _ _ hhalf,
        ENNReal.mul_rpow_of_nonneg _ _ hhalf]
    _ ≤ (((delta : ENNReal) ^ (-cardExponent) *
          (delta : ENNReal) ^ (-cardExponent)) *
        (delta : ENNReal) ^ (-cardExponent)) *
        (((delta : ENNReal) ^ (-absorbExponent) *
          ((delta : ENNReal) ^ (-frostmanExponent)) ^ (beta / 2)) *
          ((delta : ENNReal) ^ (-cardExponent)) ^ (beta / 2)) := by
      gcongr
    _ = (delta : ENNReal) ^
        (-(3 * cardExponent +
          (frostmanExponent + cardExponent) * (beta / 2) +
          absorbExponent)) := by
      rw [← ENNReal.rpow_mul, ← ENNReal.rpow_mul]
      rw [← ENNReal.rpow_add _ _ hd0 hdTop,
        ← ENNReal.rpow_add _ _ hd0 hdTop,
        ← ENNReal.rpow_add _ _ hd0 hdTop,
        ← ENNReal.rpow_add _ _ hd0 hdTop,
        ← ENNReal.rpow_add _ _ hd0 hdTop]
      congr 1
      ring

#print axioms bufferedCanonicalOuterThickFixedThreshold_pos
#print axioms bufferedCanonicalOuterThickNEnvelope_le_delta_negativePower

end
end Family8BufferedCanonicalOuterThickNEnvelopePowerAlgebraV1
