import FamilyStickyGrounding.FamilyStickyScaleChainSmallDeltaExponentBudgetProducerV1
import Mathlib.Tactic

/-!
# Power absorption for the finite canonical outer/thick envelope

This scalar successor turns independent negative-power bounds for the active
parent cardinality and selected Frostman constant into one negative-power
bound for the exact finite envelope left by Equation (45).
-/

open scoped ENNReal NNReal

namespace Family8CanonicalOuterThickNEnvelopePowerAlgebraV4

open FamilyStickyScaleChainSmallDeltaExponentBudgetProducerV1

noncomputable section

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 1000000

def canonicalOuterThickFixedThreshold (beta absorbExponent : Real) : NNReal :=
  finiteConstantSmallDeltaThreshold
    ((216 : ENNReal) ^ (beta / 2)) absorbExponent

theorem canonicalOuterThickFixedThreshold_pos
    (beta absorbExponent : Real) :
    0 < canonicalOuterThickFixedThreshold beta absorbExponent :=
  finiteConstantSmallDeltaThreshold_pos _ _

theorem canonicalOuterThickNEnvelope_le_delta_negativePower
    {delta : NNReal} {N C : ENNReal}
    {cardExponent frostmanExponent beta absorbExponent : Real}
    (hdelta : 0 < delta) (hdeltaOne : delta ≤ 1)
    (hcardExponent : 0 ≤ cardExponent)
    (hfrostmanExponent : 0 ≤ frostmanExponent)
    (hbeta : 0 ≤ beta) (habsorbExponent : 0 < absorbExponent)
    (hsmall : delta ≤
      canonicalOuterThickFixedThreshold beta absorbExponent)
    (hN : N ≤ (delta : ENNReal) ^ (-cardExponent))
    (hC : C ≤ (delta : ENNReal) ^ (-frostmanExponent)) :
    ((N * N) * N) *
        (max 1 ((216 : ENNReal) * C * N)) ^ (beta / 2) ≤
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
      max 1 ((216 : ENNReal) * C * N) ≤
        (216 : ENNReal) *
          (delta : ENNReal) ^ (-frostmanExponent) *
          (delta : ENNReal) ^ (-cardExponent) := by
    apply max_le
    · calc
        1 ≤ (216 : ENNReal) := by norm_num
        _ ≤ (216 : ENNReal) *
            (delta : ENNReal) ^ (-frostmanExponent) := by
          simpa [mul_comm] using mul_le_mul_left hfrostmanOne (216 : ENNReal)
        _ ≤ (216 : ENNReal) *
            (delta : ENNReal) ^ (-frostmanExponent) *
            (delta : ENNReal) ^ (-cardExponent) := by
          simpa [mul_comm] using mul_le_mul_left hcardOne
            ((216 : ENNReal) *
              (delta : ENNReal) ^ (-frostmanExponent))
    · exact mul_le_mul' (mul_le_mul' le_rfl hC) hN
  have hhalf : 0 ≤ beta / 2 := by linarith
  have hconstant : (216 : ENNReal) ^ (beta / 2) ≤
      (delta : ENNReal) ^ (-absorbExponent) := by
    exact finiteConstant_le_delta_negativePower (by finiteness)
      habsorbExponent hdelta hsmall
  calc
    ((N * N) * N) *
        (max 1 ((216 : ENNReal) * C * N)) ^ (beta / 2) ≤
      ((((delta : ENNReal) ^ (-cardExponent) *
          (delta : ENNReal) ^ (-cardExponent)) *
        (delta : ENNReal) ^ (-cardExponent)) *
        (((216 : ENNReal) *
          (delta : ENNReal) ^ (-frostmanExponent) *
          (delta : ENNReal) ^ (-cardExponent)) ^ (beta / 2))) := by
      exact mul_le_mul'
        (mul_le_mul' (mul_le_mul' hN hN) hN)
        (ENNReal.rpow_le_rpow hinside hhalf)
    _ = (((delta : ENNReal) ^ (-cardExponent) *
          (delta : ENNReal) ^ (-cardExponent)) *
        (delta : ENNReal) ^ (-cardExponent)) *
        (((216 : ENNReal) ^ (beta / 2) *
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

#print axioms canonicalOuterThickFixedThreshold_pos
#print axioms canonicalOuterThickNEnvelope_le_delta_negativePower

end
end Family8CanonicalOuterThickNEnvelopePowerAlgebraV4
