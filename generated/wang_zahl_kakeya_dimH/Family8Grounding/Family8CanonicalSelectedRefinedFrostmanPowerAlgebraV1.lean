import FamilyStickyGrounding.FamilyStickyScaleChainSmallDeltaExponentBudgetProducerV1
import Mathlib.Tactic

/-!
# Power bound for the canonical selected refined Frostman constant

The actual selected common-witness input uses `CF * (16 * N)`.  This scalar
module absorbs the fixed factor `16` and combines honest power estimates for
the unrefined source constant and the active-parent cardinality.
-/

open scoped ENNReal NNReal

namespace Family8CanonicalSelectedRefinedFrostmanPowerAlgebraV1

open FamilyStickyScaleChainSmallDeltaExponentBudgetProducerV1

noncomputable section

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 500000

def canonicalSelectedRefinementFixedThreshold
    (absorbExponent : Real) : NNReal :=
  finiteConstantSmallDeltaThreshold 16 absorbExponent

theorem canonicalSelectedRefinementFixedThreshold_pos
    (absorbExponent : Real) :
    0 < canonicalSelectedRefinementFixedThreshold absorbExponent :=
  finiteConstantSmallDeltaThreshold_pos _ _

theorem sourceCF_mul_sixteen_mul_card_le_delta_negativePower
    {delta : NNReal} {N CF : ENNReal}
    {cardExponent frostmanExponent absorbExponent : Real}
    (hdelta : 0 < delta) (habsorbExponent : 0 < absorbExponent)
    (hsmall : delta ≤
      canonicalSelectedRefinementFixedThreshold absorbExponent)
    (hN : N ≤ (delta : ENNReal) ^ (-cardExponent))
    (hCF : CF ≤ (delta : ENNReal) ^ (-frostmanExponent)) :
    CF * (16 * N) ≤
      (delta : ENNReal) ^
        (-(frostmanExponent + cardExponent + absorbExponent)) := by
  have hd0 : (delta : ENNReal) ≠ 0 :=
    ENNReal.coe_ne_zero.mpr hdelta.ne'
  have hdTop : (delta : ENNReal) ≠ ∞ := ENNReal.coe_ne_top
  have hconstant : (16 : ENNReal) ≤
      (delta : ENNReal) ^ (-absorbExponent) :=
    finiteConstant_le_delta_negativePower (by norm_num)
      habsorbExponent hdelta hsmall
  calc
    CF * (16 * N) = (16 : ENNReal) * (CF * N) := by ring
    _ ≤ (delta : ENNReal) ^ (-absorbExponent) *
        ((delta : ENNReal) ^ (-frostmanExponent) *
          (delta : ENNReal) ^ (-cardExponent)) :=
      mul_le_mul' hconstant (mul_le_mul' hCF hN)
    _ = (delta : ENNReal) ^
        (-(frostmanExponent + cardExponent + absorbExponent)) := by
      rw [← ENNReal.rpow_add _ _ hd0 hdTop,
        ← ENNReal.rpow_add _ _ hd0 hdTop]
      congr 1
      ring

#print axioms canonicalSelectedRefinementFixedThreshold_pos
#print axioms sourceCF_mul_sixteen_mul_card_le_delta_negativePower

end
end Family8CanonicalSelectedRefinedFrostmanPowerAlgebraV1
