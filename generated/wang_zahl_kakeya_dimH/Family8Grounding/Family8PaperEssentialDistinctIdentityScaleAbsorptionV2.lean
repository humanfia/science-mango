import Family8Grounding.Family8PaperEssentialDistinctIdentityScaleLowBranchV3
import FamilyStickyGrounding.FamilyStickyScaleChainSmallDeltaExponentBudgetProducerV1
import Mathlib.Tactic

set_option autoImplicit false
set_option warningAsError true

open scoped ENNReal NNReal

namespace Family8PaperEssentialDistinctIdentityScaleAbsorptionV2

open Family8PaperEssentialDistinctIdentityScaleLowBranchV3
open FamilyStickyScaleChainSmallDeltaExponentBudgetProducerV1

noncomputable section

/-!
# Automatic small-scale absorption for paper-distinct extraction

One positive exponent increment absorbs both fixed constants appearing in the
honest low-branch restriction theorem.  The common threshold is the minimum
of the two canonical finite-constant thresholds.
-/

def paperActualSubtypeAbsorptionThreshold (absorbExponent : Real) : NNReal :=
  min
    (finiteConstantSmallDeltaThreshold
      paperActualSubtypeLoss absorbExponent)
    (finiteConstantSmallDeltaThreshold
      paperActualSubtypeFrostmanLoss absorbExponent)

theorem paperActualSubtypeAbsorptionThreshold_pos
    (absorbExponent : Real) :
    0 < paperActualSubtypeAbsorptionThreshold absorbExponent := by
  exact lt_min
    (finiteConstantSmallDeltaThreshold_pos _ _)
    (finiteConstantSmallDeltaThreshold_pos _ _)

theorem paperActualSubtypeLoss_ne_zero :
    paperActualSubtypeLoss ≠ 0 := by
  simp [paperActualSubtypeLoss]

theorem paperActualSubtypeLoss_ne_top :
    paperActualSubtypeLoss ≠ ∞ := by
  simp [paperActualSubtypeLoss]

theorem paperActualSubtypeFrostmanLoss_ne_top :
    paperActualSubtypeFrostmanLoss ≠ ∞ := by
  unfold paperActualSubtypeFrostmanLoss
  exact ENNReal.mul_ne_top (by norm_num) paperActualSubtypeLoss_ne_top

/-- The shading-density loss is absorbed after increasing the source exponent
by `absorbExponent`. -/
theorem density_rpow_add_absorb_le_div_paperLoss
    {delta : NNReal} {sourceExponent absorbExponent : Real}
    (hdelta : 0 < delta) (habsorb : 0 < absorbExponent)
    (hsmall : delta <=
      paperActualSubtypeAbsorptionThreshold absorbExponent) :
    (delta : ENNReal) ^ (sourceExponent + absorbExponent) <=
      (delta : ENNReal) ^ sourceExponent / paperActualSubtypeLoss := by
  have hd0 : (delta : ENNReal) ≠ 0 :=
    ENNReal.coe_ne_zero.mpr hdelta.ne'
  have hdTop : (delta : ENNReal) ≠ ∞ := ENNReal.coe_ne_top
  have hloss :
      paperActualSubtypeLoss <=
        (delta : ENNReal) ^ (-absorbExponent) := by
    apply finiteConstant_le_delta_negativePower
      paperActualSubtypeLoss_ne_top habsorb hdelta
    exact hsmall.trans (min_le_left _ _)
  have hunit :
      (delta : ENNReal) ^ absorbExponent * paperActualSubtypeLoss <= 1 := by
    calc
      (delta : ENNReal) ^ absorbExponent * paperActualSubtypeLoss <=
          (delta : ENNReal) ^ absorbExponent *
            (delta : ENNReal) ^ (-absorbExponent) :=
        mul_le_mul' le_rfl hloss
      _ = (delta : ENNReal) ^
          (absorbExponent + (-absorbExponent)) :=
        (ENNReal.rpow_add absorbExponent (-absorbExponent) hd0 hdTop).symm
      _ = 1 := by simp
  apply (ENNReal.le_div_iff_mul_le
    (Or.inl paperActualSubtypeLoss_ne_zero)
    (Or.inl paperActualSubtypeLoss_ne_top)).2
  calc
    (delta : ENNReal) ^ (sourceExponent + absorbExponent) *
          paperActualSubtypeLoss =
        ((delta : ENNReal) ^ sourceExponent *
          (delta : ENNReal) ^ absorbExponent) *
            paperActualSubtypeLoss := by
      rw [ENNReal.rpow_add sourceExponent absorbExponent hd0 hdTop]
    _ = (delta : ENNReal) ^ sourceExponent *
          ((delta : ENNReal) ^ absorbExponent *
            paperActualSubtypeLoss) := by ac_rfl
    _ <= (delta : ENNReal) ^ sourceExponent * 1 :=
      mul_le_mul' le_rfl hunit
    _ = (delta : ENNReal) ^ sourceExponent := by simp

/-- The family-volume normalization loss is absorbed by the same exponent
increment. -/
theorem paperFrostmanLoss_mul_rpow_neg_le_rpow_neg_add
    {delta : NNReal} {sourceExponent absorbExponent : Real}
    (hdelta : 0 < delta) (habsorb : 0 < absorbExponent)
    (hsmall : delta <=
      paperActualSubtypeAbsorptionThreshold absorbExponent) :
    paperActualSubtypeFrostmanLoss *
        (delta : ENNReal) ^ (-sourceExponent) <=
      (delta : ENNReal) ^ (-(sourceExponent + absorbExponent)) := by
  have hd0 : (delta : ENNReal) ≠ 0 :=
    ENNReal.coe_ne_zero.mpr hdelta.ne'
  have hdTop : (delta : ENNReal) ≠ ∞ := ENNReal.coe_ne_top
  have hloss :
      paperActualSubtypeFrostmanLoss <=
        (delta : ENNReal) ^ (-absorbExponent) := by
    apply finiteConstant_le_delta_negativePower
      paperActualSubtypeFrostmanLoss_ne_top habsorb hdelta
    exact hsmall.trans (min_le_right _ _)
  calc
    paperActualSubtypeFrostmanLoss *
          (delta : ENNReal) ^ (-sourceExponent) <=
        (delta : ENNReal) ^ (-absorbExponent) *
          (delta : ENNReal) ^ (-sourceExponent) :=
      mul_le_mul' hloss le_rfl
    _ = (delta : ENNReal) ^
        ((-absorbExponent) + (-sourceExponent)) :=
      (ENNReal.rpow_add (-absorbExponent) (-sourceExponent)
        hd0 hdTop).symm
    _ = (delta : ENNReal) ^ (-(sourceExponent + absorbExponent)) := by
      congr 1
      ring

#print axioms paperActualSubtypeAbsorptionThreshold_pos
#print axioms paperActualSubtypeLoss_ne_zero
#print axioms paperActualSubtypeLoss_ne_top
#print axioms paperActualSubtypeFrostmanLoss_ne_top
#print axioms density_rpow_add_absorb_le_div_paperLoss
#print axioms paperFrostmanLoss_mul_rpow_neg_le_rpow_neg_add

end
end Family8PaperEssentialDistinctIdentityScaleAbsorptionV2
