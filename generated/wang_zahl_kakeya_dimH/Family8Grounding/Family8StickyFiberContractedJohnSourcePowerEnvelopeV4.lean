import Family8Grounding.Family8StickyFiberContractedJohnFixedSourceEnvelopeV1
import Family8Grounding.Family8UnitBallBodyVolumeUpperV1
import FamilyStickyGrounding.FamilyStickyScaleChainSmallDeltaExponentBudgetProducerV1
import Mathlib.Tactic

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 3000000

open Set MeasureTheory
open scoped ENNReal NNReal

namespace Family8StickyFiberContractedJohnSourcePowerEnvelopeV4

open LeanEval.Analysis.WangZahlKakeya
open Submission.Kakeya.ConvexGeometry
open Family8KatzTaoFrostmanPropertiesV1
open Family8StickyFiberContractedJohnFixedSourceEnvelopeV1
open Family8UnitBallBodyVolumeUpperV1
open FamilyStickyScaleChainSmallDeltaExponentBudgetProducerV1

noncomputable section

/-!
# Uniform source-power envelopes for the contracted-John first factor

The closed loss costs one copy of the source Katz--Tao exponent.  The full
unit-ball base scalar costs two copies.  All other factors are fixed and are
absorbed below datum-independent thresholds.  V1--V3 were failed syntax/name
drafts and are intentionally not imported.
-/

def contractedJohnSourceClosedLossFixedConstant : ENNReal :=
  480000 * (128 * 93312) + 2

def contractedJohnSourceBaseFixedConstant : ENNReal :=
  contractedJohnSourceClosedLossFixedConstant * ((128 * 93312) * 8)

def contractedJohnSourceClosedLossThreshold (a : Real) : NNReal :=
  finiteConstantSmallDeltaThreshold
    contractedJohnSourceClosedLossFixedConstant a

def contractedJohnSourceBaseThreshold (a : Real) : NNReal :=
  finiteConstantSmallDeltaThreshold contractedJohnSourceBaseFixedConstant a

theorem contractedJohnSourceClosedLossThreshold_pos (a : Real) :
    0 < contractedJohnSourceClosedLossThreshold a :=
  finiteConstantSmallDeltaThreshold_pos _ _

theorem contractedJohnSourceBaseThreshold_pos (a : Real) :
    0 < contractedJohnSourceBaseThreshold a :=
  finiteConstantSmallDeltaThreshold_pos _ _

theorem contractedJohnSourceClosedLossFixedConstant_ne_top :
    contractedJohnSourceClosedLossFixedConstant ≠ ∞ := by
  norm_num [contractedJohnSourceClosedLossFixedConstant]

theorem contractedJohnSourceBaseFixedConstant_ne_top :
    contractedJohnSourceBaseFixedConstant ≠ ∞ := by
  norm_num [contractedJohnSourceBaseFixedConstant,
    contractedJohnSourceClosedLossFixedConstant]

theorem stickyFiberContractedJohnSourceClosedLoss_le_fixed_mul_rpow
    {delta : NNReal} {C : ENNReal} {p : Real}
    (hdelta : 0 < delta) (hdeltaOne : delta ≤ 1) (hp : 0 < p)
    (hC : C ≤ (delta : ENNReal) ^ (-p)) :
    stickyFiberContractedJohnSourceClosedLoss C ≤
      contractedJohnSourceClosedLossFixedConstant *
        (delta : ENNReal) ^ (-p) := by
  have hdeltaOneENN : (delta : ENNReal) ≤ 1 := by
    exact_mod_cast hdeltaOne
  have hone : 1 ≤ (delta : ENNReal) ^ (-p) :=
    ENNReal.one_le_rpow_of_pos_of_le_one_of_neg
      (ENNReal.coe_pos.mpr hdelta) hdeltaOneENN (by linarith)
  unfold stickyFiberContractedJohnSourceClosedLoss
  calc
    480000 * (128 * (93312 * C)) + 2 ≤
        480000 * (128 * (93312 * (delta : ENNReal) ^ (-p))) +
          2 * (delta : ENNReal) ^ (-p) := by
      apply add_le_add
      · gcongr
      · calc
          (2 : ENNReal) = 2 * 1 := by norm_num
          _ ≤ 2 * (delta : ENNReal) ^ (-p) :=
            mul_le_mul le_rfl hone bot_le bot_le
    _ = contractedJohnSourceClosedLossFixedConstant *
          (delta : ENNReal) ^ (-p) := by
      unfold contractedJohnSourceClosedLossFixedConstant
      ring

theorem stickyFiberContractedJohnSourceClosedLoss_le_negativePower
    {delta : NNReal} {C : ENNReal} {p a : Real}
    (hdelta : 0 < delta) (hdeltaOne : delta ≤ 1)
    (hp : 0 < p) (ha : 0 < a)
    (hsmall : delta ≤ contractedJohnSourceClosedLossThreshold a)
    (hC : C ≤ (delta : ENNReal) ^ (-p)) :
    stickyFiberContractedJohnSourceClosedLoss C ≤
      (delta : ENNReal) ^ (-(p + a)) := by
  have hfixed : contractedJohnSourceClosedLossFixedConstant ≤
      (delta : ENNReal) ^ (-a) :=
    finiteConstant_le_delta_negativePower
      contractedJohnSourceClosedLossFixedConstant_ne_top ha hdelta hsmall
  have hd0 : (delta : ENNReal) ≠ 0 := ENNReal.coe_ne_zero.mpr hdelta.ne'
  have hdTop : (delta : ENNReal) ≠ ∞ := ENNReal.coe_ne_top
  calc
    stickyFiberContractedJohnSourceClosedLoss C ≤
        contractedJohnSourceClosedLossFixedConstant *
          (delta : ENNReal) ^ (-p) :=
      stickyFiberContractedJohnSourceClosedLoss_le_fixed_mul_rpow
        hdelta hdeltaOne hp hC
    _ ≤ (delta : ENNReal) ^ (-a) * (delta : ENNReal) ^ (-p) := by
      gcongr
    _ = (delta : ENNReal) ^ (-(p + a)) := by
      rw [show -(p + a) = -a + -p by ring,
        ENNReal.rpow_add _ _ hd0 hdTop]

theorem stickyFiberContractedJohnSourceBase_le_fixed_mul_rpow
    {delta : NNReal} {C : ENNReal} {p : Real}
    (hdelta : 0 < delta) (hdeltaOne : delta ≤ 1) (hp : 0 < p)
    (hC : C ≤ (delta : ENNReal) ^ (-p)) :
    stickyFiberContractedJohnSourceClosedLoss C *
          ((128 * (93312 * C)) * volume (unitBallBody : Set Space)) ≤
      contractedJohnSourceBaseFixedConstant *
        (delta : ENNReal) ^ (-(2 * p)) := by
  have hloss := stickyFiberContractedJohnSourceClosedLoss_le_fixed_mul_rpow
    hdelta hdeltaOne hp hC
  have hd0 : (delta : ENNReal) ≠ 0 := ENNReal.coe_ne_zero.mpr hdelta.ne'
  have hdTop : (delta : ENNReal) ≠ ∞ := ENNReal.coe_ne_top
  calc
    stickyFiberContractedJohnSourceClosedLoss C *
          ((128 * (93312 * C)) * volume (unitBallBody : Set Space)) ≤
        (contractedJohnSourceClosedLossFixedConstant *
            (delta : ENNReal) ^ (-p)) *
          ((128 * (93312 * (delta : ENNReal) ^ (-p))) * 8) := by
      gcongr
      exact volume_unitBallBody_le_eight
    _ = contractedJohnSourceBaseFixedConstant *
          ((delta : ENNReal) ^ (-p) * (delta : ENNReal) ^ (-p)) := by
      unfold contractedJohnSourceBaseFixedConstant
      ring
    _ = contractedJohnSourceBaseFixedConstant *
          (delta : ENNReal) ^ (-(2 * p)) := by
      rw [show -(2 * p) = -p + -p by ring,
        ENNReal.rpow_add _ _ hd0 hdTop]

theorem stickyFiberContractedJohnSourceBase_le_negativePower
    {delta : NNReal} {C : ENNReal} {p a : Real}
    (hdelta : 0 < delta) (hdeltaOne : delta ≤ 1)
    (hp : 0 < p) (ha : 0 < a)
    (hsmall : delta ≤ contractedJohnSourceBaseThreshold a)
    (hC : C ≤ (delta : ENNReal) ^ (-p)) :
    stickyFiberContractedJohnSourceClosedLoss C *
          ((128 * (93312 * C)) * volume (unitBallBody : Set Space)) ≤
      (delta : ENNReal) ^ (-(2 * p + a)) := by
  have hfixed : contractedJohnSourceBaseFixedConstant ≤
      (delta : ENNReal) ^ (-a) :=
    finiteConstant_le_delta_negativePower
      contractedJohnSourceBaseFixedConstant_ne_top ha hdelta hsmall
  have hd0 : (delta : ENNReal) ≠ 0 := ENNReal.coe_ne_zero.mpr hdelta.ne'
  have hdTop : (delta : ENNReal) ≠ ∞ := ENNReal.coe_ne_top
  calc
    stickyFiberContractedJohnSourceClosedLoss C *
          ((128 * (93312 * C)) * volume (unitBallBody : Set Space)) ≤
        contractedJohnSourceBaseFixedConstant *
          (delta : ENNReal) ^ (-(2 * p)) :=
      stickyFiberContractedJohnSourceBase_le_fixed_mul_rpow
        hdelta hdeltaOne hp hC
    _ ≤ (delta : ENNReal) ^ (-a) *
          (delta : ENNReal) ^ (-(2 * p)) := by
      gcongr
    _ = (delta : ENNReal) ^ (-(2 * p + a)) := by
      rw [show -(2 * p + a) = -a + -(2 * p) by ring,
        ENNReal.rpow_add _ _ hd0 hdTop]

#print axioms stickyFiberContractedJohnSourceClosedLoss_le_fixed_mul_rpow
#print axioms stickyFiberContractedJohnSourceClosedLoss_le_negativePower
#print axioms stickyFiberContractedJohnSourceBase_le_fixed_mul_rpow
#print axioms stickyFiberContractedJohnSourceBase_le_negativePower

end
end Family8StickyFiberContractedJohnSourcePowerEnvelopeV4
