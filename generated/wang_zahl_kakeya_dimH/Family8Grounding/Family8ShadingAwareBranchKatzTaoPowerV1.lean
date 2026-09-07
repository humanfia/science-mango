import Family8Grounding.Family8StickyShadingAwareCanonicalLogBranchSourceBudgetV2
import Family8Grounding.Family8GeneralBranchingDiscreteLongIntervalBootstrapV2
import Family8Grounding.Family8StickyShadingAwareCoverLossPowerEnvelopeV1
import FamilyStickyGrounding.FamilyStickyScaleChainSmallDeltaExponentBudgetProducerV1
import Mathlib.Tactic

/-!
# Selected coarse Katz--Tao power from the shading-aware branch budget

The genuine general-branching Katz--Tao constant is the source constant
divided by the literal lower parent-mass density.  The shading-aware branch
source budget clears exactly that denominator.  This module instantiates its
target by an explicit delta power obtained from the honest shading cover-loss
envelope and absorbs only the fixed scalar `524288 * 2^2`.
-/

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 2600000

open Set MeasureTheory
open scoped BigOperators ENNReal NNReal

namespace Family8ShadingAwareBranchKatzTaoPowerV1

open LeanEval.Analysis.WangZahlKakeya
open Submission.Kakeya.ConvexGeometry
open Submission.Kakeya.ConvexFactoring
open Submission.Kakeya.Uniformity
open Family8GeneralBranchingDiscreteLongIntervalBootstrapV2
open Family8GeneralBranchingLowerParentMassV1
open Family8StickyShadingAwareCanonicalLogBranchSourceBudgetV2
open Family8StickyShadingAwareCanonicalLogPartitionV1
open Family8StickyShadingAwareCoverLossPowerEnvelopeV1
open Family8StickyShadingAwareLogBucketSelectionV1
open FamilyStickyAtEveryScaleCoreV1
open FamilyStickyScaleChainSmallDeltaExponentBudgetProducerV1

noncomputable section

variable {delta rho : NNReal} {index : Type}
  [Fintype index] [DecidableEq index]
  {fine : UniformTubeFamily delta index}

def shadingAwareBranchKatzTaoPowerFixedConstant : ENNReal :=
  524288 * 4

def shadingAwareBranchKatzTaoPowerThreshold
    (absorbExponent : Real) : NNReal :=
  finiteConstantSmallDeltaThreshold
    shadingAwareBranchKatzTaoPowerFixedConstant absorbExponent

theorem shadingAwareBranchKatzTaoPowerThreshold_pos
    (absorbExponent : Real) :
    0 < shadingAwareBranchKatzTaoPowerThreshold absorbExponent :=
  finiteConstantSmallDeltaThreshold_pos _ _

theorem shadingAwareBranchKatzTaoPowerFixedConstant_ne_top :
    shadingAwareBranchKatzTaoPowerFixedConstant ≠ ∞ := by
  norm_num [shadingAwareBranchKatzTaoPowerFixedConstant]

/-- The actual coarse Katz--Tao constant of the same selected partition is
bounded by the cover-loss power plus one fixed-constant absorption power. -/
theorem shadingAwareLogPartition_coarseKatzTao_le_delta_negativePower
    (S : StickyScaleCover fine rho) (Y : Shading fine.bodyFamily)
    (sourceA : NNReal) (hsourceA : 0 < sourceA)
    (hdelta : 0 < delta) (hdeltaHalf : delta ≤ (2 : NNReal)⁻¹)
    (hrho : 0 < rho) (hscale : delta ≤ rho)
    (hactive : S.activeFine.Nonempty)
    (hmass : shadingMassOn Y S.activeFine ≠ 0)
    (hrhoHalf : rho ≤ (2 : NNReal)⁻¹)
    {coverExponent absorbExponent : Real}
    (hcover : stickyShadingAwareCoverLoss S Y (sourceA : ENNReal) ≤
      (delta : ENNReal) ^ (-coverExponent))
    (habsorbExponent : 0 < absorbExponent)
    (hsmall : delta ≤
      shadingAwareBranchKatzTaoPowerThreshold absorbExponent) :
    let Ppart := shadingAwareLogPartition
      S Y (sourceA : ENNReal)
        (ENNReal.coe_ne_zero.mpr hsourceA.ne') ENNReal.coe_ne_top
        hrho hscale hactive hmass
    (branchingLossCoarseKatzTaoNNReal sourceA Ppart : ENNReal) ≤
      (delta : ENNReal) ^ (-(coverExponent + absorbExponent)) := by
  dsimp only
  let Ppart := shadingAwareLogPartition
    S Y (sourceA : ENNReal)
      (ENNReal.coe_ne_zero.mpr hsourceA.ne') ENNReal.coe_ne_top
      hrho hscale hactive hmass
  let targetE : ENNReal :=
    (delta : ENNReal) ^ (-(coverExponent + absorbExponent))
  let target : NNReal := targetE.toNNReal
  have hd0 : (delta : ENNReal) ≠ 0 :=
    ENNReal.coe_ne_zero.mpr hdelta.ne'
  have htargetTop : targetE ≠ ∞ := by
    dsimp only [targetE]
    exact ENNReal.rpow_ne_top_of_ne_zero hd0 ENNReal.coe_ne_top
  have htargetCoe : (target : ENNReal) = targetE := by
    dsimp only [target]
    exact ENNReal.coe_toNNReal htargetTop
  have hfixed : shadingAwareBranchKatzTaoPowerFixedConstant ≤
      (delta : ENNReal) ^ (-absorbExponent) :=
    finiteConstant_le_delta_negativePower
      shadingAwareBranchKatzTaoPowerFixedConstant_ne_top
      habsorbExponent hdelta hsmall
  have habsorbE :
      (524288 : ENNReal) *
          stickyShadingAwareCoverLoss S Y (sourceA : ENNReal) * 2 ^ 2 ≤
        targetE := by
    calc
      (524288 : ENNReal) *
          stickyShadingAwareCoverLoss S Y (sourceA : ENNReal) * 2 ^ 2 =
        shadingAwareBranchKatzTaoPowerFixedConstant *
          stickyShadingAwareCoverLoss S Y (sourceA : ENNReal) := by
            norm_num [shadingAwareBranchKatzTaoPowerFixedConstant]
            ring
      _ ≤ (delta : ENNReal) ^ (-absorbExponent) *
          (delta : ENNReal) ^ (-coverExponent) :=
        mul_le_mul' hfixed hcover
      _ = targetE := by
        dsimp only [targetE]
        rw [← ENNReal.rpow_add _ _ hd0 ENNReal.coe_ne_top]
        congr 1
        ring
  have habsorbNN :
      524288 * stickyShadingAwareCoverLossNNReal S Y sourceA *
          (2 : NNReal) ^ 2 ≤ target := by
    apply ENNReal.coe_le_coe.mp
    simpa only [ENNReal.coe_mul, ENNReal.coe_ofNat, ENNReal.coe_pow,
      coe_stickyShadingAwareCoverLossNNReal S Y sourceA hmass,
      htargetCoe] using habsorbE
  have hbranchBudget :=
    shadingAwareLogPartition_branch_sourceBudget
      S Y sourceA target hsourceA hrho hscale hactive hmass
      hdeltaHalf hrhoHalf habsorbNN
  have hcoarseNN :=
    branchingLossCoarseKatzTao_longBudget_of_branchingBudget
      Ppart hdelta hrho sourceA target hbranchBudget
  have hcoarseE :
      (1024 : ENNReal) *
          (branchingLossCoarseKatzTaoNNReal sourceA Ppart : ENNReal) ≤
        targetE := by
    have hcast := ENNReal.coe_le_coe.mpr hcoarseNN
    simpa only [ENNReal.coe_mul, ENNReal.coe_ofNat, htargetCoe] using hcast
  calc
    (branchingLossCoarseKatzTaoNNReal sourceA Ppart : ENNReal) =
        1 * (branchingLossCoarseKatzTaoNNReal sourceA Ppart : ENNReal) := by
          rw [one_mul]
    _ ≤ (1024 : ENNReal) *
        (branchingLossCoarseKatzTaoNNReal sourceA Ppart : ENNReal) :=
      mul_le_mul' (by norm_num) le_rfl
    _ ≤ targetE := hcoarseE

#print axioms shadingAwareBranchKatzTaoPowerThreshold_pos
#print axioms shadingAwareBranchKatzTaoPowerFixedConstant_ne_top
#print axioms
  shadingAwareLogPartition_coarseKatzTao_le_delta_negativePower

end
end Family8ShadingAwareBranchKatzTaoPowerV1
