import Family8Grounding.Family8StickyShadingAwareCanonicalLogPartitionV1
import Family8Grounding.Family8EfficientSelectedBranchingSourceBudgetV2
import Mathlib.Tactic

/-!
# Branching source budget for the shading-aware logarithmic partition, V2

The finite shading-aware cover loss is converted to `NNReal`.  One parent in
the nonempty selected bucket is body-efficient and has the literal dyadic
fiber cap, so the generic branching budget applies to this same partition.
-/

open Set MeasureTheory
open scoped ENNReal NNReal BigOperators

namespace Family8StickyShadingAwareCanonicalLogBranchSourceBudgetV2

open LeanEval.Analysis.WangZahlKakeya
open Submission.Kakeya.ConvexGeometry
open Submission.Kakeya.ConvexFactoring
open Submission.Kakeya.ConvexFactoring.JointTubeFactoring
open Submission.Kakeya.Uniformity
open Family8EfficientSelectedBranchingSourceBudgetV2
open Family8StickyShadingAwareLogBucketSelectionV1
open Family8StickyShadingAwareCanonicalLogBucketSelectedV1
open Family8StickyShadingAwareCanonicalLogPartitionV1
open FamilyStickyAtEveryScaleCoreV1

noncomputable section

set_option autoImplicit false
set_option warningAsError true
set_option linter.unusedSectionVars false
set_option maxHeartbeats 1800000

variable {delta rho : NNReal} {index : Type}
  [Fintype index] [DecidableEq index]
  {fine : UniformTubeFamily delta index}

noncomputable def stickyShadingAwareCoverLossNNReal
    (S : StickyScaleCover fine rho) (Y : Shading fine.bodyFamily)
    (sourceA : NNReal) : NNReal :=
  (stickyShadingAwareCoverLoss S Y (sourceA : ENNReal)).toNNReal

@[simp] theorem coe_stickyShadingAwareCoverLossNNReal
    (S : StickyScaleCover fine rho) (Y : Shading fine.bodyFamily)
    (sourceA : NNReal)
    (hmass : shadingMassOn Y S.activeFine ≠ 0) :
    (stickyShadingAwareCoverLossNNReal S Y sourceA : ENNReal) =
      stickyShadingAwareCoverLoss S Y (sourceA : ENNReal) := by
  exact ENNReal.coe_toNNReal
    (stickyShadingAwareCoverLoss_ne_top
      S Y ENNReal.coe_ne_top hmass)

theorem shadingAwareLogPartition_branch_sourceBudget
    (S : StickyScaleCover fine rho) (Y : Shading fine.bodyFamily)
    (sourceA longTarget : NNReal) (hsourceA : 0 < sourceA)
    (hrho : 0 < rho) (hscale : delta ≤ rho)
    (hactive : S.activeFine.Nonempty)
    (hmass : shadingMassOn Y S.activeFine ≠ 0)
    (hdeltaHalf : delta ≤ (2 : NNReal)⁻¹)
    (hrhoHalf : rho ≤ (2 : NNReal)⁻¹)
    (hBranchAbsorb :
      524288 * stickyShadingAwareCoverLossNNReal S Y sourceA *
          (2 : NNReal) ^ 2 ≤ longTarget) :
    8192 * ((shadingAwareLogPartition
        S Y (sourceA : ENNReal)
          (ENNReal.coe_ne_zero.mpr hsourceA.ne') ENNReal.coe_ne_top
          hrho hscale hactive hmass).branchingLoss : NNReal) *
        sourceA * rho ^ 2 ≤
      longTarget * ((shadingAwareLogPartition
        S Y (sourceA : ENNReal)
          (ENNReal.coe_ne_zero.mpr hsourceA.ne') ENNReal.coe_ne_top
          hrho hscale hactive hmass).branching : NNReal) *
        (delta ^ 2 / 2) := by
  let Ppart := shadingAwareLogPartition
    S Y (sourceA : ENNReal)
      (ENNReal.coe_ne_zero.mpr hsourceA.ne') ENNReal.coe_ne_top
      hrho hscale hactive hmass
  obtain ⟨k, hkP⟩ := Ppart.coarseIndices_nonempty
  have hkSelected : k ∈ shadingAwareSelectedParents
      S Y (sourceA : ENNReal)
        (ENNReal.coe_ne_zero.mpr hsourceA.ne') ENNReal.coe_ne_top
        hrho hactive hmass := by
    simpa only [Ppart, shadingAwareLogPartition_coarseIndices] using hkP
  have hkEfficient : k ∈ efficientParents
      fine S.coarse S.activeFine S.parent (sourceA : ENNReal)
      (stickyShadingAwareCoverLossNNReal S Y sourceA : ENNReal) := by
    simpa only [coe_stickyShadingAwareCoverLossNNReal S Y sourceA hmass] using
      (shadingAwareSelectedParents_subset_efficient
        S Y (sourceA : ENNReal)
          (ENNReal.coe_ne_zero.mpr hsourceA.ne') ENNReal.coe_ne_top
          hrho hactive hmass hkSelected)
  have hrawCard :
      ((rawIndexFactorization S.activeFine S.parent).fiber k).card ≤
        2 * logBucketBranching
          (shadingAwareLogBucketLevel
            S Y (sourceA : ENNReal)
              (ENNReal.coe_ne_zero.mpr hsourceA.ne') ENNReal.coe_ne_top
              hrho hactive hmass) :=
    Nat.le_of_lt (shadingAwareSelected_fiber_bounds
      S Y (sourceA : ENNReal)
        (ENNReal.coe_ne_zero.mpr hsourceA.ne') ENNReal.coe_ne_top
        hrho hactive hmass k hkSelected).2
  have hbudget := branching_source_budget_of_efficientParent
    fine S.coarse S.activeFine S.parent sourceA
    (stickyShadingAwareCoverLossNNReal S Y sourceA) longTarget
    hdeltaHalf hrhoHalf 2
    (logBucketBranching
      (shadingAwareLogBucketLevel
        S Y (sourceA : ENNReal)
          (ENNReal.coe_ne_zero.mpr hsourceA.ne') ENNReal.coe_ne_top
          hrho hactive hmass))
    k hkEfficient hrawCard hBranchAbsorb
  simpa only [Ppart, shadingAwareLogPartition_branchingLoss,
    shadingAwareLogPartition_branching] using hbudget

#print axioms stickyShadingAwareCoverLossNNReal
#print axioms coe_stickyShadingAwareCoverLossNNReal
#print axioms shadingAwareLogPartition_branch_sourceBudget

end
end Family8StickyShadingAwareCanonicalLogBranchSourceBudgetV2
