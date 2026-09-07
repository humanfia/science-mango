import Family8Grounding.Family8StickyDensityAwareCanonicalLogPartitionV2
import Family8Grounding.Family8EfficientSelectedBranchingSourceBudgetV2

/-!
# Branching source budget for the canonical logarithmic partition

One canonical selected parent witnesses efficiency and the dyadic fiber cap.
Only the explicit cover-loss absorption remains an input.
-/

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 1200000

open Set MeasureTheory
open scoped ENNReal NNReal BigOperators

namespace Family8StickyDensityAwareCanonicalLogBranchSourceBudgetV1

open LeanEval.Analysis.WangZahlKakeya
open Submission.Kakeya.ConvexFactoring
open Submission.Kakeya.ConvexFactoring.JointTubeFactoring
open Submission.Kakeya.Uniformity
open FamilyStickyAtEveryScaleCoreV1
open FamilyStickyAdjacentScaleStepV2.StickyScaleCover
open Family8EfficientSelectedBranchingSourceBudgetV2
open Family8StickyDensityAwareLogBranchingNNRealAdapterV1
open Family8StickyDensityAwareCanonicalLogBucketChoiceV1
open Family8StickyDensityAwareCanonicalLogBucketSelectedV1
open Family8StickyDensityAwareCanonicalLogPartitionV2

noncomputable section

variable {delta rho : NNReal} {iota : Type}
  [Fintype iota] [DecidableEq iota]
  {fine : UniformTubeFamily delta iota}

/-- A selected efficient parent supplies the branching source budget for the
literal canonical partition. -/
theorem densityAwareLogPartition_branch_sourceBudget
    (S : StickyScaleCover fine rho) (A longTarget : NNReal)
    (hA : 0 < A) (hdelta : 0 < delta) (hrho : 0 < rho)
    (hscale : delta ≤ rho) (hactive : S.activeFine.Nonempty)
    (hdeltaHalf : delta ≤ (2 : NNReal)⁻¹)
    (hrhoHalf : rho ≤ (2 : NNReal)⁻¹)
    (hBranchAbsorb :
      524288 * stickyDensityAwareCoverLossNNReal S A *
          (2 : NNReal) ^ 2 ≤ longTarget) :
    8192 * ((densityAwareLogPartition
        S A hA hdelta hrho hscale hactive).branchingLoss : NNReal) *
        A * rho ^ 2 ≤
      longTarget * ((densityAwareLogPartition
        S A hA hdelta hrho hscale hactive).branching : NNReal) *
        (delta ^ 2 / 2) := by
  let P := densityAwareLogPartition
    S A hA hdelta hrho hscale hactive
  obtain ⟨k, hkP⟩ := P.coarseIndices_nonempty
  have hkSelected : k ∈ densityAwareSelectedParents
      S A hA hdelta hrho hactive := by
    simpa only [P, densityAwareLogPartition_coarseIndices] using hkP
  have hkEfficient : k ∈ efficientParents
      fine S.coarse S.activeFine S.parent (A : ENNReal)
      (stickyDensityAwareCoverLossNNReal S A : ENNReal) :=
    densityAwareSelectedParents_subset_efficient
      S A hA hdelta hrho hactive hkSelected
  have hrawCard :
      ((rawIndexFactorization S.activeFine S.parent).fiber k).card ≤
        2 * logBucketBranching
          (densityAwareLogBucketLevel S A hA hdelta hrho hactive) :=
    Nat.le_of_lt (efficientLogCardBucket_fiber_card_bounds
      fine S.coarse S.activeFine S.parent (A : ENNReal)
      (stickyDensityAwareCoverLossNNReal S A : ENNReal)
      (densityAwareLogBucketLevel S A hA hdelta hrho hactive)
      hkSelected).2
  have hTwo := branching_source_budget_of_efficientParent
    fine S.coarse S.activeFine S.parent A
    (stickyDensityAwareCoverLossNNReal S A) longTarget
    hdeltaHalf hrhoHalf 2
    (logBucketBranching
      (densityAwareLogBucketLevel S A hA hdelta hrho hactive))
    k hkEfficient hrawCard hBranchAbsorb
  simpa only [P, densityAwareLogPartition_branchingLoss,
    densityAwareLogPartition_branching] using hTwo

#print axioms densityAwareLogPartition_branch_sourceBudget

end
end Family8StickyDensityAwareCanonicalLogBranchSourceBudgetV1
