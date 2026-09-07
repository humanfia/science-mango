import Family8Grounding.Family8StickyDensityAwareCanonicalLogRestrictedFamiliesV2
import Mathlib.Tactic

/-!
# Canonical same-object logarithmic partition

The already chosen density-aware logarithmic bucket is packaged directly as a
literal `CoarseTubePartition`.  No large joint-factoring existential is
unpacked here.
-/

open Set MeasureTheory
open scoped BigOperators ENNReal NNReal

namespace Family8StickyDensityAwareCanonicalLogPartitionV2

open LeanEval.Analysis.WangZahlKakeya
open Submission.Kakeya.ConvexGeometry
open Submission.Kakeya.ConvexFactoring
open Submission.Kakeya.ConvexFactoring.JointTubeFactoring
open Submission.Kakeya.Uniformity
open FamilyStickyAtEveryScaleCoreV1
open FamilyStickyAdjacentScaleStepV2.StickyScaleCover
open Family8StickyDensityAwareLogBranchingNNRealAdapterV1
open Family8StickyDensityAwareCanonicalLogBucketChoiceV1
open Family8StickyDensityAwareCanonicalLogBucketSelectedV1
open Family8StickyDensityAwareCanonicalLogRestrictedFamiliesV2

noncomputable section

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 1200000

variable {delta rho : NNReal} {iota : Type*}
  [Fintype iota] [DecidableEq iota]
  {fine : UniformTubeFamily delta iota}

/-- The literal selected partition associated to the canonical logarithmic
bucket.  Its parent map is definitionally the actual Sticky parent map. -/
def densityAwareLogPartition
    (S : StickyScaleCover fine rho) (A : NNReal)
    (hA : 0 < A) (hdelta : 0 < delta) (hrho : 0 < rho)
    (hscale : delta ≤ rho) (hactive : S.activeFine.Nonempty) :
    CoarseTubePartition
      (densityAwareSelectedFineFamily S A hA hdelta hrho hactive)
      (densityAwareSelectedCoarseFamily S A hA hdelta hrho hactive) where
  scale_le := hscale
  index := selectedIndexFactorization S.activeFine S.parent
    (densityAwareSelectedParents S A hA hdelta hrho hactive)
  fine_eq_refined := rfl
  coarse_eq_refined := rfl
  coarse_nonempty := densityAwareSelectedParents_nonempty
    S A hA hdelta hrho hactive
  carrier_subset := by
    intro i hi
    have hiActive : i ∈ S.activeFine := (Finset.mem_filter.mp hi).1
    change
      ((densityAwareSelectedFineFamily
        S A hA hdelta hrho hactive).tubes i).carrier ⊆
      ((densityAwareSelectedCoarseFamily
        S A hA hdelta hrho hactive).tubes (S.parent i)).carrier
    simpa only [densityAwareSelectedFineFamily_tubes,
      densityAwareSelectedCoarseFamily_tubes] using
        S.carrier_subset i hiActive
  parent_surjective := by
    intro k hk
    exact densityAwareSelected_parent_surjective
      S A hA hdelta hrho hactive k hk
  branching := logBucketBranching
    (densityAwareLogBucketLevel S A hA hdelta hrho hactive)
  branching_pos := by
    unfold logBucketBranching
    positivity
  branchingLoss := 2
  branchingLoss_pos := by norm_num
  branching_le_loss_mul_fiber := by
    intro k hk
    have hbounds := efficientLogCardBucket_fiber_card_bounds
      fine S.coarse S.activeFine S.parent (A : ENNReal)
      (stickyDensityAwareCoverLossNNReal S A : ENNReal)
      (densityAwareLogBucketLevel S A hA hdelta hrho hactive) hk
    rw [selected_fiber_eq_raw_fiber S.activeFine S.parent
      (densityAwareSelectedParents S A hA hdelta hrho hactive) hk]
    omega
  fiber_card_le_loss_mul_branching := by
    intro k hk
    have hbounds := efficientLogCardBucket_fiber_card_bounds
      fine S.coarse S.activeFine S.parent (A : ENNReal)
      (stickyDensityAwareCoverLossNNReal S A : ENNReal)
      (densityAwareLogBucketLevel S A hA hdelta hrho hactive) hk
    rw [selected_fiber_eq_raw_fiber S.activeFine S.parent
      (densityAwareSelectedParents S A hA hdelta hrho hactive) hk]
    exact Nat.le_of_lt hbounds.2

@[simp] theorem densityAwareLogPartition_index
    (S : StickyScaleCover fine rho) (A : NNReal)
    (hA : 0 < A) (hdelta : 0 < delta) (hrho : 0 < rho)
    (hscale : delta ≤ rho) (hactive : S.activeFine.Nonempty) :
    (densityAwareLogPartition S A hA hdelta hrho hscale hactive).index =
      selectedIndexFactorization S.activeFine S.parent
        (densityAwareSelectedParents S A hA hdelta hrho hactive) :=
  rfl

@[simp] theorem densityAwareLogPartition_branching
    (S : StickyScaleCover fine rho) (A : NNReal)
    (hA : 0 < A) (hdelta : 0 < delta) (hrho : 0 < rho)
    (hscale : delta ≤ rho) (hactive : S.activeFine.Nonempty) :
    (densityAwareLogPartition S A hA hdelta hrho hscale hactive).branching =
      logBucketBranching
        (densityAwareLogBucketLevel S A hA hdelta hrho hactive) :=
  rfl

@[simp] theorem densityAwareLogPartition_branchingLoss
    (S : StickyScaleCover fine rho) (A : NNReal)
    (hA : 0 < A) (hdelta : 0 < delta) (hrho : 0 < rho)
    (hscale : delta ≤ rho) (hactive : S.activeFine.Nonempty) :
    (densityAwareLogPartition
      S A hA hdelta hrho hscale hactive).branchingLoss = 2 :=
  rfl

@[simp] theorem densityAwareLogPartition_fineIndices
    (S : StickyScaleCover fine rho) (A : NNReal)
    (hA : 0 < A) (hdelta : 0 < delta) (hrho : 0 < rho)
    (hscale : delta ≤ rho) (hactive : S.activeFine.Nonempty) :
    (densityAwareLogPartition
      S A hA hdelta hrho hscale hactive).fineIndices =
      densityAwareSelectedFine S A hA hdelta hrho hactive :=
  rfl

@[simp] theorem densityAwareLogPartition_coarseIndices
    (S : StickyScaleCover fine rho) (A : NNReal)
    (hA : 0 < A) (hdelta : 0 < delta) (hrho : 0 < rho)
    (hscale : delta ≤ rho) (hactive : S.activeFine.Nonempty) :
    (densityAwareLogPartition
      S A hA hdelta hrho hscale hactive).coarseIndices =
      densityAwareSelectedParents S A hA hdelta hrho hactive :=
  rfl

/-- The canonical partition retains the selected fine body mass. -/
theorem densityAwareLogPartition_bodyMass_withinFactor
    (S : StickyScaleCover fine rho) (A : NNReal)
    (hA : 0 < A) (hdelta : 0 < delta) (hrho : 0 < rho)
    (hscale : delta ≤ rho) (hactive : S.activeFine.Nonempty) :
    WithinFactor (2 * (Nat.log 2 (Fintype.card iota) + 1))
      (bodyMassOn fine.bodyFamily S.activeFine)
      (bodyMassOn
        (densityAwareSelectedFineFamily
          S A hA hdelta hrho hactive).bodyFamily
        (densityAwareLogPartition
          S A hA hdelta hrho hscale hactive).fineIndices) := by
  change WithinFactor (2 * (Nat.log 2 (Fintype.card iota) + 1))
    (bodyMassOn fine.bodyFamily S.activeFine)
    (bodyMassOn fine.bodyFamily
      (densityAwareSelectedFine S A hA hdelta hrho hactive))
  exact densityAwareSelectedFine_bodyMass_withinFactor
    S A hA hdelta hrho hactive

/-- Exact dyadic fiber bounds for every parent of the canonical partition. -/
theorem densityAwareLogPartition_fiber_bounds
    (S : StickyScaleCover fine rho) (A : NNReal)
    (hA : 0 < A) (hdelta : 0 < delta) (hrho : 0 < rho)
    (hscale : delta ≤ rho) (hactive : S.activeFine.Nonempty) :
    ∀ k ∈ (densityAwareLogPartition
        S A hA hdelta hrho hscale hactive).coarseIndices,
      logBucketBranching
          (densityAwareLogBucketLevel S A hA hdelta hrho hactive) ≤
        ((densityAwareLogPartition
          S A hA hdelta hrho hscale hactive).fiber k).card ∧
      ((densityAwareLogPartition
          S A hA hdelta hrho hscale hactive).fiber k).card <
        2 * logBucketBranching
          (densityAwareLogBucketLevel S A hA hdelta hrho hactive) := by
  intro k hk
  change k ∈ densityAwareSelectedParents
    S A hA hdelta hrho hactive at hk
  change logBucketBranching
        (densityAwareLogBucketLevel S A hA hdelta hrho hactive) ≤
      ((selectedIndexFactorization S.activeFine S.parent
        (densityAwareSelectedParents S A hA hdelta hrho hactive)).fiber k).card ∧
    ((selectedIndexFactorization S.activeFine S.parent
      (densityAwareSelectedParents S A hA hdelta hrho hactive)).fiber k).card <
      2 * logBucketBranching
        (densityAwareLogBucketLevel S A hA hdelta hrho hactive)
  rw [selected_fiber_eq_raw_fiber S.activeFine S.parent
    (densityAwareSelectedParents S A hA hdelta hrho hactive) hk]
  exact efficientLogCardBucket_fiber_card_bounds
    fine S.coarse S.activeFine S.parent (A : ENNReal)
    (stickyDensityAwareCoverLossNNReal S A : ENNReal)
    (densityAwareLogBucketLevel S A hA hdelta hrho hactive) hk

#print axioms densityAwareLogPartition
#print axioms densityAwareLogPartition_index
#print axioms densityAwareLogPartition_branching
#print axioms densityAwareLogPartition_branchingLoss
#print axioms densityAwareLogPartition_fineIndices
#print axioms densityAwareLogPartition_coarseIndices
#print axioms densityAwareLogPartition_bodyMass_withinFactor
#print axioms densityAwareLogPartition_fiber_bounds

end
end Family8StickyDensityAwareCanonicalLogPartitionV2
