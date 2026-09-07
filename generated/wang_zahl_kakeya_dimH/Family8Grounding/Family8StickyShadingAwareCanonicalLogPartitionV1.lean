import Family8Grounding.Family8StickyShadingAwareCanonicalLogRestrictedFamiliesV1
import Mathlib.Tactic

/-!
# Literal partition for the canonical shading-aware logarithmic bucket

This is the exact selected parent map produced by the shading-mass weighted
selector.  Its branching, active indices, retained shading mass, and source
floor all refer to the same literal partition.
-/

open Set MeasureTheory
open scoped BigOperators ENNReal NNReal

namespace Family8StickyShadingAwareCanonicalLogPartitionV1

open LeanEval.Analysis.WangZahlKakeya
open Submission.Kakeya.ConvexGeometry
open Submission.Kakeya.ConvexFactoring
open Submission.Kakeya.ConvexFactoring.JointTubeFactoring
open Submission.Kakeya.Uniformity
open FamilyStickyAtEveryScaleCoreV1
open FamilyStickyAdjacentScaleStepV2.StickyScaleCover
open Family8StickyShadingAwareLogBucketSelectionV1
open Family8StickyShadingAwareCanonicalLogBucketSelectedV1
open Family8StickyShadingAwareCanonicalLogRestrictedFamiliesV1

noncomputable section

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 1200000

variable {delta rho : NNReal} {iota : Type*}
  [Fintype iota] [DecidableEq iota]
  {fine : UniformTubeFamily delta iota}

/-- The exact selected partition; its parent map is definitionally the actual
Sticky parent map. -/
def shadingAwareLogPartition
    (S : StickyScaleCover fine rho) (Y : Shading fine.bodyFamily)
    (A : ENNReal) (hA0 : A ≠ 0) (hAtop : A ≠ ∞)
    (hrho : 0 < rho) (hscale : delta ≤ rho)
    (hactive : S.activeFine.Nonempty)
    (hmass : shadingMassOn Y S.activeFine ≠ 0) :
    CoarseTubePartition
      (shadingAwareSelectedFineFamily
        S Y A hA0 hAtop hrho hactive hmass)
      (shadingAwareSelectedCoarseFamily
        S Y A hA0 hAtop hrho hactive hmass) where
  scale_le := hscale
  index := selectedIndexFactorization S.activeFine S.parent
    (shadingAwareSelectedParents
      S Y A hA0 hAtop hrho hactive hmass)
  fine_eq_refined := rfl
  coarse_eq_refined := rfl
  coarse_nonempty := shadingAwareSelectedParents_nonempty
    S Y A hA0 hAtop hrho hactive hmass
  carrier_subset := by
    intro i hi
    have hiActive : i ∈ S.activeFine := (Finset.mem_filter.mp hi).1
    change
      ((shadingAwareSelectedFineFamily
        S Y A hA0 hAtop hrho hactive hmass).tubes i).carrier ⊆
      ((shadingAwareSelectedCoarseFamily
        S Y A hA0 hAtop hrho hactive hmass).tubes
          (S.parent i)).carrier
    simpa only [shadingAwareSelectedFineFamily_tubes,
      shadingAwareSelectedCoarseFamily_tubes] using
        S.carrier_subset i hiActive
  parent_surjective := by
    intro k hk
    exact shadingAwareSelected_parent_surjective_restricted
      S Y A hA0 hAtop hrho hactive hmass k hk
  branching := logBucketBranching
    (shadingAwareLogBucketLevel
      S Y A hA0 hAtop hrho hactive hmass)
  branching_pos := by
    unfold logBucketBranching
    positivity
  branchingLoss := 2
  branchingLoss_pos := by norm_num
  branching_le_loss_mul_fiber := by
    intro k hk
    have hbounds := shadingAwareSelected_fiber_bounds
      S Y A hA0 hAtop hrho hactive hmass k hk
    rw [selected_fiber_eq_raw_fiber S.activeFine S.parent
      (shadingAwareSelectedParents
        S Y A hA0 hAtop hrho hactive hmass) hk]
    omega
  fiber_card_le_loss_mul_branching := by
    intro k hk
    have hbounds := shadingAwareSelected_fiber_bounds
      S Y A hA0 hAtop hrho hactive hmass k hk
    rw [selected_fiber_eq_raw_fiber S.activeFine S.parent
      (shadingAwareSelectedParents
        S Y A hA0 hAtop hrho hactive hmass) hk]
    exact Nat.le_of_lt hbounds.2

@[simp] theorem shadingAwareLogPartition_index
    (S : StickyScaleCover fine rho) (Y : Shading fine.bodyFamily)
    (A : ENNReal) (hA0 : A ≠ 0) (hAtop : A ≠ ∞)
    (hrho : 0 < rho) (hscale : delta ≤ rho)
    (hactive : S.activeFine.Nonempty)
    (hmass : shadingMassOn Y S.activeFine ≠ 0) :
    (shadingAwareLogPartition
      S Y A hA0 hAtop hrho hscale hactive hmass).index =
      selectedIndexFactorization S.activeFine S.parent
        (shadingAwareSelectedParents
          S Y A hA0 hAtop hrho hactive hmass) :=
  rfl

@[simp] theorem shadingAwareLogPartition_branching
    (S : StickyScaleCover fine rho) (Y : Shading fine.bodyFamily)
    (A : ENNReal) (hA0 : A ≠ 0) (hAtop : A ≠ ∞)
    (hrho : 0 < rho) (hscale : delta ≤ rho)
    (hactive : S.activeFine.Nonempty)
    (hmass : shadingMassOn Y S.activeFine ≠ 0) :
    (shadingAwareLogPartition
      S Y A hA0 hAtop hrho hscale hactive hmass).branching =
      logBucketBranching
        (shadingAwareLogBucketLevel
          S Y A hA0 hAtop hrho hactive hmass) :=
  rfl

@[simp] theorem shadingAwareLogPartition_branchingLoss
    (S : StickyScaleCover fine rho) (Y : Shading fine.bodyFamily)
    (A : ENNReal) (hA0 : A ≠ 0) (hAtop : A ≠ ∞)
    (hrho : 0 < rho) (hscale : delta ≤ rho)
    (hactive : S.activeFine.Nonempty)
    (hmass : shadingMassOn Y S.activeFine ≠ 0) :
    (shadingAwareLogPartition
      S Y A hA0 hAtop hrho hscale hactive hmass).branchingLoss = 2 :=
  rfl

@[simp] theorem shadingAwareLogPartition_fineIndices
    (S : StickyScaleCover fine rho) (Y : Shading fine.bodyFamily)
    (A : ENNReal) (hA0 : A ≠ 0) (hAtop : A ≠ ∞)
    (hrho : 0 < rho) (hscale : delta ≤ rho)
    (hactive : S.activeFine.Nonempty)
    (hmass : shadingMassOn Y S.activeFine ≠ 0) :
    (shadingAwareLogPartition
      S Y A hA0 hAtop hrho hscale hactive hmass).fineIndices =
      shadingAwareSelectedFine
        S Y A hA0 hAtop hrho hactive hmass :=
  rfl

@[simp] theorem shadingAwareLogPartition_coarseIndices
    (S : StickyScaleCover fine rho) (Y : Shading fine.bodyFamily)
    (A : ENNReal) (hA0 : A ≠ 0) (hAtop : A ≠ ∞)
    (hrho : 0 < rho) (hscale : delta ≤ rho)
    (hactive : S.activeFine.Nonempty)
    (hmass : shadingMassOn Y S.activeFine ≠ 0) :
    (shadingAwareLogPartition
      S Y A hA0 hAtop hrho hscale hactive hmass).coarseIndices =
      shadingAwareSelectedParents
        S Y A hA0 hAtop hrho hactive hmass :=
  rfl

/-- Actual source shading mass retained by this very partition. -/
theorem shadingAwareLogPartition_shadingMass_withinFactor
    (S : StickyScaleCover fine rho) (Y : Shading fine.bodyFamily)
    (A : ENNReal) (hA0 : A ≠ 0) (hAtop : A ≠ ∞)
    (hrho : 0 < rho) (hscale : delta ≤ rho)
    (hactive : S.activeFine.Nonempty)
    (hmass : shadingMassOn Y S.activeFine ≠ 0) :
    WithinFactor (2 * (Nat.log 2 (Fintype.card iota) + 1))
      (shadingMassOn Y S.activeFine)
      (shadingMassOn Y
        (shadingAwareLogPartition
          S Y A hA0 hAtop hrho hscale hactive hmass).fineIndices) := by
  simpa only [shadingAwareLogPartition_fineIndices] using
    shadingAwareSelectedFine_withinFactor
      S Y A hA0 hAtop hrho hactive hmass

/-- Explicit selected source floor for the same literal partition. -/
theorem shadingAwareLogPartition_sourceFloor
    (S : StickyScaleCover fine rho) (Y : Shading fine.bodyFamily)
    (A : ENNReal) (hA0 : A ≠ 0) (hAtop : A ≠ ∞)
    (hrho : 0 < rho) (hscale : delta ≤ rho)
    (hactive : S.activeFine.Nonempty)
    (hmass : shadingMassOn Y S.activeFine ≠ 0) :
    shadingMassOn Y S.activeFine /
        (2 * (Nat.log 2 (Fintype.card iota) + 1) : Nat) ≤
      shadingMassOn Y
        (shadingAwareLogPartition
          S Y A hA0 hAtop hrho hscale hactive hmass).fineIndices := by
  simpa only [shadingAwareLogPartition_fineIndices] using
    shadingAwareSelectedFine_sourceFloor
      S Y A hA0 hAtop hrho hactive hmass

/-- Exact dyadic fiber bounds on the literal selected partition. -/
theorem shadingAwareLogPartition_fiber_bounds
    (S : StickyScaleCover fine rho) (Y : Shading fine.bodyFamily)
    (A : ENNReal) (hA0 : A ≠ 0) (hAtop : A ≠ ∞)
    (hrho : 0 < rho) (hscale : delta ≤ rho)
    (hactive : S.activeFine.Nonempty)
    (hmass : shadingMassOn Y S.activeFine ≠ 0) :
    ∀ k ∈ (shadingAwareLogPartition
        S Y A hA0 hAtop hrho hscale hactive hmass).coarseIndices,
      logBucketBranching
          (shadingAwareLogBucketLevel
            S Y A hA0 hAtop hrho hactive hmass) ≤
        ((shadingAwareLogPartition
          S Y A hA0 hAtop hrho hscale hactive hmass).fiber k).card ∧
      ((shadingAwareLogPartition
          S Y A hA0 hAtop hrho hscale hactive hmass).fiber k).card <
        2 * logBucketBranching
          (shadingAwareLogBucketLevel
            S Y A hA0 hAtop hrho hactive hmass) := by
  intro k hk
  change k ∈ shadingAwareSelectedParents
    S Y A hA0 hAtop hrho hactive hmass at hk
  change logBucketBranching
        (shadingAwareLogBucketLevel
          S Y A hA0 hAtop hrho hactive hmass) ≤
      ((selectedIndexFactorization S.activeFine S.parent
        (shadingAwareSelectedParents
          S Y A hA0 hAtop hrho hactive hmass)).fiber k).card ∧
    ((selectedIndexFactorization S.activeFine S.parent
      (shadingAwareSelectedParents
        S Y A hA0 hAtop hrho hactive hmass)).fiber k).card <
      2 * logBucketBranching
        (shadingAwareLogBucketLevel
          S Y A hA0 hAtop hrho hactive hmass)
  rw [selected_fiber_eq_raw_fiber S.activeFine S.parent
    (shadingAwareSelectedParents
      S Y A hA0 hAtop hrho hactive hmass) hk]
  exact shadingAwareSelected_fiber_bounds
    S Y A hA0 hAtop hrho hactive hmass k hk

#print axioms shadingAwareLogPartition
#print axioms shadingAwareLogPartition_index
#print axioms shadingAwareLogPartition_branching
#print axioms shadingAwareLogPartition_branchingLoss
#print axioms shadingAwareLogPartition_fineIndices
#print axioms shadingAwareLogPartition_coarseIndices
#print axioms shadingAwareLogPartition_shadingMass_withinFactor
#print axioms shadingAwareLogPartition_sourceFloor
#print axioms shadingAwareLogPartition_fiber_bounds

end
end Family8StickyShadingAwareCanonicalLogPartitionV1
