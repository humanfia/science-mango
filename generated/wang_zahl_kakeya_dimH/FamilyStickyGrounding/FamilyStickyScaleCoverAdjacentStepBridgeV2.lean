import FamilyStickyGrounding.FamilyStickyScaleChainBufferedHierarchyNormalizedV1

set_option autoImplicit false
set_option warningAsError true

open Set
open scoped ENNReal NNReal

namespace FamilyStickyScaleCoverAdjacentStepBridgeV2

open Submission.Kakeya.ConvexFactoring
open Submission.Kakeya.Uniformity
open FamilyStickyAtEveryScaleCoreV1
open FamilyStickyDeltaMaxFiniteChainV2
open FamilyStickyDeltaMaxFiniteChainV2.StickyScaleCover

noncomputable section

/-!
# Sticky-scale covers as exact adjacent hierarchy steps

`StickyScaleCover` already contains the parent map, its active-index
surjectivity, and literal carrier containment.  Thus it contains all of the
geometric data of an exact `AdjacentTubeStep.partition`.  The two facts not
stored by that structure are supplied explicitly below: the radius ordering
`delta <= rho` and nonemptiness of the active coarse family.

The quantitative branching fields of `CoarseTubePartition` do not require a
new hypothesis.  We use target branching one and the finite loss
`S.activeFine.card`.  Surjectivity makes every active fiber nonempty, while
every fiber is a subset of `S.activeFine`.
-/

variable {delta rho : NNReal} {iota : Type*}
  [Fintype iota] [DecidableEq iota]
  {fine : UniformTubeFamily delta iota}

/-- The index factorization already present in a Sticky scale cover. -/
def coverIndexFactorization (S : StickyScaleCover fine rho) :
    IndexFactorization iota (Fin S.coarseCard) where
  fine := S.activeFine
  coarse := S.activeCoarse
  parent := S.parent
  parent_mem := S.parent_mem

/-- The total active fine cardinality is a sufficient common fiber loss. -/
def coverBranchingLoss (S : StickyScaleCover fine rho) : Nat :=
  S.activeFine.card

theorem activeFine_nonempty_of_activeCoarse_nonempty
    (S : StickyScaleCover fine rho) (hcoarse : S.activeCoarse.Nonempty) :
    S.activeFine.Nonempty := by
  obtain ⟨k, hk⟩ := hcoarse
  obtain ⟨i, hi, _hparent⟩ := S.parent_surjective k hk
  exact ⟨i, hi⟩

theorem coverBranchingLoss_pos (S : StickyScaleCover fine rho)
    (hcoarse : S.activeCoarse.Nonempty) : 0 < coverBranchingLoss S := by
  exact Finset.card_pos.mpr
    (activeFine_nonempty_of_activeCoarse_nonempty S hcoarse)

/-- Turn a nonempty Sticky scale cover into an actual exact coarse tube
partition.  No analytic or geometric conclusion is added as an input: all
such fields are copied from `S`; only the scale ordering and the nonempty
coarse endpoint were absent from `StickyScaleCover` itself. -/
def toCoarseTubePartition (S : StickyScaleCover fine rho)
    (hscale : delta <= rho) (hcoarse : S.activeCoarse.Nonempty) :
    CoarseTubePartition fine S.coarse where
  scale_le := hscale
  index := coverIndexFactorization S
  fine_eq_refined := S.activeFine_eq_refined
  coarse_eq_refined := S.activeCoarse_eq_refined
  coarse_nonempty := hcoarse
  carrier_subset := S.carrier_subset
  parent_surjective := S.parent_surjective
  branching := 1
  branching_pos := Nat.zero_lt_one
  branchingLoss := coverBranchingLoss S
  branchingLoss_pos := coverBranchingLoss_pos S hcoarse
  branching_le_loss_mul_fiber := by
    intro k hk
    obtain ⟨i, hi, hparent⟩ := S.parent_surjective k hk
    have hfiber : (S.fiber k).Nonempty :=
      ⟨i, (S.mem_fiber i k).2 ⟨hi, hparent⟩⟩
    have hloss : 1 <= coverBranchingLoss S :=
      Finset.one_le_card.mpr
        (activeFine_nonempty_of_activeCoarse_nonempty S hcoarse)
    have hcard : 1 <= (S.fiber k).card := Finset.one_le_card.mpr hfiber
    change 1 <= coverBranchingLoss S * (S.fiber k).card
    simpa only [one_mul] using Nat.mul_le_mul hloss hcard
  fiber_card_le_loss_mul_branching := by
    intro k _hk
    change (S.fiber k).card <= coverBranchingLoss S * 1
    rw [Nat.mul_one]
    exact Finset.card_le_card (Finset.filter_subset _ _)

/-- The exact partition constructor is named `AdjacentTubeStep.partition` in
the repository (the alternative constructor is `commonFine`). -/
def toAdjacentTubeStep (S : StickyScaleCover fine rho)
    (hscale : delta <= rho) (hcoarse : S.activeCoarse.Nonempty) :
    AdjacentTubeStep fine S.coarse :=
  .partition (toCoarseTubePartition S hscale hcoarse)

@[simp] theorem toCoarseTubePartition_fineIndices
    (S : StickyScaleCover fine rho)
    (hscale : delta <= rho) (hcoarse : S.activeCoarse.Nonempty) :
    (toCoarseTubePartition S hscale hcoarse).fineIndices = S.activeFine := by
  rfl

@[simp] theorem toCoarseTubePartition_coarseIndices
    (S : StickyScaleCover fine rho)
    (hscale : delta <= rho) (hcoarse : S.activeCoarse.Nonempty) :
    (toCoarseTubePartition S hscale hcoarse).coarseIndices =
      S.activeCoarse := by
  rfl

@[simp] theorem toCoarseTubePartition_parent
    (S : StickyScaleCover fine rho)
    (hscale : delta <= rho) (hcoarse : S.activeCoarse.Nonempty)
    (i : iota) :
    (toCoarseTubePartition S hscale hcoarse).index.parent i = S.parent i := by
  rfl

@[simp] theorem toCoarseTubePartition_fiber
    (S : StickyScaleCover fine rho)
    (hscale : delta <= rho) (hcoarse : S.activeCoarse.Nonempty)
    (k : Fin S.coarseCard) :
    (toCoarseTubePartition S hscale hcoarse).fiber k = S.fiber k := by
  rfl

@[simp] theorem toAdjacentTubeStep_parentIndex
    (S : StickyScaleCover fine rho)
    (hscale : delta <= rho) (hcoarse : S.activeCoarse.Nonempty)
    (i : iota) :
    (toAdjacentTubeStep S hscale hcoarse).parentIndex i = S.parent i := by
  rfl

@[simp] theorem toAdjacentTubeStep_rawCost
    (S : StickyScaleCover fine rho)
    (hscale : delta <= rho) (hcoarse : S.activeCoarse.Nonempty) :
    (toAdjacentTubeStep S hscale hcoarse).rawCost = 0 := by
  rfl

/-- Apply the repository's existing partition-to-Sticky normalization to the
partition produced above. -/
def normalizedRoundTrip (S : StickyScaleCover fine rho)
    (hscale : delta <= rho) (hcoarse : S.activeCoarse.Nonempty) :
    StickyScaleCover fine rho :=
  FamilyStickyScaleChainBufferedHierarchyNormalizedV1.StickyScaleCover.ofCoarseTubePartition
    (toCoarseTubePartition S hscale hcoarse)

/-- Normalization loses no part of the original Sticky cover.  In particular,
the parent, fibers, coarse tube family, and all quantities defined from them
are preserved, not merely bounded in one direction. -/
theorem normalizedRoundTrip_eq (S : StickyScaleCover fine rho)
    (hscale : delta <= rho) (hcoarse : S.activeCoarse.Nonempty) :
    normalizedRoundTrip S hscale hcoarse = S := by
  cases S with
  | mk coarseCard coarse activeFine activeCoarse parent
      activeFine_eq_refined activeCoarse_eq_refined parent_mem
      parent_surjective carrier_subset =>
    subst activeFine
    subst activeCoarse
    rfl

@[simp] theorem normalizedRoundTrip_parent
    (S : StickyScaleCover fine rho)
    (hscale : delta <= rho) (hcoarse : S.activeCoarse.Nonempty)
    (i : iota) :
    (normalizedRoundTrip S hscale hcoarse).parent i = S.parent i := by
  rfl

@[simp] theorem normalizedRoundTrip_fiber
    (S : StickyScaleCover fine rho)
    (hscale : delta <= rho) (hcoarse : S.activeCoarse.Nonempty)
    (k : Fin S.coarseCard) :
    (normalizedRoundTrip S hscale hcoarse).fiber k = S.fiber k := by
  change fine.refinement.refined.filter (fun i => S.parent i = k) =
    S.activeFine.filter (fun i => S.parent i = k)
  exact (congrArg
    (fun s : Finset iota => s.filter (fun i => S.parent i = k))
    S.activeFine_eq_refined).symm

@[simp] theorem normalizedRoundTrip_coarse
    (S : StickyScaleCover fine rho)
    (hscale : delta <= rho) (hcoarse : S.activeCoarse.Nonempty) :
    (normalizedRoundTrip S hscale hcoarse).coarse = S.coarse := by
  rfl

@[simp] theorem normalizedRoundTrip_fiberDeltaMax
    (S : StickyScaleCover fine rho)
    (hscale : delta <= rho) (hcoarse : S.activeCoarse.Nonempty) :
    fiberDeltaMax (normalizedRoundTrip S hscale hcoarse) = fiberDeltaMax S := by
  rw [normalizedRoundTrip_eq]

@[simp] theorem normalizedRoundTrip_coarseDeltaMax
    (S : StickyScaleCover fine rho)
    (hscale : delta <= rho) (hcoarse : S.activeCoarse.Nonempty) :
    coarseDeltaMax (normalizedRoundTrip S hscale hcoarse) = coarseDeltaMax S := by
  rw [normalizedRoundTrip_eq]

#print axioms toCoarseTubePartition
#print axioms toAdjacentTubeStep
#print axioms normalizedRoundTrip_eq
#print axioms normalizedRoundTrip_fiberDeltaMax
#print axioms normalizedRoundTrip_coarseDeltaMax

end

end FamilyStickyScaleCoverAdjacentStepBridgeV2
