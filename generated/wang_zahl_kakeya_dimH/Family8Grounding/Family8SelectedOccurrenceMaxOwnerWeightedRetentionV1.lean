import Family8Grounding.Family8SelectedOccurrenceMaxOwnerHullAggregateV2
import Family8Grounding.Family8DoubledParentConflictWeightedRetentionV3
import Mathlib.Tactic

/-!
# Weighted conflict retention for genuine quality-selected occurrence owners

The weight on an active coarse parent is the exact refined shaded mass of
the occurrence blocks whose finite-argmax witness has that actual sticky
parent.  Consequently the existing doubled-parent greedy extraction applies
without a parent-purity callback.  Restriction to selected owners is an exact
finite partition of the refined occurrence mass.
-/

open Set MeasureTheory
open scoped BigOperators ENNReal NNReal

namespace Family8SelectedOccurrenceMaxOwnerWeightedRetentionV1

open LeanEval.Analysis.WangZahlKakeya
open Submission.Kakeya.ConvexGeometry
open Submission.Kakeya.ConvexFactoring
open Submission.Kakeya.ConvexFactoring.FullConvexMaximalDensity
open Submission.Kakeya.ConvexFactoring.GreedyOccurrenceFactorization
open Submission.Kakeya.Uniformity
open Family8DoubledParentConflictWeightedRetentionV3.ScaleCover
open Family8SelectedOccurrenceActiveParentOwnerV7
open Family8SelectedOccurrenceDensityFrostmanV1
open Family8SelectedOccurrenceMaxOwnerHullQualityV3
open Family8SelectedOccurrenceMaxOwnerHullAggregateV2
open FamilyStickyAtEveryScaleCoreV1

noncomputable section

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 5000000

local instance (p : Prop) : Decidable p := Classical.propDecidable p

variable {delta rho : NNReal} {index : Type}
  [Fintype index] [DecidableEq index]
  {fine : UniformTubeFamily delta index}
  (C : StickyScaleCover fine rho)
  (P : GreedyDensityPartition fine.bodyFamily
    (hullCandidates C.activeFine) (hullContainer fine.bodyFamily)
    C.activeFine)
  (Y : Shading fine.bodyFamily)

/-- The finite-argmax witness of an occurrence is an actual active fine
index. -/
theorem occurrenceMaxShadedWitness_mem_active
    (k : Fin (blocks fine.bodyFamily P).length) :
    occurrenceMaxShadedWitness C P Y k ∈ C.activeFine :=
  blockAt_fiber_subset_active fine.bodyFamily P k
    (occurrenceMaxShadedWitness_mem C P Y k)

/-- Hence its quality-selected owner is a literal active coarse parent. -/
theorem occurrenceMaxOwner_mem_activeCoarse
    (k : Fin (blocks fine.bodyFamily P).length) :
    occurrenceMaxOwner C P Y k ∈ C.activeCoarse :=
  C.parent_mem _ (occurrenceMaxShadedWitness_mem_active C P Y k)

/-- Exact refined occurrence mass grouped by the quality-selected actual
parent. -/
def occurrenceMaxOwnerMass
    (R : Finset (Fin (blocks fine.bodyFamily P).length))
    (p : Fin C.coarseCard) : ENNReal :=
  ∑ k ∈ R.filter (fun k => occurrenceMaxOwner C P Y k = p),
    volume (occurrenceMaxOwnerCarrier C P Y k)

/-- Occurrences whose quality-selected actual owner belongs to `B`. -/
def occurrencesMaxOwnedBy
    (R : Finset (Fin (blocks fine.bodyFamily P).length))
    (B : Finset (Fin C.coarseCard)) :
    Finset (Fin (blocks fine.bodyFamily P).length) :=
  R.filter fun k => occurrenceMaxOwner C P Y k ∈ B

@[simp] theorem mem_occurrencesMaxOwnedBy
    (R : Finset (Fin (blocks fine.bodyFamily P).length))
    (B : Finset (Fin C.coarseCard))
    (k : Fin (blocks fine.bodyFamily P).length) :
    k ∈ occurrencesMaxOwnedBy C P Y R B ↔
      k ∈ R ∧ occurrenceMaxOwner C P Y k ∈ B := by
  simp [occurrencesMaxOwnedBy]

/-- Quality-selected ownership transported to selected occurrence labels. -/
noncomputable def selectedOccurrenceMaxOwner
    (R : Finset (Fin (blocks fine.bodyFamily P).length))
    (q : {q // q ∈ selectedOccurrenceIndices P R}) : Fin C.coarseCard :=
  occurrenceMaxOwner C P Y (selectedOccurrencePosition C R q)

theorem selectedOccurrenceMaxOwner_mem_activeCoarse
    (R : Finset (Fin (blocks fine.bodyFamily P).length))
    (q : {q // q ∈ selectedOccurrenceIndices P R}) :
    selectedOccurrenceMaxOwner C P Y R q ∈ C.activeCoarse :=
  occurrenceMaxOwner_mem_activeCoarse C P Y
    (selectedOccurrencePosition C R q)

/-- Grouping over all active parents is an exact finite partition. -/
theorem sum_occurrenceMaxOwnerMass_eq
    (R : Finset (Fin (blocks fine.bodyFamily P).length)) :
    (∑ p ∈ C.activeCoarse, occurrenceMaxOwnerMass C P Y R p) =
      ∑ k ∈ R, volume (occurrenceMaxOwnerCarrier C P Y k) := by
  classical
  simpa [occurrenceMaxOwnerMass] using
    (Finset.sum_fiberwise_of_maps_to
      (s := R) (t := C.activeCoarse)
      (g := occurrenceMaxOwner C P Y)
      (fun k _hk => occurrenceMaxOwner_mem_activeCoarse C P Y k)
      (fun k => volume (occurrenceMaxOwnerCarrier C P Y k)))

/-- The same exact partition after restricting the target owner set. -/
theorem sum_occurrenceMaxOwnerMass_eq_owned
    (R : Finset (Fin (blocks fine.bodyFamily P).length))
    (B : Finset (Fin C.coarseCard)) :
    (∑ p ∈ B, occurrenceMaxOwnerMass C P Y R p) =
      ∑ k ∈ occurrencesMaxOwnedBy C P Y R B,
        volume (occurrenceMaxOwnerCarrier C P Y k) := by
  classical
  let owned := occurrencesMaxOwnedBy C P Y R B
  have hpartition := Finset.sum_fiberwise_of_maps_to
    (s := owned) (t := B)
    (g := occurrenceMaxOwner C P Y)
    (fun k hk => (mem_occurrencesMaxOwnedBy C P Y R B k).mp hk |>.2)
    (fun k => volume (occurrenceMaxOwnerCarrier C P Y k))
  calc
    (∑ p ∈ B, occurrenceMaxOwnerMass C P Y R p) =
        ∑ p ∈ B, ∑ k ∈ owned.filter
          (fun k => occurrenceMaxOwner C P Y k = p),
            volume (occurrenceMaxOwnerCarrier C P Y k) := by
      apply Finset.sum_congr rfl
      intro p hp
      unfold occurrenceMaxOwnerMass
      apply Finset.sum_congr
      · ext k
        simp only [owned, occurrencesMaxOwnedBy, Finset.mem_filter]
        constructor
        · rintro ⟨hkR, hkp⟩
          exact ⟨⟨hkR, hkp ▸ hp⟩, hkp⟩
        · rintro ⟨⟨hkR, _hkB⟩, hkp⟩
          exact ⟨hkR, hkp⟩
      · intro k _hk
        rfl
    _ = ∑ k ∈ owned,
        volume (occurrenceMaxOwnerCarrier C P Y k) := hpartition
    _ = ∑ k ∈ occurrencesMaxOwnedBy C P Y R B,
        volume (occurrenceMaxOwnerCarrier C P Y k) := rfl

/-- Membership of the selected quality owner is automatic after restricting
the occurrence set by the selector's chosen parent set. -/
theorem selectedOccurrenceMaxOwner_mem_selected_of_owned
    (R : Finset (Fin (blocks fine.bodyFamily P).length))
    (loss : ENNReal)
    (W : DoubledParentConflictWeightedSelection C
      (occurrenceMaxOwnerMass C P Y R) loss)
    (q : {q // q ∈ selectedOccurrenceIndices P
      (occurrencesMaxOwnedBy C P Y R W.selected)}) :
    selectedOccurrenceMaxOwner C P Y
        (occurrencesMaxOwnedBy C P Y R W.selected) q ∈ W.selected := by
  exact (mem_occurrencesMaxOwnedBy C P Y R W.selected
    (selectedOccurrencePosition C
      (occurrencesMaxOwnedBy C P Y R W.selected) q)).mp
        (selectedOccurrencePosition_mem C
          (occurrencesMaxOwnedBy C P Y R W.selected) q) |>.2

/-- The existing doubled-parent weighted selector retains the exact refined
quality-owner shaded mass with its certified conflict-degree loss. -/
theorem selectedMaxOwner_refinedShadedMass_retention
    (R : Finset (Fin (blocks fine.bodyFamily P).length))
    (loss : ENNReal)
    (W : DoubledParentConflictWeightedSelection C
      (occurrenceMaxOwnerMass C P Y R) loss) :
    (selectedOccurrenceMaxOwnerHullShading C P Y R).shadingMass ≤
      loss * (selectedOccurrenceMaxOwnerHullShading C P Y
        (occurrencesMaxOwnedBy C P Y R W.selected)).shadingMass := by
  rw [selectedOccurrenceMaxOwnerHullShading_mass_eq_sum,
    selectedOccurrenceMaxOwnerHullShading_mass_eq_sum]
  rw [← sum_occurrenceMaxOwnerMass_eq C P Y R,
    ← sum_occurrenceMaxOwnerMass_eq_owned C P Y R W.selected]
  exact W.mass_le

#print axioms occurrenceMaxShadedWitness_mem_active
#print axioms occurrenceMaxOwner_mem_activeCoarse
#print axioms sum_occurrenceMaxOwnerMass_eq
#print axioms sum_occurrenceMaxOwnerMass_eq_owned
#print axioms selectedOccurrenceMaxOwner_mem_selected_of_owned
#print axioms selectedMaxOwner_refinedShadedMass_retention

end

end Family8SelectedOccurrenceMaxOwnerWeightedRetentionV1
