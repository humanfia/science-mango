import Family8Grounding.Family8PaperEq45SelectedOccurrenceBundleV3
import Family8Grounding.Family8DoubledParentConflictWeightedRetentionV3
import Family8Grounding.Family8Prop51SelectedOccurrenceSourceFrostmanV1
import Mathlib.Tactic

/-!
# Actual active-parent ownership for selected occurrences

The generic occurrence API has no scale cover and therefore no `T_rho`
owner.  Here every nonempty greedy block is assigned the actual
`StickyScaleCover.parent` of a literal fine member.  `ParentPure` is the
essential condition supplied by a fibrewise greedy construction: every fine
member of the whole block has that same owner.

The existing doubled-parent weighted selection is fed the exact outer shaded
mass grouped by these actual owners.  Its arbitrary-ENNReal weight inequality
then yields literal selected-occurrence shaded-mass retention with the exact
conflict-degree loss.
-/

open Set MeasureTheory
open scoped BigOperators ENNReal NNReal

namespace Family8SelectedOccurrenceActiveParentOwnerV5

open LeanEval.Analysis.WangZahlKakeya
open Submission.Kakeya.ConvexGeometry
open Submission.Kakeya.ConvexFactoring
open Submission.Kakeya.ConvexFactoring.FullConvexMaximalDensity
open Submission.Kakeya.ConvexFactoring.GreedyOccurrenceFactorization
open Submission.Kakeya.Uniformity
open Family8DoubledParentConflictWeightedRetentionV3.ScaleCover
open Family8GreedyOccurrenceOuterDatumV1
open Family8Prop51JointOccurrenceWeightedSelectionV1
open Family8SelectedOccurrenceDensityFrostmanV1
open FamilyStickyAtEveryScaleCoreV1

noncomputable section

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 5000000

local instance (p : Prop) : Decidable p := Classical.propDecidable p

variable {delta rho : NNReal} {index : Type}
  [Fintype index] [DecidableEq index]
  {fine : UniformTubeFamily delta index}

variable (C : StickyScaleCover fine rho)
  (P : GreedyDensityPartition fine.bodyFamily
    (hullCandidates C.activeFine) (hullContainer fine.bodyFamily)
    C.activeFine)

/-- A literal fine member of a nonempty greedy occurrence fibre. -/
noncomputable def occurrenceFineWitness
    (k : Fin (blocks fine.bodyFamily P).length) : index :=
  Classical.choose (blockAt fine.bodyFamily P k).fiber_nonempty

theorem occurrenceFineWitness_mem
    (k : Fin (blocks fine.bodyFamily P).length) :
    occurrenceFineWitness C P k ∈ (blockAt fine.bodyFamily P k).fiber :=
  Classical.choose_spec (blockAt fine.bodyFamily P k).fiber_nonempty

theorem occurrenceFineWitness_mem_active
    (k : Fin (blocks fine.bodyFamily P).length) :
    occurrenceFineWitness C P k ∈ C.activeFine :=
  blockAt_fiber_subset_active fine.bodyFamily P k
    (occurrenceFineWitness_mem C P k)

/-- The actual active `T_rho` parent of the chosen fine member. -/
noncomputable def occurrenceActiveParent
    (k : Fin (blocks fine.bodyFamily P).length) : Fin C.coarseCard :=
  C.parent (occurrenceFineWitness C P k)

theorem occurrenceActiveParent_mem_activeCoarse
    (k : Fin (blocks fine.bodyFamily P).length) :
    occurrenceActiveParent C P k ∈ C.activeCoarse :=
  C.parent_mem _ (occurrenceFineWitness_mem_active C P k)

/-- The whole occurrence block, not merely its representative, has one
actual active parent. -/
def ParentPure : Prop :=
  ∀ k : Fin (blocks fine.bodyFamily P).length,
    ∀ i, i ∈ (blockAt fine.bodyFamily P k).fiber →
      C.parent i = occurrenceActiveParent C P k

/-- Exact outer occurrence mass grouped by literal active parent. -/
def occurrenceMassByActiveParent
    (Y : Shading fine.bodyFamily)
    (R : Finset (Fin (blocks fine.bodyFamily P).length))
    (p : Fin C.coarseCard) : ENNReal :=
  ∑ k ∈ R.filter (fun k => occurrenceActiveParent C P k = p),
    occurrenceOuterShadedMass P Y k

/-- Occurrences whose actual owner belongs to a selected parent set. -/
def occurrencesOwnedBy
    (R : Finset (Fin (blocks fine.bodyFamily P).length))
    (B : Finset (Fin C.coarseCard)) :
    Finset (Fin (blocks fine.bodyFamily P).length) :=
  R.filter fun k => occurrenceActiveParent C P k ∈ B

@[simp] theorem mem_occurrencesOwnedBy
    (R : Finset (Fin (blocks fine.bodyFamily P).length))
    (B : Finset (Fin C.coarseCard))
    (k : Fin (blocks fine.bodyFamily P).length) :
    k ∈ occurrencesOwnedBy C P R B ↔
      k ∈ R ∧ occurrenceActiveParent C P k ∈ B := by
  simp [occurrencesOwnedBy]

/-- Grouping by actual parent is an exact finite partition. -/
theorem sum_occurrenceMassByActiveParent_eq
    (Y : Shading fine.bodyFamily)
    (R : Finset (Fin (blocks fine.bodyFamily P).length)) :
    (∑ p ∈ C.activeCoarse, occurrenceMassByActiveParent C P Y R p) =
      ∑ k ∈ R, occurrenceOuterShadedMass P Y k := by
  classical
  simpa [occurrenceMassByActiveParent] using
    (Finset.sum_fiberwise_of_maps_to
      (s := R) (t := C.activeCoarse)
      (g := occurrenceActiveParent C P)
      (fun k _hk => occurrenceActiveParent_mem_activeCoarse C P k)
      (fun k => occurrenceOuterShadedMass P Y k))

/-- The same exact partition after restricting the target parent set. -/
theorem sum_occurrenceMassByActiveParent_eq_owned
    (Y : Shading fine.bodyFamily)
    (R : Finset (Fin (blocks fine.bodyFamily P).length))
    (B : Finset (Fin C.coarseCard)) :
    (∑ p ∈ B, occurrenceMassByActiveParent C P Y R p) =
      ∑ k ∈ occurrencesOwnedBy C P R B,
        occurrenceOuterShadedMass P Y k := by
  classical
  let owned := occurrencesOwnedBy C P R B
  have hpartition := Finset.sum_fiberwise_of_maps_to
    (s := owned) (t := B)
    (g := occurrenceActiveParent C P)
    (fun k hk => (mem_occurrencesOwnedBy C P R B k).mp hk |>.2)
    (fun k => occurrenceOuterShadedMass P Y k)
  calc
    (∑ p ∈ B, occurrenceMassByActiveParent C P Y R p) =
        ∑ p ∈ B, ∑ k ∈ owned.filter
          (fun k => occurrenceActiveParent C P k = p),
            occurrenceOuterShadedMass P Y k := by
      apply Finset.sum_congr rfl
      intro p hp
      unfold occurrenceMassByActiveParent
      apply Finset.sum_congr
      · ext k
        simp only [owned, occurrencesOwnedBy, Finset.mem_filter]
        constructor
        · rintro ⟨hkR, hkp⟩
          exact ⟨⟨hkR, hkp ▸ hp⟩, hkp⟩
        · rintro ⟨⟨hkR, _hkB⟩, hkp⟩
          exact ⟨hkR, hkp⟩
      · intro k _hk
        rfl
    _ = ∑ k ∈ owned, occurrenceOuterShadedMass P Y k := hpartition
    _ = ∑ k ∈ occurrencesOwnedBy C P R B,
        occurrenceOuterShadedMass P Y k := rfl

/-- Weighted doubled-parent selection gives literal outer occurrence
shaded-mass retention with exactly its certified degree loss. -/
theorem selectedOwner_occurrenceShadedMass_retention
    (Y : Shading fine.bodyFamily)
    (R : Finset (Fin (blocks fine.bodyFamily P).length))
    (loss : ENNReal)
    (W : DoubledParentConflictWeightedSelection C
      (occurrenceMassByActiveParent C P Y R) loss) :
    (selectedOccurrenceOuterShading P Y R).shadingMass ≤
      loss * (selectedOccurrenceOuterShading P Y
        (occurrencesOwnedBy C P R W.selected)).shadingMass := by
  rw [selectedOccurrenceOuterShading_mass_eq_sum_occurrenceOuterShadedMass,
    selectedOccurrenceOuterShading_mass_eq_sum_occurrenceOuterShadedMass]
  rw [← sum_occurrenceMassByActiveParent_eq C P Y R,
    ← sum_occurrenceMassByActiveParent_eq_owned C P Y R W.selected]
  exact W.mass_le

#print axioms occurrenceFineWitness_mem
#print axioms occurrenceActiveParent_mem_activeCoarse
#print axioms sum_occurrenceMassByActiveParent_eq
#print axioms sum_occurrenceMassByActiveParent_eq_owned
#print axioms selectedOwner_occurrenceShadedMass_retention

end

end Family8SelectedOccurrenceActiveParentOwnerV5
