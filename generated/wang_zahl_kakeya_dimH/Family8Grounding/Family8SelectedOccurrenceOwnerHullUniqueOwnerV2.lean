import Family8Grounding.Family8SelectedOccurrenceOwnerHullRefinementV2
import Family8Grounding.Family8SelectedOccurrenceActiveParentOwnerV11
import Mathlib.Tactic

/-!
# Unique ownership for genuine parent-specific occurrence hulls

The representative-owner hull refinement removes the global-block
`ParentPure` callback.  Each refined body has a literal fine witness with the
same actual parent, its admissible thickening is automatically inside the
doubled parent, and the retained parents are pairwise conflict-free.
-/

open Set MeasureTheory
open scoped BigOperators ENNReal NNReal

namespace Family8SelectedOccurrenceOwnerHullUniqueOwnerV2

open LeanEval.Analysis.WangZahlKakeya
open Submission.Kakeya.ConvexGeometry
open Submission.Kakeya.ConvexFactoring
open Submission.Kakeya.ConvexFactoring.FullConvexMaximalDensity
open Submission.Kakeya.ConvexFactoring.GreedyOccurrenceFactorization
open Submission.Kakeya.Uniformity
open Family6AffinePlankAnalyticHypothesesStableV1
open Family8Def212ConvexWolffAtEveryScaleV2
open Family8DoubledParentConflictClusteringV2.ScaleCover
open Family8DoubledParentConflictWeightedRetentionV3.ScaleCover
open Family8SelectedOccurrenceActiveParentOwnerV5
open Family8SelectedOccurrenceActiveParentOwnerV7
open Family8SelectedOccurrenceActiveParentOwnerV9
open Family8SelectedOccurrenceActiveParentOwnerV11
open Family8SelectedOccurrenceDensityFrostmanV1
open Family8SelectedOccurrenceOwnerHullRefinementV2
open Family8UniqueOwnerLocalDeltaMaxThickControlV1
open FamilyStickyAtEveryScaleCoreV1

noncomputable section

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 5000000

local instance (p : Prop) : Decidable p := Classical.propDecidable p

variable {delta rho a b Delta : NNReal} {index : Type}
  [Fintype index] [DecidableEq index]
  {fine : UniformTubeFamily delta index}
  (C : StickyScaleCover fine rho)
  {P : GreedyDensityPartition fine.bodyFamily
    (hullCandidates C.activeFine) (hullContainer fine.bodyFamily)
    C.activeFine}

/-- The literal representative fine tube is contained in the genuine
parent-specific hull of its occurrence. -/
theorem selectedOccurrenceFineWitness_carrier_subset_ownerHull
    (R : Finset (Fin (blocks fine.bodyFamily P).length))
    (q : {q // q ∈ selectedOccurrenceIndices P R}) :
    (fine.tubes (occurrenceFineWitness C P
      (selectedOccurrencePosition C R q))).carrier ⊆
      (selectedOccurrenceOwnerHullFamily C P R q : Set Space) := by
  let k := selectedOccurrencePosition C R q
  have hwitness : occurrenceFineWitness C P k ∈
      occurrenceOwnerSubfiber C P k := by
    rw [mem_occurrenceOwnerSubfiber]
    exact ⟨occurrenceFineWitness_mem C P k, rfl⟩
  change (fine.bodyFamily (occurrenceFineWitness C P k) : Set Space) ⊆
    (hullContainer fine.bodyFamily (occurrenceOwnerSubfiber C P k) : Set Space)
  exact body_subset_hullContainer fine.bodyFamily hwitness
    (occurrenceOwnerSubfiber_nonempty C P k)

/-- Conflict-free actual parents give unique ownership for the genuine
parent-specific owner-hull family, with no global `ParentPure` premise. -/
theorem thickenedPlankUniqueOwner_ownerHull_ownedOccurrences
    (hrho : 0 < rho) (hb : b ≤ rho)
    (Y : Shading fine.bodyFamily)
    (R0 : Finset (Fin (blocks fine.bodyFamily P).length))
    (loss : ENNReal)
    (W : DoubledParentConflictWeightedSelection C
      (occurrenceMassByActiveParent C P Y R0) loss)
    (D : ShadedConvexPlankFamily
      {q // q ∈ selectedOccurrenceIndices P
        (occurrencesOwnedBy C P R0 W.selected)} a b)
    (hfamily : D.family = selectedOccurrenceOwnerHullFamily C P
      (occurrencesOwnedBy C P R0 W.selected)) :
    ThickenedPlankUniqueOwner D
      (selectedOccurrenceActiveParent C
        (occurrencesOwnedBy C P R0 W.selected)) := by
  let R := occurrencesOwnedBy C P R0 W.selected
  have hinside : AdmissibleThickeningInsideOwner C R D
      (selectedOccurrenceActiveParent C R) :=
    admissibleThickeningInsideOwner_of_ownerHullFamily C P hrho hb R D hfamily
  intro theta hthetaLower hthetaUpper i j hj
  by_contra hne
  have hiOwner : selectedOccurrenceActiveParent C R i ∈ W.selected :=
    selectedOccurrenceActiveParent_mem_selected_of_owned C Y R0 loss W i
  have hjOwner : selectedOccurrenceActiveParent C R j ∈ W.selected :=
    selectedOccurrenceActiveParent_mem_selected_of_owned C Y R0 loss W j
  have hjContained : (D.family j : Set Space) ⊆
      Metric.cthickening (((theta * b : NNReal) : Real))
        (D.family i : Set Space) := by
    simpa [thickenedPlankIndices,
      Family6AffinePlankAnalyticHypothesesStableV1.containedIndices] using
        (Finset.mem_filter.mp hj).2
  let witness := occurrenceFineWitness C P
    (selectedOccurrencePosition C R j)
  have hwitnessActive : witness ∈ C.activeFine :=
    occurrenceFineWitness_mem_active C P _
  have hwitnessBody : (fine.tubes witness).carrier ⊆
      (D.family j : Set Space) := by
    rw [hfamily]
    exact selectedOccurrenceFineWitness_carrier_subset_ownerHull
      (P := P) C R j
  have hiDouble : (fine.tubes witness).carrier ⊆
      twoFoldTubeCarrier
        (C.coarse.tubes (selectedOccurrenceActiveParent C R i)) :=
    hwitnessBody.trans (hjContained.trans
      (hinside theta hthetaLower hthetaUpper i))
  have hwitnessParent : C.parent witness =
      selectedOccurrenceActiveParent C R j := rfl
  have hjParent : (fine.tubes witness).carrier ⊆
      (C.coarse.tubes (selectedOccurrenceActiveParent C R j)).carrier := by
    have hparent := C.carrier_subset witness hwitnessActive
    rw [hwitnessParent] at hparent
    exact hparent
  have hjDouble : (fine.tubes witness).carrier ⊆
      twoFoldTubeCarrier
        (C.coarse.tubes (selectedOccurrenceActiveParent C R j)) :=
    hjParent.trans (carrier_subset_twoFoldTubeCarrier
      (C.coarse.tubes (selectedOccurrenceActiveParent C R j)))
  exact W.selected_pairwise hiOwner hjOwner (fun h => hne h.symm)
    ⟨witness, hwitnessActive, hiDouble, hjDouble⟩

/-- Adding genuine Katz--Tao control on the literal owner fibres produces the
full stable thick-plank count for the refined hull family. -/
theorem frostmanThickenedPlankControl_ownerHull_ownedOccurrences
    (hrho : 0 < rho) (hb : b ≤ rho)
    (Y : Shading fine.bodyFamily)
    (R0 : Finset (Fin (blocks fine.bodyFamily P).length))
    (loss : ENNReal)
    (W : DoubledParentConflictWeightedSelection C
      (occurrenceMassByActiveParent C P Y R0) loss)
    (D : ShadedConvexPlankFamily
      {q // q ∈ selectedOccurrenceIndices P
        (occurrencesOwnedBy C P R0 W.selected)} a b)
    (hfamily : D.family = selectedOccurrenceOwnerHullFamily C P
      (occurrencesOwnedBy C P R0 W.selected))
    (hlocal : OwnerFiberIsKatzTao (Delta := Delta) C D
      (selectedOccurrenceActiveParent C
        (occurrencesOwnedBy C P R0 W.selected))) :
    FrostmanThickenedPlankControl D
      (uniqueOwnerLocalDeltaThickM D.comparisonConstant Delta a b) := by
  apply frostmanThickenedPlankControl_of_uniqueOwner_localDeltaMax D
    (selectedOccurrenceActiveParent C
      (occurrencesOwnedBy C P R0 W.selected))
  · exact thickenedPlankUniqueOwner_ownerHull_ownedOccurrences C hrho hb Y R0
      loss W D hfamily
  · exact ownerFiberDeltaMax_le_of_ownerFiberIsKatzTao
      (Delta := Delta) C D
      (selectedOccurrenceActiveParent C
        (occurrencesOwnedBy C P R0 W.selected)) hlocal

#print axioms selectedOccurrenceFineWitness_carrier_subset_ownerHull
#print axioms thickenedPlankUniqueOwner_ownerHull_ownedOccurrences
#print axioms frostmanThickenedPlankControl_ownerHull_ownedOccurrences

end


end Family8SelectedOccurrenceOwnerHullUniqueOwnerV2
