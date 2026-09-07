import Family8Grounding.Family8SelectedOccurrenceMaxOwnerWeightedRetentionV1
import Family8Grounding.Family8SelectedOccurrenceActiveParentOwnerV11
import Family8Grounding.Family8TubeClosedThickeningInsideTwoFoldV2
import Mathlib.Tactic

/-!
# Unique ownership and local Delta control for quality-owner hulls

The finite-argmax witness, its actual sticky parent, the parent-specific
closed convex hull, and the owner used by the doubled-conflict selector are
the same data.  Thus no global-block `ParentPure`, inclusion callback, or
thick-count callback is used.
-/

open Set MeasureTheory
open scoped BigOperators ENNReal NNReal

namespace Family8SelectedOccurrenceMaxOwnerHullUniqueOwnerV2

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
open Family8SelectedOccurrenceActiveParentOwnerV7
open Family8SelectedOccurrenceActiveParentOwnerV9
open Family8SelectedOccurrenceActiveParentOwnerV11
open Family8SelectedOccurrenceDensityFrostmanV1
open Family8SelectedOccurrenceMaxOwnerHullQualityV3
open Family8SelectedOccurrenceMaxOwnerHullAggregateV2
open Family8SelectedOccurrenceMaxOwnerWeightedRetentionV1
open Family8TubeClosedThickeningInsideTwoFoldV2
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

/-- A selected quality-owner hull lies in its actual sticky parent. -/
theorem selectedOccurrenceMaxOwnerHullFamily_subset_parent
    (Y : Shading fine.bodyFamily)
    (R : Finset (Fin (blocks fine.bodyFamily P).length))
    (q : {q // q ∈ selectedOccurrenceIndices P R}) :
    (selectedOccurrenceMaxOwnerHullFamily C P Y R q : Set Space) ⊆
      (C.coarse.tubes (selectedOccurrenceMaxOwner C P Y R q)).carrier := by
  exact occurrenceMaxOwnerHull_subset_parent C P Y
    (selectedOccurrencePosition C R q)

/-- The finite-argmax witness is contained in its parent-specific hull. -/
theorem selectedOccurrenceMaxShadedWitness_carrier_subset_hull
    (Y : Shading fine.bodyFamily)
    (R : Finset (Fin (blocks fine.bodyFamily P).length))
    (q : {q // q ∈ selectedOccurrenceIndices P R}) :
    (fine.tubes (occurrenceMaxShadedWitness C P Y
      (selectedOccurrencePosition C R q))).carrier ⊆
      (selectedOccurrenceMaxOwnerHullFamily C P Y R q : Set Space) := by
  let k := selectedOccurrencePosition C R q
  have hwitness : occurrenceMaxShadedWitness C P Y k ∈
      occurrenceMaxOwnerSubfiber C P Y k := by
    rw [mem_occurrenceMaxOwnerSubfiber]
    exact ⟨occurrenceMaxShadedWitness_mem C P Y k, rfl⟩
  change (fine.bodyFamily (occurrenceMaxShadedWitness C P Y k) : Set Space) ⊆
    (hullContainer fine.bodyFamily
      (occurrenceMaxOwnerSubfiber C P Y k) : Set Space)
  exact body_subset_hullContainer fine.bodyFamily hwitness
    (occurrenceMaxOwnerSubfiber_nonempty C P Y k)

/-- `AdmissibleThickeningInsideOwner` follows from the actual parent
inclusion and `b ≤ rho`. -/
theorem admissibleThickeningInsideOwner_of_maxOwnerHullFamily
    (hrho : 0 < rho) (hb : b ≤ rho)
    (Y : Shading fine.bodyFamily)
    (R : Finset (Fin (blocks fine.bodyFamily P).length))
    (D : ShadedConvexPlankFamily
      {q // q ∈ selectedOccurrenceIndices P R} a b)
    (hfamily : D.family = selectedOccurrenceMaxOwnerHullFamily C P Y R) :
    AdmissibleThickeningInsideOwner C R D
      (selectedOccurrenceMaxOwner C P Y R) := by
  intro theta _hthetaLower hthetaUpper q
  have hthetaB : theta * b ≤ rho := by
    calc
      theta * b ≤ 1 * b := by gcongr
      _ = b := one_mul b
      _ ≤ rho := hb
  apply cthickening_subset_twoFoldTubeCarrier_of_subset_of_le hrho
    (C.coarse.tubes (selectedOccurrenceMaxOwner C P Y R q))
  · rw [hfamily]
    exact selectedOccurrenceMaxOwnerHullFamily_subset_parent C Y R q
  · exact hthetaB

/-- Conflict-free actual parents force unique ownership of the genuine
quality-owner hulls. -/
theorem thickenedPlankUniqueOwner_maxOwnerHull_ownedOccurrences
    (hrho : 0 < rho) (hb : b ≤ rho)
    (Y : Shading fine.bodyFamily)
    (R0 : Finset (Fin (blocks fine.bodyFamily P).length))
    (loss : ENNReal)
    (W : DoubledParentConflictWeightedSelection C
      (occurrenceMaxOwnerMass C P Y R0) loss)
    (D : ShadedConvexPlankFamily
      {q // q ∈ selectedOccurrenceIndices P
        (occurrencesMaxOwnedBy C P Y R0 W.selected)} a b)
    (hfamily : D.family = selectedOccurrenceMaxOwnerHullFamily C P Y
      (occurrencesMaxOwnedBy C P Y R0 W.selected)) :
    ThickenedPlankUniqueOwner D
      (selectedOccurrenceMaxOwner C P Y
        (occurrencesMaxOwnedBy C P Y R0 W.selected)) := by
  let R := occurrencesMaxOwnedBy C P Y R0 W.selected
  have hinside : AdmissibleThickeningInsideOwner C R D
      (selectedOccurrenceMaxOwner C P Y R) :=
    admissibleThickeningInsideOwner_of_maxOwnerHullFamily C hrho hb Y R D
      hfamily
  intro theta hthetaLower hthetaUpper i j hj
  by_contra hne
  have hiOwner : selectedOccurrenceMaxOwner C P Y R i ∈ W.selected :=
    selectedOccurrenceMaxOwner_mem_selected_of_owned C P Y R0 loss W i
  have hjOwner : selectedOccurrenceMaxOwner C P Y R j ∈ W.selected :=
    selectedOccurrenceMaxOwner_mem_selected_of_owned C P Y R0 loss W j
  have hjContained : (D.family j : Set Space) ⊆
      Metric.cthickening (((theta * b : NNReal) : Real))
        (D.family i : Set Space) := by
    simpa [thickenedPlankIndices,
      Family6AffinePlankAnalyticHypothesesStableV1.containedIndices] using
        (Finset.mem_filter.mp hj).2
  let witness := occurrenceMaxShadedWitness C P Y
    (selectedOccurrencePosition C R j)
  have hwitnessActive : witness ∈ C.activeFine :=
    occurrenceMaxShadedWitness_mem_active C P Y _
  have hwitnessBody : (fine.tubes witness).carrier ⊆
      (D.family j : Set Space) := by
    rw [hfamily]
    exact selectedOccurrenceMaxShadedWitness_carrier_subset_hull C Y R j
  have hiDouble : (fine.tubes witness).carrier ⊆
      twoFoldTubeCarrier
        (C.coarse.tubes (selectedOccurrenceMaxOwner C P Y R i)) :=
    hwitnessBody.trans (hjContained.trans
      (hinside theta hthetaLower hthetaUpper i))
  have hwitnessParent : C.parent witness =
      selectedOccurrenceMaxOwner C P Y R j := rfl
  have hjParent : (fine.tubes witness).carrier ⊆
      (C.coarse.tubes (selectedOccurrenceMaxOwner C P Y R j)).carrier := by
    have hparent := C.carrier_subset witness hwitnessActive
    rw [hwitnessParent] at hparent
    exact hparent
  have hjDouble : (fine.tubes witness).carrier ⊆
      twoFoldTubeCarrier
        (C.coarse.tubes (selectedOccurrenceMaxOwner C P Y R j)) :=
    hjParent.trans (carrier_subset_twoFoldTubeCarrier
      (C.coarse.tubes (selectedOccurrenceMaxOwner C P Y R j)))
  exact W.selected_pairwise hiOwner hjOwner (fun h => hne h.symm)
    ⟨witness, hwitnessActive, hiDouble, hjDouble⟩

/-- Actual Katz--Tao certificates on max-owner fibres give local
`Delta_max ≤ Delta` and the complete thick-plank control. -/
theorem frostmanThickenedPlankControl_maxOwnerHull_ownedOccurrences
    (hrho : 0 < rho) (hb : b ≤ rho)
    (Y : Shading fine.bodyFamily)
    (R0 : Finset (Fin (blocks fine.bodyFamily P).length))
    (loss : ENNReal)
    (W : DoubledParentConflictWeightedSelection C
      (occurrenceMaxOwnerMass C P Y R0) loss)
    (D : ShadedConvexPlankFamily
      {q // q ∈ selectedOccurrenceIndices P
        (occurrencesMaxOwnedBy C P Y R0 W.selected)} a b)
    (hfamily : D.family = selectedOccurrenceMaxOwnerHullFamily C P Y
      (occurrencesMaxOwnedBy C P Y R0 W.selected))
    (hlocal : OwnerFiberIsKatzTao (Delta := Delta) C D
      (selectedOccurrenceMaxOwner C P Y
        (occurrencesMaxOwnedBy C P Y R0 W.selected))) :
    FrostmanThickenedPlankControl D
      (uniqueOwnerLocalDeltaThickM D.comparisonConstant Delta a b) := by
  apply frostmanThickenedPlankControl_of_uniqueOwner_localDeltaMax D
    (selectedOccurrenceMaxOwner C P Y
      (occurrencesMaxOwnedBy C P Y R0 W.selected))
  · exact thickenedPlankUniqueOwner_maxOwnerHull_ownedOccurrences C hrho hb
      Y R0 loss W D hfamily
  · exact ownerFiberDeltaMax_le_of_ownerFiberIsKatzTao
      (Delta := Delta) C D
      (selectedOccurrenceMaxOwner C P Y
        (occurrencesMaxOwnedBy C P Y R0 W.selected)) hlocal

#print axioms selectedOccurrenceMaxOwnerHullFamily_subset_parent
#print axioms selectedOccurrenceMaxShadedWitness_carrier_subset_hull
#print axioms admissibleThickeningInsideOwner_of_maxOwnerHullFamily
#print axioms thickenedPlankUniqueOwner_maxOwnerHull_ownedOccurrences
#print axioms frostmanThickenedPlankControl_maxOwnerHull_ownedOccurrences

end

end Family8SelectedOccurrenceMaxOwnerHullUniqueOwnerV2
