import Family8Grounding.Family8SelectedOccurrenceActiveParentOwnerV7
import Family8Grounding.Family8UniqueOwnerLocalDeltaMaxThickControlV1
import Mathlib.Tactic

/-!
# Unique Equation (45) owner from actual conflict-free active parents

Every retained block is parent-pure, its exact admissible closed thickenings
remain in the doubled carrier of that actual parent, and its parent belongs
to the existing doubled-conflict-free weighted selection.  A literal fine
witness converts containment in a thickening into a doubled-parent conflict,
forcing equality of the actual parents.  No winning hull is duplicated.
-/

open Set MeasureTheory
open scoped BigOperators ENNReal NNReal

namespace Family8SelectedOccurrenceActiveParentOwnerV9

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
open Family8SelectedOccurrenceDensityFrostmanV1
open Family8UniqueOwnerLocalDeltaMaxThickControlV1
open FamilyStickyAtEveryScaleCoreV1

noncomputable section

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 5000000

local instance (p : Prop) : Decidable p := Classical.propDecidable p

variable {delta rho a b : NNReal} {index : Type}
  [Fintype index] [DecidableEq index]
  {fine : UniformTubeFamily delta index}
  (C : StickyScaleCover fine rho)
  {P : GreedyDensityPartition fine.bodyFamily
    (hullCandidates C.activeFine) (hullContainer fine.bodyFamily)
    C.activeFine}

/-- Exact parent-specific geometric inclusion used in the paper's owner
argument.  It is a body inclusion, not a unique-owner or count callback. -/
def AdmissibleThickeningInsideOwner
    (R : Finset (Fin (blocks fine.bodyFamily P).length))
    (D : ShadedConvexPlankFamily
      {q // q ∈ selectedOccurrenceIndices P R} a b)
    (owner : {q // q ∈ selectedOccurrenceIndices P R} → Fin C.coarseCard) :
    Prop :=
  ∀ theta : NNReal, a / b ≤ theta → theta ≤ 1 →
    ∀ q,
      Metric.cthickening (((theta * b : NNReal) : Real))
          (D.family q : Set Space) ⊆
        twoFoldTubeCarrier (C.coarse.tubes (owner q))

theorem selectedOccurrenceActiveParent_mem_selected_of_owned
    (Y : Shading fine.bodyFamily)
    (R0 : Finset (Fin (blocks fine.bodyFamily P).length))
    (loss : ENNReal)
    (W : DoubledParentConflictWeightedSelection C
      (occurrenceMassByActiveParent C P Y R0) loss)
    (q : {q // q ∈ selectedOccurrenceIndices P
      (occurrencesOwnedBy C P R0 W.selected)}) :
    selectedOccurrenceActiveParent C
        (occurrencesOwnedBy C P R0 W.selected) q ∈ W.selected := by
  exact (mem_occurrencesOwnedBy C P R0 W.selected
    (selectedOccurrencePosition C
      (occurrencesOwnedBy C P R0 W.selected) q)).mp
        (selectedOccurrencePosition_mem C
          (occurrencesOwnedBy C P R0 W.selected) q) |>.2

/-- Conflict-free actual parents plus the literal parent-thickening geometry
produce `ThickenedPlankUniqueOwner`. -/
theorem thickenedPlankUniqueOwner_of_actualSelectedParents
    (hpure : ParentPure C P)
    (Y : Shading fine.bodyFamily)
    (R0 : Finset (Fin (blocks fine.bodyFamily P).length))
    (loss : ENNReal)
    (W : DoubledParentConflictWeightedSelection C
      (occurrenceMassByActiveParent C P Y R0) loss)
    (R : Finset (Fin (blocks fine.bodyFamily P).length))
    (hR : ∀ k, k ∈ R → occurrenceActiveParent C P k ∈ W.selected)
    (D : ShadedConvexPlankFamily
      {q // q ∈ selectedOccurrenceIndices P R} a b)
    (hfamily : D.family = selectedOccurrenceOuterFamily P R)
    (hinside : AdmissibleThickeningInsideOwner C R D
      (selectedOccurrenceActiveParent C R)) :
    ThickenedPlankUniqueOwner D (selectedOccurrenceActiveParent C R) := by
  intro theta hthetaLower hthetaUpper i j hj
  by_contra hne
  have hiOwner : selectedOccurrenceActiveParent C R i ∈ W.selected :=
    hR _ (selectedOccurrencePosition_mem C R i)
  have hjOwner : selectedOccurrenceActiveParent C R j ∈ W.selected :=
    hR _ (selectedOccurrencePosition_mem C R j)
  have hjContained : (D.family j : Set Space) ⊆
      Metric.cthickening (((theta * b : NNReal) : Real))
        (D.family i : Set Space) := by
    simpa [thickenedPlankIndices,
      Family6AffinePlankAnalyticHypothesesStableV1.containedIndices] using
        (Finset.mem_filter.mp hj).2
  let witness := occurrenceFineWitness C P
    (selectedOccurrencePosition C R j)
  have hwitnessMem : witness ∈
      (blockAt fine.bodyFamily P
        (selectedOccurrencePosition C R j)).fiber :=
    occurrenceFineWitness_mem C P _
  have hwitnessActive : witness ∈ C.activeFine :=
    occurrenceFineWitness_mem_active C P _
  have hwitnessBody : (fine.tubes witness).carrier ⊆
      (D.family j : Set Space) := by
    rw [hfamily]
    exact selectedOccurrenceFineWitness_carrier_subset_body C R j
  have hiDouble : (fine.tubes witness).carrier ⊆
      twoFoldTubeCarrier
        (C.coarse.tubes (selectedOccurrenceActiveParent C R i)) :=
    hwitnessBody.trans (hjContained.trans
      (hinside theta hthetaLower hthetaUpper i))
  have hwitnessParent : C.parent witness =
      selectedOccurrenceActiveParent C R j :=
    parent_eq_selectedOccurrenceActiveParent_of_mem C hpure R j witness
      hwitnessMem
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

/-- For the occurrence set selected by owner, owner membership is automatic. -/
theorem thickenedPlankUniqueOwner_ownedOccurrences
    (hpure : ParentPure C P)
    (Y : Shading fine.bodyFamily)
    (R0 : Finset (Fin (blocks fine.bodyFamily P).length))
    (loss : ENNReal)
    (W : DoubledParentConflictWeightedSelection C
      (occurrenceMassByActiveParent C P Y R0) loss)
    (D : ShadedConvexPlankFamily
      {q // q ∈ selectedOccurrenceIndices P
        (occurrencesOwnedBy C P R0 W.selected)} a b)
    (hfamily : D.family = selectedOccurrenceOuterFamily P
      (occurrencesOwnedBy C P R0 W.selected))
    (hinside : AdmissibleThickeningInsideOwner C
      (occurrencesOwnedBy C P R0 W.selected) D
      (selectedOccurrenceActiveParent C
        (occurrencesOwnedBy C P R0 W.selected))) :
    ThickenedPlankUniqueOwner D
      (selectedOccurrenceActiveParent C
        (occurrencesOwnedBy C P R0 W.selected)) := by
  apply thickenedPlankUniqueOwner_of_actualSelectedParents C hpure Y R0 loss W
    (occurrencesOwnedBy C P R0 W.selected)
  · intro k hk
    exact (mem_occurrencesOwnedBy C P R0 W.selected k).mp hk |>.2
  · exact hfamily
  · exact hinside

#print axioms selectedOccurrenceActiveParent_mem_selected_of_owned
#print axioms thickenedPlankUniqueOwner_of_actualSelectedParents
#print axioms thickenedPlankUniqueOwner_ownedOccurrences

end

end Family8SelectedOccurrenceActiveParentOwnerV9
