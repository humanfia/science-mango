import FamilyStickyGrounding.FamilyStickyActualSharedLocalExpectationV1
import FamilyStickyGrounding.FamilyStickyRandomModelTubeCollisionGridV1

open Set MeasureTheory
open scoped BigOperators ENNReal NNReal

namespace FamilyStickyRandomCollisionOuterFrameExpectationV1

open LeanEval.Analysis.WangZahlKakeya
open Submission.Kakeya.ConvexGeometry
open FamilyStickyActualTubeTranslationGridV1
open FamilyStickyRandomModelTubeCollisionGridV1
open FamilyStickySharedTranslationPackingIncidenceV1.ActualTubeTranslationGrid

noncomputable section
set_option linter.unusedSectionVars false

/-!
# Collision expectation from the outer tube box, without a small-radius cutoff

The collision tests are the literal carriers of `100 T₀`.  Every tube, at
every radius, is contained in its aligned frame box with sides
`200 delta, 200 delta, 1 + 200 delta`.  The Appendix incidence estimate only
uses this *outer* containment.  It does not use the converse half-box
containment that forced the auxiliary hypothesis `100 delta <= 1/2` in the
older `HasBoxDimensions 2` adapter.

This module exposes the outer box directly and repeats the thin finite
double-counting adapter with an explicit box.  Thus no large-scale hierarchy
level has to be discarded merely to orient the collision catalogue.
-/

variable {delta : NNReal} {translation tubeIndex : Type*}
  [Fintype translation] [DecidableEq translation]
  [DecidableEq tubeIndex]

/-- A chosen orthonormal frame aligned with the axis of the collision test
tube.  Existence is the unconditional finite-dimensional frame theorem. -/
noncomputable def collisionAlignedFrame
    (G : ActualTubeTranslationGrid delta translation tubeIndex)
    (K : Fin (Fintype.card (ModelCandidate G))) :
    OrthonormalBasis (Fin 3) Real Space :=
  Classical.choose
    (hundredTube (modelCandidateTube G (modelCandidateOfIndex G K))).exists_alignedFrame

theorem collisionAlignedFrame_two
    (G : ActualTubeTranslationGrid delta translation tubeIndex)
    (K : Fin (Fintype.card (ModelCandidate G))) :
    collisionAlignedFrame G K 2 =
      (hundredTube
        (modelCandidateTube G (modelCandidateOfIndex G K))).axis.direction :=
  Classical.choose_spec
    (hundredTube (modelCandidateTube G (modelCandidateOfIndex G K))).exists_alignedFrame

/-- The literal aligned outer frame box of a collision test. -/
noncomputable def collisionOuterBox
    (G : ActualTubeTranslationGrid delta translation tubeIndex)
    (K : Fin (Fintype.card (ModelCandidate G))) : FrameBox :=
  (hundredTube (modelCandidateTube G (modelCandidateOfIndex G K))).alignedFrameBox
    (collisionAlignedFrame G K)

@[simp] theorem collisionOuterBox_side
    (G : ActualTubeTranslationGrid delta translation tubeIndex)
    (K : Fin (Fintype.card (ModelCandidate G))) :
    (collisionOuterBox G K).side = collisionSide G K := by
  rfl

theorem collisionTest_subset_collisionOuterBox
    (G : ActualTubeTranslationGrid delta translation tubeIndex)
    (K : Fin (Fintype.card (ModelCandidate G))) :
    ((collisionGrid G).testBody K : Set Space) ⊆
      (collisionOuterBox G K).carrier := by
  change
    (hundredTube
        (modelCandidateTube G (modelCandidateOfIndex G K))).carrier ⊆ _
  exact
    (hundredTube
      (modelCandidateTube G (modelCandidateOfIndex G K))).carrier_subset_alignedFrameBox
        (collisionAlignedFrame G K) (collisionAlignedFrame_two G K)

/-- Sum-form shared-grid expectation using only a supplied outer frame box.
This is the exact portion of the Appendix balance argument needed by the
collision catalogue. -/
theorem sum_singleLoad_le_card_mul_mean_of_outerBox
    {G : ActualTubeTranslationGrid delta translation tubeIndex}
    {mesh motionRadius : NNReal}
    (P : IsSharedTranslationPacking G mesh motionRadius)
    (K : Fin G.testCard) (_hK : K ∈ G.activeTests)
    (B : FrameBox)
    (hbox : (G.testBody K : Set Space) ⊆ B.carrier)
    {mean : Real} (hmean : 0 ≤ mean)
    (hmesh0 : mesh ≤ B.side 0) (hmesh1 : mesh ≤ B.side 1)
    (hmeshR : mesh ≤ motionRadius)
    (hnormalized :
      297 * (G.tubes.card : Real) * (B.side 0 : Real) *
          (B.side 1 : Real) ≤
        (motionRadius : Real) ^ 2 * mean) :
    (∑ g : translation, (G.singleLoad K g : Real)) ≤
      (Fintype.card translation : Real) * mean := by
  have hgrid : forall i, i ∈ G.tubes ->
      G.toIncidenceModel.gridHitsTube K i ≤
        FamilyStickyActualSharedLocalPointBudgetV1.ActualTubeTranslationGrid.IsSharedTranslationPacking.localPointBudget
          P B := by
    intro i hi
    rw [G.toIncidenceModel_gridHitsTube]
    calc
      G.tubeHitCount K i ≤
          FamilyStickyActualTranslationPointHitV1.ActualTubeTranslationGrid.pointHitCount
            G K (G.tube i).axis.base :=
        FamilyStickyActualTranslationPointHitV1.ActualTubeTranslationGrid.tubeHitCount_le_pointHitCount_axisBase
          G K i
      _ = (P.pointHits (G.testBody K : Set Space) (G.tube i).axis.base).card :=
        FamilyStickyActualSharedLocalPointBudgetV1.ActualTubeTranslationGrid.IsSharedTranslationPacking.pointHitCount_eq_card_pointHits
          P K (G.tube i).axis.base
      _ ≤
          FamilyStickyActualSharedLocalPointBudgetV1.ActualTubeTranslationGrid.IsSharedTranslationPacking.localPointBudget
            P B :=
        FamilyStickyActualSharedLocalPointBudgetV1.ActualTubeTranslationGrid.IsSharedTranslationPacking.card_pointHits_le_localPointBudget
          P (G.testBody K : Set Space) B hbox (G.tube i).axis.base
  have hbalance :
      (G.toIncidenceModel.tubes.card : Real) *
          (FamilyStickyActualSharedLocalPointBudgetV1.ActualTubeTranslationGrid.IsSharedTranslationPacking.localPointBudget
            P B : Real) ≤
        (Fintype.card translation : Real) * mean := by
    rw [G.toIncidenceModel_tubes]
    exact FamilyStickyActualSharedLocalFeasibilityV1.balance_of_explicit_297
      P B hmesh0 hmesh1 hmeshR hmean hnormalized
  have hsum :=
    FamilyStickyRandomTranslationGridAdapterV1.TranslationIncidenceModel.sum_load_le_of_gridHitsTube_le
      G.toIncidenceModel K
      (FamilyStickyActualSharedLocalPointBudgetV1.ActualTubeTranslationGrid.IsSharedTranslationPacking.localPointBudget
        P B)
      mean hgrid hbalance
  simpa only [G.toIncidenceModel_load] using hsum

#print axioms collisionAlignedFrame_two
#print axioms collisionOuterBox_side
#print axioms collisionTest_subset_collisionOuterBox
#print axioms sum_singleLoad_le_card_mul_mean_of_outerBox

end

end FamilyStickyRandomCollisionOuterFrameExpectationV1
