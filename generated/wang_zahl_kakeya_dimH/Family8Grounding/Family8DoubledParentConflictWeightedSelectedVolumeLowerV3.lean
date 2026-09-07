import Family8Grounding.Family8DoubledParentConflictWeightedShadingMassBridgeV2
import Family8Grounding.Family8FiniteRandomRigidMotionFrostmanConnectorV1
import Mathlib.Tactic

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 3000000

open Set MeasureTheory
open scoped ENNReal NNReal BigOperators

namespace Family8DoubledParentConflictWeightedSelectedVolumeLowerV3

open LeanEval.Analysis.WangZahlKakeya
open Submission.Kakeya.ConvexGeometry
open Submission.Kakeya.ConvexFactoring
open Submission.Kakeya.Uniformity
open Family8KatzTaoFrostmanPropertiesV1
open Family8GeneralizedKatzTaoMultiplicityV1
open Family8FiniteRandomRigidMotionFrostmanConnectorV1
open Family8DoubledParentConflictWeightedRetentionV3.ScaleCover
open Family8DoubledParentConflictWeightedShadingMassBridgeV2.ScaleCover
open FamilyStickyAtEveryScaleCoreV1

noncomputable section

/-!
# Selected-parent cardinality gives actual selected tube volume

Every selected active parent has an active fine child by the defining
surjectivity of a sticky scale cover.  Choosing one such child embeds the
selected parents into the literal fine-index restriction used by the
weighted shading endpoint.  Combining that cardinality comparison with
the standard lower bound `volume(T) >= delta^2 / 2` converts the greedy
cardinality retention inequality directly into a lower bound for the
actual selected family volume.
-/

namespace ScaleCover

/-- Choose one active fine representative of each selected parent. -/
noncomputable def selectedParentFineRepresentative
    {delta rho : NNReal} {index : Type} [Fintype index]
    [DecidableEq index] {fine : UniformTubeFamily delta index}
    (S : StickyScaleCover fine rho) (Y : Shading fine.bodyFamily)
    {B : ENNReal}
    (W : DoubledParentConflictWeightedSelection S
      (parentShadingWeight S Y) B) :
    {k // k ∈ W.selected} →
      {i // i ∈ weightedSelectedFineIndices Y W} := fun k ↦
  let witness :=
    S.parent_surjective k.1 (W.selected_subset k.2)
  ⟨Classical.choose witness,
    Finset.mem_filter.mpr
      ⟨(Classical.choose_spec witness).1, by
        rw [(Classical.choose_spec witness).2]
        exact k.2⟩⟩

@[simp] theorem selectedParentFineRepresentative_parent
    {delta rho : NNReal} {index : Type} [Fintype index]
    [DecidableEq index] {fine : UniformTubeFamily delta index}
    (S : StickyScaleCover fine rho) (Y : Shading fine.bodyFamily)
    {B : ENNReal}
    (W : DoubledParentConflictWeightedSelection S
      (parentShadingWeight S Y) B)
    (k : {k // k ∈ W.selected}) :
    S.parent (selectedParentFineRepresentative S Y W k).1 = k.1 := by
  unfold selectedParentFineRepresentative
  exact (Classical.choose_spec
    (S.parent_surjective k.1 (W.selected_subset k.2))).2

/-- Distinct selected parents receive distinct fine representatives. -/
theorem selectedParentFineRepresentative_injective
    {delta rho : NNReal} {index : Type} [Fintype index]
    [DecidableEq index] {fine : UniformTubeFamily delta index}
    (S : StickyScaleCover fine rho) (Y : Shading fine.bodyFamily)
    {B : ENNReal}
    (W : DoubledParentConflictWeightedSelection S
      (parentShadingWeight S Y) B) :
    Function.Injective (selectedParentFineRepresentative S Y W) := by
  intro k l hkl
  apply Subtype.ext
  have hparent := congrArg (fun i ↦ S.parent i.1) hkl
  simpa using hparent

/-- The literal selected fine restriction contains at least one fine tube
for every selected parent. -/
theorem selected_card_le_weightedSelectedFineIndices_card
    {delta rho : NNReal} {index : Type} [Fintype index]
    [DecidableEq index] {fine : UniformTubeFamily delta index}
    (S : StickyScaleCover fine rho) (Y : Shading fine.bodyFamily)
    {B : ENNReal}
    (W : DoubledParentConflictWeightedSelection S
      (parentShadingWeight S Y) B) :
    W.selected.card ≤ (weightedSelectedFineIndices Y W).card := by
  simpa only [Fintype.card_coe] using
    (Fintype.card_le_of_injective
      (selectedParentFineRepresentative S Y W)
      (selectedParentFineRepresentative_injective S Y W))

/-- Selected-parent cardinality times the one-tube lower volume is bounded
by the literal actual volume of the selected fine restriction. -/
theorem selected_card_mul_half_sq_le_weightedSelected_actualFamilyVolume
    {delta rho : NNReal} {index : Type} [Fintype index]
    [DecidableEq index] (D : ActualTubeDatum delta index)
    {S : StickyScaleCover D.family rho} {B : ENNReal}
    (W : DoubledParentConflictWeightedSelection S
      (parentShadingWeight S D.shading) B)
    (hdeltaHalf : delta ≤ (2 : NNReal)⁻¹) :
    (W.selected.card : ENNReal) * ((delta : ENNReal) ^ 2 / 2) ≤
      (restrictActualTubeDatum D
        (weightedSelectedFineIndices D.shading W)).actualFamilyVolume := by
  have hcardNat : W.selected.card ≤
      (weightedSelectedFineIndices D.shading W).card :=
    selected_card_le_weightedSelectedFineIndices_card S D.shading W
  have hcard : (W.selected.card : ENNReal) ≤
      ((weightedSelectedFineIndices D.shading W).card : ENNReal) := by
    exact_mod_cast hcardNat
  calc
    (W.selected.card : ENNReal) * ((delta : ENNReal) ^ 2 / 2) ≤
        ((weightedSelectedFineIndices D.shading W).card : ENNReal) *
          ((delta : ENNReal) ^ 2 / 2) :=
      mul_le_mul' hcard le_rfl
    _ ≤ (restrictActualTubeDatum D
          (weightedSelectedFineIndices D.shading W)).actualFamilyVolume := by
      simpa only [Fintype.card_coe] using
        card_mul_half_sq_le_actualFamilyVolume
          (restrictActualTubeDatum D
            (weightedSelectedFineIndices D.shading W)) hdeltaHalf

/-- Direct scalar base-budget bridge: the full active-parent cardinality
and the one-tube scale are retained in actual selected family volume with
exactly the same graph-degree loss `B`. -/
theorem activeCoarse_card_mul_half_sq_le_budget_mul_weightedSelected_actualFamilyVolume
    {delta rho : NNReal} {index : Type} [Fintype index]
    [DecidableEq index] (D : ActualTubeDatum delta index)
    {S : StickyScaleCover D.family rho} {B : ENNReal}
    (W : DoubledParentConflictWeightedSelection S
      (parentShadingWeight S D.shading) B)
    (hdeltaHalf : delta ≤ (2 : NNReal)⁻¹) :
    (S.activeCoarse.card : ENNReal) * ((delta : ENNReal) ^ 2 / 2) ≤
      B * (restrictActualTubeDatum D
        (weightedSelectedFineIndices D.shading W)).actualFamilyVolume := by
  calc
    (S.activeCoarse.card : ENNReal) * ((delta : ENNReal) ^ 2 / 2) ≤
        (B * (W.selected.card : ENNReal)) *
          ((delta : ENNReal) ^ 2 / 2) :=
      mul_le_mul' W.card_le le_rfl
    _ = B * ((W.selected.card : ENNReal) *
          ((delta : ENNReal) ^ 2 / 2)) := by
      ac_rfl
    _ ≤ B * (restrictActualTubeDatum D
          (weightedSelectedFineIndices D.shading W)).actualFamilyVolume :=
      mul_le_mul' le_rfl
        (selected_card_mul_half_sq_le_weightedSelected_actualFamilyVolume
          D W hdeltaHalf)

#print axioms selectedParentFineRepresentative
#print axioms selectedParentFineRepresentative_parent
#print axioms selectedParentFineRepresentative_injective
#print axioms selected_card_le_weightedSelectedFineIndices_card
#print axioms selected_card_mul_half_sq_le_weightedSelected_actualFamilyVolume
#print axioms
  activeCoarse_card_mul_half_sq_le_budget_mul_weightedSelected_actualFamilyVolume

end ScaleCover
end
end Family8DoubledParentConflictWeightedSelectedVolumeLowerV3
