import Family8Grounding.Family8DoubledParentConflictWeightedRestrictedCoverEndpointV2
import Family8Grounding.Family8RestrictedActualDatumDensityRetentionV1
import Mathlib.Tactic

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 3000000

open Set MeasureTheory
open scoped ENNReal NNReal BigOperators

namespace Family8DoubledParentConflictWeightedShadingMassBridgeV2

open LeanEval.Analysis.WangZahlKakeya
open Submission.Kakeya.ConvexGeometry
open Submission.Kakeya.ConvexFactoring
open Submission.Kakeya.Uniformity
open Family8KatzTaoFrostmanPropertiesV1
open Family8GeneralizedKatzTaoMultiplicityV1
open Family8DoubledParentConflictWeightedRetentionV3.ScaleCover
open Family8DoubledParentConflictWeightedRestrictedCoverEndpointV2.ScaleCover
open FamilyStickyAtEveryScaleCoreV1

noncomputable section

/-!
# The weighted parent selection as an actual shading restriction

Give each active parent the exact sum of the source shading masses in its
assigned fine fibre.  The abstract arbitrary-weight inequality of the
doubled-parent greedy selection then becomes the literal shading-mass
retention inequality for the selected fine subtype.  When every fine index
is active, it also gives the source-to-selected average-multiplicity loss
needed immediately before applying the Frostman property.
-/

namespace ScaleCover

/-- Exact multiplicity-counted shading mass assigned to one parent. -/
def parentShadingWeight
    {delta rho : NNReal} {index : Type} [Fintype index]
    [DecidableEq index] {fine : UniformTubeFamily delta index}
    (S : StickyScaleCover fine rho) (Y : Shading fine.bodyFamily)
    (k : Fin S.coarseCard) : ENNReal :=
  ∑ i ∈ S.fiber k, volume (Y.carrier i)

/-- The original fine indices whose assigned parent survived the weighted
selection. -/
def weightedSelectedFineIndices
    {delta rho : NNReal} {index : Type} [Fintype index]
    [DecidableEq index] {fine : UniformTubeFamily delta index}
    {S : StickyScaleCover fine rho} {B : ENNReal}
    (Y : Shading fine.bodyFamily)
    (W : DoubledParentConflictWeightedSelection S
      (parentShadingWeight S Y) B) : Finset index :=
  S.activeFine.filter fun i ↦ S.parent i ∈ W.selected

/-- The selected-cover fine type is canonically the same subtype as the
literal selected finset used by `restrictActualTubeDatum`. -/
noncomputable def weightedSelectedAssignedFineEquiv
    {delta rho : NNReal} {index : Type} [Fintype index]
    [DecidableEq index] {fine : UniformTubeFamily delta index}
    {S : StickyScaleCover fine rho} {B : ENNReal}
    (Y : Shading fine.bodyFamily)
    (W : DoubledParentConflictWeightedSelection S
      (parentShadingWeight S Y) B) :
    WeightedSelectedAssignedFine W ≃
      {i // i ∈ weightedSelectedFineIndices Y W} where
  toFun i := ⟨i.1, Finset.mem_filter.mpr ⟨i.2.1, i.2.2⟩⟩
  invFun i := ⟨i.1, Finset.mem_filter.mp i.2⟩
  left_inv i := by
    apply Subtype.ext
    rfl
  right_inv i := by
    apply Subtype.ext
    rfl

/-- Under the canonical equivalence, the actual restricted family is
literally the selected assigned fine family. -/
@[simp] theorem restrictActualTubeDatum_weightedSelected_tubes
    {delta rho : NNReal} {index : Type} [Fintype index]
    [DecidableEq index] (D : ActualTubeDatum delta index)
    {S : StickyScaleCover D.family rho} {B : ENNReal}
    (W : DoubledParentConflictWeightedSelection S
      (parentShadingWeight S D.shading) B)
    (i : WeightedSelectedAssignedFine W) :
    (restrictActualTubeDatum D
      (weightedSelectedFineIndices D.shading W)).family.tubes
        (weightedSelectedAssignedFineEquiv D.shading W i) =
      (weightedSelectedAssignedFineFamily W).tubes i :=
  rfl

/-- The same equivalence preserves each literal shading carrier. -/
@[simp] theorem restrictActualTubeDatum_weightedSelected_shadingCarrier
    {delta rho : NNReal} {index : Type} [Fintype index]
    [DecidableEq index] (D : ActualTubeDatum delta index)
    {S : StickyScaleCover D.family rho} {B : ENNReal}
    (W : DoubledParentConflictWeightedSelection S
      (parentShadingWeight S D.shading) B)
    (i : WeightedSelectedAssignedFine W) :
    (restrictActualTubeDatum D
      (weightedSelectedFineIndices D.shading W)).shading.carrier
        (weightedSelectedAssignedFineEquiv D.shading W i) =
      D.shading.carrier i.1 :=
  rfl

/-- Active fine shading mass is exactly the sum of the parent weights. -/
theorem activeFine_shadingMass_eq_sum_parentShadingWeight
    {delta rho : NNReal} {index : Type} [Fintype index]
    [DecidableEq index] {fine : UniformTubeFamily delta index}
    (S : StickyScaleCover fine rho) (Y : Shading fine.bodyFamily) :
    (∑ i ∈ S.activeFine, volume (Y.carrier i)) =
      ∑ k ∈ S.activeCoarse, parentShadingWeight S Y k := by
  classical
  unfold parentShadingWeight StickyScaleCover.fiber
  exact (Finset.sum_fiberwise_of_maps_to
    (s := S.activeFine) (t := S.activeCoarse) (g := S.parent)
    S.parent_mem (fun i ↦ volume (Y.carrier i))).symm

/-- The sum of the selected parent weights is exactly the shading mass of
the literal selected fine subtype. -/
theorem sum_selected_parentShadingWeight_eq_restrict_shadingMass
    {delta rho : NNReal} {index : Type} [Fintype index]
    [DecidableEq index] (D : ActualTubeDatum delta index)
    {S : StickyScaleCover D.family rho} {B : ENNReal}
    (W : DoubledParentConflictWeightedSelection S
      (parentShadingWeight S D.shading) B) :
    (∑ k ∈ W.selected, parentShadingWeight S D.shading k) =
      (restrictActualTubeDatum D
        (weightedSelectedFineIndices D.shading W)).shading.shadingMass := by
  classical
  let selectedFine := weightedSelectedFineIndices D.shading W
  have hmaps : ∀ i ∈ selectedFine, S.parent i ∈ W.selected := by
    intro i hi
    exact (Finset.mem_filter.mp hi).2
  have hpartition :
      (∑ i ∈ selectedFine, volume (D.shading.carrier i)) =
        ∑ k ∈ W.selected,
          ∑ i ∈ selectedFine.filter (fun i ↦ S.parent i = k),
            volume (D.shading.carrier i) :=
    (Finset.sum_fiberwise_of_maps_to
      (s := selectedFine) (t := W.selected) (g := S.parent)
      hmaps (fun i ↦ volume (D.shading.carrier i))).symm
  have hfiber : ∀ k ∈ W.selected,
      selectedFine.filter (fun i ↦ S.parent i = k) = S.fiber k := by
    intro k hk
    ext i
    simp only [selectedFine, weightedSelectedFineIndices,
      StickyScaleCover.mem_fiber, Finset.mem_filter]
    constructor
    · intro hi
      exact ⟨hi.1.1, hi.2⟩
    · intro hi
      exact ⟨⟨hi.1, hi.2 ▸ hk⟩, hi.2⟩
  rw [restrictActualTubeDatum_shadingMass]
  rw [hpartition]
  apply Finset.sum_congr rfl
  intro k hk
  rw [hfiber k hk]
  rfl

/-- The abstract parent-weight retention inequality is the actual selected
fine shading-mass inequality. -/
theorem activeFine_shadingMass_le_mul_restrict_shadingMass
    {delta rho : NNReal} {index : Type} [Fintype index]
    [DecidableEq index] (D : ActualTubeDatum delta index)
    {S : StickyScaleCover D.family rho} {B : ENNReal}
    (W : DoubledParentConflictWeightedSelection S
      (parentShadingWeight S D.shading) B) :
    (∑ i ∈ S.activeFine, volume (D.shading.carrier i)) ≤
      B * (restrictActualTubeDatum D
        (weightedSelectedFineIndices D.shading W)).shading.shadingMass := by
  rw [activeFine_shadingMass_eq_sum_parentShadingWeight]
  calc
    (∑ k ∈ S.activeCoarse, parentShadingWeight S D.shading k) ≤
        B * ∑ k ∈ W.selected, parentShadingWeight S D.shading k :=
      W.mass_le
    _ = B * (restrictActualTubeDatum D
        (weightedSelectedFineIndices D.shading W)).shading.shadingMass := by
      rw [sum_selected_parentShadingWeight_eq_restrict_shadingMass D W]

/-- If the sticky cover uses every fine index, the weighted selection
retains the full source shading mass with exactly the graph-degree loss. -/
theorem source_shadingMass_le_mul_weightedSelected_shadingMass
    {delta rho : NNReal} {index : Type} [Fintype index]
    [DecidableEq index] (D : ActualTubeDatum delta index)
    {S : StickyScaleCover D.family rho} {B : ENNReal}
    (W : DoubledParentConflictWeightedSelection S
      (parentShadingWeight S D.shading) B)
    (hactive : S.activeFine = Finset.univ) :
    D.shading.shadingMass ≤
      B * (restrictActualTubeDatum D
        (weightedSelectedFineIndices D.shading W)).shading.shadingMass := by
  rw [Shading.shadingMass, ← hactive]
  exact activeFine_shadingMass_le_mul_restrict_shadingMass D W

/-- With all fine indices active, the same sharp loss transports source
average multiplicity to the actual selected subtype. -/
theorem source_averageMultiplicity_le_mul_weightedSelected
    {delta rho : NNReal} {index : Type} [Fintype index]
    [DecidableEq index] (D : ActualTubeDatum delta index)
    {S : StickyScaleCover D.family rho} {B : ENNReal}
    (W : DoubledParentConflictWeightedSelection S
      (parentShadingWeight S D.shading) B)
    (hactive : S.activeFine = Finset.univ) :
    D.shading.averageMultiplicity ≤
      B * (restrictActualTubeDatum D
        (weightedSelectedFineIndices D.shading W)).shading.averageMultiplicity := by
  let selected := weightedSelectedFineIndices D.shading W
  let refined := restrictActualTubeDatum D selected
  have hmass : D.shading.shadingMass ≤
      B * refined.shading.shadingMass := by
    exact source_shadingMass_le_mul_weightedSelected_shadingMass
      D W hactive
  have hunion : refined.shading.shadedUnion ⊆ D.shading.shadedUnion :=
    restrictActualTubeDatum_shadedUnion_subset D selected
  unfold Shading.averageMultiplicity
  calc
    D.shading.shadingMass / volume D.shading.shadedUnion ≤
        (B * refined.shading.shadingMass) /
          volume D.shading.shadedUnion :=
      ENNReal.div_le_div_right hmass _
    _ ≤ (B * refined.shading.shadingMass) /
          volume refined.shading.shadedUnion :=
      ENNReal.div_le_div_left (measure_mono hunion) _
    _ = B * (refined.shading.shadingMass /
          volume refined.shading.shadedUnion) := by
      simp only [div_eq_mul_inv]
      ac_rfl

#print axioms restrictActualTubeDatum_weightedSelected_tubes
#print axioms restrictActualTubeDatum_weightedSelected_shadingCarrier
#print axioms activeFine_shadingMass_eq_sum_parentShadingWeight
#print axioms sum_selected_parentShadingWeight_eq_restrict_shadingMass
#print axioms activeFine_shadingMass_le_mul_restrict_shadingMass
#print axioms source_shadingMass_le_mul_weightedSelected_shadingMass
#print axioms source_averageMultiplicity_le_mul_weightedSelected

end ScaleCover
end
end Family8DoubledParentConflictWeightedShadingMassBridgeV2
