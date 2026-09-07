import Family8Grounding.Family8PlankRetainedOwnerActiveCellCommonBallContainerV1
import Mathlib.Tactic

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 4000000

open Set MeasureTheory
open scoped BigOperators ENNReal NNReal InnerProductSpace

namespace Family8PlankRetainedOwnerActiveCertifiedOwnerIncidenceV1

open LeanEval.Analysis.WangZahlKakeya
open Submission.Kakeya.ConvexGeometry
open Submission.Kakeya.ConvexFactoring
open Submission.Kakeya.ConvexFactoring.HeavyParentSelection
open Submission.Kakeya.ConvexFactoring.CubeWeightUniformization
open Family6AffinePlankAnalyticHypothesesStableV1
open Family6CanonicalCertifiedPlankSlabIncidenceCoreV3
open Family8PlankThickControlActualClusterV1
open Family8PlankThickControlMutualContainmentClusteringV2
open Family8PlankThickControlOwnerFiberLogBucketV2
open Family8PlankThickControlRetainedOwnerFamilyV3
open Family8PlankRetainedOwnerCellRestrictedCanonicalSlabV1
open Family8PlankRetainedOwnerThickenedInducedShadingV2
open Family8PlankRetainedOwnerActiveCellCommonBallContainerV1

noncomputable section

universe u v

variable {iota : Type u} [Fintype iota] [DecidableEq iota]
variable {a b : NNReal}

/-!
# Active certified rows and their deduplicated selected owners

The cell restriction leaves empty fine carriers in the old retained index
type.  This file first reindexes the literal plank datum by the nonempty
support from V280.  Its certified incidence inherits the *same* framed
planks and the *same* selected slab certificate as the old V279 incidence,
so active membership maps injectively into the old member set.

For each slab query we then take the finite image of the active members under
the selected-owner map.  This is the actual deduplicated coarse set
`P_{theta,S}`.  Every such owner has an active fine preimage and its literal
thickened body lies in the same controlled thickening of `S`.
-/

/-- The cell-restricted retained fine datum, reindexed by exactly its
nonempty carriers. -/
def activeRetainedOwnerCellPlankDatum
    (D : ShadedConvexPlankFamily iota a b) {theta : NNReal}
    (C : MutualThickeningClustering D theta)
    (q : Fin (Nat.log 2 (Fintype.card iota) + 1))
    {cellIndex : Type v} (cell : cellIndex → Set Space)
    (hcell : ∀ p, MeasurableSet (cell p)) (selected : Finset cellIndex) :
    ShadedConvexPlankFamily
      {i // i ∈ activeRetainedOwnerCellIndices D C q cell hcell selected}
      a b where
  family := selectedCoarseFamily
    (retainedOwnerCellRestrictedPlankDatum D C q cell hcell selected).family
    (activeRetainedOwnerCellIndices D C q cell hcell selected)
  shading := selectedCoarseShading
    (retainedOwnerCellRestrictedPlankDatum D C q cell hcell selected).shading
    (activeRetainedOwnerCellIndices D C q cell hcell selected)
  comparisonConstant := D.comparisonConstant
  all_isPlank i := D.all_isPlank i.1.1
  ambient := D.ambient
  ambientComparisonConstant := D.ambientComparisonConstant
  ambient_is_unit_scale := D.ambient_is_unit_scale
  contained_in_ambient i := D.contained_in_ambient i.1.1

@[simp] theorem activeRetainedOwnerCellPlankDatum_family_apply
    (D : ShadedConvexPlankFamily iota a b) {theta : NNReal}
    (C : MutualThickeningClustering D theta)
    (q : Fin (Nat.log 2 (Fintype.card iota) + 1))
    {cellIndex : Type v} (cell : cellIndex → Set Space)
    (hcell : ∀ p, MeasurableSet (cell p)) (selected : Finset cellIndex)
    (i : {i // i ∈ activeRetainedOwnerCellIndices D C q cell hcell selected}) :
    (activeRetainedOwnerCellPlankDatum D C q cell hcell selected).family i =
      D.family i.1.1 := rfl

@[simp] theorem activeRetainedOwnerCellPlankDatum_shading_carrier
    (D : ShadedConvexPlankFamily iota a b) {theta : NNReal}
    (C : MutualThickeningClustering D theta)
    (q : Fin (Nat.log 2 (Fintype.card iota) + 1))
    {cellIndex : Type v} (cell : cellIndex → Set Space)
    (hcell : ∀ p, MeasurableSet (cell p)) (selected : Finset cellIndex)
    (i : {i // i ∈ activeRetainedOwnerCellIndices D C q cell hcell selected}) :
    (activeRetainedOwnerCellPlankDatum D C q cell hcell selected).shading.carrier i =
      (retainedOwnerFinalFineShading D C q cell hcell selected).carrier i.1 := rfl

theorem activeRetainedOwnerCellPlankDatum_carrier_nonempty
    (D : ShadedConvexPlankFamily iota a b) {theta : NNReal}
    (C : MutualThickeningClustering D theta)
    (q : Fin (Nat.log 2 (Fintype.card iota) + 1))
    {cellIndex : Type v} (cell : cellIndex → Set Space)
    (hcell : ∀ p, MeasurableSet (cell p)) (selected : Finset cellIndex)
    (i : {i // i ∈ activeRetainedOwnerCellIndices D C q cell hcell selected}) :
    Set.Nonempty
      ((activeRetainedOwnerCellPlankDatum D C q cell hcell selected).shading.carrier i) := by
  simpa using
    (mem_activeRetainedOwnerCellIndices D C q cell hcell selected i.1).1 i.2

/-- Restrict the old canonical incidence without choosing new slab
certificates.  Hence all later membership comparisons are definitional
rather than a certificate-coherence assumption. -/
def activeRetainedOwnerCellCertifiedIncidence
    (D : ShadedConvexPlankFamily iota a b) {theta : NNReal}
    (C : MutualThickeningClustering D theta)
    (q : Fin (Nat.log 2 (Fintype.card iota) + 1))
    {cellIndex : Type v} (cell : cellIndex → Set Space)
    (hcell : ∀ p, MeasurableSet (cell p)) (selected : Finset cellIndex)
    (hmass : (retainedOwnerPlankFamily D C q).shading.shadingMass ≠ 0)
    (hactive : (activeRetainedOwnerCellIndices D C q cell hcell selected).Nonempty) :
    CanonicalCertifiedPlankSlabIncidence
      {i // i ∈ activeRetainedOwnerCellIndices D C q cell hcell selected}
      {i // i ∈ activeRetainedOwnerCellIndices D C q cell hcell selected}
      (activeRetainedOwnerCellPlankDatum D C q cell hcell selected) 1 1 := by
  let R := retainedOwnerCellRestrictedCanonicalUnitSlabIncidence
    D C q cell hcell selected hmass
  let hindex : Nonempty
      {i // i ∈ activeRetainedOwnerCellIndices D C q cell hcell selected} :=
    ⟨⟨hactive.choose, hactive.choose_spec⟩⟩
  exact
    { one_le_tangentComparisonConstant := R.one_le_tangentComparisonConstant
      index_nonempty := hindex
      sourceToIndex := id
      indexToSource := id
      source_leftInverse := fun _ => rfl
      index_rightInverse := fun _ => rfl
      plank := fun i => R.plank i.1
      selector := R.selector
      selected_tangent_coverage := fun i => R.selected_tangent_coverage i.1 }

/-- Active certified membership is exactly old V279 membership of the
underlying retained fine index. -/
theorem mem_activeRetainedOwnerCellCertifiedIncidence_iff
    (D : ShadedConvexPlankFamily iota a b) {theta : NNReal}
    (C : MutualThickeningClustering D theta)
    (q : Fin (Nat.log 2 (Fintype.card iota) + 1))
    {cellIndex : Type v} (cell : cellIndex → Set Space)
    (hcell : ∀ p, MeasurableSet (cell p)) (selected : Finset cellIndex)
    (hmass : (retainedOwnerPlankFamily D C q).shading.shadingMass ≠ 0)
    (hactive : (activeRetainedOwnerCellIndices D C q cell hcell selected).Nonempty)
    (tau : NNReal) (S : ConvexBody Space)
    (i : {i // i ∈ activeRetainedOwnerCellIndices D C q cell hcell selected}) :
    i ∈ (activeRetainedOwnerCellCertifiedIncidence
      D C q cell hcell selected hmass hactive).members tau S ↔
      i.1 ∈ (retainedOwnerCellRestrictedCanonicalUnitSlabIncidence
        D C q cell hcell selected hmass).members tau S := by
  classical
  by_cases hS : IsSlab 1 tau S
  · simp only [CanonicalCertifiedPlankSlabIncidence.mem_members_of_isSlab _ hS]
    rfl
  · rw [CanonicalCertifiedPlankSlabIncidence.members_eq_empty_of_not_isSlab _ hS,
      CanonicalCertifiedPlankSlabIncidence.members_eq_empty_of_not_isSlab _ hS]
    simp

/-- The active row represented back in the old retained index type. -/
def activeCertifiedMembersInRetained
    (D : ShadedConvexPlankFamily iota a b) {theta : NNReal}
    (C : MutualThickeningClustering D theta)
    (q : Fin (Nat.log 2 (Fintype.card iota) + 1))
    {cellIndex : Type v} (cell : cellIndex → Set Space)
    (hcell : ∀ p, MeasurableSet (cell p)) (selected : Finset cellIndex)
    (hmass : (retainedOwnerPlankFamily D C q).shading.shadingMass ≠ 0)
    (hactive : (activeRetainedOwnerCellIndices D C q cell hcell selected).Nonempty)
    (tau : NNReal) (S : ConvexBody Space) :
    Finset {i // i ∈ retainedOwnerSourceIndices C q} :=
  ((activeRetainedOwnerCellCertifiedIncidence
      D C q cell hcell selected hmass hactive).members tau S).map
    ⟨Subtype.val, Subtype.val_injective⟩

theorem activeCertifiedMembersInRetained_subset_all
    (D : ShadedConvexPlankFamily iota a b) {theta : NNReal}
    (C : MutualThickeningClustering D theta)
    (q : Fin (Nat.log 2 (Fintype.card iota) + 1))
    {cellIndex : Type v} (cell : cellIndex → Set Space)
    (hcell : ∀ p, MeasurableSet (cell p)) (selected : Finset cellIndex)
    (hmass : (retainedOwnerPlankFamily D C q).shading.shadingMass ≠ 0)
    (hactive : (activeRetainedOwnerCellIndices D C q cell hcell selected).Nonempty)
    (tau : NNReal) (S : ConvexBody Space) :
    activeCertifiedMembersInRetained
        D C q cell hcell selected hmass hactive tau S ⊆
      (retainedOwnerCellRestrictedCanonicalUnitSlabIncidence
        D C q cell hcell selected hmass).members tau S := by
  classical
  intro i hi
  simp only [activeCertifiedMembersInRetained, Finset.mem_map] at hi
  obtain ⟨j, hj, rfl⟩ := hi
  exact (mem_activeRetainedOwnerCellCertifiedIncidence_iff
    D C q cell hcell selected hmass hactive tau S j).1 hj

theorem activeCertified_members_card_le_all
    (D : ShadedConvexPlankFamily iota a b) {theta : NNReal}
    (C : MutualThickeningClustering D theta)
    (q : Fin (Nat.log 2 (Fintype.card iota) + 1))
    {cellIndex : Type v} (cell : cellIndex → Set Space)
    (hcell : ∀ p, MeasurableSet (cell p)) (selected : Finset cellIndex)
    (hmass : (retainedOwnerPlankFamily D C q).shading.shadingMass ≠ 0)
    (hactive : (activeRetainedOwnerCellIndices D C q cell hcell selected).Nonempty)
    (tau : NNReal) (S : ConvexBody Space) :
    ((activeRetainedOwnerCellCertifiedIncidence
        D C q cell hcell selected hmass hactive).members tau S).card ≤
      ((retainedOwnerCellRestrictedCanonicalUnitSlabIncidence
        D C q cell hcell selected hmass).members tau S).card := by
  rw [← Finset.card_map]
  exact Finset.card_le_card
    (activeCertifiedMembersInRetained_subset_all
      D C q cell hcell selected hmass hactive tau S)

/-- The actual deduplicated selected coarse owners represented in one active
certified slab row. -/
def activeSelectedOwnersInCertifiedSlab
    (D : ShadedConvexPlankFamily iota a b) {theta : NNReal}
    (C : MutualThickeningClustering D theta)
    (q : Fin (Nat.log 2 (Fintype.card iota) + 1))
    {cellIndex : Type v} (cell : cellIndex → Set Space)
    (hcell : ∀ p, MeasurableSet (cell p)) (selected : Finset cellIndex)
    (hmass : (retainedOwnerPlankFamily D C q).shading.shadingMass ≠ 0)
    (hactive : (activeRetainedOwnerCellIndices D C q cell hcell selected).Nonempty)
    (tau : NNReal) (S : ConvexBody Space) :
    Finset {s // s ∈ selectedOwnerLogBucket C q} :=
  ((activeRetainedOwnerCellCertifiedIncidence
      D C q cell hcell selected hmass hactive).members tau S).image
    fun i => selectedOwnerOfRetained C q i.1

theorem mem_activeSelectedOwnersInCertifiedSlab_iff
    (D : ShadedConvexPlankFamily iota a b) {theta : NNReal}
    (C : MutualThickeningClustering D theta)
    (q : Fin (Nat.log 2 (Fintype.card iota) + 1))
    {cellIndex : Type v} (cell : cellIndex → Set Space)
    (hcell : ∀ p, MeasurableSet (cell p)) (selected : Finset cellIndex)
    (hmass : (retainedOwnerPlankFamily D C q).shading.shadingMass ≠ 0)
    (hactive : (activeRetainedOwnerCellIndices D C q cell hcell selected).Nonempty)
    (tau : NNReal) (S : ConvexBody Space)
    (s : {s // s ∈ selectedOwnerLogBucket C q}) :
    s ∈ activeSelectedOwnersInCertifiedSlab
        D C q cell hcell selected hmass hactive tau S ↔
      ∃ i : {i // i ∈ activeRetainedOwnerCellIndices D C q cell hcell selected},
        i ∈ (activeRetainedOwnerCellCertifiedIncidence
          D C q cell hcell selected hmass hactive).members tau S ∧
        selectedOwnerOfRetained C q i.1 = s := by
  classical
  simp [activeSelectedOwnersInCertifiedSlab]

theorem activeSelectedOwnersInCertifiedSlab_card_le_active
    (D : ShadedConvexPlankFamily iota a b) {theta : NNReal}
    (C : MutualThickeningClustering D theta)
    (q : Fin (Nat.log 2 (Fintype.card iota) + 1))
    {cellIndex : Type v} (cell : cellIndex → Set Space)
    (hcell : ∀ p, MeasurableSet (cell p)) (selected : Finset cellIndex)
    (hmass : (retainedOwnerPlankFamily D C q).shading.shadingMass ≠ 0)
    (hactive : (activeRetainedOwnerCellIndices D C q cell hcell selected).Nonempty)
    (tau : NNReal) (S : ConvexBody Space) :
    (activeSelectedOwnersInCertifiedSlab
      D C q cell hcell selected hmass hactive tau S).card ≤
      ((activeRetainedOwnerCellCertifiedIncidence
        D C q cell hcell selected hmass hactive).members tau S).card := by
  classical
  exact Finset.card_image_le

/-- Each deduplicated owner has a literal active fine preimage in the row,
and that preimage certifies containment of the owner's thickened body in the
same double-radius thickening of the queried slab. -/
theorem activeSelectedOwnerThickenedBody_subset_sameSlabThickening
    (D : ShadedConvexPlankFamily iota a b) {theta : NNReal}
    (C : MutualThickeningClustering D theta)
    (q : Fin (Nat.log 2 (Fintype.card iota) + 1))
    {cellIndex : Type v} (cell : cellIndex → Set Space)
    (hcell : ∀ p, MeasurableSet (cell p)) (selected : Finset cellIndex)
    (hmass : (retainedOwnerPlankFamily D C q).shading.shadingMass ≠ 0)
    (hactive : (activeRetainedOwnerCellIndices D C q cell hcell selected).Nonempty)
    {tau : NNReal} {S : ConvexBody Space} (hS : IsSlab 1 tau S)
    (s : {s // s ∈ selectedOwnerLogBucket C q})
    (hs : s ∈ activeSelectedOwnersInCertifiedSlab
      D C q cell hcell selected hmass hactive tau S) :
    (ownerThickenedBody D theta s.1 : Set Space) ⊆
      Metric.cthickening (2 * ((theta * b : NNReal) : Real))
        (S : Set Space) := by
  obtain ⟨i, hi, his⟩ :=
    (mem_activeSelectedOwnersInCertifiedSlab_iff
      D C q cell hcell selected hmass hactive tau S s).1 hs
  subst s
  apply activeOwnerThickenedBody_subset_certifiedSlabThickening
    D C q cell hcell selected hmass hS i
  exact (mem_activeRetainedOwnerCellCertifiedIncidence_iff
    D C q cell hcell selected hmass hactive tau S i).1 hi

#print axioms activeRetainedOwnerCellPlankDatum
#print axioms activeRetainedOwnerCellPlankDatum_carrier_nonempty
#print axioms activeRetainedOwnerCellCertifiedIncidence
#print axioms mem_activeRetainedOwnerCellCertifiedIncidence_iff
#print axioms activeCertifiedMembersInRetained_subset_all
#print axioms activeCertified_members_card_le_all
#print axioms mem_activeSelectedOwnersInCertifiedSlab_iff
#print axioms activeSelectedOwnersInCertifiedSlab_card_le_active
#print axioms activeSelectedOwnerThickenedBody_subset_sameSlabThickening

end
end Family8PlankRetainedOwnerActiveCertifiedOwnerIncidenceV1
