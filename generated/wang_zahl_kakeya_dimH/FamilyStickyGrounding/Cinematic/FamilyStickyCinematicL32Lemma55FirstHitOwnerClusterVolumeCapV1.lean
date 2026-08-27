import FamilyStickyGrounding.Cinematic.FamilyStickyCinematicL32Lemma55E2FineRectangleFirstHitY2V1
import FamilyStickyGrounding.Cinematic.FamilyStickyCinematicL32Lemma55Lemma316TwoStageGreedyClusteringAtScalesV1

set_option autoImplicit false
set_option warningAsError true

open Set MeasureTheory
open scoped BigOperators ENNReal

namespace FamilyStickyCinematicL32Lemma55FirstHitOwnerClusterVolumeCapV1

open FamilyStickyCinematicL32CurvilinearRectanglePointMultiplicityV1
open FamilyStickyCinematicL32CurvilinearRectangleGlobalMeasureBoundV1
open FamilyStickyCinematicL32Lemma312PivotCenteredContainerV1
open FamilyStickyCinematicL32Lemma55CenteredRectangleDilationV1
open FamilyStickyCinematicL32Lemma312PivotCenteredContainerTwoScaleV1
open FamilyStickyCinematicL32Lemma316CompactC2GreedySelectionV1
open FamilyStickyCinematicL32Lemma55E2FineRectangleFirstHitY2V1
open FamilyStickyCinematicL32Lemma55Lemma316TwoStageGreedyClusteringAtScalesV1
open FamilyStickyCinematicL32Lemma55Lemma316TwoStageGreedyClusteringTwoScaleV1

noncomputable section

universe u

/-!
# First-hit mass inside one owner container

The owner-fibre weight is the literal volume of its first-hit Y2 pieces.
Global first-hit disjointness and containment in the common owner dilation
bound their sum by the volume of that dilation.  No uniform lower bound on
the individual pieces is used.
-/

/-- General measure form of the lossless owner-fibre mass bound. -/
theorem ownerClusterMass_measure_le_target
    {point : Type u} [MeasurableSpace point]
    {index : Type*} [DecidableEq index]
    (mu : Measure point) (vertices : Finset index) (owner : index -> index)
    (shadingAt : index -> Set point) (pivot : index) (target : Set point)
    (hmeasurable : forall i, i ∈ vertices -> MeasurableSet (shadingAt i))
    (hdisjoint : Set.PairwiseDisjoint (vertices : Set index) shadingAt)
    (hsubset : forall i, i ∈ vertices -> owner i = pivot ->
      shadingAt i ⊆ target) :
    ownerClusterMass vertices owner (fun i => mu (shadingAt i)) pivot <=
      mu target := by
  classical
  let cluster := vertices.filter fun i => owner i = pivot
  have hclusterDisjoint :
      Set.PairwiseDisjoint (cluster : Set index) shadingAt := by
    intro i hi j hj hij
    change Disjoint (shadingAt i) (shadingAt j)
    apply hdisjoint
    · exact Finset.filter_subset _ _ hi
    · exact Finset.filter_subset _ _ hj
    · exact hij
  have hclusterMeasurable : forall i, i ∈ cluster ->
      MeasurableSet (shadingAt i) := by
    intro i hi
    exact hmeasurable i (Finset.filter_subset _ _ hi)
  have hunionSubset :
      (⋃ i ∈ (cluster : Set index), shadingAt i) ⊆ target := by
    intro x hx
    simp only [Set.mem_iUnion] at hx
    obtain ⟨i, hi, hxi⟩ := hx
    have hiData := Finset.mem_filter.mp hi
    exact hsubset i hiData.1 hiData.2 hxi
  calc
    ownerClusterMass vertices owner (fun i => mu (shadingAt i)) pivot =
        ∑ i ∈ cluster, mu (shadingAt i) := by
      rfl
    _ = mu (⋃ i ∈ (cluster : Set index), shadingAt i) :=
      (measure_biUnion_finset hclusterDisjoint hclusterMeasurable).symm
    _ <= mu target := measure_mono hunionSubset

/-- For the two-stage clustering carrying a literal cluster-carrier field,
the first-hit volume in one owner fibre lies in its owner dilation. -/
theorem firstHitY2_ownerClusterMass_le_ownerDilation
    {index : Type u} [DecidableEq index]
    (source : Set (Real × Real)) (vertices : Finset index)
    (rectangleAt : index -> C2GraphRectangle)
    (domain : Set Real) (center : C2GraphRectangle)
    (delta localScale referenceScale comparisonLambda curvatureRatio : Real)
    (C : CompactC2TwoStageGreedyClusteringAtScalesOutcome vertices
      rectangleAt domain center delta localScale referenceScale
        comparisonLambda curvatureRatio
        (fun i => volume
          (firstHitFineRectangleY2 source vertices rectangleAt delta i)))
    (hsource : MeasurableSet source) (pivot : index) :
    ownerClusterMass vertices C.owner
        (fun i => volume
          (firstHitFineRectangleY2 source vertices rectangleAt delta i))
        pivot <=
      volume
        ((centeredC2GraphRectangleDilation (rectangleAt pivot) delta
          localScale (pyzLemma312PackingLambda 100)).carrier
            (pyzLemma312PackingLambda 100 * delta)) := by
  apply ownerClusterMass_measure_le_target volume vertices C.owner
    (firstHitFineRectangleY2 source vertices rectangleAt delta) pivot
  · intro i _hi
    exact measurableSet_firstHitFineRectangleY2
      source vertices rectangleAt delta hsource i
  · exact firstHitFineRectangleY2_pairwiseDisjoint
      source vertices rectangleAt delta
  · intro i hi howner
    apply (firstHitFineRectangleY2_subset_carrier
      source vertices rectangleAt delta i).trans
    simpa only [howner] using C.cluster_carrier_subset i hi

/-- Exact carrier area turns the preceding owner-dilation volume into the
explicit PYZ scale expression. -/
theorem firstHitY2_ownerClusterMass_le_explicitDilationArea
    {index : Type u} [DecidableEq index]
    (source : Set (Real × Real)) (vertices : Finset index)
    (rectangleAt : index -> C2GraphRectangle)
    (domain : Set Real) (center : C2GraphRectangle)
    (delta localScale referenceScale comparisonLambda curvatureRatio : Real)
    (C : CompactC2TwoStageGreedyClusteringAtScalesOutcome vertices
      rectangleAt domain center delta localScale referenceScale
        comparisonLambda curvatureRatio
        (fun i => volume
          (firstHitFineRectangleY2 source vertices rectangleAt delta i)))
    (hsource : MeasurableSet source) (pivot : index) :
    ownerClusterMass vertices C.owner
        (fun i => volume
          (firstHitFineRectangleY2 source vertices rectangleAt delta i))
        pivot <=
      ENNReal.ofReal (2 * (pyzLemma312PackingLambda 100 * delta)) *
        ENNReal.ofReal
          (Real.sqrt
            (pyzLemma312PackingLambda 100 * delta / localScale)) := by
  calc
    ownerClusterMass vertices C.owner
        (fun i => volume
          (firstHitFineRectangleY2 source vertices rectangleAt delta i))
        pivot <=
      volume
        ((centeredC2GraphRectangleDilation (rectangleAt pivot) delta
          localScale (pyzLemma312PackingLambda 100)).carrier
            (pyzLemma312PackingLambda 100 * delta)) :=
      firstHitY2_ownerClusterMass_le_ownerDilation source vertices
        rectangleAt domain center delta localScale referenceScale
        comparisonLambda curvatureRatio C hsource pivot
    _ = ENNReal.ofReal (2 * (pyzLemma312PackingLambda 100 * delta)) *
        ENNReal.ofReal
          (Real.sqrt
            (pyzLemma312PackingLambda 100 * delta / localScale)) := by
      rw [volume_c2GraphRectangle_carrier,
        centeredC2GraphRectangleDilation_length]

/-- Lossless first-hit mass, the two-stage mass transport, and the owner-area
cap combine to bound the whole source by selected cardinality times one
explicit dilation area. -/
theorem volume_source_le_neighbourBound_mul_selectedCard_mul_dilationArea
    {index : Type u} [DecidableEq index]
    (source : Set (Real × Real)) (vertices : Finset index)
    (rectangleAt : index -> C2GraphRectangle)
    (domain : Set Real) (center : C2GraphRectangle)
    (delta localScale referenceScale comparisonLambda curvatureRatio : Real)
    (C : CompactC2TwoStageGreedyClusteringAtScalesOutcome vertices
      rectangleAt domain center delta localScale referenceScale
        comparisonLambda curvatureRatio
        (fun i => volume
          (firstHitFineRectangleY2 source vertices rectangleAt delta i)))
    (hsource : MeasurableSet source)
    (hcover : forall x, x ∈ source ->
      exists i, i ∈ vertices ∧ x ∈ (rectangleAt i).carrier delta) :
    volume source <=
      pyzClosedNeighbourBound
          (pyzLemma312TwoScalePackingLambda
            comparisonLambda curvatureRatio) *
        (C.selected.card : ENNReal) *
        (ENNReal.ofReal (2 * (pyzLemma312PackingLambda 100 * delta)) *
          ENNReal.ofReal
            (Real.sqrt
              (pyzLemma312PackingLambda 100 * delta / localScale))) := by
  let area : ENNReal :=
    ENNReal.ofReal (2 * (pyzLemma312PackingLambda 100 * delta)) *
      ENNReal.ofReal
        (Real.sqrt
          (pyzLemma312PackingLambda 100 * delta / localScale))
  have hmass :
      (∑ i ∈ vertices,
        volume (firstHitFineRectangleY2
          source vertices rectangleAt delta i)) = volume source :=
    sum_measure_firstHitFineRectangleY2_eq_source volume source vertices
      rectangleAt delta hsource hcover
  have hcluster : forall b, b ∈ C.selected ->
      (∑ i ∈ vertices.filter (fun i => C.owner i = b),
        volume (firstHitFineRectangleY2
          source vertices rectangleAt delta i)) <= area := by
    intro b _hb
    simpa only [ownerClusterMass, area] using
      (firstHitY2_ownerClusterMass_le_explicitDilationArea source vertices
        rectangleAt domain center delta localScale referenceScale
        comparisonLambda curvatureRatio C hsource b)
  calc
    volume source =
        ∑ i ∈ vertices,
          volume (firstHitFineRectangleY2
            source vertices rectangleAt delta i) := hmass.symm
    _ <= pyzClosedNeighbourBound
          (pyzLemma312TwoScalePackingLambda
            comparisonLambda curvatureRatio) *
        ∑ b ∈ C.selected,
          ∑ i ∈ vertices.filter (fun i => C.owner i = b),
            volume (firstHitFineRectangleY2
              source vertices rectangleAt delta i) :=
      C.raw_mass_le_selected_cluster_mass
    _ <= pyzClosedNeighbourBound
          (pyzLemma312TwoScalePackingLambda
            comparisonLambda curvatureRatio) *
        ∑ _b ∈ C.selected, area := by
      gcongr with b hb
      exact hcluster b hb
    _ = pyzClosedNeighbourBound
          (pyzLemma312TwoScalePackingLambda
            comparisonLambda curvatureRatio) *
        (C.selected.card : ENNReal) * area := by
      simp [nsmul_eq_mul, mul_assoc]
    _ = pyzClosedNeighbourBound
          (pyzLemma312TwoScalePackingLambda
            comparisonLambda curvatureRatio) *
        (C.selected.card : ENNReal) *
        (ENNReal.ofReal (2 * (pyzLemma312PackingLambda 100 * delta)) *
          ENNReal.ofReal
            (Real.sqrt
              (pyzLemma312PackingLambda 100 * delta / localScale))) := by
      rfl


#print axioms ownerClusterMass_measure_le_target
#print axioms firstHitY2_ownerClusterMass_le_ownerDilation
#print axioms firstHitY2_ownerClusterMass_le_explicitDilationArea
#print axioms volume_source_le_neighbourBound_mul_selectedCard_mul_dilationArea

end

end FamilyStickyCinematicL32Lemma55FirstHitOwnerClusterVolumeCapV1
