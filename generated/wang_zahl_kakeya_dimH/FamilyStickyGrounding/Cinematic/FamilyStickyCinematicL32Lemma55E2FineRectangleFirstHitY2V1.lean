import FamilyStickyGrounding.Cinematic.FamilyStickyCinematicL32Lemma55FiniteMeasurableFirstHitPartitionV1
import FamilyStickyGrounding.Cinematic.FamilyStickyCinematicL32CurvilinearRectangleGlobalMeasureBoundV1
import FamilyStickyGrounding.Cinematic.FamilyStickyCinematicL32Prop41FiniteProjectedShadingE2MassV1
import FamilyStickyGrounding.Cinematic.FamilyStickyCinematicL32Lemma55Lemma316TwoStageGreedyClusteringTwoScaleV1

set_option autoImplicit false
set_option warningAsError true

open Set MeasureTheory
open scoped BigOperators ENNReal

namespace FamilyStickyCinematicL32Lemma55E2FineRectangleFirstHitY2V1

open FamilyStickyCinematicL32CurvilinearRectanglePointMultiplicityV1
open FamilyStickyCinematicL32CurvilinearRectangleVolumeV1
open FamilyStickyCinematicL32CurvilinearRectangleGlobalMeasureBoundV1
open FamilyStickyCinematicL32FiniteProjectedShadingMultiplicitySliceV1
open FamilyStickyCinematicL32FiniteProjectedPositiveMultiplicityDyadicV1
open FamilyStickyCinematicL32PyzLowMultiplicityRestrictedThreeHalfV1
open FamilyStickyCinematicL32Lemma55CenteredRectangleDilationV1
open FamilyStickyCinematicL32Lemma55FiniteMeasurableFirstHitPartitionV1
open FamilyStickyCinematicL32Lemma312PivotCenteredContainerV1
open FamilyStickyCinematicL32Lemma55Lemma316TwoStageGreedyClusteringTwoScaleV1

noncomputable section

universe u v

/-!
# Literal measurable `Y₂(R)` assignment from a finite fine-rectangle cover

Given the paper-faithful geometric statement that a measurable source set is
covered by finitely many selected fine rectangle carriers, assign every source
point to the first selected carrier containing it.  This produces measurable,
pairwise-disjoint shadings inside the actual fine rectangles and transports the
source measure exactly, with no overlap or occupied-label loss.

For the actual projected E2 cell, measurability is already automatic.  Thus the
only geometric input exposed by the projected-E2 theorem below is the literal
selected-fine-rectangle cover.
-/

/-- Deterministic first-hit shading inside the selected fine rectangles. -/
noncomputable def firstHitFineRectangleY2
    {index : Type u} [DecidableEq index]
    (source : Set (Real × Real)) (items : Finset index)
    (rectangleAt : index -> C2GraphRectangle) (delta : Real)
    (i : index) : Set (Real × Real) :=
  finiteFirstHitFiber source items
    (fun j => (rectangleAt j).carrier delta) i

theorem measurableSet_firstHitFineRectangleY2
    {index : Type u} [DecidableEq index]
    (source : Set (Real × Real)) (items : Finset index)
    (rectangleAt : index -> C2GraphRectangle) (delta : Real)
    (hsource : MeasurableSet source) (i : index) :
    MeasurableSet
      (firstHitFineRectangleY2 source items rectangleAt delta i) := by
  apply measurableSet_finiteFirstHitFiber
  · exact hsource
  · intro j _hj
    simpa only [C2GraphRectangle.carrier] using
      measurableSet_graphRectangle_carrier
        (rectangleAt j).rectangle delta
        (measurable_c2GraphRectangle_graph (rectangleAt j))

theorem firstHitFineRectangleY2_subset_source
    {index : Type u} [DecidableEq index]
    (source : Set (Real × Real)) (items : Finset index)
    (rectangleAt : index -> C2GraphRectangle) (delta : Real)
    (i : index) :
    firstHitFineRectangleY2 source items rectangleAt delta i ⊆ source :=
  finiteFirstHitFiber_subset_source source items
    (fun j => (rectangleAt j).carrier delta) i

theorem firstHitFineRectangleY2_subset_carrier
    {index : Type u} [DecidableEq index]
    (source : Set (Real × Real)) (items : Finset index)
    (rectangleAt : index -> C2GraphRectangle) (delta : Real)
    (i : index) :
    firstHitFineRectangleY2 source items rectangleAt delta i ⊆
      (rectangleAt i).carrier delta :=
  finiteFirstHitFiber_subset_event source items
    (fun j => (rectangleAt j).carrier delta) i

theorem firstHitFineRectangleY2_pairwiseDisjoint
    {index : Type u} [DecidableEq index]
    (source : Set (Real × Real)) (items : Finset index)
    (rectangleAt : index -> C2GraphRectangle) (delta : Real) :
    Set.PairwiseDisjoint (items : Set index)
      (firstHitFineRectangleY2 source items rectangleAt delta) :=
  finiteFirstHitFibers_pairwiseDisjoint source items
    (fun j => (rectangleAt j).carrier delta)

theorem biUnion_firstHitFineRectangleY2_eq_source
    {index : Type u} [DecidableEq index]
    (source : Set (Real × Real)) (items : Finset index)
    (rectangleAt : index -> C2GraphRectangle) (delta : Real)
    (hcover : forall x, x ∈ source ->
      exists i, i ∈ items ∧ x ∈ (rectangleAt i).carrier delta) :
    (⋃ i ∈ (items : Set index),
      firstHitFineRectangleY2 source items rectangleAt delta i) = source :=
  biUnion_finiteFirstHitFiber_eq_source source items
    (fun j => (rectangleAt j).carrier delta) hcover

theorem sum_measure_firstHitFineRectangleY2_eq_source
    {index : Type u} [DecidableEq index]
    (mu : Measure (Real × Real))
    (source : Set (Real × Real)) (items : Finset index)
    (rectangleAt : index -> C2GraphRectangle) (delta : Real)
    (hsource : MeasurableSet source)
    (hcover : forall x, x ∈ source ->
      exists i, i ∈ items ∧ x ∈ (rectangleAt i).carrier delta) :
    (∑ i ∈ items,
      mu (firstHitFineRectangleY2 source items rectangleAt delta i)) =
        mu source := by
  apply sum_measure_finiteFirstHitFiber_eq_source
  · exact hsource
  · intro j _hj
    simpa only [C2GraphRectangle.carrier] using
      measurableSet_graphRectangle_carrier
        (rectangleAt j).rectangle delta
        (measurable_c2GraphRectangle_graph (rectangleAt j))
  · exact hcover

/-- On a projected dyadic E2 cell, the first-hit assignment needs only the
literal cover by the selected fine rectangle carriers. -/
theorem projectedE2_firstHitFineRectangleY2_package
    {tube : Type u} {index : Type v}
    [DecidableEq tube] [DecidableEq index]
    (Z : FiniteProjectedShading (Real × Real) tube) (label : Int)
    (items : Finset index) (rectangleAt : index -> C2GraphRectangle)
    (delta : Real)
    (hcover : forall x,
      x ∈ projectedPositiveMultiplicityDyadicCell Z label ->
        exists i, i ∈ items ∧ x ∈ (rectangleAt i).carrier delta) :
    (forall i,
      MeasurableSet (firstHitFineRectangleY2
        (projectedPositiveMultiplicityDyadicCell Z label)
        items rectangleAt delta i)) ∧
    Set.PairwiseDisjoint (items : Set index)
      (firstHitFineRectangleY2
        (projectedPositiveMultiplicityDyadicCell Z label)
        items rectangleAt delta) ∧
    (⋃ i ∈ (items : Set index),
      firstHitFineRectangleY2
        (projectedPositiveMultiplicityDyadicCell Z label)
        items rectangleAt delta i) =
          projectedPositiveMultiplicityDyadicCell Z label ∧
    (forall mu : Measure (Real × Real),
      (∑ i ∈ items,
        mu (firstHitFineRectangleY2
          (projectedPositiveMultiplicityDyadicCell Z label)
          items rectangleAt delta i)) =
        mu (projectedPositiveMultiplicityDyadicCell Z label)) ∧
    (forall i,
      firstHitFineRectangleY2
        (projectedPositiveMultiplicityDyadicCell Z label)
        items rectangleAt delta i ⊆ (rectangleAt i).carrier delta) := by
  have hE2 : MeasurableSet
      (projectedPositiveMultiplicityDyadicCell Z label) :=
    measurableSet_projectedPositiveMultiplicityDyadicCell Z label
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro i
    exact measurableSet_firstHitFineRectangleY2 _ _ _ _ hE2 i
  · exact firstHitFineRectangleY2_pairwiseDisjoint _ _ _ _
  · exact biUnion_firstHitFineRectangleY2_eq_source _ _ _ _ hcover
  · intro mu
    exact sum_measure_firstHitFineRectangleY2_eq_source
      mu _ _ _ _ hE2 hcover
  · intro i
    exact firstHitFineRectangleY2_subset_carrier _ _ _ _ i

/-- The first-hit shading of every raw vertex is automatically contained in
the enlarged first-stage owner rectangle supplied by the existing two-stage
greedy clustering outcome. -/
theorem firstHitFineRectangleY2_subset_twoStageOwnerContainer
    {index : Type u} [DecidableEq index]
    (source : Set (Real × Real)) (vertices : Finset index)
    (rectangleAt : index -> C2GraphRectangle)
    (domain : Set Real) (center : C2GraphRectangle)
    (delta localScale referenceScale comparisonLambda curvatureRatio : Real)
    (weight : index -> ENNReal)
    (C : CompactC2TwoStageGreedyClusteringAtScalesOutcome vertices
      rectangleAt domain center delta localScale referenceScale
        comparisonLambda curvatureRatio weight)
    (i : index) (hi : i ∈ vertices) :
    firstHitFineRectangleY2 source vertices rectangleAt delta i ⊆
      (centeredC2GraphRectangleDilation (rectangleAt (C.owner i)) delta
        localScale (pyzLemma312PackingLambda 100)).carrier
          (pyzLemma312PackingLambda 100 * delta) :=
  (firstHitFineRectangleY2_subset_carrier
    source vertices rectangleAt delta i).trans (C.cluster_carrier_subset i hi)

#print axioms firstHitFineRectangleY2
#print axioms measurableSet_firstHitFineRectangleY2
#print axioms firstHitFineRectangleY2_pairwiseDisjoint
#print axioms biUnion_firstHitFineRectangleY2_eq_source
#print axioms sum_measure_firstHitFineRectangleY2_eq_source
#print axioms projectedE2_firstHitFineRectangleY2_package
#print axioms firstHitFineRectangleY2_subset_twoStageOwnerContainer

end

end FamilyStickyCinematicL32Lemma55E2FineRectangleFirstHitY2V1
