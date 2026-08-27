import FamilyStickyGrounding.Cinematic.FamilyStickyCinematicL32Lemma55E2FineRectangleFirstHitY2V1
import FamilyStickyGrounding.Cinematic.FamilyStickyCinematicL32Prop41ActualY1E2SpatialActivePatternFloorCoverV1

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 2000000

open Set MeasureTheory
open scoped BigOperators ENNReal

namespace FamilyStickyCinematicL32Prop41ActualY1E2SpatialActivePatternFirstHitY2ConnectorV1

open Submission.Kakeya.ConvexGeometry
open Submission.Kakeya.Uniformity
open FamilyStickyCinematicL32FiniteProjectedPositiveMultiplicityDyadicV1
open FamilyStickyCinematicL32FiniteProjectedShadingMultiplicitySliceV1
open FamilyStickyCinematicL32ActualProjectedCenteredHalfTangencyStageV1
open FamilyStickyCinematicL32ActualProjectedCenteredHalfPointSourceV1
open FamilyStickyCinematicL32Prop41ActualY1FineCoarseRectangleProducerV1
open FamilyStickyCinematicL32Prop41ActualY1E2SpatialActivePatternFloorCoverV1
open FamilyStickyCinematicL32Lemma55E2FineRectangleFirstHitY2V1

noncomputable section

universe u

/-!
# Actual E2 spatial cover to measurable first-hit Y2

The occupied active-pattern/floor labels cover the actual projected E2 cell.
Feeding that literal cover into the finite first-hit construction produces
measurable, pairwise-disjoint Y2 fibres with exact total E2 mass.  No selected
survivor cover or measurable-assignment callback is assumed.
-/

theorem actualCenteredHalfProjectedE2_spatialActivePattern_firstHitY2_package
    {radius : NNReal} {iota : Type u} [DecidableEq iota]
    (fine : UniformTubeFamily radius iota)
    (physical Y1 : FiniteProjectedShading (Real × Real) iota)
    (label : Int) {mesh : Real}
    (hmesh : 0 < mesh)
    (f f1 f2 : Real -> Real) (outerA outerB : Real)
    (hOuter : outerA ≤ outerB)
    (hf : ∀ z, HasDerivAt f (f1 z) z)
    (hf1 : ∀ z, HasDerivAt f1 (f2 z) z)
    (globalScale : Real) (globalCenter : Tube radius)
    (ceiling exponent : Real)
    (pointSource : ActualCenteredHalfPointRectangleSource
      (projectedPositiveMultiplicityDyadicCell Y1 label) globalCenter
      (actualProjectedCenteredHalfTangencyCenterTubeAt fine physical
        f f1 f2 outerA outerB hOuter hf hf1 globalScale globalCenter
        ceiling exponent)
      f outerA outerB globalScale)
    (hparameter : ∀ z, z ∈ Icc outerA outerB -> |z| ≤ 1)
    (fineT coarseDelta coarseT : Real)
    (hmeshBase : mesh ≤ Real.sqrt ((radius : Real) / fineT) / 2) :
    let source := projectedPositiveMultiplicityDyadicCell Y1 label
    let patternAt := physical.activeAtPoint
    let fineLabels : Finset
      (SpatialActivePatternLabel physical.ambient patternAt source mesh) :=
        Finset.univ
    let pointAt := spatialActivePatternRepresentative
      physical.ambient patternAt source mesh
    let tubeAt := actualProjectedCenteredHalfTangencyCenterTubeAt fine physical
      f f1 f2 outerA outerB hOuter hf hf1 globalScale globalCenter
      ceiling exponent
    let D := y1FineCoarseRectangleData fine Y1 fineLabels pointAt tubeAt
      f f1 f2 hf hf1 (radius : Real) fineT coarseDelta coarseT
    (forall r, MeasurableSet
      (firstHitFineRectangleY2 source fineLabels D.fineRectangleAt
        (radius : Real) r)) ∧
    Set.PairwiseDisjoint (fineLabels : Set _)
      (firstHitFineRectangleY2 source fineLabels D.fineRectangleAt
        (radius : Real)) ∧
    (⋃ r ∈ (fineLabels : Set _),
      firstHitFineRectangleY2 source fineLabels D.fineRectangleAt
        (radius : Real) r) = source ∧
    (forall mu : Measure (Real × Real),
      (∑ r ∈ fineLabels,
        mu (firstHitFineRectangleY2 source fineLabels D.fineRectangleAt
          (radius : Real) r)) = mu source) ∧
    (forall r,
      firstHitFineRectangleY2 source fineLabels D.fineRectangleAt
          (radius : Real) r ⊆
        (D.fineRectangleAt r).carrier (radius : Real)) := by
  dsimp only
  apply projectedE2_firstHitFineRectangleY2_package Y1 label
  exact actualCenteredHalfPointSource_spatialActivePattern_fineRectangle_cover
    fine physical Y1
    (projectedPositiveMultiplicityDyadicCell Y1 label) hmesh
    f f1 f2 outerA outerB hOuter hf hf1 globalScale globalCenter
    ceiling exponent pointSource hparameter fineT coarseDelta coarseT hmeshBase

#print axioms actualCenteredHalfProjectedE2_spatialActivePattern_firstHitY2_package

end

end FamilyStickyCinematicL32Prop41ActualY1E2SpatialActivePatternFirstHitY2ConnectorV1
