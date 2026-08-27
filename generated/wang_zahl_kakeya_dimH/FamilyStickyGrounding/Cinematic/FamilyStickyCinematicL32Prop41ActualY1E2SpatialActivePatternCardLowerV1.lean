import FamilyStickyGrounding.Cinematic.FamilyStickyCinematicL32Prop41ActualY1E2SpatialActivePatternFirstHitY2ConnectorV1
import FamilyStickyGrounding.Cinematic.FamilyStickyCinematicL32CurvilinearRectangleGlobalMeasureBoundV1
import Mathlib.Tactic

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 2000000

open Set MeasureTheory
open scoped BigOperators ENNReal

namespace FamilyStickyCinematicL32Prop41ActualY1E2SpatialActivePatternCardLowerV1

open Submission.Kakeya.ConvexGeometry
open Submission.Kakeya.Uniformity
open FamilyStickyCinematicL32ActualProjectedCenteredHalfPointSourceV1
open FamilyStickyCinematicL32CurvilinearRectanglePointMultiplicityV1
open FamilyStickyCinematicL32ActualProjectedCenteredHalfTangencyStageV1
open FamilyStickyCinematicL32CurvilinearRectangleGlobalMeasureBoundV1
open FamilyStickyCinematicL32FiniteProjectedPositiveMultiplicityDyadicV1
open FamilyStickyCinematicL32FiniteProjectedShadingMultiplicitySliceV1
open FamilyStickyCinematicL32PyzLowMultiplicityRestrictedThreeHalfV1
open FamilyStickyCinematicL32Lemma55E2FineRectangleFirstHitY2V1
open FamilyStickyCinematicL32Prop41ActualY1E2SpatialActivePatternFloorCoverV1
open FamilyStickyCinematicL32Prop41ActualY1FineCoarseRectangleProducerV1

noncomputable section

universe u v

/-!
# Raw spatial E2 cover cardinal lower bound

The actual occupied active-pattern/floor labels cover E2 before any G-prime
retention or random sampling.  The measurable first-hit partition preserves
the total E2 mass, while each first-hit fibre lies in one literal fine
rectangle.  Exact rectangle area therefore yields the denominator-free lower
cardinality inequality below.

No statement in this module says that a retained, sampled, or three-shift
selected subfamily still covers E2.
-/

/-- A finite fine-rectangle cover with a common exact base length has enough
labels to carry the source volume. -/
theorem volume_source_le_card_mul_fineArea_of_firstHitCover
    {index : Type u} [DecidableEq index]
    (source : Set (Real × Real)) (items : Finset index)
    (rectangleAt : index -> C2GraphRectangle)
    (delta baseLength : Real)
    (hsource : MeasurableSet source)
    (hcover : forall x, x ∈ source ->
      exists i, i ∈ items ∧ x ∈ (rectangleAt i).carrier delta)
    (hlength : forall i, i ∈ items ->
      (rectangleAt i).rectangle.right -
          (rectangleAt i).rectangle.left = baseLength) :
    volume source <=
      (items.card : ENNReal) *
        (ENNReal.ofReal (2 * delta) * ENNReal.ofReal baseLength) := by
  let area : ENNReal :=
    ENNReal.ofReal (2 * delta) * ENNReal.ofReal baseLength
  have hmass :
      (∑ i ∈ items,
        volume (firstHitFineRectangleY2
          source items rectangleAt delta i)) = volume source :=
    sum_measure_firstHitFineRectangleY2_eq_source volume source items
      rectangleAt delta hsource hcover
  calc
    volume source =
        ∑ i ∈ items,
          volume (firstHitFineRectangleY2
            source items rectangleAt delta i) := hmass.symm
    _ <= ∑ i ∈ items, volume ((rectangleAt i).carrier delta) := by
      apply Finset.sum_le_sum
      intro i _hi
      exact measure_mono
        (firstHitFineRectangleY2_subset_carrier
          source items rectangleAt delta i)
    _ = ∑ _i ∈ items, area := by
      apply Finset.sum_congr rfl
      intro i hi
      rw [volume_c2GraphRectangle_carrier, hlength i hi]
    _ = (items.card : ENNReal) * area := by
      simp [nsmul_eq_mul]
    _ = (items.card : ENNReal) *
        (ENNReal.ofReal (2 * delta) * ENNReal.ofReal baseLength) := rfl

/-- Actual centered-half specialization on the occupied spatial
active-pattern/floor labels covering the projected E2 cell. -/
theorem actualCenteredHalfProjectedE2_volume_le_spatialActivePattern_card_mul_fineArea
    {radius : NNReal} {iota : Type v} [DecidableEq iota]
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
    volume source <=
      (fineLabels.card : ENNReal) *
        (ENNReal.ofReal (2 * (radius : Real)) *
          ENNReal.ofReal (Real.sqrt ((radius : Real) / fineT))) := by
  dsimp only
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
  apply volume_source_le_card_mul_fineArea_of_firstHitCover
    source fineLabels D.fineRectangleAt (radius : Real)
      (Real.sqrt ((radius : Real) / fineT))
  · exact measurableSet_projectedPositiveMultiplicityDyadicCell Y1 label
  · exact actualCenteredHalfPointSource_spatialActivePattern_fineRectangle_cover
      fine physical Y1 source hmesh f f1 f2 outerA outerB hOuter hf hf1
      globalScale globalCenter ceiling exponent pointSource hparameter fineT
      coarseDelta coarseT hmeshBase
  · intro r _hr
    exact centeredTubeC2GraphRectangle_length
      (tubeAt (pointAt r)) f f1 f2 hf hf1 (pointAt r).2
        (radius : Real) fineT

#print axioms volume_source_le_card_mul_fineArea_of_firstHitCover
#print axioms actualCenteredHalfProjectedE2_volume_le_spatialActivePattern_card_mul_fineArea

end

end FamilyStickyCinematicL32Prop41ActualY1E2SpatialActivePatternCardLowerV1
