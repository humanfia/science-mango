import FamilyStickyGrounding.Cinematic.FamilyStickyCinematicL32Prop41ActualY1SharpPointSlopeV1

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 2000000

open Set
open scoped Interval

namespace FamilyStickyCinematicL32Prop41ActualY1PaperFineTangencyV1

open Submission.Kakeya.ConvexGeometry
open Submission.Kakeya.Uniformity
open FamilyStickyCinematicL32ActualProjectedCenteredHalfPointSourceV1
open FamilyStickyCinematicL32ActualProjectedCenteredHalfY1ActiveGeometryV1
open FamilyStickyCinematicL32CenteredFractionIntervalsV1
open FamilyStickyCinematicL32CenteredFractionNestingV1
open FamilyStickyCinematicL32Prop41ActualY1FineCoarseRectangleProducerV1
open FamilyStickyCinematicL32Prop41ActualY1FineCoarseTangencyBranchV1
open FamilyStickyCinematicL32Prop41ActualY1SharpFineScaleTangencyV1
open FamilyStickyCinematicL32Prop41ActualY1SharpPointSlopeV1
open FamilyStickyCinematicL32RectangleTangencyV1
open FamilyStickyCinematicL32TubeC2GraphRectangleV1
open FamilyStickyWZ2TubeCarrierCoordinateAdapterV1

noncomputable section

universe u v

/-!
# Actual fine tangency at the explicit paper scale

This is the literal rectangle endpoint of the sharpened Lemma 3.8(2c)
argument.  The only numeric input is `ActualY1SharpFineScaleNumerics`;
the fine parameter, canonical margin, and vertical propagation budget are
all derived.
-/

/-- Every actual active Y1 tube is `5 * radius` tangent to its assigned
literal fine rectangle at `fineT = 10^8 * tGlobal * globalDelta / radius`.
The same fine rectangle is contained in the assigned coarse rectangle. -/
theorem activeY1_paperFine_tangent_and_fine_subset_coarse
    {radius : NNReal} {iota : Type u} [DecidableEq iota]
    (fine : UniformTubeFamily radius iota)
    (physical :
      FamilyStickyCinematicL32FiniteProjectedShadingMultiplicitySliceV1.FiniteProjectedShading
        (Real × Real) iota)
    (E : Set (Real × Real))
    (activeAtPoint : Real × Real -> Finset iota)
    (centerTube : Tube radius) (tubeAt : Real × Real -> Tube radius)
    (f f1 f2 : Real -> Real) (outerA outerB : Real)
    (hOuter : outerA <= outerB)
    (hf : forall z, HasDerivAt f (f1 z) z)
    (hf1 : forall z, HasDerivAt f1 (f2 z) z)
    (tGlobal globalDelta : Real)
    (facts : ActualCenteredHalfY1ActiveGeometryFacts fine physical E
      activeAtPoint tubeAt f f1 f2 outerA outerB hOuter hf hf1
      tGlobal globalDelta)
    (pointSource : ActualCenteredHalfPointRectangleSource E centerTube tubeAt
      f outerA outerB tGlobal)
    (N : ActualY1SharpFineScaleNumerics
      (radius : Real) globalDelta tGlobal (outerB - outerA))
    (hparameter : forall z, z ∈ Icc outerA outerB -> |z| <= 1)
    (hft : forall z, z ∈ Icc outerA outerB -> |f z| <= 2)
    (hf1Lower : forall z, z ∈ Icc outerA outerB -> 1 <= |f1 z|)
    (hf1Upper : forall z, z ∈ Icc outerA outerB -> |f1 z| <= 2)
    (hf2 : forall z, z ∈ Icc outerA outerB -> |f2 z| <= 1 / 100)
    (hf2Continuous : ContinuousOn f2 (Icc outerA outerB))
    (q : Real × Real) (hq : q ∈ E)
    (i : iota) (hi : i ∈ activeAtPoint q) :
    let fineT :=
      prop41Y1PaperFineT (radius : Real) globalDelta tGlobal
    let fineR := centeredTubeC2GraphRectangle (tubeAt q) f f1 f2 hf hf1
      q.2 (radius : Real) fineT
    let coarseR := centeredTubeC2GraphRectangle (tubeAt q) f f1 f2 hf hf1
      q.2 globalDelta tGlobal
    fineR.carrier (radius : Real) ⊆
        cinematicVerticalNeighborhood
          (cinematicTraceValue f
            (tubeGraphA (fine.tubes i)) (tubeGraphB (fine.tubes i))
            (tubeGraphC (fine.tubes i)) (tubeGraphD (fine.tubes i)))
          fineR.rectangle.base (5 * (radius : Real)) ∧
      fineR.carrier (radius : Real) ⊆ coarseR.carrier globalDelta := by
  dsimp only
  let fineT := prop41Y1PaperFineT (radius : Real) globalDelta tGlobal
  have hslope :
      |tubeCinematicTraceFirstValue (fine.tubes i) f f1 q.2 -
          tubeCinematicTraceFirstValue (tubeAt q) f f1 q.2| <=
        prop41Y1SharpSlopeConstant *
          Real.sqrt (tGlobal * globalDelta) :=
    FamilyStickyCinematicL32Prop41ActualY1SharpPointSlopeV1.ActualCenteredHalfY1ActiveGeometryFacts.actual_pointSlope_le_sharpScale
      fine physical E activeAtPoint tubeAt f f1 f2 outerA outerB hOuter
      hf hf1 tGlobal globalDelta facts N hparameter hft hf1Lower hf1Upper
      hf2 hf2Continuous q hq (pointSource.hpointTheta q hq) i hi
  have hcanonicalMargin :
      actualY1FineHalfWidth (radius : Real) fineT <=
        3 * (outerB - outerA) / 32 := by
    simpa only [fineT, actualY1FineHalfWidth] using
      prop41Y1PaperFine_canonicalMargin N
  have hqTheta := pointSource.hpointTheta q hq
  have hmargins := mem_sixteenth_has_quarter_margin hqTheta
  have hbase : Icc
      (q.2 - actualY1FineHalfWidth (radius : Real) fineT)
      (q.2 + actualY1FineHalfWidth (radius : Real) fineT) ⊆
      Icc outerA outerB := by
    intro z hz
    apply quarter_subset_whole hOuter
    constructor
    · linarith [hz.1, hcanonicalMargin, hmargins.1]
    · linarith [hz.2, hcanonicalMargin, hmargins.2]
  constructor
  · apply actualTube_centeredRectangle_tangent_of_pointSlope
      (fine.tubes i) (tubeAt q) f f1 f2 hf hf1
      hparameter hf1Upper hf2
      (mul_nonneg (by norm_num) N.tGlobal_pos.le)
      (facts.hactiveCoefficientUpper q hq i hi)
      (facts.hactiveFullWitness q hq i hi) hslope hbase
    have hbudget := prop41Y1PaperFine_propagation_budget N
    have hcoefficient : 5 * (6 * tGlobal) = 30 * tGlobal := by ring
    rw [hcoefficient]
    simpa only [fineT, actualY1FineHalfWidth] using hbudget
  · exact centeredTubeC2GraphRectangle_carrier_subset
      (tubeAt q) f f1 f2 hf hf1 q.2 (radius : Real) fineT
      globalDelta tGlobal N.fineDelta_le_globalDelta
      (by
        simpa only [fineT] using
          prop41Y1PaperFine_baseScale_le_coarseBaseScale N)

/-- Retained-good-pair endpoint at the explicit paper fine scale. -/
theorem retainedY1Pair_paperFine_tangent_and_fine_subset_coarse
    {radius : NNReal} {iota : Type u} [DecidableEq iota]
    {fineLabel : Type v} [DecidableEq fineLabel]
    (fine : UniformTubeFamily radius iota)
    (physical :
      FamilyStickyCinematicL32FiniteProjectedShadingMultiplicitySliceV1.FiniteProjectedShading
        (Real × Real) iota)
    (E : Set (Real × Real))
    (Y1 :
      FamilyStickyCinematicL32FiniteProjectedShadingMultiplicitySliceV1.FiniteProjectedShading
        (Real × Real) iota)
    (fineLabels : Finset fineLabel) (pointAt : fineLabel -> Real × Real)
    (centerTube : Tube radius) (tubeAt : Real × Real -> Tube radius)
    (f f1 f2 : Real -> Real) (outerA outerB : Real)
    (hOuter : outerA <= outerB)
    (hf : forall z, HasDerivAt f (f1 z) z)
    (hf1 : forall z, HasDerivAt f1 (f2 z) z)
    (tGlobal globalDelta : Real)
    (facts : ActualCenteredHalfY1ActiveGeometryFacts fine physical E
      Y1.activeAtPoint tubeAt f f1 f2 outerA outerB hOuter hf hf1
      tGlobal globalDelta)
    (pointSource : ActualCenteredHalfPointRectangleSource E centerTube tubeAt
      f outerA outerB tGlobal)
    (hpointE : forall r, r ∈ fineLabels -> pointAt r ∈ E)
    (N : ActualY1SharpFineScaleNumerics
      (radius : Real) globalDelta tGlobal (outerB - outerA))
    (hparameter : forall z, z ∈ Icc outerA outerB -> |z| <= 1)
    (hft : forall z, z ∈ Icc outerA outerB -> |f z| <= 2)
    (hf1Lower : forall z, z ∈ Icc outerA outerB -> 1 <= |f1 z|)
    (hf1Upper : forall z, z ∈ Icc outerA outerB -> |f1 z| <= 2)
    (hf2 : forall z, z ∈ Icc outerA outerB -> |f2 z| <= 1 / 100)
    (hf2Continuous : ContinuousOn f2 (Icc outerA outerB))
    (keep : iota -> fineLabel -> Prop) (i : iota) (r : fineLabel)
    (hpair : (i, r) ∈
      (y1FineCoarseRectangleData fine Y1 fineLabels pointAt tubeAt f f1 f2
        hf hf1 (radius : Real)
        (prop41Y1PaperFineT (radius : Real) globalDelta tGlobal)
        globalDelta tGlobal).retainedGoodPairs keep) :
    let D := y1FineCoarseRectangleData fine Y1 fineLabels pointAt tubeAt
      f f1 f2 hf hf1 (radius : Real)
      (prop41Y1PaperFineT (radius : Real) globalDelta tGlobal)
      globalDelta tGlobal
    (D.fineRectangleAt r).carrier (radius : Real) ⊆
        cinematicVerticalNeighborhood
          (cinematicTraceValue f
            (tubeGraphA (fine.tubes i)) (tubeGraphB (fine.tubes i))
            (tubeGraphC (fine.tubes i)) (tubeGraphD (fine.tubes i)))
          (D.fineRectangleAt r).rectangle.base (5 * (radius : Real)) ∧
      (D.fineRectangleAt r).carrier (radius : Real) ⊆
        (D.coarseRectangleAt r).carrier globalDelta := by
  dsimp only
  have hretained := y1FineCoarseRectangleData_retainedPair_active
    fine Y1 fineLabels pointAt tubeAt f f1 f2 hf hf1
      (radius : Real)
      (prop41Y1PaperFineT (radius : Real) globalDelta tGlobal)
      globalDelta tGlobal keep i r hpair
  have hqE : pointAt r ∈ E := hpointE r hretained.1
  simpa only [y1FineCoarseRectangleData] using
    activeY1_paperFine_tangent_and_fine_subset_coarse
      fine physical E Y1.activeAtPoint centerTube tubeAt f f1 f2 outerA
      outerB hOuter hf hf1 tGlobal globalDelta facts pointSource N
      hparameter hft hf1Lower hf1Upper hf2 hf2Continuous (pointAt r) hqE
      i hretained.2.1

#print axioms activeY1_paperFine_tangent_and_fine_subset_coarse
#print axioms retainedY1Pair_paperFine_tangent_and_fine_subset_coarse

end

end FamilyStickyCinematicL32Prop41ActualY1PaperFineTangencyV1
