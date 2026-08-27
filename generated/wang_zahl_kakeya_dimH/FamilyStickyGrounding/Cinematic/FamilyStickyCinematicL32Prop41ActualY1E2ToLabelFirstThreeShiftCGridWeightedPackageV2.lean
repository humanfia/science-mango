import FamilyStickyGrounding.Cinematic.FamilyStickyCinematicL32Prop41ActualY1E2SpatialFirstHitWeightedGPrimeSamplingConnectorV1
import FamilyStickyGrounding.Cinematic.FamilyStickyCinematicL32Prop41ActualY1SamplingPaperFineGPrimeLabelFirstThreeShiftCGridWeightedUniformPackageV2
import Mathlib.Tactic

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 6000000

open Set MeasureTheory
open scoped ENNReal

namespace FamilyStickyCinematicL32Prop41ActualY1E2ToLabelFirstThreeShiftCGridWeightedPackageV2

open Submission.Kakeya.ConvexGeometry
open Submission.Kakeya.Uniformity
open FamilyStickyCinematicL32ActualProjectedCenteredHalfPointSourceV1
open FamilyStickyCinematicL32ActualProjectedCenteredHalfTangencyStageV1
open FamilyStickyCinematicL32ActualProjectedCenteredHalfY1ActiveGeometryV1
open FamilyStickyCinematicL32ActualTubeCoefficientDistancesV1
open FamilyStickyCinematicL32ActualTubeCoefficientMetricV1
open FamilyStickyCinematicL32CenteredFractionIntervalsV1
open FamilyStickyCinematicL32FiniteMeasurableIncidencePatternV1
open FamilyStickyCinematicL32FiniteMetricMaximalCoverV1
open FamilyStickyCinematicL32FiniteProjectedPositiveMultiplicityDyadicV1
open FamilyStickyCinematicL32FiniteProjectedShadingMultiplicitySliceV1
open FamilyStickyCinematicL32Prop41ActualGlobalNormCoarseFiberV1
open FamilyStickyCinematicL32Prop41ActualGPrimeDegreeRichMassProducerV1
open FamilyStickyCinematicL32Prop41ActualGPrimeLabelFirstFineSeparatedPairE2ConnectorV1
open FamilyStickyCinematicL32Prop41ActualGPrimeLabelFirstFineSeparatedPairMassProducerV1
open FamilyStickyCinematicL32Prop41ActualY1E2SpatialActivePatternCardLowerV1
open FamilyStickyCinematicL32Prop41ActualY1E2SpatialFirstHitWeightedGPrimeSamplingConnectorV1
open FamilyStickyCinematicL32Prop41ActualY1E2SpatialActivePatternFloorCoverV1
open FamilyStickyCinematicL32Prop41ActualY1E2ToLabelFirstSelectedMassTopV1
open FamilyStickyCinematicL32Prop41ActualY1E2ToLabelFirstSelectedMassV1
open FamilyStickyCinematicL32Prop41ActualY1FineCoarseRectangleProducerV1
open FamilyStickyCinematicL32Prop41ActualY1PaperFineCNormalizedThreeShiftScaleProducerV1
open FamilyStickyCinematicL32Prop41ActualY1SamplingPaperFineGPrimeLabelFirstThreeShiftCGridUniformPackageV1
open FamilyStickyCinematicL32Prop41ActualY1SamplingPaperFineGPrimeLabelFirstThreeShiftCGridWeightedUniformPackageV2
open FamilyStickyCinematicL32Prop41ActualY1SamplingPaperFineGPrimeLabelFirstProvenanceV1
open FamilyStickyCinematicL32Prop41ActualY1SharpFineScaleTangencyV1
open FamilyStickyCinematicL32Prop41CanonicalMaximizerNonconcentrationV1
open FamilyStickyCinematicL32Prop41CanonicalRichSeparatedPairConsumerV1
open FamilyStickyCinematicL32Prop41CoarseRectangleIncidenceDataV1
open FamilyStickyCinematicL32Prop41FiniteRichSeparatedPairSelectionV1
open FamilyStickyCinematicL32PyzE2DyadicDegreeWindowV1

noncomputable section

universe u

/-!
# Actual E2 to tube-local shifted C-grid label-first selected mass

This is the ordinary G-prime top connector with tube-local shifted C-grid
normalization.  Its selected package carries the exact final endpoint maps
and the honest combined sampling/grid/trace loss constant 72.
-/

theorem exists_actualCenteredHalfPaperFineE2_labelFirstThreeShiftCGridWeightedPackageV2
    {radius : NNReal} {iota : Type u} [DecidableEq iota]
    (base : Set (Real × Real)) (hbase : MeasurableSet base)
    (fine : UniformTubeFamily radius iota)
    (physical : FiniteProjectedShading (Real × Real) iota)
    (label : Int) {mesh : Real} (hmesh : 0 < mesh)
    (f f1 f2 : Real -> Real) (outerA outerB : Real)
    (hOuter : outerA <= outerB)
    (hf : forall z, HasDerivAt f (f1 z) z)
    (hf1 : forall z, HasDerivAt f1 (f2 z) z)
    (tGlobal globalDelta : Real) (globalCenter : Tube radius)
    (ceiling exponent : Real)
    (pointSource : ActualCenteredHalfPointRectangleSource
      (actualCenteredHalfPaperFineE2 base hbase fine physical label f f1 f2
        outerA outerB hOuter hf hf1 tGlobal globalCenter ceiling exponent
          globalDelta)
      globalCenter
      (actualCenteredHalfPaperFineTubeAt fine physical f f1 f2 outerA outerB
        hOuter hf hf1 tGlobal globalCenter ceiling exponent)
      f outerA outerB tGlobal)
    (facts : ActualCenteredHalfY1ActiveGeometryFacts fine physical
      (actualCenteredHalfPaperFineE2 base hbase fine physical label f f1 f2
        outerA outerB hOuter hf hf1 tGlobal globalCenter ceiling exponent
          globalDelta)
      (actualCenteredHalfPaperFineY1 base hbase fine physical f f1 f2
        outerA outerB hOuter hf hf1 tGlobal globalCenter ceiling exponent
          globalDelta).activeAtPoint
      (actualCenteredHalfPaperFineTubeAt fine physical f f1 f2 outerA outerB
        hOuter hf hf1 tGlobal globalCenter ceiling exponent)
      f f1 f2 outerA outerB hOuter hf hf1 tGlobal globalDelta)
    (hparameter : forall z, z ∈ Icc outerA outerB -> |z| <= 1)
    (sharp : ActualY1SharpFineScaleNumerics
      (radius : Real) globalDelta tGlobal (outerB - outerA))
    (hft : forall z, z ∈ Icc outerA outerB -> |f z| <= 2)
    (hf1Lower : forall z, z ∈ Icc outerA outerB -> 1 <= |f1 z|)
    (hf1Upper : forall z, z ∈ Icc outerA outerB -> |f1 z| <= 2)
    (hf2 : forall z, z ∈ Icc outerA outerB -> |f2 z| <= 1 / 100)
    (hf2Continuous : ContinuousOn f2 (Icc outerA outerB))
    (hmeshBase : mesh <= Real.sqrt ((radius : Real) /
      prop41Y1PaperFineT (radius : Real) globalDelta tGlobal) / 2)
    (hsource : (actualCenteredHalfPaperFineE2 base hbase fine physical label
      f f1 f2 outerA outerB hOuter hf hf1 tGlobal globalCenter ceiling
        exponent globalDelta).Nonempty)
    (hactive : forall q,
      q ∈ actualCenteredHalfPaperFineE2 base hbase fine physical label
        f f1 f2 outerA outerB hOuter hf hf1 tGlobal globalCenter ceiling
          exponent globalDelta ->
      ((actualCenteredHalfPaperFineY1 base hbase fine physical f f1 f2
        outerA outerB hOuter hf hf1 tGlobal globalCenter ceiling exponent
          globalDelta).activeAtPoint q).Nonempty)
    (N : CanonicalNormNonconcentrationData iota)
    (hNfamily : N.family =
      actualGlobalNormIndexFamily fine physical tGlobal globalCenter)
    (hdistance : forall i j, N.distance i j =
      projectedTubePairCoefficientDistance
        ((actualCenteredHalfPaperFineE2SpatialIncidenceData base hbase fine
          physical label mesh f f1 f2 outerA outerB hOuter hf hf1 tGlobal
            globalDelta globalCenter ceiling exponent).fine.tubes i)
        ((actualCenteredHalfPaperFineE2SpatialIncidenceData base hbase fine
          physical label mesh f f1 f2 outerA outerB hOuter hf hf1 tGlobal
            globalDelta globalCenter ceiling exponent).fine.tubes j))
    (ballRadius : Real)
    (hroom : automaticCanonicalNearCap N ballRadius <
      pyzE2DegreeLower label)
    (hnearRadiusLower : N.delta <= 10 * ballRadius)
    (hnearRadiusUpper : 10 * ballRadius <= N.ceiling)
    (hballRadiusLower : N.delta <= ballRadius)
    (hballRadiusUpper : ballRadius <= N.ceiling)
    (hsmall : ActualY1PaperFineCNormalizedThreeShiftPairScaleSmallness
      (radius : Real) globalDelta tGlobal (4 * ballRadius)) :
    let D := actualCenteredHalfPaperFineE2SpatialIncidenceData base hbase fine
      physical label mesh f f1 f2 outerA outerB hOuter hf hf1 tGlobal
        globalDelta globalCenter ceiling exponent
    exists Q : ActualGPrimeE2FirstHitWeightedSampledOutcome
      N D label ballRadius,
      Nonempty
        (ActualGPrimeLabelFirstThreeShiftCGridPaperFineWeightedUniformPackageV2
          fine N D (fun _ _ => True) Q.sampled.pair.left Q.sampled.pair.right
            ballRadius Q.sampled.omega
              (actualGPrimeE2FirstHitLabelWeight D label)
                f outerA outerB globalDelta tGlobal) := by
  dsimp only
  let Y1 := actualCenteredHalfPaperFineY1 base hbase fine physical
    f f1 f2 outerA outerB hOuter hf hf1 tGlobal globalCenter ceiling exponent
      globalDelta
  let source := actualCenteredHalfPaperFineE2 base hbase fine physical label
    f f1 f2 outerA outerB hOuter hf hf1 tGlobal globalCenter ceiling exponent
      globalDelta
  let patternAt := physical.activeAtPoint
  let fineLabels : Finset
      (ActualCenteredHalfPaperFineE2SpatialLabel base hbase fine physical
        label mesh f f1 f2 outerA outerB hOuter hf hf1 tGlobal globalCenter
          ceiling exponent globalDelta) := Finset.univ
  let pointAt := spatialActivePatternRepresentative physical.ambient patternAt
    source mesh
  let tubeAt := actualCenteredHalfPaperFineTubeAt fine physical f f1 f2
    outerA outerB hOuter hf hf1 tGlobal globalCenter ceiling exponent
  let fineT := prop41Y1PaperFineT (radius : Real) globalDelta tGlobal
  let D := actualCenteredHalfPaperFineE2SpatialIncidenceData base hbase fine
    physical label mesh f f1 f2 outerA outerB hOuter hf hf1 tGlobal
      globalDelta globalCenter ceiling exponent
  change source.Nonempty at hsource
  change forall q, q ∈ source -> (Y1.activeAtPoint q).Nonempty at hactive
  have pointSource' : ActualCenteredHalfPointRectangleSource source
      globalCenter tubeAt f outerA outerB tGlobal := by
    simpa only [source, tubeAt, actualCenteredHalfPaperFineE2,
      actualCenteredHalfPaperFineY1, actualCenteredHalfPaperFineTubeAt] using
        pointSource
  have facts' : ActualCenteredHalfY1ActiveGeometryFacts fine physical source
      Y1.activeAtPoint tubeAt f f1 f2 outerA outerB hOuter hf hf1 tGlobal
        globalDelta := by
    simpa only [source, Y1, tubeAt, actualCenteredHalfPaperFineE2,
      actualCenteredHalfPaperFineY1, actualCenteredHalfPaperFineTubeAt] using
        facts
  have hQ :=
    exists_actualCenteredHalfPaperFineE2_spatialFirstHit_weightedSampledOutcome
      base hbase fine physical label hmesh f f1 f2 outerA outerB hOuter hf hf1
        tGlobal globalCenter ceiling exponent globalDelta pointSource hparameter
          hmeshBase hsource hactive N hNfamily hdistance ballRadius hroom
            hnearRadiusLower hnearRadiusUpper hballRadiusLower hballRadiusUpper
  dsimp only at hQ
  obtain ⟨Q⟩ := hQ
  have hpointE : forall r, r ∈ fineLabels -> pointAt r ∈ source := by
    intro r _hr
    exact (spatialActivePatternRepresentative_spec physical.ambient patternAt
      source mesh r).1
  have hDpaper : D = y1FineCoarseRectangleData fine Y1 fineLabels pointAt
      tubeAt f f1 f2 hf hf1 (radius : Real) fineT globalDelta tGlobal := by
    rfl
  obtain ⟨P⟩ :=
    exists_actualGPrimeLabelFirstThreeShiftCGridPaperFineWeightedUniformPackageV2_of_sampledOutcome
      fine physical source Y1 fineLabels pointAt globalCenter tubeAt f f1 f2
        outerA outerB hOuter hf hf1 tGlobal globalDelta facts' pointSource'
          hpointE sharp hparameter hft hf1Lower hf1Upper hf2 hf2Continuous
            N D hDpaper (fun _ _ => True) ballRadius
              (pyzE2DegreeLower label)
                (actualGPrimeE2FirstHitLabelWeight D label) hdistance Q.sampled
                  hsmall
  exact ⟨Q, ⟨P⟩⟩

#print axioms exists_actualCenteredHalfPaperFineE2_labelFirstThreeShiftCGridWeightedPackageV2

end

end FamilyStickyCinematicL32Prop41ActualY1E2ToLabelFirstThreeShiftCGridWeightedPackageV2
