import FamilyStickyGrounding.Cinematic.FamilyStickyCinematicL32Prop41ActualY1E2ToLabelFirstThreeShiftCGridWeightedPackageV2
import FamilyStickyGrounding.Cinematic.FamilyStickyCinematicL32Prop41ActualY1SamplingPaperFineGPrimeLabelFirstThreeShiftCGridWeightedDependentFixedCChoiceAggregatorV2
import FamilyStickyGrounding.Cinematic.FamilyStickyCinematicL32Prop41ActualY1SamplingPaperFineGPrimeLabelFirstThreeShiftCGridWeightedAutomaticReferenceScaleV2
import Mathlib.Tactic

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 6000000

open Set MeasureTheory
open scoped ENNReal

namespace FamilyStickyCinematicL32Prop41ActualY1E2ToLabelFirstThreeShiftCGridWeightedFullyActualTopV2

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
open FamilyStickyCinematicL32FiniteOccupiedCodeLocalCompactThirdStageV1
open FamilyStickyCinematicL32FiniteOccupiedCodeLocalCompactThirdStageMassOutcomeV1
open FamilyStickyCinematicL32FiniteProjectedPositiveMultiplicityDyadicV1
open FamilyStickyCinematicL32FiniteProjectedShadingMultiplicitySliceV1
open FamilyStickyCinematicL32Lemma312TwoCenterAutomaticCurvatureRatioV1
open FamilyStickyCinematicL32Prop41ActualGPrimeThreeShiftCGridWeightedE2FixedCThirdStageMassOutcomeV2
open FamilyStickyCinematicL32Prop41ActualGlobalNormCoarseFiberV1
open FamilyStickyCinematicL32Prop41ActualGPrimeDegreeRichMassProducerV1
open FamilyStickyCinematicL32Prop41ActualGPrimeLabelFirstFineSeparatedPairE2ConnectorV1
open FamilyStickyCinematicL32Prop41ActualGPrimeLabelFirstFineSeparatedPairMassProducerV1
open FamilyStickyCinematicL32Prop41ActualY1E2SpatialActivePatternCardLowerV1
open FamilyStickyCinematicL32Prop41ActualY1E2SpatialFirstHitWeightedGPrimeSamplingConnectorV1
open FamilyStickyCinematicL32Prop41ActualY1E2ToLabelFirstThreeShiftCGridWeightedPackageV2
open FamilyStickyCinematicL32Prop41ActualY1E2SpatialActivePatternFloorCoverV1
open FamilyStickyCinematicL32Prop41ActualY1E2ToLabelFirstSelectedMassTopV1
open FamilyStickyCinematicL32Prop41ActualY1E2ToLabelFirstSelectedMassV1
open FamilyStickyCinematicL32Prop41ActualY1FineCoarseRectangleProducerV1
open FamilyStickyCinematicL32Prop41ActualY1PaperFineCNormalizedSelectedCountingNumericsV1
open FamilyStickyCinematicL32Prop41ActualY1PaperFineCNormalizedThreeShiftScaleProducerV1
open FamilyStickyCinematicL32Prop41ActualY1SamplingPaperFineGPrimeLabelFirstCNormalizedRightCLocalCoverTwoCenterLocalCompactOutcomeRepoV2V1
open FamilyStickyCinematicL32Prop41ActualY1SamplingPaperFineGPrimeLabelFirstThreeShiftCGridRestrictedCoefficientBallV1
open FamilyStickyCinematicL32Prop41ActualY1SamplingPaperFineGPrimeLabelFirstThreeShiftCGridUniformPackageV1
open FamilyStickyCinematicL32Prop41ActualY1SamplingPaperFineGPrimeLabelFirstThreeShiftCGridThirdStageSelectedSampledLensV2
open FamilyStickyCinematicL32Prop41ActualY1SamplingPaperFineGPrimeLabelFirstThreeShiftCGridWeightedUniformPackageV2
open FamilyStickyCinematicL32Prop41ActualY1SamplingPaperFineGPrimeLabelFirstThreeShiftCGridWeightedAutomaticReferenceScaleV2
open FamilyStickyCinematicL32Prop41ActualY1SamplingPaperFineGPrimeLabelFirstThreeShiftCGridWeightedDependentFixedCChoiceAggregatorV2
open FamilyStickyCinematicL32Prop41ActualY1RetainedThreeShiftCGridRestrictedCanonicalFibresV1
open FamilyStickyCinematicL32Prop41ActualY1SamplingPaperFineGPrimeLabelFirstProvenanceV1
open FamilyStickyCinematicL32Prop41ActualY1SharpFineScaleTangencyV1
open FamilyStickyCinematicL32Prop41CanonicalMaximizerNonconcentrationV1
open FamilyStickyCinematicL32Prop41CanonicalRichSeparatedPairConsumerV1
open FamilyStickyCinematicL32Prop41CoarseRectangleIncidenceDataV1
open FamilyStickyCinematicL32Prop41FiniteRichSeparatedPairSelectionV1
open FamilyStickyCinematicL32Prop41FiniteRandomSamplingExtractionV1
open FamilyStickyCinematicL32Prop41GlobalScaleNearFiberPackingV1
open FamilyStickyCinematicL32Prop41SampledLensCardinalityAssemblyV1
open FamilyStickyCinematicL32Prop41SelectedSubfamilyTwoScaleAutomaticOutcomeFromCurveBudgetRepoV2V1
open FamilyStickyCinematicL32PyzE2DyadicDegreeWindowV1

noncomputable section

universe u

/-!
# Actual E2 to tube-local shifted C-grid label-first selected mass

This is the ordinary G-prime top connector with tube-local shifted C-grid
normalization.  Its selected package carries the exact final endpoint maps
and the honest combined sampling/grid/trace loss constant 72.
-/

theorem actualCenteredHalfPaperFineE2_labelFirstThreeShiftCGridWeighted_globalSampledLens
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
      (radius : Real) globalDelta tGlobal (4 * ballRadius))
    (hcount : ActualY1PaperFineCNormalizedSelectedCountingSmallness
      (radius : Real) globalDelta tGlobal (4 * ballRadius)) :
    let source := actualCenteredHalfPaperFineE2 base hbase fine physical
      label f f1 f2 outerA outerB hOuter hf hf1 tGlobal globalCenter ceiling
        exponent globalDelta
    let D := actualCenteredHalfPaperFineE2SpatialIncidenceData base hbase fine
      physical label mesh f f1 f2 outerA outerB hOuter hf hf1 tGlobal
        globalDelta globalCenter ceiling exponent
    exists Q : ActualGPrimeE2FirstHitWeightedSampledOutcome
      N D label ballRadius,
    exists P :
      ActualGPrimeLabelFirstThreeShiftCGridPaperFineWeightedUniformPackageV2
        fine N D (fun _ _ => True) Q.sampled.pair.left Q.sampled.pair.right
          ballRadius Q.sampled.omega
            (actualGPrimeE2FirstHitLabelWeight D label)
              f outerA outerB globalDelta tGlobal,
      let referenceScale :=
        actualGPrimeThreeShiftCGridWeightedAutomaticReferenceScale P
      let comparisonLambda :=
        actualY1PaperFineCNormalizedAutomaticComparisonLambda
          (radius := radius) globalDelta tGlobal (4 * ballRadius)
      let centerGap := (401 / 100 : Real) * (ballRadius + 6 * tGlobal)
      let curvatureRatio := twoCenterAutomaticCurvatureRatio
        (4 * ballRadius) centerGap referenceScale
      let codeBound : ENNReal := projectedCoefficientPackingCap ballRadius
        (2 * (ballRadius + 6 * tGlobal))
      let localPacking := finiteOccupiedCodeLocalPacking
        comparisonLambda curvatureRatio
      let thirdPacking := finiteOccupiedCodeThirdPacking codeBound
        comparisonLambda curvatureRatio curvatureRatio
      let cap := actualGPrimeThreeShiftCGridWeightedE2WideCap
        (radius : Real) ballRadius globalDelta tGlobal
      volume source *
          ((pyzE2DegreeLower label *
            (pyzE2DegreeLower label -
              automaticCanonicalNearCap N ballRadius) : Nat) : ENNReal) <=
        72 *
          ((richSeparatedCenterPairs N.family
            (canonicalTenRadiusSeparated N ballRadius)
            (fun _ _ => True)).card : ENNReal) *
          (localPacking * thirdPacking *
            ENNReal.ofReal
              (sampledLensBound
                (selectedSubfamilyAutomaticDepthFromCurveBudget
                  (actualThreeShiftCGridRestrictedGlobalTubeFamily
                    P.gridSelection P.selected
                      (actualGPrimeLabelFirstThreeShiftCGridFinalTraceShift
                        (P := P))).card)
                (twoSidedZeroColorLoad 1 1 Q.sampled.omega)) * cap) := by
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
  let referenceScale :=
    actualGPrimeThreeShiftCGridWeightedAutomaticReferenceScale P
  have hreferenceScale : 0 <= referenceScale := by
    simpa only [referenceScale] using
      actualGPrimeThreeShiftCGridWeightedAutomaticReferenceScale_nonneg P
  have hreferenceMargin :
      max ((401 / 100 : Real) *
          actualGPrimeLabelFirstThreeShiftCGridRestrictedCoefficientRadius
            tGlobal (actualGPrimeLabelFirstThreeShiftCGridFinalTraceShift
              (P := P)))
        (2 * actualGPrimeLabelFirstThreeShiftCGridRestrictedCoefficientRadius
            tGlobal (actualGPrimeLabelFirstThreeShiftCGridFinalTraceShift
              (P := P)) + 0) < 3 * referenceScale := by
    simpa only [referenceScale] using
      actualGPrimeThreeShiftCGridWeightedAutomaticReferenceMargin_lt P
  have hDfine : D.fine = fine := by
    rfl
  have htop :=
    actualGPrimeThreeShiftCGridWeightedE2_source_mul_gap_le_globalSampledLens
      fine physical source Y1 fineLabels pointAt globalCenter tubeAt f f1 f2
        outerA outerB hOuter hf hf1 tGlobal globalDelta facts' pointSource'
          hpointE N D hDpaper label ballRadius Q P sharp hsmall hcount
            referenceScale hreferenceScale hparameter hft hf1Lower hf1Upper
              hf2 hf2Continuous hDfine hNfamily hreferenceMargin
  refine ⟨Q, P, ?_⟩
  simpa only [referenceScale, source, D, Y1,
    actualCenteredHalfPaperFineE2SpatialIncidenceData,
    actualCenteredHalfProjectedE2SpatialIncidenceData,
    y1FineCoarseRectangleData,
    actualCenteredHalfPaperFineE2,
    actualCenteredHalfPaperFineY1] using htop

#print axioms actualCenteredHalfPaperFineE2_labelFirstThreeShiftCGridWeighted_globalSampledLens

end

end FamilyStickyCinematicL32Prop41ActualY1E2ToLabelFirstThreeShiftCGridWeightedFullyActualTopV2
