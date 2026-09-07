import FamilyStickyGrounding.Cinematic.FamilyStickyCinematicL32PyzActualNormFirstAllCenterMassWeightedBranchHighV5D
import Mathlib.Tactic

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 6000000

open Set MeasureTheory
open scoped BigOperators ENNReal NNReal

namespace FamilyStickyCinematicL32PyzActualNormFirstAllCenterHighConcreteQPRetentionV4

open Submission.Kakeya.ConvexGeometry
open Submission.Kakeya.Uniformity
open FamilyStickyCinematicL32ActualProjectedCenteredHalfPointSourceV1
open FamilyStickyCinematicL32ActualProjectedCenteredHalfTangencyStageV1
open FamilyStickyCinematicL32ActualProjectedCenteredHalfY1ActiveGeometryV1
open FamilyStickyCinematicL32ActualProjectedNormLocalizedPointSourceV1
open FamilyStickyCinematicL32ActualProjectedNormSourceFamilyV1
open FamilyStickyCinematicL32ActualProjectedShadingCriticalFamilyV1
open FamilyStickyCinematicL32ActualTubeCoefficientDistancesV1
open FamilyStickyCinematicL32ActualTubeCoefficientMetricV1
open FamilyStickyCinematicL32CenteredFractionIntervalsV1
open FamilyStickyCinematicL32FiniteMeasurableIncidencePatternV1
open FamilyStickyCinematicL32FiniteOccupiedCodeLocalCompactThirdStageMassOutcomeV1
open FamilyStickyCinematicL32FiniteOccupiedCodeLocalCompactThirdStageV1
open FamilyStickyCinematicL32Lemma312TwoCenterAutomaticCurvatureRatioV1
open FamilyStickyCinematicL32Prop41ActualGPrimeLabelFirstFineSeparatedPairE2ConnectorV1
open FamilyStickyCinematicL32Prop41ActualGPrimeLabelFirstFineSeparatedPairMassProducerV1
open FamilyStickyCinematicL32Prop41ActualGPrimeThreeShiftCGridWeightedE2FixedCThirdStageMassOutcomeV2
open FamilyStickyCinematicL32Prop41ActualY1E2SpatialActivePatternCardLowerV1
open FamilyStickyCinematicL32Prop41ActualY1E2SpatialActivePatternFloorCoverV1
open FamilyStickyCinematicL32Prop41ActualY1E2SpatialFirstHitWeightedGPrimeSamplingConnectorV1
open FamilyStickyCinematicL32Prop41ActualY1E2ToLabelFirstSelectedMassV1
open FamilyStickyCinematicL32Prop41ActualY1E2ToLabelFirstSelectedMassTopV1
open FamilyStickyCinematicL32Prop41ActualY1E2ToLabelFirstThreeShiftCGridWeightedPackageV2
open FamilyStickyCinematicL32Prop41ActualY1SamplingPaperFineGPrimeLabelFirstCNormalizedRightCLocalCoverTwoCenterLocalCompactOutcomeRepoV2V1
open FamilyStickyCinematicL32Prop41ActualY1SamplingPaperFineGPrimeLabelFirstProvenanceV1
open FamilyStickyCinematicL32Prop41ActualY1SamplingPaperFineGPrimeLabelFirstThreeShiftCGridRestrictedCoefficientBallV1
open FamilyStickyCinematicL32Prop41ActualY1SamplingPaperFineGPrimeLabelFirstThreeShiftCGridThirdStageSelectedSampledLensV2
open FamilyStickyCinematicL32Prop41ActualY1SamplingPaperFineGPrimeLabelFirstThreeShiftCGridUniformPackageV1
open FamilyStickyCinematicL32Prop41ActualY1SamplingPaperFineGPrimeLabelFirstThreeShiftCGridWeightedAutomaticReferenceScaleV2
open FamilyStickyCinematicL32Prop41ActualY1SamplingPaperFineGPrimeLabelFirstThreeShiftCGridWeightedDependentFixedCChoiceAggregatorV2
open FamilyStickyCinematicL32Prop41ActualY1SamplingPaperFineGPrimeLabelFirstThreeShiftCGridWeightedUniformPackageV2
open FamilyStickyCinematicL32Prop41CanonicalRichSeparatedPairConsumerV1
open FamilyStickyCinematicL32Prop41CoarseRectangleIncidenceDataV1
open FamilyStickyCinematicL32Prop41FiniteRichSeparatedPairSelectionV1
open FamilyStickyCinematicL32Prop41GlobalScaleNearFiberPackingV1
open FamilyStickyCinematicL32ContinuumCriticalSingleDyadicSelectionV1
open FamilyStickyCinematicL32FiniteIncidenceTangencyAfterNormCoverV1
open FamilyStickyCinematicL32FiniteMetricMaximalCoverV1
open FamilyStickyCinematicL32Lemma57EssentiallyDistinctTubeImageV1
open FamilyStickyCinematicL32TubePairTraceV1
open FamilyStickyWZ2TubeCarrierCoordinateAdapterV1
open FamilyStickyCinematicL32FiniteNormGlobalCoverLocalizationV1
open FamilyStickyCinematicL32FiniteProjectedPositiveMultiplicityDyadicV1
open FamilyStickyCinematicL32FiniteProjectedShadingMultiplicitySliceV1
open FamilyStickyCinematicL32Lemma57DyadicCeilBucketV1
open FamilyStickyCinematicL32Prop41ActualGlobalNormCoarseFiberV1
open FamilyStickyCinematicL32Prop41ActualGPrimeDegreeRichMassProducerV1
open FamilyStickyCinematicL32Prop41ActualY1FineCoarseRectangleProducerV1
open FamilyStickyCinematicL32Prop41ActualY1PaperFineCNormalizedSelectedCountingNumericsV1
open FamilyStickyCinematicL32Prop41ActualY1PaperFineCNormalizedThreeShiftScaleProducerV1
open FamilyStickyCinematicL32Prop41ActualY1RetainedThreeShiftCGridRestrictedCanonicalFibresV1
open FamilyStickyCinematicL32Prop41ActualY1SharpFineScaleTangencyV1
open FamilyStickyCinematicL32Prop41CanonicalMaximizerNonconcentrationV1
open FamilyStickyCinematicL32Prop41FiniteRandomSamplingExtractionV1
open FamilyStickyCinematicL32Prop41SampledLensCardinalityAssemblyV1
open FamilyStickyCinematicL32Prop41SelectedSubfamilyTwoScaleAutomaticOutcomeFromCurveBudgetRepoV2V1
open FamilyStickyCinematicL32PyzActualAllCenterBinUniformityV1
open FamilyStickyCinematicL32PyzActualAllCenterCanonicalPayloadFinalV5
open FamilyStickyCinematicL32PyzActualNormFirstExtremalConcreteCBucketCapV1
open FamilyStickyCinematicL32PyzE2DyadicDegreeWindowV1
open FamilyStickyCinematicL32PyzActualNormFirstAllCenterHighHalfSampledLensV3
open FamilyStickyCinematicL32PyzActualNormFirstAllCenterMassWeightedBranchTypesV5C
open FamilyStickyCinematicL32PyzActualNormFirstAllCenterMassWeightedBranchHighV5D
open FamilyStickyCinematicL32Prop41ActualPositiveCenterHighPayloadWeightedFullyActualConnectorV1

noncomputable section

universe u

local instance tubeDecidableEq {radius : NNReal} :
    DecidableEq (Tube radius) := Classical.decEq _

/-!
# Concrete Q/P choice retained before all-center summation

The source endpoint is proposition-valued.  Therefore its witnesses cannot
be eliminated by pattern matching into a data structure in `Type`.  This
module instead names the two actual witnesses with `Classical.choose`, proves
their literal specification, and defines the right-hand side from those
named witnesses.  No scalar right-hand side is chosen independently.
-/

noncomputable def positiveCenterHighPayload_baseConcreteQ
    {radius : NNReal} {iota : Type u} [DecidableEq iota]
    (base : Set (Real × Real)) (hbase : MeasurableSet base)
    (fine : UniformTubeFamily radius iota)
    (physical : FiniteProjectedShading (Real × Real) iota)
    (f f1 f2 : Real -> Real) (outerA outerB : Real)
    (hOuter : outerA <= outerB)
    (hf : forall z, HasDerivAt f (f1 z) z)
    (hf1 : forall z, HasDerivAt f1 (f2 z) z)
    (tGlobal : Real) (globalCenter : Tube radius)
    (tangencyExponent normExponent : Real) (logCount : Nat)
    (H : ActualHighPayloadWithNormNonconcentration volume base hbase fine
      physical f f1 f2 outerA outerB hOuter hf hf1 tGlobal globalCenter
        tangencyExponent normExponent logCount)
    (mesh ballRadius : Real)
    (h : PositiveCenterHighPayloadBaseWeightedGlobalSampledLensConclusion
      base hbase fine physical f f1 f2 outerA outerB hOuter hf hf1 tGlobal
        globalCenter tangencyExponent normExponent logCount H mesh
          ballRadius) :=
  Classical.choose h

noncomputable def positiveCenterHighPayload_baseConcreteP
    {radius : NNReal} {iota : Type u} [DecidableEq iota]
    (base : Set (Real × Real)) (hbase : MeasurableSet base)
    (fine : UniformTubeFamily radius iota)
    (physical : FiniteProjectedShading (Real × Real) iota)
    (f f1 f2 : Real -> Real) (outerA outerB : Real)
    (hOuter : outerA <= outerB)
    (hf : forall z, HasDerivAt f (f1 z) z)
    (hf1 : forall z, HasDerivAt f1 (f2 z) z)
    (tGlobal : Real) (globalCenter : Tube radius)
    (tangencyExponent normExponent : Real) (logCount : Nat)
    (H : ActualHighPayloadWithNormNonconcentration volume base hbase fine
      physical f f1 f2 outerA outerB hOuter hf hf1 tGlobal globalCenter
        tangencyExponent normExponent logCount)
    (mesh ballRadius : Real)
    (h : PositiveCenterHighPayloadBaseWeightedGlobalSampledLensConclusion
      base hbase fine physical f f1 f2 outerA outerB hOuter hf hf1 tGlobal
        globalCenter tangencyExponent normExponent logCount H mesh
          ballRadius) :=
  Classical.choose (Classical.choose_spec h)

theorem positiveCenterHighPayload_baseConcreteQP_spec
    {radius : NNReal} {iota : Type u} [DecidableEq iota]
    (base : Set (Real × Real)) (hbase : MeasurableSet base)
    (fine : UniformTubeFamily radius iota)
    (physical : FiniteProjectedShading (Real × Real) iota)
    (f f1 f2 : Real -> Real) (outerA outerB : Real)
    (hOuter : outerA <= outerB)
    (hf : forall z, HasDerivAt f (f1 z) z)
    (hf1 : forall z, HasDerivAt f1 (f2 z) z)
    (tGlobal : Real) (globalCenter : Tube radius)
    (tangencyExponent normExponent : Real) (logCount : Nat)
    (H : ActualHighPayloadWithNormNonconcentration volume base hbase fine
      physical f f1 f2 outerA outerB hOuter hf hf1 tGlobal globalCenter
        tangencyExponent normExponent logCount)
    (mesh ballRadius : Real)
    (h : PositiveCenterHighPayloadBaseWeightedGlobalSampledLensConclusion
      base hbase fine physical f f1 f2 outerA outerB hOuter hf hf1 tGlobal
        globalCenter tangencyExponent normExponent logCount H mesh
          ballRadius) :
    let globalDelta := dyadicCeilUpper H.payload.tangencyLabel
    let N := positiveCenterHighPayloadGlobalNormData H
    let Q := positiveCenterHighPayload_baseConcreteQ base hbase fine physical
      f f1 f2 outerA outerB hOuter hf hf1 tGlobal globalCenter
        tangencyExponent normExponent logCount H mesh ballRadius h
    let P := positiveCenterHighPayload_baseConcreteP base hbase fine physical
      f f1 f2 outerA outerB hOuter hf hf1 tGlobal globalCenter
        tangencyExponent normExponent logCount H mesh ballRadius h
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
    volume base *
        ((pyzE2DegreeLower H.payload.finalLabel *
          (pyzE2DegreeLower H.payload.finalLabel -
            automaticCanonicalNearCap N ballRadius) : Nat) : ENNReal) <=
      actualAllCenterPostNormBinLoss radius tGlobal physical.ambient.card *
        (72 *
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
                (twoSidedZeroColorLoad 1 1 Q.sampled.omega)) * cap)) := by
  unfold PositiveCenterHighPayloadBaseWeightedGlobalSampledLensConclusion at h
  dsimp only at h ⊢
  exact Classical.choose_spec (Classical.choose_spec h)

def positiveCenterHighPayload_baseConcreteSampledLensRHS
    {radius : NNReal} {iota : Type u} [DecidableEq iota]
    (base : Set (Real × Real)) (hbase : MeasurableSet base)
    (fine : UniformTubeFamily radius iota)
    (physical : FiniteProjectedShading (Real × Real) iota)
    (f f1 f2 : Real -> Real) (outerA outerB : Real)
    (hOuter : outerA <= outerB)
    (hf : forall z, HasDerivAt f (f1 z) z)
    (hf1 : forall z, HasDerivAt f1 (f2 z) z)
    (tGlobal : Real) (globalCenter : Tube radius)
    (tangencyExponent normExponent : Real) (logCount : Nat)
    (H : ActualHighPayloadWithNormNonconcentration volume base hbase fine
      physical f f1 f2 outerA outerB hOuter hf hf1 tGlobal globalCenter
        tangencyExponent normExponent logCount)
    (mesh ballRadius : Real)
    (h : PositiveCenterHighPayloadBaseWeightedGlobalSampledLensConclusion
      base hbase fine physical f f1 f2 outerA outerB hOuter hf hf1 tGlobal
        globalCenter tangencyExponent normExponent logCount H mesh
          ballRadius) : ENNReal :=
  let globalDelta := dyadicCeilUpper H.payload.tangencyLabel
  let N := positiveCenterHighPayloadGlobalNormData H
  let Q := positiveCenterHighPayload_baseConcreteQ base hbase fine physical
    f f1 f2 outerA outerB hOuter hf hf1 tGlobal globalCenter
      tangencyExponent normExponent logCount H mesh ballRadius h
  let P := positiveCenterHighPayload_baseConcreteP base hbase fine physical
    f f1 f2 outerA outerB hOuter hf hf1 tGlobal globalCenter
      tangencyExponent normExponent logCount H mesh ballRadius h
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
  actualAllCenterPostNormBinLoss radius tGlobal physical.ambient.card *
    (72 *
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
            (twoSidedZeroColorLoad 1 1 Q.sampled.omega)) * cap))

theorem positiveCenterHighPayload_base_mul_degree_le_concreteSampledLensRHS
    {radius : NNReal} {iota : Type u} [DecidableEq iota]
    (base : Set (Real × Real)) (hbase : MeasurableSet base)
    (fine : UniformTubeFamily radius iota)
    (physical : FiniteProjectedShading (Real × Real) iota)
    (f f1 f2 : Real -> Real) (outerA outerB : Real)
    (hOuter : outerA <= outerB)
    (hf : forall z, HasDerivAt f (f1 z) z)
    (hf1 : forall z, HasDerivAt f1 (f2 z) z)
    (tGlobal : Real) (globalCenter : Tube radius)
    (tangencyExponent normExponent : Real) (logCount : Nat)
    (H : ActualHighPayloadWithNormNonconcentration volume base hbase fine
      physical f f1 f2 outerA outerB hOuter hf hf1 tGlobal globalCenter
        tangencyExponent normExponent logCount)
    (mesh ballRadius : Real)
    (h : PositiveCenterHighPayloadBaseWeightedGlobalSampledLensConclusion
      base hbase fine physical f f1 f2 outerA outerB hOuter hf hf1 tGlobal
        globalCenter tangencyExponent normExponent logCount H mesh
          ballRadius) :
    volume base *
        ((pyzE2DegreeLower H.payload.finalLabel *
          (pyzE2DegreeLower H.payload.finalLabel -
            automaticCanonicalNearCap
              (positiveCenterHighPayloadGlobalNormData H) ballRadius) :
          Nat) : ENNReal) <=
      positiveCenterHighPayload_baseConcreteSampledLensRHS
        base hbase fine physical f f1 f2 outerA outerB hOuter hf hf1
          tGlobal globalCenter tangencyExponent normExponent logCount H mesh
            ballRadius h := by
  unfold positiveCenterHighPayload_baseConcreteSampledLensRHS
  dsimp only
  exact positiveCenterHighPayload_baseConcreteQP_spec base hbase fine physical
    f f1 f2 outerA outerB hOuter hf hf1 tGlobal globalCenter
      tangencyExponent normExponent logCount H mesh ballRadius h

#print axioms positiveCenterHighPayload_baseConcreteQP_spec
#print axioms
  positiveCenterHighPayload_base_mul_degree_le_concreteSampledLensRHS

end

end FamilyStickyCinematicL32PyzActualNormFirstAllCenterHighConcreteQPRetentionV4
