import FamilyStickyGrounding.Cinematic.FamilyStickyCinematicL32Prop41ActualGPrimeArbitrarySeparatedPairWeightedUniformPackageV2
import FamilyStickyGrounding.Cinematic.FamilyStickyCinematicL32Prop41ActualY1SamplingPaperFineGPrimeLabelFirstThreeShiftCGridWeightedDependentFixedCChoiceAggregatorV2
import FamilyStickyGrounding.Cinematic.FamilyStickyCinematicL32Prop41ActualY1SamplingPaperFineGPrimeLabelFirstThreeShiftCGridWeightedAutomaticReferenceScaleV2
import Mathlib.Tactic

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 8000000

open Set MeasureTheory
open scoped BigOperators ENNReal Interval

namespace FamilyStickyCinematicL32Prop41ActualGPrimeArbitraryPairE2FirstHitOwnerCapV2

open Submission.Kakeya.ConvexGeometry
open Submission.Kakeya.Uniformity
open FamilyStickyCinematicL32ActualProjectedCenteredHalfPointSourceV1
open FamilyStickyCinematicL32ActualProjectedCenteredHalfY1ActiveGeometryV1
open FamilyStickyCinematicL32CurvilinearRectanglePointMultiplicityV1
open FamilyStickyCinematicL32FiniteNestedValueFibresThirdStageAtScalesV1
open FamilyStickyCinematicL32FiniteNestedValueFibresExternalPivotThirdStageV1
open FamilyStickyCinematicL32FiniteOccupiedCodeLocalCompactThirdStageV1
open FamilyStickyCinematicL32FiniteOccupiedCodeLocalCompactThirdStageMassOutcomeV1
open FamilyStickyCinematicL32FiniteProjectedShadingMultiplicitySliceV1
open FamilyStickyCinematicL32Lemma312TwoCenterAutomaticCurvatureRatioV1
open FamilyStickyCinematicL32Prop41ActualGPrimeLabelFirstWeightedFineSeparatedPairMassProducerV1
open FamilyStickyCinematicL32Prop41ActualGPrimeThreeShiftCGridWeightedE2FixedCThirdStageMassOutcomeV2
open FamilyStickyCinematicL32Prop41ActualGlobalNormCoarseFiberV1
open FamilyStickyCinematicL32Prop41ActualY1E2SpatialFirstHitWeightedGPrimeSamplingConnectorV1
open FamilyStickyCinematicL32Prop41ActualY1FineCoarseRectangleProducerV1
open FamilyStickyCinematicL32Prop41ActualY1PaperFineCNormalizedSelectedCountingNumericsV1
open FamilyStickyCinematicL32Prop41ActualY1PaperFineCNormalizedThreeShiftScaleProducerV1
open FamilyStickyCinematicL32Prop41ActualY1RetainedThreeShiftCGridRestrictedCanonicalFibresV1
open FamilyStickyCinematicL32Prop41ActualY1SamplingPaperFineGPrimeLabelFirstProvenanceV1
open FamilyStickyCinematicL32Prop41ActualY1SamplingPaperFineGPrimeLabelFirstCNormalizedRightCLocalCoverTwoCenterLocalCompactOutcomeRepoV2V1
open FamilyStickyCinematicL32Prop41ActualY1SamplingPaperFineGPrimeLabelFirstThreeShiftCGridRestrictedCoefficientBallV1
open FamilyStickyCinematicL32Prop41ActualY1SamplingPaperFineGPrimeLabelFirstThreeShiftCGridWeightedExactCMassPartitionV2
open FamilyStickyCinematicL32Prop41ActualY1SamplingPaperFineGPrimeLabelFirstThreeShiftCGridThirdStageSelectedSampledLensV2
open FamilyStickyCinematicL32Prop41ActualY1SamplingPaperFineGPrimeLabelFirstThreeShiftCGridWeightedAutomaticReferenceScaleV2
open FamilyStickyCinematicL32Prop41ActualY1SamplingPaperFineGPrimeLabelFirstThreeShiftCGridWeightedDependentFixedCChoiceAggregatorV2
open FamilyStickyCinematicL32Prop41ActualY1SamplingPaperFineGPrimeLabelFirstThreeShiftCGridWeightedSelectedMassOuterTopV2
open FamilyStickyCinematicL32Prop41ActualY1SamplingPaperFineGPrimeLabelFirstThreeShiftCGridWeightedUniformPackageV2
open FamilyStickyCinematicL32Prop41ActualY1SharpFineScaleTangencyV1
open FamilyStickyCinematicL32Prop41CanonicalMaximizerNonconcentrationV1
open FamilyStickyCinematicL32Prop41CoarseRectangleIncidenceDataV1
open FamilyStickyCinematicL32Prop41FiniteRandomSamplingExtractionV1
open FamilyStickyCinematicL32Prop41GlobalScaleNearFiberPackingV1
open FamilyStickyCinematicL32Prop41SampledLensCardinalityAssemblyV1
open FamilyStickyCinematicL32Prop41SelectedSubfamilyTwoScaleAutomaticOutcomeFromCurveBudgetRepoV2V1
open FamilyStickyCinematicL32Prop41WeightedThreeShiftPigeonholeV1

noncomputable section

universe u v

/-!
# An actual owner cap for each weighted separated pair

The existing fixed-C/third-stage construction is package-local: it never uses
that the two centres were selected by a global maximisation.  This module
applies it to an arbitrary weighted package and then uses the honest factor
`72` sample/grid/trace retention to bound the complete common-label weight of
that displayed pair.

The result is a genuine per-pair geometric cap.  Summing these caps over all
pairs is still a separate incidence-packing problem; no pair-count or ambient
cardinality estimate is hidden here.
-/

/-- The common E2 first-hit weight of the displayed centres is controlled by
the actual all-C owner/third-stage/sampled-lens construction. -/
theorem actualGPrimeWeightedCommonFineCenterMass_le_ownerEnvelope
    {radius : NNReal} {iota : Type u} [DecidableEq iota]
    {fineLabel : Type v} [DecidableEq fineLabel]
    (fine : UniformTubeFamily radius iota)
    (physical : FiniteProjectedShading (Real × Real) iota)
    (E : Set (Real × Real))
    (Y1 : FiniteProjectedShading (Real × Real) iota)
    (fineLabels : Finset fineLabel) (pointAt : fineLabel -> Real × Real)
    (globalCenter : Tube radius) (tubeAt : Real × Real -> Tube radius)
    (f f1 f2 : Real -> Real) (outerA outerB : Real)
    (hOuter : outerA <= outerB)
    (hfDeriv : forall z, HasDerivAt f (f1 z) z)
    (hf1Deriv : forall z, HasDerivAt f1 (f2 z) z)
    (tGlobal globalDelta : Real)
    (facts : ActualCenteredHalfY1ActiveGeometryFacts fine physical E
      Y1.activeAtPoint tubeAt f f1 f2 outerA outerB hOuter hfDeriv hf1Deriv
      tGlobal globalDelta)
    (pointSource : ActualCenteredHalfPointRectangleSource E globalCenter
      tubeAt f outerA outerB tGlobal)
    (hpointE : forall r, r ∈ fineLabels -> pointAt r ∈ E)
    (N : CanonicalNormNonconcentrationData iota)
    (D : CoarseRectangleIncidenceData (point := Real × Real)
      (radius := radius) (iota := iota) fineLabel)
    (hD : D = y1FineCoarseRectangleData fine Y1 fineLabels pointAt tubeAt
      f f1 f2 hfDeriv hf1Deriv (radius : Real)
      (prop41Y1PaperFineT (radius : Real) globalDelta tGlobal)
      globalDelta tGlobal)
    (e2Label : Int)
    (keep : iota -> fineLabel -> Prop) (left right : iota)
    (ballRadius : Real)
    (omega : (N.family -> Fin 1) × (N.family -> Fin 1))
    (P : ActualGPrimeLabelFirstThreeShiftCGridPaperFineWeightedUniformPackageV2
      fine N D keep left right ballRadius omega
        (actualGPrimeE2FirstHitLabelWeight D e2Label)
        f outerA outerB globalDelta tGlobal)
    (sharp : ActualY1SharpFineScaleNumerics
      (radius : Real) globalDelta tGlobal (outerB - outerA))
    (hsmall : ActualY1PaperFineCNormalizedThreeShiftPairScaleSmallness
      (radius : Real) globalDelta tGlobal (4 * ballRadius))
    (hcount : ActualY1PaperFineCNormalizedSelectedCountingSmallness
      (radius : Real) globalDelta tGlobal (4 * ballRadius))
    (hparameter : forall z, z ∈ Icc outerA outerB -> |z| <= 1)
    (hfunction : forall z, z ∈ Icc outerA outerB -> |f z| <= 2)
    (hfirstLower : forall z, z ∈ Icc outerA outerB -> 1 <= |f1 z|)
    (hfirst : forall z, z ∈ Icc outerA outerB -> |f1 z| <= 2)
    (hsecond : forall z, z ∈ Icc outerA outerB -> |f2 z| <= 1 / 100)
    (hsecondContinuous : ContinuousOn f2 (Icc outerA outerB))
    (hDfine : D.fine = fine)
    (hfamily : N.family =
      actualGlobalNormIndexFamily fine physical tGlobal globalCenter)
    (hballRadiusLower : N.delta <= ballRadius) :
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
    actualGPrimeWeightedCommonFineCenterMass N D keep
        (actualGPrimeE2FirstHitLabelWeight D e2Label) left right <=
      72 * (localPacking * thirdPacking *
        ENNReal.ofReal
          (sampledLensBound
            (selectedSubfamilyAutomaticDepthFromCurveBudget
              (actualThreeShiftCGridRestrictedGlobalTubeFamily
                P.gridSelection P.selected
                  (actualGPrimeLabelFirstThreeShiftCGridFinalTraceShift
                    (P := P))).card)
            (twoSidedZeroColorLoad 1 1 omega)) * cap) := by
  dsimp only
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
  obtain ⟨selectedCard, hfibre, hselected⟩ :=
    exists_actualGPrimeThreeShiftCGridWeightedE2_selectedCard
      fine physical E Y1 fineLabels pointAt globalCenter tubeAt f f1 f2
        outerA outerB hOuter hfDeriv hf1Deriv tGlobal globalDelta facts
          pointSource hpointE N D hD e2Label keep left right ballRadius omega
            P sharp hsmall hcount referenceScale hreferenceScale hparameter
              hfunction hfirstLower hfirst hsecond hsecondContinuous hDfine
                hfamily hreferenceMargin
  have hfibreOuter : forall c, c ∈
      actualThreeShiftCGridRestrictedOccupiedValues P.gridSelection P.selected
        (actualGPrimeLabelFirstThreeShiftCGridFinalTraceShift (P := P)) ->
      finiteENNRealWeight
          (actualThreeShiftCGridRestrictedFiber P.gridSelection P.selected
            (actualGPrimeLabelFirstThreeShiftCGridFinalTraceShift (P := P)) c)
          (actualGPrimeLabelFirstSurvivorWeightAt N D keep left right
            ballRadius omega (actualGPrimeE2FirstHitLabelWeight D e2Label)) <=
        finiteOccupiedCodeLocalPacking
            (actualY1PaperFineCNormalizedAutomaticComparisonLambda
              (radius := radius) globalDelta tGlobal (4 * ballRadius))
            (twoCenterAutomaticCurvatureRatio (4 * ballRadius)
              ((401 / 100 : Real) * (ballRadius + 6 * tGlobal)) referenceScale) *
          finiteOccupiedCodeThirdPacking
            (projectedCoefficientPackingCap ballRadius
              (2 * (ballRadius + 6 * tGlobal)) : ENNReal)
            (actualY1PaperFineCNormalizedAutomaticComparisonLambda
              (radius := radius) globalDelta tGlobal (4 * ballRadius))
            (twoCenterAutomaticCurvatureRatio (4 * ballRadius)
              ((401 / 100 : Real) * (ballRadius + 6 * tGlobal)) referenceScale)
            (twoCenterAutomaticCurvatureRatio (4 * ballRadius)
              ((401 / 100 : Real) * (ballRadius + 6 * tGlobal)) referenceScale) *
          (selectedCard c : ENNReal) *
          actualGPrimeThreeShiftCGridWeightedE2WideCap
            (radius : Real) ballRadius globalDelta tGlobal := by
    intro c hc
    have hcWeighted : c ∈
        actualGPrimeThreeShiftCGridWeightedOccupiedCValues P := by
      simpa only [actualGPrimeThreeShiftCGridWeightedOccupiedCValues,
        actualGPrimeThreeShiftCGridWeightedFinalTraceShift,
        actualGPrimeLabelFirstThreeShiftCGridFinalTraceShift] using hc
    have hmass := hfibre c hcWeighted
    change finiteENNRealWeight
        (actualGPrimeThreeShiftCGridWeightedExactCFiber P c)
        (actualGPrimeLabelFirstSurvivorWeightAt N D keep left right
          ballRadius omega (actualGPrimeE2FirstHitLabelWeight D e2Label)) <= _
      at hmass
    simpa only [actualGPrimeThreeShiftCGridWeightedExactCFiber,
      actualGPrimeThreeShiftCGridWeightedFinalTraceShift,
      actualGPrimeLabelFirstThreeShiftCGridFinalTraceShift] using hmass
  have hselectedOuter : forall c, c ∈
      actualThreeShiftCGridRestrictedOccupiedValues P.gridSelection P.selected
        (actualGPrimeLabelFirstThreeShiftCGridFinalTraceShift (P := P)) ->
      ((selectedCard c : Nat) : Real) <=
        sampledLensBound
          (selectedSubfamilyAutomaticDepthFromCurveBudget
            (actualThreeShiftCGridRestrictedGlobalTubeFamily P.gridSelection
              P.selected
                (actualGPrimeLabelFirstThreeShiftCGridFinalTraceShift
                  (P := P))).card)
          ((actualThreeShiftCGridRestrictedTubeFamilyAt P.gridSelection
            P.selected
              (actualGPrimeLabelFirstThreeShiftCGridFinalTraceShift
                (P := P)) c).card : Real) := by
    intro c hc
    apply hselected c
    simpa only [actualGPrimeThreeShiftCGridWeightedOccupiedCValues,
      actualGPrimeThreeShiftCGridWeightedFinalTraceShift,
      actualGPrimeLabelFirstThreeShiftCGridFinalTraceShift] using hc
  have hmass :=
    finiteENNRealWeight_actualGPrimeThreeShiftCGrid_selected_le_globalSampledLens
      fine N D keep left right ballRadius omega
        (actualGPrimeE2FirstHitLabelWeight D e2Label) f outerA outerB
          globalDelta tGlobal P selectedCard
            (finiteOccupiedCodeLocalPacking
              (actualY1PaperFineCNormalizedAutomaticComparisonLambda
                (radius := radius) globalDelta tGlobal (4 * ballRadius))
              (twoCenterAutomaticCurvatureRatio (4 * ballRadius)
                ((401 / 100 : Real) * (ballRadius + 6 * tGlobal))
                  referenceScale))
            (finiteOccupiedCodeThirdPacking
              (projectedCoefficientPackingCap ballRadius
                (2 * (ballRadius + 6 * tGlobal)) : ENNReal)
              (actualY1PaperFineCNormalizedAutomaticComparisonLambda
                (radius := radius) globalDelta tGlobal (4 * ballRadius))
              (twoCenterAutomaticCurvatureRatio (4 * ballRadius)
                ((401 / 100 : Real) * (ballRadius + 6 * tGlobal))
                  referenceScale)
              (twoCenterAutomaticCurvatureRatio (4 * ballRadius)
                ((401 / 100 : Real) * (ballRadius + 6 * tGlobal))
                  referenceScale))
            (actualGPrimeThreeShiftCGridWeightedE2WideCap
              (radius : Real) ballRadius globalDelta tGlobal)
            hfibreOuter hselectedOuter
  calc
    actualGPrimeWeightedCommonFineCenterMass N D keep
        (actualGPrimeE2FirstHitLabelWeight D e2Label) left right <=
      ∑ r ∈ actualGPrimeBilateralRetainedFineLabels
        N D keep left right ballRadius,
          actualGPrimeE2FirstHitLabelWeight D e2Label r :=
      weightedCommonFineCenterMass_le_bilateralWeight N D keep left right
        ballRadius hballRadiusLower
          (actualGPrimeE2FirstHitLabelWeight D e2Label)
    _ <= 72 * finiteENNRealWeight P.selected
        (actualGPrimeLabelFirstSurvivorWeightAt N D keep left right
          ballRadius omega (actualGPrimeE2FirstHitLabelWeight D e2Label)) := by
      simpa only [finiteENNRealWeight,
        actualGPrimeLabelFirstSurvivorWeightAt] using
          P.seventyTwo_weight_retention
    _ <= 72 *
        (finiteOccupiedCodeLocalPacking
            (actualY1PaperFineCNormalizedAutomaticComparisonLambda
              (radius := radius) globalDelta tGlobal (4 * ballRadius))
            (twoCenterAutomaticCurvatureRatio (4 * ballRadius)
              ((401 / 100 : Real) * (ballRadius + 6 * tGlobal))
                referenceScale) *
          finiteOccupiedCodeThirdPacking
            (projectedCoefficientPackingCap ballRadius
              (2 * (ballRadius + 6 * tGlobal)) : ENNReal)
            (actualY1PaperFineCNormalizedAutomaticComparisonLambda
              (radius := radius) globalDelta tGlobal (4 * ballRadius))
            (twoCenterAutomaticCurvatureRatio (4 * ballRadius)
              ((401 / 100 : Real) * (ballRadius + 6 * tGlobal))
                referenceScale)
            (twoCenterAutomaticCurvatureRatio (4 * ballRadius)
              ((401 / 100 : Real) * (ballRadius + 6 * tGlobal))
                referenceScale) *
          ENNReal.ofReal
            (sampledLensBound
              (selectedSubfamilyAutomaticDepthFromCurveBudget
                (actualThreeShiftCGridRestrictedGlobalTubeFamily
                  P.gridSelection P.selected
                    (actualGPrimeLabelFirstThreeShiftCGridFinalTraceShift
                      (P := P))).card)
              (twoSidedZeroColorLoad 1 1 omega)) *
          actualGPrimeThreeShiftCGridWeightedE2WideCap
            (radius : Real) ballRadius globalDelta tGlobal) := by
      gcongr

#print axioms actualGPrimeWeightedCommonFineCenterMass_le_ownerEnvelope

end

end FamilyStickyCinematicL32Prop41ActualGPrimeArbitraryPairE2FirstHitOwnerCapV2
