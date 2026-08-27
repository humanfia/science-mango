import FamilyStickyGrounding.Cinematic.FamilyStickyCinematicL32Prop41ActualGPrimeThreeShiftCGridWeightedE2FixedCThirdStageMassOutcomeV2
import FamilyStickyGrounding.Cinematic.FamilyStickyCinematicL32Prop41ActualY1SamplingPaperFineGPrimeLabelFirstThreeShiftCGridWeightedFixedCThirdStageSampledLensConsumerV2

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 8000000

open Set
open scoped BigOperators ENNReal Interval

namespace FamilyStickyCinematicL32Prop41ActualGPrimeThreeShiftCGridWeightedE2FixedCThirdStageMassAndSampledLensV2

open Submission.Kakeya.ConvexGeometry
open Submission.Kakeya.Uniformity
open FamilyStickyCinematicL32ActualProjectedCenteredHalfPointSourceV1
open FamilyStickyCinematicL32ActualProjectedCenteredHalfY1ActiveGeometryV1
open FamilyStickyCinematicL32CurvilinearRectanglePointMultiplicityV1
open FamilyStickyCinematicL32FiniteNestedValueFibresExternalPivotThirdStageV1
open FamilyStickyCinematicL32FiniteNestedValueFibresThirdStageAtScalesV1
open FamilyStickyCinematicL32FiniteOccupiedCodeLocalCompactThirdStageV1
open FamilyStickyCinematicL32FiniteOccupiedCodeLocalCompactThirdStageMassOutcomeV1
open FamilyStickyCinematicL32FiniteProjectedShadingMultiplicitySliceV1
open FamilyStickyCinematicL32Lemma312TwoCenterAutomaticCurvatureRatioV1
open FamilyStickyCinematicL32Prop41ActualGPrimeThreeShiftCGridWeightedE2FixedCMassInputsV2
open FamilyStickyCinematicL32Prop41ActualGPrimeThreeShiftCGridWeightedE2FixedCThirdStageMassOutcomeV2
open FamilyStickyCinematicL32Prop41ActualGlobalNormCoarseFiberV1
open FamilyStickyCinematicL32FiniteValueFibresWeightedV1
open FamilyStickyCinematicL32Prop41ActualY1E2SpatialFirstHitWeightedGPrimeSamplingConnectorV1
open FamilyStickyCinematicL32Prop41ActualY1FineCoarseRectangleProducerV1
open FamilyStickyCinematicL32Prop41ActualY1PaperFineCNormalizedSelectedCountingNumericsV1
open FamilyStickyCinematicL32Prop41ActualY1PaperFineCNormalizedThreeShiftScaleProducerV1
open FamilyStickyCinematicL32Prop41ActualY1SamplingPaperFineGPrimeLabelFirstCNormalizedRightCLocalCoverTwoCenterLocalCompactOutcomeRepoV2V1
open FamilyStickyCinematicL32Prop41ActualY1SamplingPaperFineGPrimeLabelFirstProvenanceV1
open FamilyStickyCinematicL32Prop41ActualY1SamplingPaperFineGPrimeLabelFirstThreeShiftCGridRestrictedCoefficientBallV1
open FamilyStickyCinematicL32Prop41ActualY1RetainedThreeShiftCGridRestrictedCanonicalFibresV1
open FamilyStickyCinematicL32Prop41ActualY1SamplingPaperFineGPrimeLabelFirstThreeShiftCGridThirdStageSelectedSampledLensV2
open FamilyStickyCinematicL32Prop41ActualY1SamplingPaperFineGPrimeLabelFirstThreeShiftCGridWeightedExactCMassPartitionV2
open FamilyStickyCinematicL32Prop41ActualY1SamplingPaperFineGPrimeLabelFirstThreeShiftCGridWeightedFixedCThirdStageSampledLensConsumerV2
open FamilyStickyCinematicL32Prop41ActualY1SamplingPaperFineGPrimeLabelFirstThreeShiftCGridWeightedRightCLocalCoverFiniteOccupiedCodeCurvatureDataV2
open FamilyStickyCinematicL32Prop41ActualY1SamplingPaperFineGPrimeLabelFirstThreeShiftCGridWeightedUniformPackageV2
open FamilyStickyCinematicL32Prop41ActualY1SharpFineScaleTangencyV1
open FamilyStickyCinematicL32Prop41CanonicalMaximizerNonconcentrationV1
open FamilyStickyCinematicL32Prop41CoarseRectangleIncidenceDataV1
open FamilyStickyCinematicL32Prop41GlobalScaleNearFiberPackingV1
open FamilyStickyCinematicL32Prop41SampledLensCardinalityAssemblyV1
open FamilyStickyCinematicL32Prop41SelectedSubfamilyTwoScaleAutomaticOutcomeFromCurveBudgetRepoV2V1
open FamilyStickyCinematicL32Prop41SharpCommonCReferenceV1
open FamilyStickyCinematicL32Prop41WeightedThreeShiftPigeonholeV1

noncomputable section

local instance c2GraphRectangleDecidableEq : DecidableEq C2GraphRectangle :=
  Classical.decEq _

local instance tubeDecidableEq {radius : NNReal} :
    DecidableEq (Tube radius) := Classical.decEq _

universe u v

/-!
# Automatic weighted-E2 fixed-C mass and sampled-lens outcome

This specialization discharges both mass callbacks of the frozen same-outcome
consumer.  In particular, the third-stage family used in the honest first-hit
mass estimate is literally the family used in the sampled-lens estimate.
-/

/-- On one occupied normalized-C fibre, construct one third-stage outcome and
simultaneously obtain its honest E2 first-hit mass bound and sampled-lens card
bound. -/
theorem exists_actualGPrimeThreeShiftCGridWeightedE2_fixedCThirdStageOutcome_mass_and_sampledLens
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
    (c : Real)
    (sharp : ActualY1SharpFineScaleNumerics
      (radius : Real) globalDelta tGlobal (outerB - outerA))
    (hsmall : ActualY1PaperFineCNormalizedThreeShiftPairScaleSmallness
      (radius : Real) globalDelta tGlobal (4 * ballRadius))
    (hcount : ActualY1PaperFineCNormalizedSelectedCountingSmallness
      (radius : Real) globalDelta tGlobal (4 * ballRadius))
    (referenceScale : Real) (hreferenceScale : 0 <= referenceScale)
    (hparameter : forall z, z ∈ Icc outerA outerB -> |z| <= 1)
    (hfunction : forall z, z ∈ Icc outerA outerB -> |f z| <= 2)
    (hfirstLower : forall z, z ∈ Icc outerA outerB -> 1 <= |f1 z|)
    (hfirst : forall z, z ∈ Icc outerA outerB -> |f1 z| <= 2)
    (hsecond : forall z, z ∈ Icc outerA outerB -> |f2 z| <= 1 / 100)
    (hsecondContinuous : ContinuousOn f2 (Icc outerA outerB))
    (hDfine : D.fine = fine)
    (hfamily : N.family =
      actualGlobalNormIndexFamily fine physical tGlobal globalCenter)
    (hc : c ∈ actualGPrimeThreeShiftCGridWeightedOccupiedCValues P)
    (hreferenceMargin :
      max ((401 / 100 : Real) *
          actualGPrimeLabelFirstThreeShiftCGridRestrictedCoefficientRadius
            tGlobal (actualGPrimeLabelFirstThreeShiftCGridFinalTraceShift
              (P := P)))
        (2 * actualGPrimeLabelFirstThreeShiftCGridRestrictedCoefficientRadius
            tGlobal (actualGPrimeLabelFirstThreeShiftCGridFinalTraceShift
              (P := P)) + 0) < 3 * referenceScale) :
    let labelWeight := actualGPrimeE2FirstHitLabelWeight D e2Label
    let code := ActualGPrimeThreeShiftCGridFixedCCode fine N D keep left right
      ballRadius omega labelWeight f outerA outerB globalDelta tGlobal P
        pointAt tubeAt c
    let rawAt : code -> Finset (ActualGPrimeLabelFirstSurvivor
        N D keep left right ballRadius omega) :=
      actualGPrimeThreeShiftCGridFixedCRawAt fine N D keep left right
        ballRadius omega labelWeight f outerA outerB globalDelta tGlobal P
          pointAt tubeAt c
    let rectangleAt := actualGPrimeThreeShiftCGridLocalCompactRectangleAt
      N D keep left right ballRadius omega globalDelta tGlobal
    let localCenterAt := actualGPrimeThreeShiftCGridFixedCLocalCenterAt fine N D
      keep left right ballRadius omega labelWeight f f1 f2 outerA outerB hOuter
        hfDeriv hf1Deriv globalDelta tGlobal P pointAt tubeAt c
    let globalReference := globalCenterFixedCommonCReference globalCenter c
      f f1 f2 hfDeriv hf1Deriv outerA outerB hOuter
    let delta := actualY1PaperFineCNormalizedChoiceLocalDelta
      (radius : Real) globalDelta tGlobal (4 * ballRadius)
    let localScale := 4 * ballRadius
    let comparisonLambda :=
      actualY1PaperFineCNormalizedAutomaticComparisonLambda
        (radius := radius) globalDelta tGlobal (4 * ballRadius)
    let centerGap := (401 / 100 : Real) * (ballRadius + 6 * tGlobal)
    let curvatureRatio := twoCenterAutomaticCurvatureRatio
      localScale centerGap referenceScale
    let codeBound : ENNReal := projectedCoefficientPackingCap ballRadius
      (2 * (ballRadius + 6 * tGlobal))
    let weight := actualGPrimeThreeShiftCGridWeightedE2SurvivorWeight
      N D e2Label keep left right ballRadius omega
    let weightAt : code -> ActualGPrimeLabelFirstSurvivor
        N D keep left right ballRadius omega -> ENNReal := fun _ a => weight a
    let G :=
      actualGPrimeThreeShiftCGridRightCLocalCover_finiteOccupiedCodeLocalCompactCurvatureData
        fine physical E Y1 fineLabels pointAt globalCenter tubeAt f f1 f2
          outerA outerB hOuter hfDeriv hf1Deriv tGlobal globalDelta facts
            pointSource hpointE N D hD keep left right ballRadius omega
              labelWeight P c sharp hsmall referenceScale hreferenceScale
                hparameter hfunction hfirst hsecond
    let selectedAt := finiteOccupiedCodeLocalCompactSelectedAt rawAt
      rectangleAt (Icc outerA outerB) localCenterAt globalReference codeBound
        weightAt G
    let clusterWeightAt := finiteOccupiedCodeLocalCompactClusterWeightAt rawAt
      rectangleAt (Icc outerA outerB) localCenterAt globalReference codeBound
        weightAt G
    let vertices := codeSelectedCandidates (Finset.univ : Finset code)
      selectedAt
    let candidateWeight := codeSelectedCandidateWeight clusterWeightAt
    let thirdPacking := finiteOccupiedCodeThirdPacking codeBound
      comparisonLambda curvatureRatio curvatureRatio
    let sourceMass := finiteENNRealWeight
      (actualGPrimeThreeShiftCGridWeightedExactCFiber P c) weight
    let cap := actualGPrimeThreeShiftCGridWeightedE2WideCap
      (radius : Real) ballRadius globalDelta tGlobal
    Exists fun Q : CompactC2AtScalesThirdStageOutcome vertices
      (codeSelectedRectangleAt rectangleAt) (Icc outerA outerB)
        globalReference delta localScale referenceScale comparisonLambda
          candidateWeight thirdPacking =>
      (sourceMass <=
          finiteOccupiedCodeLocalPacking comparisonLambda curvatureRatio *
            thirdPacking * (Q.selected.card : ENNReal) * cap) ∧
        (Q.selected.card : Real) <=
          sampledLensBound
            (selectedSubfamilyAutomaticDepthFromCurveBudget
              (actualThreeShiftCGridRestrictedGlobalTubeFamily
                P.gridSelection P.selected
                  (actualGPrimeLabelFirstThreeShiftCGridFinalTraceShift
                    (P := P))).card)
            ((actualThreeShiftCGridRestrictedTubeFamilyAt
              P.gridSelection P.selected
                (actualGPrimeLabelFirstThreeShiftCGridFinalTraceShift
                  (P := P)) c).card : Real) := by
  dsimp only
  let weight : ActualGPrimeLabelFirstSurvivor
      N D keep left right ballRadius omega -> ENNReal :=
    fun a => actualGPrimeE2FirstHitLabelWeight D e2Label
      (actualGPrimeLabelFirstLabel N D keep left right ballRadius omega a)
  let sourceMass := finiteENNRealWeight
    (actualGPrimeThreeShiftCGridWeightedExactCFiber P c) weight
  let cap := actualGPrimeThreeShiftCGridWeightedE2WideCap
    (radius : Real) ballRadius globalDelta tGlobal
  apply
    exists_actualGPrimeThreeShiftCGrid_fixedCThirdStageOutcome_mass_and_sampledLens
      fine physical E Y1 fineLabels pointAt globalCenter tubeAt f f1 f2
        outerA outerB hOuter hfDeriv hf1Deriv tGlobal globalDelta facts
          pointSource hpointE N D hD keep left right ballRadius omega
            (actualGPrimeE2FirstHitLabelWeight D e2Label) P c sharp hsmall
              hcount referenceScale hreferenceScale hparameter hfunction
                hfirstLower hfirst hsecond hsecondContinuous hDfine hfamily hc
                  hreferenceMargin sourceMass cap weight
  · simpa only [sourceMass, weight] using
      actualGPrimeThreeShiftCGridWeightedE2_exactCFiberMass_le_sum_fixedCRawAt
        fine N D e2Label keep left right ballRadius omega f outerA outerB
          globalDelta tGlobal P pointAt tubeAt c
  · simpa only [cap, actualGPrimeThreeShiftCGridWeightedE2WideCap, weight] using
      actualGPrimeThreeShiftCGridWeightedE2_fixedC_clusterWeightAt_le_wideSourceArea
        fine physical E Y1 fineLabels pointAt globalCenter tubeAt f f1 f2
          outerA outerB hOuter hfDeriv hf1Deriv tGlobal globalDelta facts
            pointSource hpointE N D hD e2Label keep left right ballRadius omega
              P c sharp hsmall referenceScale hreferenceScale hparameter
                hfunction hfirst hsecond

#print axioms exists_actualGPrimeThreeShiftCGridWeightedE2_fixedCThirdStageOutcome_mass_and_sampledLens

end

end FamilyStickyCinematicL32Prop41ActualGPrimeThreeShiftCGridWeightedE2FixedCThirdStageMassAndSampledLensV2
