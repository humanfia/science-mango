import FamilyStickyGrounding.Cinematic.FamilyStickyCinematicL32Prop41ActualY1SamplingPaperFineGPrimeLabelFirstThreeShiftCGridWeightedFixedCThirdStageMassOutcomeV2
import FamilyStickyGrounding.Cinematic.FamilyStickyCinematicL32Prop41ActualY1SamplingPaperFineGPrimeLabelFirstThreeShiftCGridThirdStageSelectedSampledLensV2
import FamilyStickyGrounding.Cinematic.FamilyStickyCinematicL32Prop41ActualY1SamplingPaperFineGPrimeLabelFirstThreeShiftCGridWeightedExactCThirdStageVerticesNonemptyV2
import FamilyStickyGrounding.Cinematic.FamilyStickyCinematicL32Prop41ActualY1SamplingPaperFineGPrimeLabelFirstThreeShiftCGridWeightedRightCLocalCoverFiniteOccupiedCodeCurvatureDataV2
import Mathlib.Tactic

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 8000000

open Set
open scoped BigOperators ENNReal Interval

namespace FamilyStickyCinematicL32Prop41ActualY1SamplingPaperFineGPrimeLabelFirstThreeShiftCGridWeightedFixedCThirdStageSampledLensConsumerV2

open Submission.Kakeya.ConvexGeometry
open Submission.Kakeya.Uniformity
open FamilyStickyWZ2TubeCarrierCoordinateAdapterV1
open FamilyStickyCinematicL32ActualProjectedCenteredHalfPointSourceV1
open FamilyStickyCinematicL32ActualProjectedCenteredHalfY1ActiveGeometryV1
open FamilyStickyCinematicL32CurvilinearRectanglePointMultiplicityV1
open FamilyStickyCinematicL32FiniteNestedValueFibresThirdStageAtScalesV1
open FamilyStickyCinematicL32FiniteNestedValueFibresExternalPivotThirdStageV1
open FamilyStickyCinematicL32FiniteOccupiedCodeLocalCompactThirdStageV1
open FamilyStickyCinematicL32FiniteOccupiedCodeLocalCompactThirdStageMassOutcomeV1
open FamilyStickyCinematicL32Prop41ActualY1GridRightCLocalCoverSelectedGenericV1
open FamilyStickyCinematicL32FiniteProjectedShadingMultiplicitySliceV1
open FamilyStickyCinematicL32Lemma312TwoCenterAutomaticCurvatureRatioV1
open FamilyStickyCinematicL32Prop41ActualY1FineCoarseRectangleProducerV1
open FamilyStickyCinematicL32Prop41ActualGlobalNormCoarseFiberV1
open FamilyStickyCinematicL32Prop41ActualY1PaperFineCNormalizedSelectedCountingNumericsV1
open FamilyStickyCinematicL32Prop41ActualY1PaperFineCNormalizedThreeShiftScaleProducerV1
open FamilyStickyCinematicL32Prop41ActualY1SamplingPaperFineGPrimeLabelFirstProvenanceV1
open FamilyStickyCinematicL32Prop41ActualY1SamplingPaperFineGPrimeLabelFirstCNormalizedRightCLocalCoverTwoCenterLocalCompactOutcomeRepoV2V1
open FamilyStickyCinematicL32Prop41ActualY1SamplingPaperFineGPrimeLabelFirstThreeShiftCGridWeightedRightCLocalCoverFiniteOccupiedCodeCurvatureDataV2
open FamilyStickyCinematicL32Prop41ActualY1SamplingPaperFineGPrimeLabelFirstThreeShiftCGridUniformPackageV1
open FamilyStickyCinematicL32Prop41ActualY1SamplingPaperFineGPrimeLabelFirstThreeShiftCGridWeightedUniformPackageV2
open FamilyStickyCinematicL32Prop41ActualY1SamplingPaperFineGPrimeLabelFirstThreeShiftCGridThirdStageSelectedSampledLensV2
open FamilyStickyCinematicL32Prop41ActualY1SamplingPaperFineGPrimeLabelFirstThreeShiftCGridRestrictedCoefficientBallV1
open FamilyStickyCinematicL32Prop41ActualY1SamplingPaperFineGPrimeLabelFirstThreeShiftCGridWeightedExactCMassPartitionV2
open FamilyStickyCinematicL32Prop41SampledLensCardinalityAssemblyV1
open FamilyStickyCinematicL32Prop41SelectedSubfamilyTwoScaleAutomaticOutcomeFromCurveBudgetRepoV2V1
open FamilyStickyCinematicL32Prop41ActualY1RetainedThreeShiftCGridRestrictedCanonicalFibresV1
open FamilyStickyCinematicL32Prop41ActualY1SamplingPaperFineGPrimeLabelFirstThreeShiftCGridWeightedExactCThirdStageVerticesNonemptyV2
open FamilyStickyCinematicL32Prop41ActualY1SamplingPaperFineGPrimeLabelFirstThreeShiftCGridWeightedFixedCThirdStageMassOutcomeV2
open FamilyStickyCinematicL32Prop41ActualY1SharpFineScaleTangencyV1
open FamilyStickyCinematicL32Prop41CanonicalMaximizerNonconcentrationV1
open FamilyStickyCinematicL32Prop41CoarseRectangleIncidenceDataV1
open FamilyStickyCinematicL32Prop41GlobalScaleNearFiberPackingV1
open FamilyStickyCinematicL32Prop41SharpCommonCReferenceV1

noncomputable section

local instance c2GraphRectangleDecidableEq : DecidableEq C2GraphRectangle :=
  Classical.decEq _

local instance tubeDecidableEq {radius : NNReal} :
    DecidableEq (Tube radius) := Classical.decEq _

universe u v

/-!
# Actual fixed-C third-stage mass and sampled-lens consumer

This thin layer takes the third-stage outcome chosen by the mass producer and
feeds the very same selected family to the V2 sampled-lens theorem.  Occupied
C supplies nonempty tagged vertices, while raw-code membership supplies both
selected-subset and literal common-C transport.
-/

/-- Produce one fixed-C third-stage outcome carrying both its honest mass
estimate and its sampled-lens selected-cardinality estimate. -/
theorem exists_actualGPrimeThreeShiftCGrid_fixedCThirdStageOutcome_mass_and_sampledLens
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
    (keep : iota -> fineLabel -> Prop) (left right : iota)
    (ballRadius : Real)
    (omega : (N.family -> Fin 1) × (N.family -> Fin 1))
    (labelWeight : fineLabel -> ENNReal)
    (P : ActualGPrimeLabelFirstThreeShiftCGridPaperFineWeightedUniformPackageV2 fine N D
      keep left right ballRadius omega labelWeight f outerA outerB globalDelta tGlobal)
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
    (hc : c ∈
      actualGPrimeThreeShiftCGridWeightedOccupiedCValues P)
    (hreferenceMargin :
      max ((401 / 100 : Real) *
          actualGPrimeLabelFirstThreeShiftCGridRestrictedCoefficientRadius
            tGlobal (actualGPrimeLabelFirstThreeShiftCGridFinalTraceShift
              (P := P)))
        (2 * actualGPrimeLabelFirstThreeShiftCGridRestrictedCoefficientRadius
            tGlobal (actualGPrimeLabelFirstThreeShiftCGridFinalTraceShift
              (P := P)) + 0) < 3 * referenceScale)
    (sourceMass cap : ENNReal)
    (weight : ActualGPrimeLabelFirstSurvivor
      N D keep left right ballRadius omega -> ENNReal) :
    let code := ActualGPrimeThreeShiftCGridFixedCCode fine N D keep left right
      ballRadius omega labelWeight f outerA outerB globalDelta tGlobal P pointAt tubeAt c
    let rawAt : code -> Finset (ActualGPrimeLabelFirstSurvivor
        N D keep left right ballRadius omega) :=
      actualGPrimeThreeShiftCGridFixedCRawAt fine N D keep left right
        ballRadius omega labelWeight f outerA outerB globalDelta tGlobal P pointAt tubeAt c
    let rectangleAt := actualGPrimeThreeShiftCGridLocalCompactRectangleAt
      N D keep left right ballRadius omega globalDelta tGlobal
    let localCenterAt := actualGPrimeThreeShiftCGridFixedCLocalCenterAt fine N D
      keep left right ballRadius omega labelWeight f f1 f2 outerA outerB hOuter hfDeriv
        hf1Deriv globalDelta tGlobal P pointAt tubeAt c
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
    let weightAt : code -> ActualGPrimeLabelFirstSurvivor
        N D keep left right ballRadius omega -> ENNReal := fun _ a => weight a
    let G :=
      actualGPrimeThreeShiftCGridRightCLocalCover_finiteOccupiedCodeLocalCompactCurvatureData
        fine physical E Y1 fineLabels pointAt globalCenter tubeAt f f1 f2
          outerA outerB hOuter hfDeriv hf1Deriv tGlobal globalDelta facts
            pointSource hpointE N D hD keep left right ballRadius omega labelWeight P c
              sharp hsmall referenceScale hreferenceScale hparameter hfunction
                hfirst hsecond
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
    forall (_hpartition : sourceMass <=
      ∑ k ∈ (Finset.univ : Finset code), ∑ a ∈ rawAt k, weightAt k a),
    (forall k, forall a, a ∈ selectedAt k -> clusterWeightAt k a <= cap) ->
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
  intro hpartition hcap
  obtain ⟨Q, hmass⟩ :=
    exists_actualGPrimeThreeShiftCGrid_fixedCThirdStageOutcome_and_mass_le
      fine physical E Y1 fineLabels pointAt globalCenter tubeAt f f1 f2
        outerA outerB hOuter hfDeriv hf1Deriv tGlobal globalDelta facts
          pointSource hpointE N D hD keep left right ballRadius omega labelWeight
            P c sharp hsmall referenceScale hreferenceScale hparameter hfunction
              hfirst hsecond sourceMass cap weight hpartition hcap
  refine ⟨Q, hmass, ?_⟩
  let code := ActualGPrimeThreeShiftCGridFixedCCode fine N D keep left right
    ballRadius omega labelWeight f outerA outerB globalDelta tGlobal P pointAt tubeAt c
  let rawAt : code -> Finset (ActualGPrimeLabelFirstSurvivor
      N D keep left right ballRadius omega) :=
    actualGPrimeThreeShiftCGridFixedCRawAt fine N D keep left right
      ballRadius omega labelWeight f outerA outerB globalDelta tGlobal P pointAt tubeAt c
  let rectangleAt := actualGPrimeThreeShiftCGridLocalCompactRectangleAt
    N D keep left right ballRadius omega globalDelta tGlobal
  let localCenterAt := actualGPrimeThreeShiftCGridFixedCLocalCenterAt fine N D
    keep left right ballRadius omega labelWeight f f1 f2 outerA outerB hOuter hfDeriv
      hf1Deriv globalDelta tGlobal P pointAt tubeAt c
  let globalReference := globalCenterFixedCommonCReference globalCenter c
    f f1 f2 hfDeriv hf1Deriv outerA outerB hOuter
  let codeBound : ENNReal := projectedCoefficientPackingCap ballRadius
    (2 * (ballRadius + 6 * tGlobal))
  let weightAt : code -> ActualGPrimeLabelFirstSurvivor
      N D keep left right ballRadius omega -> ENNReal := fun _ a => weight a
  let G :=
    actualGPrimeThreeShiftCGridRightCLocalCover_finiteOccupiedCodeLocalCompactCurvatureData
      fine physical E Y1 fineLabels pointAt globalCenter tubeAt f f1 f2
        outerA outerB hOuter hfDeriv hf1Deriv tGlobal globalDelta facts
          pointSource hpointE N D hD keep left right ballRadius omega labelWeight P c
            sharp hsmall referenceScale hreferenceScale hparameter hfunction
              hfirst hsecond
  let selectedAt := finiteOccupiedCodeLocalCompactSelectedAt rawAt
    rectangleAt (Icc outerA outerB) localCenterAt globalReference codeBound
      weightAt G
  let clusterWeightAt := finiteOccupiedCodeLocalCompactClusterWeightAt rawAt
    rectangleAt (Icc outerA outerB) localCenterAt globalReference codeBound
      weightAt G
  let vertices := codeSelectedCandidates (Finset.univ : Finset code) selectedAt
  let candidateWeight := codeSelectedCandidateWeight clusterWeightAt
  let comparisonLambda :=
    actualY1PaperFineCNormalizedAutomaticComparisonLambda
      (radius := radius) globalDelta tGlobal (4 * ballRadius)
  let centerGap := (401 / 100 : Real) * (ballRadius + 6 * tGlobal)
  let curvatureRatio := twoCenterAutomaticCurvatureRatio
    (4 * ballRadius) centerGap referenceScale
  let thirdPacking := finiteOccupiedCodeThirdPacking codeBound
    comparisonLambda curvatureRatio curvatureRatio
  have hvertices : vertices.Nonempty := by
    exact
      actualGPrimeThreeShiftCGridWeighted_codeSelectedCandidates_nonempty
        P pointAt tubeAt c hc rectangleAt (Icc outerA outerB) localCenterAt
          globalReference codeBound weightAt G
  have hselectedAt : forall k a, a ∈ selectedAt k -> a ∈ P.selected := by
    intro k a ha
    have haRaw : a ∈ rawAt k :=
      finiteOccupiedCodeLocalCompactSelectedAt_subset rawAt rectangleAt
        (Icc outerA outerB) localCenterAt globalReference codeBound weightAt G k ha
    apply actualY1GridRightCLocalCoverUnderlyingFiber_subset P.selected
      (actualGPrimeLabelFirstLabel N D keep left right ballRadius omega)
      (actualGPrimeLabelFirstThreeShiftCGridRightTube N D keep left right
        ballRadius omega P.gridLabel)
      pointAt tubeAt ballRadius (c, k.1)
    simpa only [rawAt, actualGPrimeThreeShiftCGridFixedCRawAt] using haRaw
  have hfixedC : forall k a, a ∈ selectedAt k ->
      tubeGraphC
        (actualGPrimeLabelFirstThreeShiftCGridRightTube N D keep left right
          ballRadius omega P.gridLabel a) = c := by
    intro k a ha
    have haRaw : a ∈ rawAt k :=
      finiteOccupiedCodeLocalCompactSelectedAt_subset rawAt rectangleAt
        (Icc outerA outerB) localCenterAt globalReference codeBound weightAt G k ha
    apply actualY1GridRightCLocalCoverUnderlyingFiber_rightGraphC P.selected
      (actualGPrimeLabelFirstLabel N D keep left right ballRadius omega)
      (actualGPrimeLabelFirstThreeShiftCGridRightTube N D keep left right
        ballRadius omega P.gridLabel)
      pointAt tubeAt ballRadius c k.1 a
    simpa only [rawAt, actualGPrimeThreeShiftCGridFixedCRawAt] using haRaw
  exact
    actualGPrimeLabelFirstThreeShiftCGrid_thirdStageSelected_card_le_sampledLensBound
      (fine := fine) (physical := physical) (tGlobal := tGlobal)
      (globalCenter := globalCenter) (N := N) (D := D) (keep := keep)
      (left := left) (right := right) (ballRadius := ballRadius)
      (omega := omega) (labelWeight := labelWeight) (f := f)
      (outerA := outerA) (outerB := outerB) (globalDelta := globalDelta)
      (P := P) selectedAt c referenceScale candidateWeight thirdPacking
        f1 f2 hOuter hfDeriv hf1Deriv Q hvertices hselectedAt hfixedC
          hDfine hfamily sharp hsmall hcount hparameter hfunction hfirstLower
            hfirst hsecond hsecondContinuous hreferenceMargin

#print axioms exists_actualGPrimeThreeShiftCGrid_fixedCThirdStageOutcome_mass_and_sampledLens

end

end FamilyStickyCinematicL32Prop41ActualY1SamplingPaperFineGPrimeLabelFirstThreeShiftCGridWeightedFixedCThirdStageSampledLensConsumerV2
