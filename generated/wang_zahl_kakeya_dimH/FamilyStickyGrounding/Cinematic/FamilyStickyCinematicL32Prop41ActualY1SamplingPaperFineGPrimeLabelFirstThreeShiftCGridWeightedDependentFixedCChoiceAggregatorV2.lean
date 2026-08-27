import FamilyStickyGrounding.Cinematic.FamilyStickyCinematicL32Prop41ActualGPrimeThreeShiftCGridWeightedE2FixedCThirdStageMassAndSampledLensV2
import FamilyStickyGrounding.Cinematic.FamilyStickyCinematicL32Prop41ActualY1SamplingPaperFineGPrimeLabelFirstThreeShiftCGridWeightedFixedCThirdStageSampledLensConsumerV2
import FamilyStickyGrounding.Cinematic.FamilyStickyCinematicL32Prop41ActualY1SamplingPaperFineGPrimeLabelFirstThreeShiftCGridWeightedSourceMassOuterTopV2
import Mathlib.Tactic

set_option autoImplicit false
set_option warningAsError true

open Set MeasureTheory
open scoped BigOperators ENNReal Interval

namespace FamilyStickyCinematicL32Prop41ActualY1SamplingPaperFineGPrimeLabelFirstThreeShiftCGridWeightedDependentFixedCChoiceAggregatorV2

open Submission.Kakeya.ConvexGeometry
open Submission.Kakeya.Uniformity
open FamilyStickyCinematicL32ActualProjectedCenteredHalfPointSourceV1
open FamilyStickyCinematicL32ActualProjectedCenteredHalfY1ActiveGeometryV1
open FamilyStickyCinematicL32CurvilinearRectanglePointMultiplicityV1
open FamilyStickyCinematicL32FiniteNestedValueFibresThirdStageAtScalesV1
open FamilyStickyCinematicL32FiniteNestedValueFibresExternalPivotThirdStageV1
open FamilyStickyCinematicL32FiniteOccupiedCodeLocalCompactThirdStageV1
open FamilyStickyCinematicL32FiniteOccupiedCodeLocalCompactThirdStageMassOutcomeV1
open FamilyStickyCinematicL32Lemma312TwoCenterAutomaticCurvatureRatioV1
open FamilyStickyCinematicL32Prop41ActualGPrimeThreeShiftCGridWeightedE2FixedCThirdStageMassAndSampledLensV2
open FamilyStickyCinematicL32Prop41ActualGPrimeThreeShiftCGridWeightedE2FixedCThirdStageMassOutcomeV2
open FamilyStickyCinematicL32Prop41ActualGlobalNormCoarseFiberV1
open FamilyStickyCinematicL32Prop41ActualY1E2SpatialFirstHitWeightedGPrimeSamplingConnectorV1
open FamilyStickyCinematicL32FiniteProjectedPositiveMultiplicityDyadicV1
open FamilyStickyCinematicL32Prop41ActualGPrimeDegreeRichMassProducerV1
open FamilyStickyCinematicL32Prop41ActualGPrimeLabelFirstWeightedSeparatedSamplingOutcomeV1
open FamilyStickyCinematicL32Prop41ActualY1SamplingPaperFineGPrimeLabelFirstThreeShiftCGridWeightedSourceMassOuterTopV2
open FamilyStickyCinematicL32Prop41CanonicalRichSeparatedPairConsumerV1
open FamilyStickyCinematicL32Prop41FiniteRichSeparatedPairSelectionV1
open FamilyStickyCinematicL32Prop41FiniteRandomSamplingExtractionV1
open FamilyStickyCinematicL32PyzE2DyadicDegreeWindowV1
open FamilyStickyCinematicL32Prop41ActualY1FineCoarseRectangleProducerV1
open FamilyStickyCinematicL32Prop41ActualY1PaperFineCNormalizedSelectedCountingNumericsV1
open FamilyStickyCinematicL32Prop41ActualY1PaperFineCNormalizedThreeShiftScaleProducerV1
open FamilyStickyCinematicL32Prop41ActualY1SharpFineScaleTangencyV1
open FamilyStickyCinematicL32Prop41GlobalScaleNearFiberPackingV1
open FamilyStickyCinematicL32FiniteProjectedShadingMultiplicitySliceV1
open FamilyStickyCinematicL32Prop41ActualY1RetainedThreeShiftCGridRestrictedCanonicalFibresV1
open FamilyStickyCinematicL32Prop41ActualY1SamplingPaperFineGPrimeLabelFirstProvenanceV1
open FamilyStickyCinematicL32Prop41ActualY1SamplingPaperFineGPrimeLabelFirstCNormalizedRightCLocalCoverTwoCenterLocalCompactOutcomeRepoV2V1
open FamilyStickyCinematicL32Prop41ActualY1SamplingPaperFineGPrimeLabelFirstThreeShiftCGridRestrictedCoefficientBallV1
open FamilyStickyCinematicL32Prop41ActualY1SamplingPaperFineGPrimeLabelFirstThreeShiftCGridWeightedExactCMassPartitionV2
open FamilyStickyCinematicL32Prop41ActualY1SamplingPaperFineGPrimeLabelFirstThreeShiftCGridThirdStageSelectedSampledLensV2
open FamilyStickyCinematicL32Prop41ActualY1SamplingPaperFineGPrimeLabelFirstThreeShiftCGridWeightedUniformPackageV2
open FamilyStickyCinematicL32Prop41CanonicalMaximizerNonconcentrationV1
open FamilyStickyCinematicL32Prop41CoarseRectangleIncidenceDataV1
open FamilyStickyCinematicL32Prop41SampledLensCardinalityAssemblyV1
open FamilyStickyCinematicL32Prop41SelectedSubfamilyTwoScaleAutomaticOutcomeFromCurveBudgetRepoV2V1
open FamilyStickyCinematicL32Prop41WeightedThreeShiftPigeonholeV1

noncomputable section

local instance c2GraphRectangleDecidableEq : DecidableEq C2GraphRectangle :=
  Classical.decEq _

local instance tubeDecidableEq {radius : NNReal} :
    DecidableEq (Tube radius) := Classical.decEq _

universe u v

/-!
# Dependent fixed-C choice for the weighted all-fibre top

The third-stage outcome type depends on the literal normalized coefficient
`c`.  This lemma makes one outcome in every occupied fibre and, crucially,
uses the card of that same outcome in both the fibre-mass and sampled-lens
bounds.
-/

/-- Choose one dependent outcome in every occupied value and extend its card
by zero off the occupied set.  The two exported inequalities use the same
chosen outcome in each fibre. -/
theorem exists_selectedCard_of_forall_exists_same_outcome
    (values : Finset Real)
    (Outcome : Real -> Type*)
    (cardAt : forall c, Outcome c -> Nat)
    (massAt : Real -> ENNReal)
    (localPacking thirdPacking cap : ENNReal)
    (lensAt : Real -> Real)
    (hchoice : forall c, c ∈ values ->
      Exists fun Q : Outcome c =>
        massAt c <=
            localPacking * thirdPacking * (cardAt c Q : ENNReal) * cap ∧
          ((cardAt c Q : Nat) : Real) <= lensAt c) :
    Exists fun selectedCard : Real -> Nat =>
      (forall c, c ∈ values ->
        massAt c <=
          localPacking * thirdPacking * (selectedCard c : ENNReal) * cap) ∧
      (forall c, c ∈ values ->
        ((selectedCard c : Nat) : Real) <= lensAt c) := by
  classical
  choose Q hQ using hchoice
  let selectedCard : Real -> Nat := fun c =>
    if hc : c ∈ values then cardAt c (Q c hc) else 0
  refine ⟨selectedCard, ?_, ?_⟩
  · intro c hc
    simpa only [selectedCard, dif_pos hc] using (hQ c hc).1
  · intro c hc
    simpa only [selectedCard, dif_pos hc] using (hQ c hc).2


/-- Choose the same automatic third-stage outcome in every occupied exact-C
fibre and export the mass and sampled-lens bounds for one total card function. -/
theorem exists_actualGPrimeThreeShiftCGridWeightedE2_selectedCard
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
    (hreferenceMargin :
      max ((401 / 100 : Real) *
          actualGPrimeLabelFirstThreeShiftCGridRestrictedCoefficientRadius
            tGlobal (actualGPrimeLabelFirstThreeShiftCGridFinalTraceShift
              (P := P)))
        (2 * actualGPrimeLabelFirstThreeShiftCGridRestrictedCoefficientRadius
            tGlobal (actualGPrimeLabelFirstThreeShiftCGridFinalTraceShift
              (P := P)) + 0) < 3 * referenceScale) :
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
    Exists fun selectedCard : Real -> Nat =>
      (forall c, c ∈ actualGPrimeThreeShiftCGridWeightedOccupiedCValues P ->
        finiteENNRealWeight
            (actualGPrimeThreeShiftCGridWeightedExactCFiber P c)
            (actualGPrimeThreeShiftCGridWeightedE2SurvivorWeight
              N D e2Label keep left right ballRadius omega) <=
          localPacking * thirdPacking * (selectedCard c : ENNReal) * cap) ∧
      (forall c, c ∈ actualGPrimeThreeShiftCGridWeightedOccupiedCValues P ->
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
                  (P := P)) c).card : Real)) := by
  dsimp only
  apply exists_selectedCard_of_forall_exists_same_outcome
    (actualGPrimeThreeShiftCGridWeightedOccupiedCValues P)
    (fun _ => Nat) (fun _ n => n)
    (fun c => finiteENNRealWeight
      (actualGPrimeThreeShiftCGridWeightedExactCFiber P c)
      (actualGPrimeThreeShiftCGridWeightedE2SurvivorWeight
        N D e2Label keep left right ballRadius omega))
    (finiteOccupiedCodeLocalPacking
      (actualY1PaperFineCNormalizedAutomaticComparisonLambda
        (radius := radius) globalDelta tGlobal (4 * ballRadius))
      (twoCenterAutomaticCurvatureRatio (4 * ballRadius)
        ((401 / 100 : Real) * (ballRadius + 6 * tGlobal)) referenceScale))
    (finiteOccupiedCodeThirdPacking
      (projectedCoefficientPackingCap ballRadius
        (2 * (ballRadius + 6 * tGlobal)) : ENNReal)
      (actualY1PaperFineCNormalizedAutomaticComparisonLambda
        (radius := radius) globalDelta tGlobal (4 * ballRadius))
      (twoCenterAutomaticCurvatureRatio (4 * ballRadius)
        ((401 / 100 : Real) * (ballRadius + 6 * tGlobal)) referenceScale)
      (twoCenterAutomaticCurvatureRatio (4 * ballRadius)
        ((401 / 100 : Real) * (ballRadius + 6 * tGlobal)) referenceScale))
    (actualGPrimeThreeShiftCGridWeightedE2WideCap
      (radius : Real) ballRadius globalDelta tGlobal)
    (fun c => sampledLensBound
      (selectedSubfamilyAutomaticDepthFromCurveBudget
        (actualThreeShiftCGridRestrictedGlobalTubeFamily P.gridSelection
          P.selected
            (actualGPrimeLabelFirstThreeShiftCGridFinalTraceShift
              (P := P))).card)
      ((actualThreeShiftCGridRestrictedTubeFamilyAt P.gridSelection P.selected
        (actualGPrimeLabelFirstThreeShiftCGridFinalTraceShift (P := P)) c).card : Real))
  intro c hc
  obtain ⟨Q, hmass, hcard⟩ :=
    exists_actualGPrimeThreeShiftCGridWeightedE2_fixedCThirdStageOutcome_mass_and_sampledLens
      fine physical E Y1 fineLabels pointAt globalCenter tubeAt f f1 f2
        outerA outerB hOuter hfDeriv hf1Deriv tGlobal globalDelta facts
          pointSource hpointE N D hD e2Label keep left right ballRadius omega
            P c sharp hsmall hcount referenceScale hreferenceScale hparameter
              hfunction hfirstLower hfirst hsecond hsecondContinuous hDfine
                hfamily hc hreferenceMargin
  exact ⟨Q.selected.card, hmass, hcard⟩


/-- The package-level E2 source mass is controlled by the global sampled-lens
expression after choosing all dependent fixed-C outcomes. -/
theorem actualGPrimeThreeShiftCGridWeightedE2_source_mul_gap_le_globalSampledLens
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
    (e2Label : Int) (ballRadius : Real)
    (Q : ActualGPrimeE2FirstHitWeightedSampledOutcome
      N D e2Label ballRadius)
    (P : ActualGPrimeLabelFirstThreeShiftCGridPaperFineWeightedUniformPackageV2
      fine N D (fun _ _ => True) Q.sampled.pair.left Q.sampled.pair.right
        ballRadius Q.sampled.omega
          (actualGPrimeE2FirstHitLabelWeight D e2Label)
            f outerA outerB globalDelta tGlobal)
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
    (hreferenceMargin :
      max ((401 / 100 : Real) *
          actualGPrimeLabelFirstThreeShiftCGridRestrictedCoefficientRadius
            tGlobal (actualGPrimeLabelFirstThreeShiftCGridFinalTraceShift
              (P := P)))
        (2 * actualGPrimeLabelFirstThreeShiftCGridRestrictedCoefficientRadius
            tGlobal (actualGPrimeLabelFirstThreeShiftCGridFinalTraceShift
              (P := P)) + 0) < 3 * referenceScale) :
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
    volume (projectedPositiveMultiplicityDyadicCell D.shading e2Label) *
        ((pyzE2DegreeLower e2Label *
          (pyzE2DegreeLower e2Label -
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
  obtain ⟨selectedCard, hfibre, hselected⟩ :=
    exists_actualGPrimeThreeShiftCGridWeightedE2_selectedCard
      fine physical E Y1 fineLabels pointAt globalCenter tubeAt f f1 f2
        outerA outerB hOuter hfDeriv hf1Deriv tGlobal globalDelta facts
          pointSource hpointE N D hD e2Label (fun _ _ => True)
            Q.sampled.pair.left Q.sampled.pair.right ballRadius Q.sampled.omega
              P sharp hsmall hcount referenceScale hreferenceScale hparameter
                hfunction hfirstLower hfirst hsecond hsecondContinuous hDfine
                  hfamily hreferenceMargin
  have hfibreOuter : forall c, c ∈
      actualThreeShiftCGridRestrictedOccupiedValues P.gridSelection P.selected
        (actualGPrimeLabelFirstThreeShiftCGridFinalTraceShift (P := P)) ->
      finiteENNRealWeight
          (actualThreeShiftCGridRestrictedFiber P.gridSelection P.selected
            (actualGPrimeLabelFirstThreeShiftCGridFinalTraceShift (P := P)) c)
          (actualGPrimeLabelFirstSurvivorWeightAt N D (fun _ _ => True)
            Q.sampled.pair.left Q.sampled.pair.right ballRadius Q.sampled.omega
              (actualGPrimeE2FirstHitLabelWeight D e2Label)) <=
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
        (actualGPrimeLabelFirstSurvivorWeightAt N D (fun _ _ => True)
          Q.sampled.pair.left Q.sampled.pair.right ballRadius Q.sampled.omega
            (actualGPrimeE2FirstHitLabelWeight D e2Label)) <= _ at hmass
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
  have htop :=
    actualGPrimeThreeShiftCGrid_source_mul_gap_le_globalSampledLens
      fine N D (fun _ _ => True) ballRadius (pyzE2DegreeLower e2Label)
        (actualGPrimeE2FirstHitLabelWeight D e2Label) Q.sampled f outerA
          outerB globalDelta tGlobal P selectedCard
            (finiteOccupiedCodeLocalPacking
              (actualY1PaperFineCNormalizedAutomaticComparisonLambda
                (radius := radius) globalDelta tGlobal (4 * ballRadius))
              (twoCenterAutomaticCurvatureRatio (4 * ballRadius)
                ((401 / 100 : Real) * (ballRadius + 6 * tGlobal)) referenceScale))
            (finiteOccupiedCodeThirdPacking
              (projectedCoefficientPackingCap ballRadius
                (2 * (ballRadius + 6 * tGlobal)) : ENNReal)
              (actualY1PaperFineCNormalizedAutomaticComparisonLambda
                (radius := radius) globalDelta tGlobal (4 * ballRadius))
              (twoCenterAutomaticCurvatureRatio (4 * ballRadius)
                ((401 / 100 : Real) * (ballRadius + 6 * tGlobal)) referenceScale)
              (twoCenterAutomaticCurvatureRatio (4 * ballRadius)
                ((401 / 100 : Real) * (ballRadius + 6 * tGlobal)) referenceScale))
            (actualGPrimeThreeShiftCGridWeightedE2WideCap
              (radius : Real) ballRadius globalDelta tGlobal)
            hfibreOuter hselectedOuter
  rw [Q.firstHit_mass_eq] at htop
  exact htop

#print axioms exists_selectedCard_of_forall_exists_same_outcome
#print axioms exists_actualGPrimeThreeShiftCGridWeightedE2_selectedCard
#print axioms actualGPrimeThreeShiftCGridWeightedE2_source_mul_gap_le_globalSampledLens

end

end FamilyStickyCinematicL32Prop41ActualY1SamplingPaperFineGPrimeLabelFirstThreeShiftCGridWeightedDependentFixedCChoiceAggregatorV2
