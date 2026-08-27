import FamilyStickyGrounding.Cinematic.FamilyStickyCinematicL32Prop41ActualGPrimeThreeShiftCGridWeightedE2FixedCMassInputsV2

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 8000000

open Set
open scoped BigOperators ENNReal Interval

namespace FamilyStickyCinematicL32Prop41ActualGPrimeThreeShiftCGridWeightedE2FixedCThirdStageMassOutcomeV2

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
open FamilyStickyCinematicL32Lemma312PivotCenteredContainerV1
open FamilyStickyCinematicL32Lemma312TwoCenterAutomaticCurvatureRatioV1
open FamilyStickyCinematicL32Prop41ActualGPrimeThreeShiftCGridWeightedE2FixedCMassInputsV2
open FamilyStickyCinematicL32Prop41ActualY1E2SpatialFirstHitWeightedGPrimeSamplingConnectorV1
open FamilyStickyCinematicL32Prop41ActualY1FineCoarseRectangleProducerV1
open FamilyStickyCinematicL32Prop41ActualY1PaperFineCNormalizedThreeShiftScaleProducerV1
open FamilyStickyCinematicL32Prop41ActualY1SamplingPaperFineGPrimeLabelFirstCNormalizedRightCLocalCoverTwoCenterLocalCompactOutcomeRepoV2V1
open FamilyStickyCinematicL32Prop41ActualY1SamplingPaperFineGPrimeLabelFirstProvenanceV1
open FamilyStickyCinematicL32Prop41ActualY1SamplingPaperFineGPrimeLabelFirstThreeShiftCGridWeightedExactCMassPartitionV2
open FamilyStickyCinematicL32Prop41ActualY1SamplingPaperFineGPrimeLabelFirstThreeShiftCGridWeightedFixedCThirdStageMassOutcomeV2
open FamilyStickyCinematicL32Prop41ActualY1SamplingPaperFineGPrimeLabelFirstThreeShiftCGridWeightedRightCLocalCoverFiniteOccupiedCodeCurvatureDataV2
open FamilyStickyCinematicL32Prop41ActualY1SamplingPaperFineGPrimeLabelFirstThreeShiftCGridWeightedUniformPackageV2
open FamilyStickyCinematicL32Prop41ActualY1SharpFineScaleTangencyV1
open FamilyStickyCinematicL32Prop41CanonicalMaximizerNonconcentrationV1
open FamilyStickyCinematicL32Prop41CoarseRectangleIncidenceDataV1
open FamilyStickyCinematicL32Prop41GlobalScaleNearFiberPackingV1
open FamilyStickyCinematicL32Prop41SharpCommonCReferenceV1
open FamilyStickyCinematicL32Prop41WeightedThreeShiftPigeonholeV1

noncomputable section

local instance c2GraphRectangleDecidableEq : DecidableEq C2GraphRectangle :=
  Classical.decEq _

local instance tubeDecidableEq {radius : NNReal} :
    DecidableEq (Tube radius) := Classical.decEq _

universe u v

/-!
# Automatic actual weighted-E2 fixed-C third-stage mass outcome

The source mass is the literal first-hit mass on one exact normalized-C
fibre.  The inner source-code partition and the wide-source owner cap are
generated automatically, so the result exposes only the geometric hypotheses
already needed by the frozen V2 curvature producer.
-/

/-- First-hit survivor weight used throughout the actual E2 route. -/
noncomputable def actualGPrimeThreeShiftCGridWeightedE2SurvivorWeight
    {radius : NNReal} {iota : Type u} [DecidableEq iota]
    {fineLabel : Type v} [DecidableEq fineLabel]
    (N : CanonicalNormNonconcentrationData iota)
    (D : CoarseRectangleIncidenceData (point := Real × Real)
      (radius := radius) (iota := iota) fineLabel)
    (e2Label : Int) (keep : iota -> fineLabel -> Prop) (left right : iota)
    (ballRadius : Real)
    (omega : (N.family -> Fin 1) × (N.family -> Fin 1)) :
    ActualGPrimeLabelFirstSurvivor
      N D keep left right ballRadius omega -> ENNReal :=
  fun a => actualGPrimeE2FirstHitLabelWeight D e2Label
    (actualGPrimeLabelFirstLabel N D keep left right ballRadius omega a)

/-- Explicit honest wide-source area cap. -/
noncomputable def actualGPrimeThreeShiftCGridWeightedE2WideCap
    (radius ballRadius globalDelta tGlobal : Real) : ENNReal :=
  ENNReal.ofReal (2 * (radius + 6 * (4 * ballRadius))) *
    ENNReal.ofReal
      (Real.sqrt
          (pyzLemma312PackingLambda 100 *
            actualY1PaperFineCNormalizedChoiceLocalDelta radius globalDelta
              tGlobal (4 * ballRadius) / (4 * ballRadius)) +
        Real.sqrt
          (radius / prop41Y1PaperFineT radius globalDelta tGlobal))

/-- Run the frozen local and third greedy stages on one exact normalized-C
fibre with both mass inputs discharged automatically. -/
theorem exists_actualGPrimeThreeShiftCGridWeightedE2_fixedCThirdStageOutcome_and_mass_le
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
    (referenceScale : Real) (hreferenceScale : 0 <= referenceScale)
    (hparameter : forall z, z ∈ Icc outerA outerB -> |z| <= 1)
    (hfunction : forall z, z ∈ Icc outerA outerB -> |f z| <= 2)
    (hfirst : forall z, z ∈ Icc outerA outerB -> |f1 z| <= 2)
    (hsecond : forall z, z ∈ Icc outerA outerB -> |f2 z| <= 1 / 100) :
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
      sourceMass <=
        finiteOccupiedCodeLocalPacking comparisonLambda curvatureRatio *
          thirdPacking * (Q.selected.card : ENNReal) * cap := by
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
    exists_actualGPrimeThreeShiftCGrid_fixedCThirdStageOutcome_and_mass_le
      fine physical E Y1 fineLabels pointAt globalCenter tubeAt f f1 f2
        outerA outerB hOuter hfDeriv hf1Deriv tGlobal globalDelta facts
          pointSource hpointE N D hD keep left right ballRadius omega
            (actualGPrimeE2FirstHitLabelWeight D e2Label) P c sharp hsmall
              referenceScale hreferenceScale hparameter hfunction hfirst
                hsecond sourceMass cap weight
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

#print axioms actualGPrimeThreeShiftCGridWeightedE2SurvivorWeight
#print axioms actualGPrimeThreeShiftCGridWeightedE2WideCap
#print axioms exists_actualGPrimeThreeShiftCGridWeightedE2_fixedCThirdStageOutcome_and_mass_le

end

end FamilyStickyCinematicL32Prop41ActualGPrimeThreeShiftCGridWeightedE2FixedCThirdStageMassOutcomeV2
