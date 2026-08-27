import FamilyStickyGrounding.Cinematic.FamilyStickyCinematicL32Prop41ActualGPrimeThreeShiftCGridWeightedE2FirstHitOwnerCapV1
import FamilyStickyGrounding.Cinematic.FamilyStickyCinematicL32Prop41ActualY1SamplingPaperFineGPrimeLabelFirstThreeShiftCGridWeightedExactCMassPartitionV2
import FamilyStickyGrounding.Cinematic.FamilyStickyCinematicL32Prop41ActualY1SamplingPaperFineGPrimeLabelFirstThreeShiftCGridWeightedFixedCThirdStageMassOutcomeV2
import Mathlib.Tactic

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 8000000

open Set
open scoped BigOperators ENNReal Interval

namespace FamilyStickyCinematicL32Prop41ActualGPrimeThreeShiftCGridWeightedE2FixedCMassInputsV2

open Submission.Kakeya.ConvexGeometry
open Submission.Kakeya.Uniformity
open FamilyStickyCinematicL32ActualProjectedCenteredHalfPointSourceV1
open FamilyStickyCinematicL32ActualProjectedCenteredHalfY1ActiveGeometryV1
open FamilyStickyCinematicL32CurvilinearRectanglePointMultiplicityV1
open FamilyStickyCinematicL32FiniteOccupiedCodeLocalCompactThirdStageV1
open FamilyStickyCinematicL32FiniteProjectedShadingMultiplicitySliceV1
open FamilyStickyCinematicL32FiniteValueFibresWeightedV1
open FamilyStickyCinematicL32Lemma312PivotCenteredContainerV1
open FamilyStickyCinematicL32Lemma312TwoCenterAutomaticCurvatureRatioV1
open FamilyStickyCinematicL32Prop41ActualGPrimeThreeShiftCGridWeightedE2FirstHitOwnerCapV1
open FamilyStickyCinematicL32Prop41ActualY1FineCoarseRectangleProducerV1
open FamilyStickyCinematicL32Prop41ActualY1PaperFineCNormalizedThreeShiftScaleProducerV1
open FamilyStickyCinematicL32Prop41ActualY1SamplingPaperFineGPrimeLabelFirstCNormalizedRightCLocalCoverTwoCenterLocalCompactOutcomeRepoV2V1
open FamilyStickyCinematicL32Prop41ActualY1SamplingPaperFineGPrimeLabelFirstProvenanceV1
open FamilyStickyCinematicL32Prop41ActualY1SamplingPaperFineGPrimeLabelFirstThreeShiftCGridWeightedExactCMassPartitionV2
open FamilyStickyCinematicL32Prop41ActualY1SamplingPaperFineGPrimeLabelFirstThreeShiftCGridWeightedRightCLocalCoverFiniteOccupiedCodeCurvatureDataV2
open FamilyStickyCinematicL32Prop41ActualY1SamplingPaperFineGPrimeLabelFirstThreeShiftCGridUniformPackageV1
open FamilyStickyCinematicL32Prop41ActualY1SamplingPaperFineGPrimeLabelFirstThreeShiftCGridWeightedUniformPackageV2
open FamilyStickyCinematicL32Prop41ActualY1E2SpatialFirstHitWeightedGPrimeSamplingConnectorV1
open FamilyStickyCinematicL32Prop41CoarseRectangleIncidenceDataV1
open FamilyStickyCinematicL32Prop41CanonicalMaximizerNonconcentrationV1
open FamilyStickyCinematicL32Prop41ENNRealSeventyTwoWeightedRetentionV1
open FamilyStickyCinematicL32Prop41GlobalScaleNearFiberPackingV1
open FamilyStickyCinematicL32Prop41SharpCommonCReferenceV1
open FamilyStickyCinematicL32Prop41ActualY1SharpFineScaleTangencyV1
open FamilyStickyCinematicL32Prop41ActualY1GridRightCLocalCoverSelectedGenericV1
open FamilyStickyCinematicL32Prop41WeightedThreeShiftPigeonholeV1

noncomputable section

local instance tubeDecidableEq {radius : NNReal} :
    DecidableEq (Tube radius) := Classical.decEq _

universe u v

/-!
# Automatic fixed-C mass inputs for the actual weighted E2 route

The first theorem is the exact inner partition: the weight of one literal
normalized-C fibre is the sum over the occupied source-cover code fibres used
by the V2 curvature package.  It is valid for arbitrary extended-real weights,
including infinity.
-/

theorem actualGPrimeThreeShiftCGridWeightedE2_exactCFiberMass_le_sum_fixedCRawAt
    {radius : NNReal} {iota : Type u} [DecidableEq iota]
    {fineLabel : Type v} [DecidableEq fineLabel]
    (fine : UniformTubeFamily radius iota)
    (N : CanonicalNormNonconcentrationData iota)
    (D : CoarseRectangleIncidenceData (point := Real × Real)
      (radius := radius) (iota := iota) fineLabel)
    (e2Label : Int)
    (keep : iota -> fineLabel -> Prop) (left right : iota)
    (ballRadius : Real)
    (omega : (N.family -> Fin 1) × (N.family -> Fin 1))
    (f : Real -> Real) (outerA outerB globalDelta tGlobal : Real)
    (P : ActualGPrimeLabelFirstThreeShiftCGridPaperFineWeightedUniformPackageV2
      fine N D keep left right ballRadius omega
        (actualGPrimeE2FirstHitLabelWeight D e2Label)
        f outerA outerB globalDelta tGlobal)
    (pointAt : fineLabel -> Real × Real)
    (tubeAt : Real × Real -> Tube radius) (c : Real) :
    let labelWeight := actualGPrimeE2FirstHitLabelWeight D e2Label
    let code := ActualGPrimeThreeShiftCGridFixedCCode fine N D keep left right
      ballRadius omega labelWeight f outerA outerB globalDelta tGlobal P
        pointAt tubeAt c
    let rawAt : code -> Finset (ActualGPrimeLabelFirstSurvivor
        N D keep left right ballRadius omega) :=
      actualGPrimeThreeShiftCGridFixedCRawAt fine N D keep left right
        ballRadius omega labelWeight f outerA outerB globalDelta tGlobal P
          pointAt tubeAt c
    let weight : ActualGPrimeLabelFirstSurvivor
        N D keep left right ballRadius omega -> ENNReal :=
      fun a => labelWeight
        (actualGPrimeLabelFirstLabel N D keep left right ballRadius omega a)
    finiteENNRealWeight
        (actualGPrimeThreeShiftCGridWeightedExactCFiber P c) weight <=
      ∑ k ∈ (Finset.univ : Finset code),
        ∑ a ∈ rawAt k, weight a := by
  dsimp only
  let sourceCodes :=
    actualGPrimeThreeShiftCGridWeightedSourceCodesAtC P pointAt tubeAt c
  let weight : ActualGPrimeLabelFirstSurvivor
      N D keep left right ballRadius omega -> ENNReal :=
    fun a => actualGPrimeE2FirstHitLabelWeight D e2Label
      (actualGPrimeLabelFirstLabel N D keep left right ballRadius omega a)
  have hpartition :=
    actualGPrimeThreeShiftCGridWeighted_exactCFiberMass_eq_sum_sourceCodeFiberMass
      P pointAt tubeAt c weight
  rw [hpartition]
  have hattach :=
    sum_subtype_univ_labelWeight_eq_finset sourceCodes
      (fun coverCenter =>
        finiteENNRealWeight
          (actualGPrimeThreeShiftCGridWeightedExactCSourceCodeFiber
            P pointAt tubeAt c coverCenter) weight)
      (fun x : ENNReal => x)
  rw [← hattach]
  rfl

/-- The canonical V2 curvature datum satisfies the wide first-hit cap for
every locally selected pivot.  The proof uses the same E2 weight as the exact
code partition above. -/
theorem actualGPrimeThreeShiftCGridWeightedE2_fixedC_clusterWeightAt_le_wideSourceArea
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
    let codeBound : ENNReal := projectedCoefficientPackingCap ballRadius
      (2 * (ballRadius + 6 * tGlobal))
    let weightAt : code -> ActualGPrimeLabelFirstSurvivor
        N D keep left right ballRadius omega -> ENNReal :=
      fun _ a => labelWeight
        (actualGPrimeLabelFirstLabel N D keep left right ballRadius omega a)
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
    forall k, forall a, a ∈ selectedAt k ->
      clusterWeightAt k a <=
        ENNReal.ofReal
            (2 * ((radius : Real) + 6 * (4 * ballRadius))) *
          ENNReal.ofReal
            (Real.sqrt
                (pyzLemma312PackingLambda 100 *
                  actualY1PaperFineCNormalizedChoiceLocalDelta
                    (radius : Real) globalDelta tGlobal (4 * ballRadius) /
                      (4 * ballRadius)) +
              Real.sqrt ((radius : Real) /
                prop41Y1PaperFineT (radius : Real) globalDelta tGlobal)) := by
  dsimp only
  intro k a _ha
  let labelWeight := actualGPrimeE2FirstHitLabelWeight D e2Label
  let rawAt :=
    actualGPrimeThreeShiftCGridFixedCRawAt fine N D keep left right ballRadius
      omega labelWeight f outerA outerB globalDelta tGlobal P pointAt tubeAt c
  let localCenterAt :=
    actualGPrimeThreeShiftCGridFixedCLocalCenterAt fine N D keep left right
      ballRadius omega labelWeight f f1 f2 outerA outerB hOuter hfDeriv
        hf1Deriv globalDelta tGlobal P pointAt tubeAt c
  let globalReference := globalCenterFixedCommonCReference globalCenter c
    f f1 f2 hfDeriv hf1Deriv outerA outerB hOuter
  let comparisonLambda :=
    actualY1PaperFineCNormalizedAutomaticComparisonLambda
      (radius := radius) globalDelta tGlobal (4 * ballRadius)
  let centerGap := (401 / 100 : Real) * (ballRadius + 6 * tGlobal)
  let curvatureRatio := twoCenterAutomaticCurvatureRatio
    (4 * ballRadius) centerGap referenceScale
  let codeBound : ENNReal := projectedCoefficientPackingCap ballRadius
    (2 * (ballRadius + 6 * tGlobal))
  let G :=
    actualGPrimeThreeShiftCGridRightCLocalCover_finiteOccupiedCodeLocalCompactCurvatureData
      fine physical E Y1 fineLabels pointAt globalCenter tubeAt f f1 f2
        outerA outerB hOuter hfDeriv hf1Deriv tGlobal globalDelta facts
          pointSource hpointE N D hD keep left right ballRadius omega
            labelWeight P c sharp hsmall referenceScale hreferenceScale
              hparameter hfunction hfirst hsecond
  have hrawSubset : forall k, rawAt k ⊆ P.selected := by
    intro k'
    simpa only [rawAt, actualGPrimeThreeShiftCGridFixedCRawAt] using
      actualY1GridRightCLocalCoverUnderlyingFiber_subset P.selected
        (actualGPrimeLabelFirstLabel N D keep left right ballRadius omega)
        (actualGPrimeLabelFirstThreeShiftCGridRightTube N D keep left right
          ballRadius omega P.gridLabel)
        pointAt tubeAt ballRadius (c, k'.1)
  simpa only [labelWeight, rawAt, localCenterAt, globalReference,
    comparisonLambda, centerGap, curvatureRatio, codeBound, G,
    FamilyStickyCinematicL32Prop41ActualY1SamplingPaperFineGPrimeLabelFirstThreeShiftCGridRightCLocalCoverFiniteOccupiedCodeCurvatureDataV1.actualGPrimeThreeShiftCGridLocalCompactRectangleAt,
    FamilyStickyCinematicL32Prop41ActualY1SamplingPaperFineGPrimeLabelFirstThreeShiftCGridWeightedRightCLocalCoverFiniteOccupiedCodeCurvatureDataV2.actualGPrimeThreeShiftCGridLocalCompactRectangleAt]
    using
      actualGPrimeThreeShiftCGridWeightedE2_clusterWeightAt_le_wideSourceArea
        fine Y1 fineLabels pointAt tubeAt f f1 f2 hfDeriv hf1Deriv
          (prop41Y1PaperFineT (radius : Real) globalDelta tGlobal) globalDelta
            tGlobal N D hD e2Label keep left right ballRadius omega outerA
              outerB globalDelta tGlobal P hOuter rawAt hrawSubset localCenterAt
                globalReference referenceScale comparisonLambda curvatureRatio
                  centerGap curvatureRatio codeBound G k a

#print axioms actualGPrimeThreeShiftCGridWeightedE2_exactCFiberMass_le_sum_fixedCRawAt
#print axioms actualGPrimeThreeShiftCGridWeightedE2_fixedC_clusterWeightAt_le_wideSourceArea

end

end FamilyStickyCinematicL32Prop41ActualGPrimeThreeShiftCGridWeightedE2FixedCMassInputsV2
