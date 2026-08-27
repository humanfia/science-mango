import FamilyStickyGrounding.Cinematic.FamilyStickyCinematicL32FiniteOccupiedCodeLocalCompactThirdStageMassOutcomeV1
import FamilyStickyGrounding.Cinematic.FamilyStickyCinematicL32Prop41ActualY1SamplingPaperFineGPrimeLabelFirstThreeShiftCGridWeightedRightCLocalCoverFiniteOccupiedCodeCurvatureDataV2
import Mathlib.Tactic

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 8000000

open Set
open scoped BigOperators ENNReal Interval

namespace FamilyStickyCinematicL32Prop41ActualY1SamplingPaperFineGPrimeLabelFirstThreeShiftCGridWeightedFixedCThirdStageMassOutcomeV2

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
open FamilyStickyCinematicL32FiniteProjectedShadingMultiplicitySliceV1
open FamilyStickyCinematicL32Lemma312TwoCenterAutomaticCurvatureRatioV1
open FamilyStickyCinematicL32Prop41ActualY1FineCoarseRectangleProducerV1
open FamilyStickyCinematicL32Prop41ActualY1PaperFineCNormalizedThreeShiftScaleProducerV1
open FamilyStickyCinematicL32Prop41ActualY1SamplingPaperFineGPrimeLabelFirstProvenanceV1
open FamilyStickyCinematicL32Prop41ActualY1SamplingPaperFineGPrimeLabelFirstCNormalizedRightCLocalCoverTwoCenterLocalCompactOutcomeRepoV2V1
open FamilyStickyCinematicL32Prop41ActualY1SamplingPaperFineGPrimeLabelFirstThreeShiftCGridWeightedRightCLocalCoverFiniteOccupiedCodeCurvatureDataV2
open FamilyStickyCinematicL32Prop41ActualY1SamplingPaperFineGPrimeLabelFirstThreeShiftCGridUniformPackageV1
open FamilyStickyCinematicL32Prop41ActualY1SamplingPaperFineGPrimeLabelFirstThreeShiftCGridWeightedUniformPackageV2
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
# Actual fixed-C third-stage outcome with mass transport

This module is a mechanical specialization of the frozen actual curvature
adapter.  It does not restate any geometric field: the adapter constructs
the complete `FiniteOccupiedCodeLocalCompactCurvatureData`, after which the
package-free occupied-code mass theorem makes both greedy choices.
-/

/-- For one literal normalized endpoint value `c`, automatically run all
occupied-code local outcomes and the cross-code third-stage weighted greedy
selection.  The only remaining mass inputs are the honest one-time raw-code
mass cover and the owner-cluster cap. -/
theorem exists_actualGPrimeThreeShiftCGrid_fixedCThirdStageOutcome_and_mass_le
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
    (referenceScale : Real) (hreferenceScale : 0 <= referenceScale)
    (hparameter : forall z, z ∈ Icc outerA outerB -> |z| <= 1)
    (hfunction : forall z, z ∈ Icc outerA outerB -> |f z| <= 2)
    (hfirst : forall z, z ∈ Icc outerA outerB -> |f1 z| <= 2)
    (hsecond : forall z, z ∈ Icc outerA outerB -> |f2 z| <= 1 / 100)
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
      sourceMass <=
        finiteOccupiedCodeLocalPacking comparisonLambda curvatureRatio *
          thirdPacking * (Q.selected.card : ENNReal) * cap := by
  dsimp only
  intro hpartition hcap
  let G :=
    actualGPrimeThreeShiftCGridRightCLocalCover_finiteOccupiedCodeLocalCompactCurvatureData
      fine physical E Y1 fineLabels pointAt globalCenter tubeAt f f1 f2
        outerA outerB hOuter hfDeriv hf1Deriv tGlobal globalDelta facts
          pointSource hpointE N D hD keep left right ballRadius omega labelWeight P c
            sharp hsmall referenceScale hreferenceScale hparameter hfunction
              hfirst hsecond
  exact
    exists_finiteOccupiedCodeLocalCompactThirdStageOutcome_and_mass_le
      (actualGPrimeThreeShiftCGridFixedCRawAt fine N D keep left right
        ballRadius omega labelWeight f outerA outerB globalDelta tGlobal P pointAt tubeAt c)
      (actualGPrimeThreeShiftCGridLocalCompactRectangleAt N D keep left right
        ballRadius omega globalDelta tGlobal)
      (Icc outerA outerB)
      (actualGPrimeThreeShiftCGridFixedCLocalCenterAt fine N D keep left right
        ballRadius omega labelWeight f f1 f2 outerA outerB hOuter hfDeriv hf1Deriv
          globalDelta tGlobal P pointAt tubeAt c)
      (globalCenterFixedCommonCReference globalCenter c f f1 f2 hfDeriv
        hf1Deriv outerA outerB hOuter)
      (projectedCoefficientPackingCap ballRadius
        (2 * (ballRadius + 6 * tGlobal)) : ENNReal)
      (fun _ a => weight a) G sourceMass cap hpartition hcap

#print axioms exists_actualGPrimeThreeShiftCGrid_fixedCThirdStageOutcome_and_mass_le

end

end FamilyStickyCinematicL32Prop41ActualY1SamplingPaperFineGPrimeLabelFirstThreeShiftCGridWeightedFixedCThirdStageMassOutcomeV2
