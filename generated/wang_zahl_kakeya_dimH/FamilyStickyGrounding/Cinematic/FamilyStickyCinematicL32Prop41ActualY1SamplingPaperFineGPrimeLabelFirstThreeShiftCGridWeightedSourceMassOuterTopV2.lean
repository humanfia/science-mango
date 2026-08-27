import FamilyStickyGrounding.Cinematic.FamilyStickyCinematicL32Prop41ActualY1SamplingPaperFineGPrimeLabelFirstThreeShiftCGridWeightedSelectedMassOuterTopV2
import Mathlib.Tactic

set_option autoImplicit false
set_option warningAsError true

open scoped BigOperators ENNReal

namespace FamilyStickyCinematicL32Prop41ActualY1SamplingPaperFineGPrimeLabelFirstThreeShiftCGridWeightedSourceMassOuterTopV2

open Submission.Kakeya.ConvexGeometry
open Submission.Kakeya.Uniformity
open FamilyStickyCinematicL32FiniteProjectedShadingMultiplicitySliceV1
open FamilyStickyCinematicL32Prop41ActualY1RetainedThreeShiftCGridRestrictedCanonicalFibresV1
open FamilyStickyCinematicL32Prop41ActualY1SamplingPaperFineGPrimeLabelFirstProvenanceV1
open FamilyStickyCinematicL32Prop41ActualGPrimeLabelFirstWeightedSeparatedSamplingOutcomeV1
open FamilyStickyCinematicL32Prop41ActualY1SamplingPaperFineGPrimeLabelFirstThreeShiftCGridThirdStageSelectedSampledLensV2
open FamilyStickyCinematicL32Prop41ActualY1SamplingPaperFineGPrimeLabelFirstThreeShiftCGridWeightedSelectedMassOuterTopV2
open FamilyStickyCinematicL32Prop41ActualY1SamplingPaperFineGPrimeLabelFirstThreeShiftCGridWeightedUniformPackageV2
open FamilyStickyCinematicL32Prop41CanonicalMaximizerNonconcentrationV1
open FamilyStickyCinematicL32Prop41ActualGPrimeDegreeRichMassProducerV1
open FamilyStickyCinematicL32Prop41CanonicalRichSeparatedPairConsumerV1
open FamilyStickyCinematicL32Prop41CoarseRectangleIncidenceDataV1
open FamilyStickyCinematicL32Prop41FiniteRandomSamplingExtractionV1
open FamilyStickyCinematicL32Prop41FiniteRichSeparatedPairSelectionV1
open FamilyStickyCinematicL32Prop41SampledLensCardinalityAssemblyV1
open FamilyStickyCinematicL32Prop41SelectedSubfamilyTwoScaleAutomaticOutcomeFromCurveBudgetRepoV2V1
open FamilyStickyCinematicL32Prop41WeightedThreeShiftPigeonholeV1

noncomputable section

universe u v

/-!
# Weighted source mass through the all-C third-stage sampled-lens top

This is the final package-level algebra before specializing the label weight
to the actual E2 first-hit partition.  It composes the honest factor-72
weighted G-prime/grid/trace retention with the all-C selected-mass bound.
-/

/-- The weighted source degree-gap mass is controlled by the all-C
third-stage sampled-lens expression. -/
theorem actualGPrimeThreeShiftCGrid_source_mul_gap_le_globalSampledLens
    {radius : NNReal} {iota : Type u} [DecidableEq iota]
    {fineLabel : Type v} [DecidableEq fineLabel]
    (fine : UniformTubeFamily radius iota)
    (N : CanonicalNormNonconcentrationData iota)
    (D : CoarseRectangleIncidenceData (point := Real × Real)
      (radius := radius) (iota := iota) fineLabel)
    (keep : iota -> fineLabel -> Prop) (ballRadius : Real)
    (degreeLower : Nat) (labelWeight : fineLabel -> ENNReal)
    (Q : ActualGPrimeWeightedFineSeparatedSampledOutcome
      N D keep ballRadius degreeLower labelWeight)
    (f : Real -> Real) (outerA outerB globalDelta tGlobal : Real)
    (P : ActualGPrimeLabelFirstThreeShiftCGridPaperFineWeightedUniformPackageV2
      fine N D keep Q.pair.left Q.pair.right ballRadius Q.omega labelWeight
        f outerA outerB globalDelta tGlobal)
    (selectedCard : Real -> Nat)
    (localPacking thirdPacking cap : ENNReal)
    (hfibre : forall c, c ∈
      actualThreeShiftCGridRestrictedOccupiedValues P.gridSelection P.selected
        (actualGPrimeLabelFirstThreeShiftCGridFinalTraceShift (P := P)) ->
      finiteENNRealWeight
          (actualThreeShiftCGridRestrictedFiber P.gridSelection P.selected
            (actualGPrimeLabelFirstThreeShiftCGridFinalTraceShift (P := P)) c)
          (actualGPrimeLabelFirstSurvivorWeightAt N D keep Q.pair.left
            Q.pair.right ballRadius Q.omega labelWeight) <=
        localPacking * thirdPacking * (selectedCard c : ENNReal) * cap)
    (hselected : forall c, c ∈
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
                (P := P)) c).card : Real)) :
    (∑ r ∈ D.fineLabels, labelWeight r) *
        ((degreeLower *
          (degreeLower - automaticCanonicalNearCap N ballRadius) : Nat) :
            ENNReal) <=
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
              (twoSidedZeroColorLoad 1 1 Q.omega)) * cap) := by
  have hsource :=
    P.source_mul_gap_le_seventyTwo_pairCount_mul_selectedWeight
      fine N D keep ballRadius degreeLower labelWeight Q
  have hmass :=
    finiteENNRealWeight_actualGPrimeThreeShiftCGrid_selected_le_globalSampledLens
      fine N D keep Q.pair.left Q.pair.right ballRadius Q.omega labelWeight
        f outerA outerB globalDelta tGlobal P selectedCard localPacking
          thirdPacking cap hfibre hselected
  calc
    (∑ r ∈ D.fineLabels, labelWeight r) *
          ((degreeLower *
            (degreeLower - automaticCanonicalNearCap N ballRadius) : Nat) :
              ENNReal) <=
        72 *
          ((richSeparatedCenterPairs N.family
            (canonicalTenRadiusSeparated N ballRadius)
            (fun _ _ => True)).card : ENNReal) *
          (∑ a ∈ P.selected,
            labelWeight (actualGPrimeLabelFirstLabel N D keep Q.pair.left
              Q.pair.right ballRadius Q.omega a)) := hsource
    _ <= 72 *
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
              (twoSidedZeroColorLoad 1 1 Q.omega)) * cap) := by
      gcongr
      simpa only [finiteENNRealWeight,
        actualGPrimeLabelFirstSurvivorWeightAt] using hmass

#print axioms actualGPrimeThreeShiftCGrid_source_mul_gap_le_globalSampledLens

end

end FamilyStickyCinematicL32Prop41ActualY1SamplingPaperFineGPrimeLabelFirstThreeShiftCGridWeightedSourceMassOuterTopV2
