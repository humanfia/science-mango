import FamilyStickyGrounding.Cinematic.FamilyStickyCinematicL32FiniteNestedValueFibresThirdStageMassSelectedCardLoadTopV1
import FamilyStickyGrounding.Cinematic.FamilyStickyCinematicL32Prop41ActualY1RetainedThreeShiftCGridRestrictedCanonicalFibresWeightedV1
import FamilyStickyGrounding.Cinematic.FamilyStickyCinematicL32Prop41ActualY1SamplingPaperFineGPrimeLabelFirstThreeShiftCGridRestrictedLoadBridgeV1
import FamilyStickyGrounding.Cinematic.FamilyStickyCinematicL32Prop41ActualY1SamplingPaperFineGPrimeLabelFirstThreeShiftCGridThirdStageSelectedSampledLensV2
import Mathlib.Tactic

set_option autoImplicit false
set_option warningAsError true

open Set
open scoped BigOperators ENNReal

namespace FamilyStickyCinematicL32Prop41ActualY1SamplingPaperFineGPrimeLabelFirstThreeShiftCGridWeightedSelectedMassOuterTopV2
open Submission.Kakeya.ConvexGeometry
open Submission.Kakeya.Uniformity

open FamilyStickyCinematicL32FiniteNestedValueFibresThirdStageMassSelectedCardLoadTopV1
open FamilyStickyCinematicL32FiniteProjectedShadingMultiplicitySliceV1
open FamilyStickyCinematicL32Prop41ActualY1RetainedThreeShiftCGridRestrictedCanonicalFibresV1
open FamilyStickyCinematicL32Prop41ActualY1RetainedThreeShiftCGridRestrictedCanonicalFibresWeightedV1
open FamilyStickyCinematicL32Prop41ActualY1SamplingPaperFineGPrimeLabelFirstProvenanceV1
open FamilyStickyCinematicL32Prop41ActualY1SamplingPaperFineGPrimeLabelFirstThreeShiftCGridRestrictedLoadBridgeV1
open FamilyStickyCinematicL32Prop41ActualY1SamplingPaperFineGPrimeLabelFirstThreeShiftCGridThirdStageSelectedSampledLensV2
open FamilyStickyCinematicL32Prop41SampledLensCardinalityAssemblyV1
open FamilyStickyCinematicL32Prop41ActualY1SamplingPaperFineGPrimeLabelFirstThreeShiftCGridWeightedUniformPackageV2
open FamilyStickyCinematicL32Prop41CanonicalMaximizerNonconcentrationV1
open FamilyStickyCinematicL32Prop41CoarseRectangleIncidenceDataV1
open FamilyStickyCinematicL32Prop41FiniteRandomSamplingExtractionV1
open FamilyStickyCinematicL32Prop41SelectedSubfamilyTwoScaleAutomaticOutcomeFromCurveBudgetRepoV2V1
open FamilyStickyCinematicL32Prop41WeightedThreeShiftPigeonholeV1

noncomputable section

local instance tubeDecidableEq {radius : NNReal} :
    DecidableEq (Tube radius) := Classical.decEq _

universe u v

/-!
# Weighted V2 selected-mass aggregation over all final normalized-C fibres

The per-C third-stage outcomes have dependent candidate types, so only their
selected cardinalities cross the outer boundary.  This adapter performs the
lossless weighted C-fibre partition, deduplicated curve aggregation, and the
replacement of the final global curve carrier by the original two-sided
random-sample load.
-/

/-- Once every occupied final-C fibre has a third-stage mass estimate and a
sampled-lens selected-cardinality estimate, the entire V2 selected weight is
bounded with one global sampled-lens factor. -/
theorem finiteENNRealWeight_actualGPrimeThreeShiftCGrid_selected_le_globalSampledLens
    {radius : NNReal} {iota : Type u} [DecidableEq iota]
    {fineLabel : Type v} [DecidableEq fineLabel]
    (fine : UniformTubeFamily radius iota)
    (N : CanonicalNormNonconcentrationData iota)
    (D : CoarseRectangleIncidenceData (point := Real × Real)
      (radius := radius) (iota := iota) fineLabel)
    (keep : iota -> fineLabel -> Prop) (left right : iota)
    (ballRadius : Real)
    (omega : (N.family -> Fin 1) × (N.family -> Fin 1))
    (labelWeight : fineLabel -> ENNReal)
    (f : Real -> Real) (outerA outerB globalDelta tGlobal : Real)
    (P : ActualGPrimeLabelFirstThreeShiftCGridPaperFineWeightedUniformPackageV2
      fine N D keep left right ballRadius omega labelWeight f outerA outerB
        globalDelta tGlobal)
    (selectedCard : Real -> Nat)
    (localPacking thirdPacking cap : ENNReal)
    (hfibre : forall c, c ∈
      actualThreeShiftCGridRestrictedOccupiedValues P.gridSelection P.selected
        (actualGPrimeLabelFirstThreeShiftCGridFinalTraceShift (P := P)) ->
      finiteENNRealWeight
          (actualThreeShiftCGridRestrictedFiber P.gridSelection P.selected
            (actualGPrimeLabelFirstThreeShiftCGridFinalTraceShift (P := P)) c)
          (actualGPrimeLabelFirstSurvivorWeightAt N D keep left right
            ballRadius omega labelWeight) <=
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
    finiteENNRealWeight P.selected
        (actualGPrimeLabelFirstSurvivorWeightAt N D keep left right ballRadius
          omega labelWeight) <=
      localPacking * thirdPacking *
        ENNReal.ofReal
          (sampledLensBound
            (selectedSubfamilyAutomaticDepthFromCurveBudget
              (actualThreeShiftCGridRestrictedGlobalTubeFamily P.gridSelection
                P.selected
                  (actualGPrimeLabelFirstThreeShiftCGridFinalTraceShift
                    (P := P))).card)
            (twoSidedZeroColorLoad 1 1 omega)) * cap := by
  let shift :=
    actualGPrimeLabelFirstThreeShiftCGridFinalTraceShift (P := P)
  let values := actualThreeShiftCGridRestrictedOccupiedValues P.gridSelection
    P.selected shift
  let fiber := actualThreeShiftCGridRestrictedFiber P.gridSelection P.selected
    shift
  let curveFiber := actualThreeShiftCGridRestrictedTubeFamilyAt
    P.gridSelection P.selected shift
  let globalCurves := actualThreeShiftCGridRestrictedGlobalTubeFamily
    P.gridSelection P.selected shift
  let weight := actualGPrimeLabelFirstSurvivorWeightAt N D keep left right
    ballRadius omega labelWeight
  let massAt : Real -> ENNReal := fun c => finiteENNRealWeight (fiber c) weight
  let depth := selectedSubfamilyAutomaticDepthFromCurveBudget globalCurves.card
  have hpartition : finiteENNRealWeight P.selected weight <=
      ∑ c ∈ values, massAt c := by
    exact (finiteENNRealWeight_eq_sum_actualThreeShiftCGridRestrictedFiberWeight
      P.gridSelection P.selected shift weight).le
  have hdisjoint : (values : Set Real).PairwiseDisjoint curveFiber := by
    exact pairwiseDisjoint_actualThreeShiftCGridRestrictedTubeFamilyAt
      P.gridSelection P.selected_subset_grid shift
  have hsubset : values.biUnion curveFiber ⊆ globalCurves := by
    rw [biUnion_actualThreeShiftCGridRestrictedTubeFamilyAt_eq_global
      P.gridSelection P.selected shift]
  have hload : (globalCurves.card : Real) <= twoSidedZeroColorLoad 1 1 omega := by
    exact
      actualGPrimeLabelFirstThreeShiftCGridRestrictedGlobalTubeFamily_card_cast_le_load
        N D keep left right ballRadius omega P.gridSelection P.selected shift
  apply
    mass_le_local_mul_third_mul_sampledLensBound_load_mul_cap_of_selectedCard
      (finiteENNRealWeight P.selected weight) values massAt selectedCard
        localPacking thirdPacking cap curveFiber globalCurves depth
          (twoSidedZeroColorLoad 1 1 omega)
  · exact selectedSubfamilyAutomaticDepthFromCurveBudget_nonneg _
  · exact hpartition
  · intro c hc
    simpa only [values, massAt, fiber, weight, shift] using hfibre c hc
  · exact hdisjoint
  · exact hsubset
  · exact hload
  · intro c hc
    simpa only [values, depth, globalCurves, curveFiber, shift] using
      hselected c hc

#print axioms finiteENNRealWeight_actualGPrimeThreeShiftCGrid_selected_le_globalSampledLens

end

end FamilyStickyCinematicL32Prop41ActualY1SamplingPaperFineGPrimeLabelFirstThreeShiftCGridWeightedSelectedMassOuterTopV2
