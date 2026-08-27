import FamilyStickyGrounding.Cinematic.FamilyStickyCinematicL32Prop41ActualChoiceOfShiftPairLocalWeightedBridgeV1
import FamilyStickyGrounding.Cinematic.FamilyStickyCinematicL32Prop41ActualY1RetainedThreeShiftCGridTangencyV1
import FamilyStickyGrounding.Cinematic.FamilyStickyCinematicL32Prop41ActualY1RetainedThreeShiftCGridWeightedSelectionV1
import Mathlib.Tactic

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 4000000

open Set
open scoped BigOperators ENNReal

namespace FamilyStickyCinematicL32Prop41ActualY1RetainedThreeShiftCGridWeightedTangencyV1

open Submission.Kakeya.ConvexGeometry
open Submission.Kakeya.Uniformity
open FamilyStickyCinematicL32ActualProjectedCenteredHalfPointSourceV1
open FamilyStickyCinematicL32ActualTubeConstantShiftV1
open FamilyStickyCinematicL32ActualProjectedCenteredHalfY1ActiveGeometryV1
open FamilyStickyCinematicL32CenteredFractionIntervalsV1
open FamilyStickyCinematicL32CenteredFractionNestingV1
open FamilyStickyCinematicL32CurvilinearRectangleCarrierV1
open FamilyStickyCinematicL32CurvilinearRectanglePointMultiplicityV1
open FamilyStickyCinematicL32FiniteProjectedShadingMultiplicitySliceV1
open FamilyStickyCinematicL32Prop41ActualChoiceOfShiftPairLocalBridgeV1
open FamilyStickyCinematicL32Prop41ActualChoiceOfShiftPairLocalWeightedBridgeV1
open FamilyStickyCinematicL32Prop41FiniteGeneralPositionExactRootReproductionV1
open FamilyStickyCinematicL32Prop41ActualY1FineCoarseRectangleProducerV1
open FamilyStickyCinematicL32Prop41ActualY1PaperFineCNormalizedThreeShiftScaleProducerV1
open FamilyStickyCinematicL32Prop41ActualY1PaperFineTangencyV1
open FamilyStickyCinematicL32Prop41ActualY1RetainedCNormalizedThreeShiftPerturbationReadyV1
open FamilyStickyCinematicL32Prop41ActualY1RetainedThreeShiftCGridSelectionV1
open FamilyStickyCinematicL32Prop41ActualY1RetainedThreeShiftCGridTangencyV1
open FamilyStickyCinematicL32Prop41ActualY1RetainedThreeShiftCGridWeightedSelectionV1
open FamilyStickyCinematicL32Prop41ActualY1RetainedThreeShiftPerturbationReadyV1
open FamilyStickyCinematicL32Prop41ActualY1SamplingPaperFineGPrimeLabelFirstApproxCSelectionV1
open FamilyStickyCinematicL32Prop41ActualY1SharpFineScaleTangencyV1
open FamilyStickyCinematicL32Prop41CoarseRectangleIncidenceDataV1
open FamilyStickyCinematicL32Prop41PairLocalActualLensRectangleCoreV1
open FamilyStickyCinematicL32Prop41TangencyProductToScaleV1
open FamilyStickyCinematicL32Prop41ThreeShiftPigeonholeV1
open FamilyStickyCinematicL32Prop41WeightedThreeShiftPigeonholeV1
open FamilyStickyCinematicL32RectangleTangencyV1
open FamilyStickyCinematicL32ThreeShiftCGridTubeNormalizationV1

noncomputable section

universe u v w

/-!
# Weighted actual C-grid and trace-shift selection

The two finite choices are both made against the same fixed `ENNReal` weight.
Consequently their losses compose to exactly nine.  The geometry and endpoint
maps are identical to the cardinal construction, but no simultaneous
cardinality-retention claim is made.
-/

/-- Actual weight-aware grid-plus-trace selection with complete final local
data and an honest factor-nine mass retention. -/
theorem exists_uniform_threeShift_weighted_perturbationReady_of_actualRetainedY1ThreeShiftCGrid
    {radius : NNReal} {iota : Type u} [DecidableEq iota]
    {fineLabel : Type v} [DecidableEq fineLabel]
    {alpha : Type w} [DecidableEq alpha]
    (fine : UniformTubeFamily radius iota)
    (physical : FiniteProjectedShading (Real × Real) iota)
    (E : Set (Real × Real))
    (Y1 : FiniteProjectedShading (Real × Real) iota)
    (fineLabels : Finset fineLabel) (pointAt : fineLabel -> Real × Real)
    (centerTube : Tube radius) (tubeAt : Real × Real -> Tube radius)
    (f f1 f2 : Real -> Real) (outerA outerB : Real)
    (hOuter : outerA <= outerB)
    (hf : forall z, HasDerivAt f (f1 z) z)
    (hf1 : forall z, HasDerivAt f1 (f2 z) z)
    (tGlobal globalDelta : Real)
    (facts : ActualCenteredHalfY1ActiveGeometryFacts fine physical E
      Y1.activeAtPoint tubeAt f f1 f2 outerA outerB hOuter hf hf1
      tGlobal globalDelta)
    (pointSource : ActualCenteredHalfPointRectangleSource E centerTube tubeAt
      f outerA outerB tGlobal)
    (hpointE : forall r, r ∈ fineLabels -> pointAt r ∈ E)
    (N : ActualY1SharpFineScaleNumerics
      (radius : Real) globalDelta tGlobal (outerB - outerA))
    (hparameter : forall z, z ∈ Icc outerA outerB -> |z| <= 1)
    (hft : forall z, z ∈ Icc outerA outerB -> |f z| <= 2)
    (hf1Lower : forall z, z ∈ Icc outerA outerB -> 1 <= |f1 z|)
    (hf1Upper : forall z, z ∈ Icc outerA outerB -> |f1 z| <= 2)
    (hf2 : forall z, z ∈ Icc outerA outerB -> |f2 z| <= 1 / 100)
    (hf2Continuous : ContinuousOn f2 (Icc outerA outerB))
    (items : Finset alpha)
    (leftIndex rightIndex : alpha -> iota)
    (labelAt : alpha -> fineLabel)
    (keep : iota -> fineLabel -> Prop)
    {localDelta pairScale rho traceQ lambda : Real}
    (S : ActualY1PaperFineCNormalizedChoiceScaleNumerics
      (radius : Real) globalDelta tGlobal localDelta pairScale rho)
    (selection : ActualRetainedY1ApproxCPairSelection
      (y1FineCoarseRectangleData fine Y1 fineLabels pointAt tubeAt
        f f1 f2 hf hf1 (radius : Real)
        (prop41Y1PaperFineT (radius : Real) globalDelta tGlobal)
        globalDelta tGlobal)
      items leftIndex rightIndex labelAt keep pairScale (radius : Real))
    (hitems : items.Nonempty)
    (htraceQ : 1 <= traceQ)
    (hlambda : 0 < lambda) (hrhoLambda : rho <= lambda)
    (hshiftDominates :
      10 * prop41TangencyScaleFactor traceQ < lambda)
    (hstrengthenedScale :
      (10 * prop41TangencyScaleFactor traceQ + lambda) * localDelta <
        pairScale / 46080)
    (htraceRadius : 2 * (rho * localDelta) <= traceQ * localDelta)
    (weight : alpha -> ENNReal) :
    let D := y1FineCoarseRectangleData fine Y1 fineLabels pointAt tubeAt
      f f1 f2 hf hf1 (radius : Real)
      (prop41Y1PaperFineT (radius : Real) globalDelta tGlobal)
      globalDelta tGlobal
    exists (grid : ActualRetainedY1WeightedThreeShiftCGridSelection D items
        leftIndex rightIndex labelAt keep pairScale weight)
      (k : Fin 3) (eta : Real) (fiber : Finset alpha)
      (_P : forall a, a ∈ fiber ->
        PerturbationReadyPairLocalActualLensRectangleData
          (traceTranslateTube
            (threeShiftCGridNormalizeTube grid.gridLabel
              (fine.tubes (leftIndex a)))
            (eta * (lambda * localDelta)))
          (threeShiftCGridNormalizeTube grid.gridLabel
            (fine.tubes (rightIndex a)))
          f (D.fineRectangleAt (labelAt a)) outerA outerB localDelta
          pairScale lambda (2 * lambda)),
      eta = threeShiftValue k ∧
      eta ∈ ({(-1 : Real), 0, 1} : Set Real) ∧
      grid.selected.Nonempty ∧
      grid.selected ⊆ items ∧
      finiteENNRealWeight items weight <=
        3 * finiteENNRealWeight grid.selected weight ∧
      fiber.Nonempty ∧
      fiber ⊆ grid.selected ∧
      finiteENNRealWeight grid.selected weight <=
        3 * finiteENNRealWeight fiber weight ∧
      finiteENNRealWeight items weight <=
        9 * finiteENNRealWeight fiber weight ∧
      forall a, a ∈ fiber ->
        (leftIndex a, labelAt a) ∈ D.retainedGoodPairs keep ∧
        (rightIndex a, labelAt a) ∈ D.retainedGoodPairs keep ∧
        (D.fineRectangleAt (labelAt a)).carrier (radius : Real) ⊆
          (D.coarseRectangleAt (labelAt a)).carrier globalDelta := by
  dsimp only
  let fineT := prop41Y1PaperFineT (radius : Real) globalDelta tGlobal
  let D := y1FineCoarseRectangleData fine Y1 fineLabels pointAt tubeAt
    f f1 f2 hf hf1 (radius : Real) fineT globalDelta tGlobal
  have hweightedGrid : Nonempty
      (ActualRetainedY1WeightedThreeShiftCGridSelection D items
        leftIndex rightIndex labelAt keep pairScale weight) := by
    simpa only [D, fineT] using
      exists_actualRetainedY1WeightedThreeShiftCGridSelection
        (y1FineCoarseRectangleData fine Y1 fineLabels pointAt tubeAt
          f f1 f2 hf hf1 (radius : Real)
          (prop41Y1PaperFineT (radius : Real) globalDelta tGlobal)
          globalDelta tGlobal)
        items leftIndex rightIndex labelAt keep pairScale selection
          N.fineDelta_pos hitems weight
  obtain ⟨weightedGrid⟩ := hweightedGrid
  let restrictedSelection : ActualRetainedY1ApproxCPairSelection D
      weightedGrid.selected leftIndex rightIndex labelAt keep pairScale
        (radius : Real) := by
    have selectionD : ActualRetainedY1ApproxCPairSelection D items
        leftIndex rightIndex labelAt keep pairScale (radius : Real) := by
      simpa only [D, fineT] using selection
    exact
      FamilyStickyCinematicL32Prop41ActualY1RetainedThreeShiftCGridWeightedSelectionV1.ActualRetainedY1ApproxCPairSelection.restrict
        selectionD weightedGrid.selected_subset
  let grid : ActualRetainedY1ThreeShiftCGridSelection D weightedGrid.selected
      leftIndex rightIndex labelAt keep pairScale :=
    weightedGrid.toOrdinaryOnSelected
  let T : alpha -> Tube radius := fun a =>
    threeShiftCGridNormalizeTube weightedGrid.gridLabel
      (fine.tubes (leftIndex a))
  let U : alpha -> Tube radius := fun a =>
    threeShiftCGridNormalizeTube weightedGrid.gridLabel
      (fine.tubes (rightIndex a))
  let rectangles : alpha -> C2GraphRectangle :=
    fun a => D.fineRectangleAt (labelAt a)
  have hdata : forall a, a ∈ weightedGrid.selected ->
      ActualTwoFamilyRectangleTangencyData
        (T a) (U a) f (rectangles a) outerA outerB localDelta
          pairScale rho := by
    intro a ha
    have haGrid : a ∈ grid.selected := by
      simpa only [grid,
        ActualRetainedY1WeightedThreeShiftCGridSelection.toOrdinaryOnSelected]
        using ha
    have h :=
      retainedY1ThreeShiftCGridSelectedPair_actualTwoFamilyRectangleTangencyData
        fine physical E Y1 fineLabels pointAt centerTube tubeAt f f1 f2
        outerA outerB hOuter hf hf1 tGlobal globalDelta facts pointSource
        hpointE N hparameter hft hf1Lower hf1Upper hf2 hf2Continuous
        weightedGrid.selected leftIndex rightIndex labelAt keep S
          restrictedSelection grid a haGrid
    simpa only [T, U, rectangles, D, fineT, grid,
      ActualRetainedY1WeightedThreeShiftCGridSelection.toOrdinaryOnSelected]
      using h
  obtain ⟨k, eta, fiber, P, heta, hetaMem, hfiber, hfiberGrid,
      htraceWeight⟩ :=
    exists_uniform_threeShift_weighted_perturbationReadyPairLocalActualLensRectangleData
      weightedGrid.selected T U rectangles f f1 f2
        weightedGrid.selected_nonempty S.localDelta_pos S.pairScale_pos
          htraceQ hlambda hrhoLambda hshiftDominates hstrengthenedScale
            htraceRadius N.outerWidth_lower (fun z _hz => hf z)
              (fun z _hz => hf1 z) hparameter hft hf1Lower hf1Upper hf2
                hf2Continuous hdata weight
  have hnine : finiteENNRealWeight items weight <=
      9 * finiteENNRealWeight fiber weight := by
    calc
      finiteENNRealWeight items weight <=
          3 * finiteENNRealWeight weightedGrid.selected weight :=
        weightedGrid.grid_weight_retention
      _ <= 3 * (3 * finiteENNRealWeight fiber weight) := by
        gcongr
      _ = 9 * finiteENNRealWeight fiber weight := by ring
  refine ⟨weightedGrid, k, eta, fiber, ?_, heta, hetaMem,
    weightedGrid.selected_nonempty, weightedGrid.selected_subset,
    weightedGrid.grid_weight_retention, hfiber, hfiberGrid, htraceWeight,
    hnine, ?_⟩
  · intro a ha
    simpa only [T, U, rectangles, D, fineT] using P a ha
  · intro a ha
    have haGrid : a ∈ weightedGrid.selected := hfiberGrid ha
    have hleft := weightedGrid.left_retained a haGrid
    have hright := weightedGrid.right_retained a haGrid
    have hleftResult :=
      retainedY1Pair_paperFine_tangent_and_fine_subset_coarse
        fine physical E Y1 fineLabels pointAt centerTube tubeAt f f1 f2
          outerA outerB hOuter hf hf1 tGlobal globalDelta facts pointSource
          hpointE N hparameter hft hf1Lower hf1Upper hf2 hf2Continuous keep
          (leftIndex a) (labelAt a) (by
            simpa only [D, fineT] using hleft)
    exact ⟨hleft, hright, by
      simpa only [D, fineT] using hleftResult.2⟩

#print axioms exists_uniform_threeShift_weighted_perturbationReady_of_actualRetainedY1ThreeShiftCGrid

end

end FamilyStickyCinematicL32Prop41ActualY1RetainedThreeShiftCGridWeightedTangencyV1
