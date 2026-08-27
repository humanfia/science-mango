import FamilyStickyGrounding.Cinematic.FamilyStickyCinematicL32Prop41ActualY1RetainedCNormalizedThreeShiftPerturbationReadyV1
import FamilyStickyGrounding.Cinematic.FamilyStickyCinematicL32Prop41ActualY1RetainedThreeShiftCGridSelectionV1

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 4000000

open Set

namespace FamilyStickyCinematicL32Prop41ActualY1RetainedThreeShiftCGridTangencyV1

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
open FamilyStickyCinematicL32Prop41ActualTubeCNormalizationV1
open FamilyStickyCinematicL32Prop41FiniteGeneralPositionExactRootReproductionV1
open FamilyStickyCinematicL32Prop41ActualY1FineCoarseRectangleProducerV1
open FamilyStickyCinematicL32Prop41ActualY1PaperFineCNormalizedThreeShiftScaleProducerV1
open FamilyStickyCinematicL32Prop41ActualY1PaperFineTangencyV1
open FamilyStickyCinematicL32Prop41ActualY1RetainedCNormalizedThreeShiftPerturbationReadyV1
open FamilyStickyCinematicL32Prop41ActualY1RetainedThreeShiftCGridSelectionV1
open FamilyStickyCinematicL32Prop41ActualY1RetainedThreeShiftPerturbationReadyV1
open FamilyStickyCinematicL32Prop41ActualY1SamplingPaperFineGPrimeLabelFirstApproxCSelectionV1
open FamilyStickyCinematicL32Prop41ActualY1SharpFineScaleTangencyV1
open FamilyStickyCinematicL32Prop41CoarseRectangleIncidenceDataV1
open FamilyStickyCinematicL32Prop41TangencyProductToScaleV1
open FamilyStickyCinematicL32Prop41ThreeShiftPigeonholeV1
open FamilyStickyCinematicL32RectangleTangencyV1
open FamilyStickyCinematicL32ThreeShiftCGridPigeonholeV1
open FamilyStickyCinematicL32ThreeShiftCGridTubeNormalizationV1
open FamilyStickyCinematicL32TubePairTraceV1
open FamilyStickyWZ2TubeCarrierCoordinateAdapterV1

noncomputable section

universe u v w

/-!
# Actual retained tangency after tube-local shifted C-grid normalization

Both endpoints are normalized independently as functions of their own tubes.
On a selected common grid code their graph-C coordinates agree.  Each
normalization moves graph-C by at most one tube radius, so the original
five-radius retained tangency becomes a six-radius tangency on each side.
-/

/-- A retained pair in the uniform grid fibre supplies exact-common-C
two-family tangency data for the independently normalized tubes. -/
theorem retainedY1ThreeShiftCGridSelectedPair_actualTwoFamilyRectangleTangencyData
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
    {localDelta pairScale rho : Real}
    (S : ActualY1PaperFineCNormalizedChoiceScaleNumerics
      (radius : Real) globalDelta tGlobal localDelta pairScale rho)
    (selection : ActualRetainedY1ApproxCPairSelection
      (y1FineCoarseRectangleData fine Y1 fineLabels pointAt tubeAt
        f f1 f2 hf hf1 (radius : Real)
        (prop41Y1PaperFineT (radius : Real) globalDelta tGlobal)
        globalDelta tGlobal)
      items leftIndex rightIndex labelAt keep pairScale (radius : Real))
    (grid : ActualRetainedY1ThreeShiftCGridSelection
      (y1FineCoarseRectangleData fine Y1 fineLabels pointAt tubeAt
        f f1 f2 hf hf1 (radius : Real)
        (prop41Y1PaperFineT (radius : Real) globalDelta tGlobal)
        globalDelta tGlobal)
      items leftIndex rightIndex labelAt keep pairScale)
    (a : alpha) (ha : a ∈ grid.selected) :
    let D := y1FineCoarseRectangleData fine Y1 fineLabels pointAt tubeAt
      f f1 f2 hf hf1 (radius : Real)
      (prop41Y1PaperFineT (radius : Real) globalDelta tGlobal)
      globalDelta tGlobal
    ActualTwoFamilyRectangleTangencyData
      (threeShiftCGridNormalizeTube grid.gridLabel
        (fine.tubes (leftIndex a)))
      (threeShiftCGridNormalizeTube grid.gridLabel
        (fine.tubes (rightIndex a)))
      f (D.fineRectangleAt (labelAt a)) outerA outerB localDelta
        pairScale rho := by
  dsimp only
  let fineT := prop41Y1PaperFineT (radius : Real) globalDelta tGlobal
  let D := y1FineCoarseRectangleData fine Y1 fineLabels pointAt tubeAt
    f f1 f2 hf hf1 (radius : Real) fineT globalDelta tGlobal
  have haItems : a ∈ items := grid.selected_subset ha
  have Q :=
    retainedY1ApproxCSelectedPair_actualTwoFamilyRectangleTangencyData
      fine physical E Y1 fineLabels pointAt centerTube tubeAt f f1 f2
      outerA outerB hOuter hf hf1 tGlobal globalDelta facts pointSource
      hpointE N hparameter hft hf1Lower hf1Upper hf2 hf2Continuous
      items leftIndex rightIndex labelAt keep
      (S.toFiveBudget N.fineDelta_pos.le) S.normalized_tangency_budget
      selection a haItems
  have hleftRetained : (leftIndex a, labelAt a) ∈
      D.retainedGoodPairs keep := by
    simpa only [D, fineT] using grid.left_retained a ha
  have hrightRetained : (rightIndex a, labelAt a) ∈
      D.retainedGoodPairs keep := by
    simpa only [D, fineT] using grid.right_retained a ha
  have hleftResult := retainedY1Pair_paperFine_tangent_and_fine_subset_coarse
    fine physical E Y1 fineLabels pointAt centerTube tubeAt f f1 f2
      outerA outerB hOuter hf hf1 tGlobal globalDelta facts pointSource
      hpointE N hparameter hft hf1Lower hf1Upper hf2 hf2Continuous keep
      (leftIndex a) (labelAt a) (by
        simpa only [D, fineT] using hleftRetained)
  have hrightResult := retainedY1Pair_paperFine_tangent_and_fine_subset_coarse
    fine physical E Y1 fineLabels pointAt centerTube tubeAt f f1 f2
      outerA outerB hOuter hf hf1 tGlobal globalDelta facts pointSource
      hpointE N hparameter hft hf1Lower hf1Upper hf2 hf2Continuous keep
      (rightIndex a) (labelAt a) (by
        simpa only [D, fineT] using hrightRetained)
  have hbaseWhole :
      (D.fineRectangleAt (labelAt a)).rectangle.base ⊆
        Icc outerA outerB := by
    intro z hz
    have hleftWhole := quarter_subset_whole hOuter Q.left_mem_quarter
    have hrightWhole := quarter_subset_whole hOuter Q.right_mem_quarter
    exact ⟨hleftWhole.1.trans hz.1, hz.2.trans hrightWhole.2⟩
  have hunit : forall z,
      z ∈ (D.fineRectangleAt (labelAt a)).rectangle.base -> |z| <= 1 := by
    intro z hz
    exact hparameter z (hbaseWhole hz)
  have hcarrierMono : (D.fineRectangleAt (labelAt a)).carrier localDelta ⊆
      (D.fineRectangleAt (labelAt a)).carrier (radius : Real) :=
    c2GraphRectangle_carrier_mono_radius _ S.localDelta_le_fineDelta
  have hleftFine :
      (D.fineRectangleAt (labelAt a)).carrier (radius : Real) ⊆
        cinematicVerticalNeighborhood
          (actualTubeCinematicTrace f (fine.tubes (leftIndex a)))
          (D.fineRectangleAt (labelAt a)).rectangle.base
          (5 * (radius : Real)) := by
    change (D.fineRectangleAt (labelAt a)).carrier (radius : Real) ⊆
      cinematicVerticalNeighborhood
        (cinematicTraceValue f
          (tubeGraphA (fine.tubes (leftIndex a)))
          (tubeGraphB (fine.tubes (leftIndex a)))
          (tubeGraphC (fine.tubes (leftIndex a)))
          (tubeGraphD (fine.tubes (leftIndex a))))
        (D.fineRectangleAt (labelAt a)).rectangle.base
        (5 * (radius : Real))
    simpa only [D, fineT] using hleftResult.1
  have hrightFine :
      (D.fineRectangleAt (labelAt a)).carrier (radius : Real) ⊆
        cinematicVerticalNeighborhood
          (actualTubeCinematicTrace f (fine.tubes (rightIndex a)))
          (D.fineRectangleAt (labelAt a)).rectangle.base
          (5 * (radius : Real)) := by
    change (D.fineRectangleAt (labelAt a)).carrier (radius : Real) ⊆
      cinematicVerticalNeighborhood
        (cinematicTraceValue f
          (tubeGraphA (fine.tubes (rightIndex a)))
          (tubeGraphB (fine.tubes (rightIndex a)))
          (tubeGraphC (fine.tubes (rightIndex a)))
          (tubeGraphD (fine.tubes (rightIndex a))))
        (D.fineRectangleAt (labelAt a)).rectangle.base
        (5 * (radius : Real))
    simpa only [D, fineT] using hrightResult.1
  have hleftGap :
      |threeShiftNormalizedC (radius : Real) grid.gridLabel
          (tubeGraphC (fine.tubes (leftIndex a))) -
        tubeGraphC (fine.tubes (leftIndex a))| <= (radius : Real) := by
    simpa only [threeShiftCGridNormalizeTube,
      tubeGraphC_normalizeTubeC, y1FineCoarseRectangleData,
      abs_sub_comm] using grid.left_c_change a ha
  have hrightGap :
      |threeShiftNormalizedC (radius : Real) grid.gridLabel
          (tubeGraphC (fine.tubes (rightIndex a))) -
        tubeGraphC (fine.tubes (rightIndex a))| <= (radius : Real) := by
    simpa only [threeShiftCGridNormalizeTube,
      tubeGraphC_normalizeTubeC, y1FineCoarseRectangleData,
      abs_sub_comm] using grid.right_c_change a ha
  have hleftGridFine :
      (D.fineRectangleAt (labelAt a)).carrier (radius : Real) ⊆
        cinematicVerticalNeighborhood
          (actualTubeCinematicTrace f
            (threeShiftCGridNormalizeTube grid.gridLabel
              (fine.tubes (leftIndex a))))
          (D.fineRectangleAt (labelAt a)).rectangle.base
          (5 * (radius : Real) + (radius : Real)) := by
    exact hleftFine.trans (by
      simpa only [threeShiftCGridNormalizeTube] using
        actualTubeCinematicTrace_neighborhood_subset_normalizeTubeC_of_gap
          (fine.tubes (leftIndex a))
          (threeShiftNormalizedC (radius : Real) grid.gridLabel
            (tubeGraphC (fine.tubes (leftIndex a))))
          f (D.fineRectangleAt (labelAt a)).rectangle.base
          (5 * (radius : Real)) (radius : Real) hunit hleftGap)
  have hrightGridFine :
      (D.fineRectangleAt (labelAt a)).carrier (radius : Real) ⊆
        cinematicVerticalNeighborhood
          (actualTubeCinematicTrace f
            (threeShiftCGridNormalizeTube grid.gridLabel
              (fine.tubes (rightIndex a))))
          (D.fineRectangleAt (labelAt a)).rectangle.base
          (5 * (radius : Real) + (radius : Real)) := by
    exact hrightFine.trans (by
      simpa only [threeShiftCGridNormalizeTube] using
        actualTubeCinematicTrace_neighborhood_subset_normalizeTubeC_of_gap
          (fine.tubes (rightIndex a))
          (threeShiftNormalizedC (radius : Real) grid.gridLabel
            (tubeGraphC (fine.tubes (rightIndex a))))
          f (D.fineRectangleAt (labelAt a)).rectangle.base
          (5 * (radius : Real)) (radius : Real) hunit hrightGap)
  have hleftTangent :
      (D.fineRectangleAt (labelAt a)).carrier localDelta ⊆
        cinematicVerticalNeighborhood
          (actualTubeCinematicTrace f
            (threeShiftCGridNormalizeTube grid.gridLabel
              (fine.tubes (leftIndex a))))
          (D.fineRectangleAt (labelAt a)).rectangle.base
          (rho * localDelta) := by
    exact hcarrierMono.trans (hleftGridFine.trans
      (cinematicVerticalNeighborhood_mono_radius _ _ (by
        calc
          5 * (radius : Real) + (radius : Real) =
              6 * (radius : Real) := by ring
          _ <= rho * localDelta := S.normalized_tangency_budget)))
  have hrightTangent :
      (D.fineRectangleAt (labelAt a)).carrier localDelta ⊆
        cinematicVerticalNeighborhood
          (actualTubeCinematicTrace f
            (threeShiftCGridNormalizeTube grid.gridLabel
              (fine.tubes (rightIndex a))))
          (D.fineRectangleAt (labelAt a)).rectangle.base
          (rho * localDelta) := by
    exact hcarrierMono.trans (hrightGridFine.trans
      (cinematicVerticalNeighborhood_mono_radius _ _ (by
        calc
          5 * (radius : Real) + (radius : Real) =
              6 * (radius : Real) := by ring
          _ <= rho * localDelta := S.normalized_tangency_budget)))
  exact {
    left_mem_quarter := Q.left_mem_quarter
    right_mem_quarter := Q.right_mem_quarter
    rectangle_width := Q.rectangle_width
    common_c := by
      simpa only [D, fineT, y1FineCoarseRectangleData] using
        grid.common_c a ha
    coefficient_lower := by
      simpa only [D, fineT, y1FineCoarseRectangleData] using
        grid.coefficient_lower a ha
    tangent_first := by
      change (D.fineRectangleAt (labelAt a)).carrier localDelta ⊆
        cinematicVerticalNeighborhood
          (actualTubeCinematicTrace f
            (threeShiftCGridNormalizeTube grid.gridLabel
              (fine.tubes (leftIndex a))))
          (D.fineRectangleAt (labelAt a)).rectangle.base
          (rho * localDelta)
      exact hleftTangent
    tangent_second := by
      change (D.fineRectangleAt (labelAt a)).carrier localDelta ⊆
        cinematicVerticalNeighborhood
          (actualTubeCinematicTrace f
            (threeShiftCGridNormalizeTube grid.gridLabel
              (fine.tubes (rightIndex a))))
          (D.fineRectangleAt (labelAt a)).rectangle.base
          (rho * localDelta)
      exact hrightTangent
  }

/-- The two independent finite selections cost exactly a factor nine:
one third for the common shifted C-grid and one third for the trace shift.
The returned tubes are normalized per source tube, so repeated pairs do not
create pair-dependent normalized tube copies. -/
theorem exists_uniform_threeShift_perturbationReady_of_actualRetainedY1ThreeShiftCGrid
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
    (htraceRadius : 2 * (rho * localDelta) <= traceQ * localDelta) :
    let D := y1FineCoarseRectangleData fine Y1 fineLabels pointAt tubeAt
      f f1 f2 hf hf1 (radius : Real)
      (prop41Y1PaperFineT (radius : Real) globalDelta tGlobal)
      globalDelta tGlobal
    exists (grid : ActualRetainedY1ThreeShiftCGridSelection D items
        leftIndex rightIndex labelAt keep pairScale)
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
      items.card <= 3 * grid.selected.card ∧
      fiber.Nonempty ∧
      fiber ⊆ grid.selected ∧
      items.card <= 9 * fiber.card ∧
      forall a, a ∈ fiber ->
        (leftIndex a, labelAt a) ∈ D.retainedGoodPairs keep ∧
        (rightIndex a, labelAt a) ∈ D.retainedGoodPairs keep ∧
        (D.fineRectangleAt (labelAt a)).carrier (radius : Real) ⊆
          (D.coarseRectangleAt (labelAt a)).carrier globalDelta := by
  dsimp only
  let fineT := prop41Y1PaperFineT (radius : Real) globalDelta tGlobal
  let D := y1FineCoarseRectangleData fine Y1 fineLabels pointAt tubeAt
    f f1 f2 hf hf1 (radius : Real) fineT globalDelta tGlobal
  have hgrid :
      Nonempty (ActualRetainedY1ThreeShiftCGridSelection D items
        leftIndex rightIndex labelAt keep pairScale) := by
    simpa only [D, fineT] using
      exists_actualRetainedY1ThreeShiftCGridSelection
        (y1FineCoarseRectangleData fine Y1 fineLabels pointAt tubeAt
          f f1 f2 hf hf1 (radius : Real)
          (prop41Y1PaperFineT (radius : Real) globalDelta tGlobal)
          globalDelta tGlobal)
        items leftIndex rightIndex labelAt keep pairScale selection
        N.fineDelta_pos hitems
  obtain ⟨grid⟩ := hgrid
  let T : alpha -> Tube radius := fun a =>
    threeShiftCGridNormalizeTube grid.gridLabel
      (fine.tubes (leftIndex a))
  let U : alpha -> Tube radius := fun a =>
    threeShiftCGridNormalizeTube grid.gridLabel
      (fine.tubes (rightIndex a))
  let rectangles : alpha -> C2GraphRectangle :=
    fun a => D.fineRectangleAt (labelAt a)
  have hdata : forall a, a ∈ grid.selected ->
      ActualTwoFamilyRectangleTangencyData
        (T a) (U a) f (rectangles a) outerA outerB localDelta
          pairScale rho := by
    intro a ha
    simpa only [T, U, rectangles, D, fineT] using
      retainedY1ThreeShiftCGridSelectedPair_actualTwoFamilyRectangleTangencyData
        fine physical E Y1 fineLabels pointAt centerTube tubeAt f f1 f2
        outerA outerB hOuter hf hf1 tGlobal globalDelta facts pointSource
        hpointE N hparameter hft hf1Lower hf1Upper hf2 hf2Continuous
        items leftIndex rightIndex labelAt keep S selection grid a ha
  obtain ⟨k, eta, fiber, P, heta, hetaMem, hfiber, hfiberGrid, hcard⟩ :=
    exists_uniform_threeShift_perturbationReadyPairLocalActualLensRectangleData
      grid.selected T U rectangles f f1 f2 grid.selected_nonempty
      S.localDelta_pos S.pairScale_pos htraceQ hlambda hrhoLambda
      hshiftDominates hstrengthenedScale htraceRadius N.outerWidth_lower
      (fun z _hz => hf z) (fun z _hz => hf1 z) hparameter hft hf1Lower
      hf1Upper hf2 hf2Continuous hdata
  have hcardNine : items.card <= 9 * fiber.card := by
    calc
      items.card <= 3 * grid.selected.card := grid.grid_cardinal_retention
      _ <= 3 * (3 * fiber.card) := Nat.mul_le_mul_left 3 hcard
      _ = 9 * fiber.card := by ring
  refine ⟨grid, k, eta, fiber, ?_, heta, hetaMem,
    grid.selected_nonempty, grid.selected_subset,
    grid.grid_cardinal_retention, hfiber, hfiberGrid, hcardNine, ?_⟩
  · intro a ha
    simpa only [T, U, rectangles, D, fineT] using P a ha
  · intro a ha
    have haGrid : a ∈ grid.selected := hfiberGrid ha
    have hleft : (leftIndex a, labelAt a) ∈ D.retainedGoodPairs keep := by
      exact grid.left_retained a haGrid
    have hright : (rightIndex a, labelAt a) ∈ D.retainedGoodPairs keep := by
      exact grid.right_retained a haGrid
    have hleftResult :=
      retainedY1Pair_paperFine_tangent_and_fine_subset_coarse
        fine physical E Y1 fineLabels pointAt centerTube tubeAt f f1 f2
        outerA outerB hOuter hf hf1 tGlobal globalDelta facts pointSource
        hpointE N hparameter hft hf1Lower hf1Upper hf2 hf2Continuous keep
        (leftIndex a) (labelAt a) (by
          simpa only [D, fineT] using hleft)
    exact ⟨hleft, hright, by
      simpa only [D, fineT] using hleftResult.2⟩

/-- The exact final maps returned by the grid-plus-trace selection retain the
three pointwise facts needed by the local counting endpoint.  In particular,
the common-C and coefficient conclusions refer to the *translated normalized
left tube* and the normalized right tube, rather than to the pre-trace pair.
The last conclusion records the raw-right-to-grid-right C displacement used by
the local metric-cover argument. -/
theorem actualRetainedY1ThreeShiftCGrid_finalMapFacts
    {point : Type*} [MeasurableSpace point]
    {radius : NNReal} {iota : Type*} [DecidableEq iota]
    {fineLabel : Type*} [DecidableEq fineLabel]
    {alpha : Type*} [DecidableEq alpha]
    (D : CoarseRectangleIncidenceData
      (point := point) (radius := radius) (iota := iota) fineLabel)
    (items : Finset alpha)
    (leftIndex rightIndex : alpha -> iota)
    (labelAt : alpha -> fineLabel)
    (keep : iota -> fineLabel -> Prop)
    (pairScale : Real)
    (grid : ActualRetainedY1ThreeShiftCGridSelection D items
      leftIndex rightIndex labelAt keep pairScale)
    (f : Real -> Real) (outerA outerB localDelta lambda eta : Real)
    (fiber : Finset alpha)
    (P_data : forall a, a ∈ fiber ->
      PerturbationReadyPairLocalActualLensRectangleData
        (traceTranslateTube
          (threeShiftCGridNormalizeTube grid.gridLabel
            (D.fine.tubes (leftIndex a)))
          (eta * (lambda * localDelta)))
        (threeShiftCGridNormalizeTube grid.gridLabel
          (D.fine.tubes (rightIndex a)))
        f (D.fineRectangleAt (labelAt a)) outerA outerB localDelta
          pairScale lambda (2 * lambda))
    (hfiberGrid : fiber ⊆ grid.selected) :
    (forall a, a ∈ fiber ->
      tubeGraphC
          (traceTranslateTube
            (threeShiftCGridNormalizeTube grid.gridLabel
              (D.fine.tubes (leftIndex a)))
            (eta * (lambda * localDelta))) =
        tubeGraphC
          (threeShiftCGridNormalizeTube grid.gridLabel
            (D.fine.tubes (rightIndex a)))) ∧
    (forall a, a ∈ fiber ->
      pairScale < tubePairCoefficientDistance
        (traceTranslateTube
          (threeShiftCGridNormalizeTube grid.gridLabel
            (D.fine.tubes (leftIndex a)))
          (eta * (lambda * localDelta)))
        (threeShiftCGridNormalizeTube grid.gridLabel
          (D.fine.tubes (rightIndex a)))) ∧
    (forall a, a ∈ fiber ->
      |tubeGraphC (D.fine.tubes (rightIndex a)) -
          tubeGraphC
            (threeShiftCGridNormalizeTube grid.gridLabel
              (D.fine.tubes (rightIndex a)))| <= (radius : Real)) := by
  refine ⟨?_, ?_, ?_⟩
  · intro a ha
    exact (P_data a ha).data.common_c
  · intro a ha
    exact (P_data a ha).coefficient_strict
  · intro a ha
    exact grid.right_c_change a (hfiberGrid ha)

#print axioms exists_uniform_threeShift_perturbationReady_of_actualRetainedY1ThreeShiftCGrid
#print axioms retainedY1ThreeShiftCGridSelectedPair_actualTwoFamilyRectangleTangencyData
#print axioms actualRetainedY1ThreeShiftCGrid_finalMapFacts

end

end FamilyStickyCinematicL32Prop41ActualY1RetainedThreeShiftCGridTangencyV1
