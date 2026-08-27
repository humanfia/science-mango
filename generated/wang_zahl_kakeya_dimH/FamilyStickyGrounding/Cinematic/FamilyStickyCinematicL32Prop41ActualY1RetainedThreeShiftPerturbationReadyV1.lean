import FamilyStickyGrounding.Cinematic.FamilyStickyCinematicL32Prop41ActualY1PaperFineTangencyV1
import FamilyStickyGrounding.Cinematic.FamilyStickyCinematicL32Prop41FiniteGeneralPositionExactRootReproductionV1

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 2000000

open Set

namespace FamilyStickyCinematicL32Prop41ActualY1RetainedThreeShiftPerturbationReadyV1

open Submission.Kakeya.ConvexGeometry
open Submission.Kakeya.Uniformity
open FamilyStickyCinematicL32ActualTubeConstantShiftV1
open FamilyStickyCinematicL32ActualProjectedCenteredHalfPointSourceV1
open FamilyStickyCinematicL32ActualProjectedCenteredHalfY1ActiveGeometryV1
open FamilyStickyCinematicL32CenteredFractionIntervalsV1
open FamilyStickyCinematicL32CurvilinearRectangleCarrierV1
open FamilyStickyCinematicL32CurvilinearRectanglePointMultiplicityV1
open FamilyStickyCinematicL32FiniteProjectedShadingMultiplicitySliceV1
open FamilyStickyCinematicL32Prop41ActualChoiceOfShiftPairLocalBridgeV1
open FamilyStickyCinematicL32Prop41ActualY1FineCoarseRectangleProducerV1
open FamilyStickyCinematicL32Prop41ActualY1FineCoarseTangencyBranchV1
open FamilyStickyCinematicL32Prop41ActualY1PaperFineTangencyV1
open FamilyStickyCinematicL32Prop41ActualY1SharpFineScaleTangencyV1
open FamilyStickyCinematicL32Prop41CoarseRectangleIncidenceDataV1
open FamilyStickyCinematicL32Prop41FiniteGeneralPositionExactRootReproductionV1
open FamilyStickyCinematicL32Prop41TangencyProductToScaleV1
open FamilyStickyCinematicL32Prop41ThreeShiftPigeonholeV1
open FamilyStickyCinematicL32RectangleTangencyV1
open FamilyStickyCinematicL32TubeC2GraphRectangleV1
open FamilyStickyCinematicL32TubePairTraceV1
open FamilyStickyWZ2TubeCarrierCoordinateAdapterV1

noncomputable section

universe u v w x

/-!
# Retained actual Y1 pairs feed the perturbation-ready three-shift producer

An item for `choiceOfShift` is a pair of tubes tangent to one rectangle,
whereas a retained `Y1` good pair is one tube--rectangle incidence.  The
structure below records only the genuinely upstream pairing choices: two
retained incidences over the same fine label, exact common `c`, and the
required coefficient separation.  It contains no rectangle-identification
or tangency field.

The theorem at the end derives both literal tangencies from
`retainedY1Pair_paperFine_tangent_and_fine_subset_coarse`, identifies the
source rectangle definitionally with the actual paper fine rectangle, and
feeds the strengthened uniform three-shift producer.  Its output is already
`PerturbationReadyPairLocalActualLensRectangleData`.
-/

/-- Pair-selection data over retained good incidences.  In particular,
neither tangency nor fine/coarse rectangle containment is an input. -/
structure ActualRetainedY1PairSelection
    {point : Type u} [MeasurableSpace point]
    {radius : NNReal} {iota : Type v} [DecidableEq iota]
    {fineLabel : Type w} [DecidableEq fineLabel]
    {alpha : Type x}
    (D : CoarseRectangleIncidenceData
      (point := point) (radius := radius) (iota := iota) fineLabel)
    (items : Finset alpha)
    (leftIndex rightIndex : alpha -> iota)
    (labelAt : alpha -> fineLabel)
    (keep : iota -> fineLabel -> Prop) (pairScale : Real) : Prop where
  left_retained : forall a, a ∈ items ->
    (leftIndex a, labelAt a) ∈ D.retainedGoodPairs keep
  right_retained : forall a, a ∈ items ->
    (rightIndex a, labelAt a) ∈ D.retainedGoodPairs keep
  common_c : forall a, a ∈ items ->
    tubeGraphC (D.fine.tubes (leftIndex a)) =
      tubeGraphC (D.fine.tubes (rightIndex a))
  coefficient_lower : forall a, a ∈ items ->
    2 * pairScale <= tubePairCoefficientDistance
      (D.fine.tubes (leftIndex a)) (D.fine.tubes (rightIndex a))

/-- The single scalar adapter between the literal paper fine rectangle and
the `(delta,t,rho)` notation of the three-shift producer.  This is kept as
one named record so that no scale bookkeeping is scattered among geometric
hypotheses. -/
structure ActualY1PaperFineChoiceScaleNumerics
    (fineDelta globalDelta tGlobal localDelta pairScale rho : Real) : Prop where
  localDelta_pos : 0 < localDelta
  pairScale_pos : 0 < pairScale
  localDelta_le_fineDelta : localDelta <= fineDelta
  retained_tangency_budget : 5 * fineDelta <= rho * localDelta
  rectangle_ratio :
    localDelta / pairScale <=
      fineDelta / prop41Y1PaperFineT fineDelta globalDelta tGlobal

/-- Monotonicity of a fixed literal `C2GraphRectangle` in its carrier
thickness. -/
theorem c2GraphRectangle_carrier_mono_radius
    (R : C2GraphRectangle) {delta Delta : Real} (h : delta <= Delta) :
    R.carrier delta ⊆ R.carrier Delta := by
  rintro p ⟨hpBase, hpVertical⟩
  exact ⟨hpBase, hpVertical.trans h⟩

/-- Two actual retained `Y1` incidences over the same paper fine rectangle
produce the complete tangency record consumed by `choiceOfShift`.

The canonical-quarter endpoint placement and rectangle width are derived
from the paper fine scale.  Both tube tangencies and fine-to-coarse
containment are theorems, not fields of `selection`. -/
theorem retainedY1SelectedPair_actualTwoFamilyRectangleTangencyData
    {radius : NNReal} {iota : Type u} [DecidableEq iota]
    {fineLabel : Type v} [DecidableEq fineLabel]
    {alpha : Type w}
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
    (S : ActualY1PaperFineChoiceScaleNumerics
      (radius : Real) globalDelta tGlobal localDelta pairScale rho)
    (selection : ActualRetainedY1PairSelection
      (y1FineCoarseRectangleData fine Y1 fineLabels pointAt tubeAt
        f f1 f2 hf hf1 (radius : Real)
        (prop41Y1PaperFineT (radius : Real) globalDelta tGlobal)
        globalDelta tGlobal)
      items leftIndex rightIndex labelAt keep pairScale)
    (a : alpha) (ha : a ∈ items) :
    let D := y1FineCoarseRectangleData fine Y1 fineLabels pointAt tubeAt
      f f1 f2 hf hf1 (radius : Real)
      (prop41Y1PaperFineT (radius : Real) globalDelta tGlobal)
      globalDelta tGlobal
    ActualTwoFamilyRectangleTangencyData
      (fine.tubes (leftIndex a)) (fine.tubes (rightIndex a)) f
      (D.fineRectangleAt (labelAt a)) outerA outerB localDelta pairScale rho := by
  dsimp only
  let fineT := prop41Y1PaperFineT (radius : Real) globalDelta tGlobal
  let D := y1FineCoarseRectangleData fine Y1 fineLabels pointAt tubeAt
    f f1 f2 hf hf1 (radius : Real) fineT globalDelta tGlobal
  have hleftRetained : (leftIndex a, labelAt a) ∈
      D.retainedGoodPairs keep := by
    simpa only [D, fineT] using selection.left_retained a ha
  have hrightRetained : (rightIndex a, labelAt a) ∈
      D.retainedGoodPairs keep := by
    simpa only [D, fineT] using selection.right_retained a ha
  have hretainedActive := y1FineCoarseRectangleData_retainedPair_active
    fine Y1 fineLabels pointAt tubeAt f f1 f2 hf hf1 (radius : Real)
      fineT globalDelta tGlobal keep (leftIndex a) (labelAt a) hleftRetained
  have hlabel : labelAt a ∈ fineLabels := hretainedActive.1
  have htheta := pointSource.hpointTheta
    (pointAt (labelAt a)) (hpointE (labelAt a) hlabel)
  have hmargins := mem_sixteenth_has_quarter_margin htheta
  have hhalfWidth :
      Real.sqrt ((radius : Real) / fineT) / 2 <=
        3 * (outerB - outerA) / 32 := by
    simpa only [fineT, actualY1FineHalfWidth] using
      prop41Y1PaperFine_canonicalMargin N
  have hhalfWidthNonneg :
      0 <= Real.sqrt ((radius : Real) / fineT) / 2 :=
    div_nonneg (Real.sqrt_nonneg _) (by norm_num)
  have hendpoints :
      (D.fineRectangleAt (labelAt a)).rectangle.left ∈
          centeredFractionIcc outerA outerB (1 / 4 : Real) ∧
        (D.fineRectangleAt (labelAt a)).rectangle.right ∈
          centeredFractionIcc outerA outerB (1 / 4 : Real) := by
    change
      (pointAt (labelAt a)).2 -
            Real.sqrt ((radius : Real) / fineT) / 2 ∈
          centeredFractionIcc outerA outerB (1 / 4 : Real) ∧
        (pointAt (labelAt a)).2 +
            Real.sqrt ((radius : Real) / fineT) / 2 ∈
          centeredFractionIcc outerA outerB (1 / 4 : Real)
    constructor <;> constructor <;>
      linarith [hmargins.1, hmargins.2]
  have hrectangleWidth :
      Real.sqrt (localDelta / pairScale) <=
        (D.fineRectangleAt (labelAt a)).rectangle.right -
          (D.fineRectangleAt (labelAt a)).rectangle.left := by
    calc
      Real.sqrt (localDelta / pairScale) <=
          Real.sqrt ((radius : Real) / fineT) :=
        Real.sqrt_le_sqrt S.rectangle_ratio
      _ = (D.fineRectangleAt (labelAt a)).rectangle.right -
          (D.fineRectangleAt (labelAt a)).rectangle.left := by
        symm
        simpa only [D, y1FineCoarseRectangleData] using
          centeredTubeC2GraphRectangle_length
            (tubeAt (pointAt (labelAt a))) f f1 f2 hf hf1
            (pointAt (labelAt a)).2 (radius : Real) fineT
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
  have hcarrierMono : (D.fineRectangleAt (labelAt a)).carrier localDelta ⊆
      (D.fineRectangleAt (labelAt a)).carrier (radius : Real) :=
    c2GraphRectangle_carrier_mono_radius _ S.localDelta_le_fineDelta
  have hleftFine :
      (D.fineRectangleAt (labelAt a)).carrier (radius : Real) ⊆
        cinematicVerticalNeighborhood
          (cinematicTraceValue f
            (tubeGraphA (fine.tubes (leftIndex a)))
            (tubeGraphB (fine.tubes (leftIndex a)))
            (tubeGraphC (fine.tubes (leftIndex a)))
            (tubeGraphD (fine.tubes (leftIndex a))))
          (D.fineRectangleAt (labelAt a)).rectangle.base
          (5 * (radius : Real)) := by
    simpa only [D, fineT] using hleftResult.1
  have hrightFine :
      (D.fineRectangleAt (labelAt a)).carrier (radius : Real) ⊆
        cinematicVerticalNeighborhood
          (cinematicTraceValue f
            (tubeGraphA (fine.tubes (rightIndex a)))
            (tubeGraphB (fine.tubes (rightIndex a)))
            (tubeGraphC (fine.tubes (rightIndex a)))
            (tubeGraphD (fine.tubes (rightIndex a))))
          (D.fineRectangleAt (labelAt a)).rectangle.base
          (5 * (radius : Real)) := by
    simpa only [D, fineT] using hrightResult.1
  have hleftTangent : (D.fineRectangleAt (labelAt a)).carrier localDelta ⊆
      cinematicVerticalNeighborhood
        (cinematicTraceValue f
          (tubeGraphA (fine.tubes (leftIndex a)))
          (tubeGraphB (fine.tubes (leftIndex a)))
          (tubeGraphC (fine.tubes (leftIndex a)))
          (tubeGraphD (fine.tubes (leftIndex a))))
        (D.fineRectangleAt (labelAt a)).rectangle.base
        (rho * localDelta) := by
    exact hcarrierMono.trans (hleftFine.trans
      (cinematicVerticalNeighborhood_mono_radius _ _
        S.retained_tangency_budget))
  have hrightTangent : (D.fineRectangleAt (labelAt a)).carrier localDelta ⊆
      cinematicVerticalNeighborhood
        (cinematicTraceValue f
          (tubeGraphA (fine.tubes (rightIndex a)))
          (tubeGraphB (fine.tubes (rightIndex a)))
          (tubeGraphC (fine.tubes (rightIndex a)))
          (tubeGraphD (fine.tubes (rightIndex a))))
        (D.fineRectangleAt (labelAt a)).rectangle.base
        (rho * localDelta) := by
    exact hcarrierMono.trans (hrightFine.trans
      (cinematicVerticalNeighborhood_mono_radius _ _
        S.retained_tangency_budget))
  exact {
    left_mem_quarter := hendpoints.1
    right_mem_quarter := hendpoints.2
    rectangle_width := hrectangleWidth
    common_c := by
      simpa only [D, fineT, y1FineCoarseRectangleData] using
        selection.common_c a ha
    coefficient_lower := by
      simpa only [D, fineT, y1FineCoarseRectangleData] using
        selection.coefficient_lower a ha
    tangent_first := hleftTangent
    tangent_second := hrightTangent
  }

/-- Final zero-tangency-assumption connector from actual retained good pairs
to the strengthened uniform three-shift perturbation-ready producer.

The final conjunct retains, on the selected fiber, the two honest retained
incidences and the actual fine-to-coarse carrier inclusion.  The source
rectangle appearing in every `PerturbationReadyPairLocalActualLensRectangleData`
is definitionally `D.fineRectangleAt (labelAt a)`. -/
theorem exists_uniform_threeShift_perturbationReady_of_actualRetainedY1Pairs
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
    (S : ActualY1PaperFineChoiceScaleNumerics
      (radius : Real) globalDelta tGlobal localDelta pairScale rho)
    (selection : ActualRetainedY1PairSelection
      (y1FineCoarseRectangleData fine Y1 fineLabels pointAt tubeAt
        f f1 f2 hf hf1 (radius : Real)
        (prop41Y1PaperFineT (radius : Real) globalDelta tGlobal)
        globalDelta tGlobal)
      items leftIndex rightIndex labelAt keep pairScale)
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
    exists (k : Fin 3) (eta : Real) (fiber : Finset alpha)
      (_P : forall a, a ∈ fiber ->
        PerturbationReadyPairLocalActualLensRectangleData
          (traceTranslateTube (fine.tubes (leftIndex a))
            (eta * (lambda * localDelta)))
          (fine.tubes (rightIndex a)) f
          (D.fineRectangleAt (labelAt a)) outerA outerB localDelta
          pairScale lambda (2 * lambda)),
      eta = threeShiftValue k ∧
      eta ∈ ({(-1 : Real), 0, 1} : Set Real) ∧
      fiber.Nonempty ∧
      fiber ⊆ items ∧
      items.card <= 3 * fiber.card ∧
      forall a, a ∈ fiber ->
        (leftIndex a, labelAt a) ∈ D.retainedGoodPairs keep ∧
        (rightIndex a, labelAt a) ∈ D.retainedGoodPairs keep ∧
        (D.fineRectangleAt (labelAt a)).carrier (radius : Real) ⊆
          (D.coarseRectangleAt (labelAt a)).carrier globalDelta := by
  dsimp only
  let fineT := prop41Y1PaperFineT (radius : Real) globalDelta tGlobal
  let D := y1FineCoarseRectangleData fine Y1 fineLabels pointAt tubeAt
    f f1 f2 hf hf1 (radius : Real) fineT globalDelta tGlobal
  let T : alpha -> Tube radius := fun a => fine.tubes (leftIndex a)
  let U : alpha -> Tube radius := fun a => fine.tubes (rightIndex a)
  let rectangles : alpha -> C2GraphRectangle :=
    fun a => D.fineRectangleAt (labelAt a)
  have hdata : forall a, a ∈ items ->
      ActualTwoFamilyRectangleTangencyData
        (T a) (U a) f (rectangles a) outerA outerB localDelta
          pairScale rho := by
    intro a ha
    simpa only [T, U, rectangles, D, fineT] using
      retainedY1SelectedPair_actualTwoFamilyRectangleTangencyData
        fine physical E Y1 fineLabels pointAt centerTube tubeAt f f1 f2
        outerA outerB hOuter hf hf1 tGlobal globalDelta facts pointSource
        hpointE N hparameter hft hf1Lower hf1Upper hf2 hf2Continuous
        items leftIndex rightIndex labelAt keep S selection a ha
  obtain ⟨k, eta, fiber, P, heta, hetaMem, hfiber, hfiberItems, hcard⟩ :=
    exists_uniform_threeShift_perturbationReadyPairLocalActualLensRectangleData
      items T U rectangles f f1 f2 hitems S.localDelta_pos
      S.pairScale_pos htraceQ hlambda hrhoLambda hshiftDominates
      hstrengthenedScale htraceRadius N.outerWidth_lower
      (fun z _hz => hf z) (fun z _hz => hf1 z) hparameter hft hf1Lower
      hf1Upper hf2 hf2Continuous hdata
  refine ⟨k, eta, fiber, ?_, heta, hetaMem, hfiber, hfiberItems, hcard, ?_⟩
  · intro a ha
    simpa only [T, U, rectangles, D, fineT] using P a ha
  · intro a ha
    have haItems : a ∈ items := hfiberItems ha
    have hleft : (leftIndex a, labelAt a) ∈ D.retainedGoodPairs keep := by
      simpa only [D, fineT] using selection.left_retained a haItems
    have hright : (rightIndex a, labelAt a) ∈ D.retainedGoodPairs keep := by
      simpa only [D, fineT] using selection.right_retained a haItems
    have hleftResult :=
      retainedY1Pair_paperFine_tangent_and_fine_subset_coarse
        fine physical E Y1 fineLabels pointAt centerTube tubeAt f f1 f2
        outerA outerB hOuter hf hf1 tGlobal globalDelta facts pointSource
        hpointE N hparameter hft hf1Lower hf1Upper hf2 hf2Continuous keep
        (leftIndex a) (labelAt a) (by
          simpa only [D, fineT] using hleft)
    exact ⟨hleft, hright, by
      simpa only [D, fineT] using hleftResult.2⟩

#print axioms c2GraphRectangle_carrier_mono_radius
#print axioms retainedY1SelectedPair_actualTwoFamilyRectangleTangencyData
#print axioms exists_uniform_threeShift_perturbationReady_of_actualRetainedY1Pairs

end

end FamilyStickyCinematicL32Prop41ActualY1RetainedThreeShiftPerturbationReadyV1
