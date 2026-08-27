import FamilyStickyGrounding.Cinematic.FamilyStickyCinematicL32Prop41ActualY1RetainedThreeShiftCGridTangencyV1
import FamilyStickyGrounding.Cinematic.FamilyStickyCinematicL32Prop41ActualY1RetainedThreeShiftCGridRestrictedCanonicalFibresV1

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 4000000

open Set

namespace FamilyStickyCinematicL32Prop41ActualY1SamplingPaperFineGPrimeLabelFirstThreeShiftCGridUniformPackageV1

open Submission.Kakeya.ConvexGeometry
open Submission.Kakeya.Uniformity
open FamilyStickyCinematicL32ActualProjectedCenteredHalfPointSourceV1
open FamilyStickyCinematicL32ActualProjectedCenteredHalfY1ActiveGeometryV1
open FamilyStickyCinematicL32ActualTubeCoefficientDistancesV1
open FamilyStickyCinematicL32ActualTubeConstantShiftV1
open FamilyStickyCinematicL32FiniteMetricMaximalCoverV1
open FamilyStickyCinematicL32FiniteProjectedShadingMultiplicitySliceV1
open FamilyStickyCinematicL32Prop41ActualGlobalNormCoarseFiberV1
open FamilyStickyCinematicL32Prop41ActualGlobalNormCoarseFiberRandomSamplingV1
open FamilyStickyCinematicL32Prop41ActualY1FineCoarseRectangleProducerV1
open FamilyStickyCinematicL32Prop41ActualY1PaperFineCNormalizedThreeShiftScaleProducerV1
open FamilyStickyCinematicL32Prop41ActualY1RetainedThreeShiftCGridCanonicalFibresV1
open FamilyStickyCinematicL32Prop41ActualY1RetainedThreeShiftCGridSelectionV1
open FamilyStickyCinematicL32Prop41ActualY1RetainedThreeShiftCGridTangencyV1
open FamilyStickyCinematicL32Prop41ActualY1RetainedThreeShiftCGridRestrictedCanonicalFibresV1
open FamilyStickyCinematicL32Prop41ActualY1SamplingPaperFineGPrimeLabelFirstApproxCSelectionV1
open FamilyStickyCinematicL32Prop41ActualY1SamplingPaperFineGPrimeLabelFirstProvenanceV1
open FamilyStickyCinematicL32Prop41ActualY1SharpFineScaleTangencyV1
open FamilyStickyCinematicL32Prop41CanonicalMaximizerNonconcentrationV1
open FamilyStickyCinematicL32Prop41CoarseRectangleIncidenceDataV1
open FamilyStickyCinematicL32Prop41FiniteGeneralPositionExactRootReproductionV1
open FamilyStickyCinematicL32Prop41FiniteRandomSamplingExtractionV1
open FamilyStickyCinematicL32Prop41SeparatedCoefficientBallPairV1
open FamilyStickyCinematicL32Prop41ThreeShiftPigeonholeV1
open FamilyStickyCinematicL32ThreeShiftCGridTubeNormalizationV1
open FamilyStickyCinematicL32TubePairTraceV1
open FamilyStickyWZ2TubeCarrierCoordinateAdapterV1

noncomputable section

universe u v

/-!
# Actual label-first G-prime package after tube-local shifted C normalization

The first finite selection chooses a shifted C grid on which both tubes in
each retained pair land in one common cell.  The second selection chooses one
global trace translation of the left endpoints.  The resulting endpoint maps
are tube-local:
`T a = traceTranslateTube (gridNormalize left a) shift` and
`U a = gridNormalize right a`.

The two selections cost a factor nine.  Combined with the unchanged
label-first sampling survival factor eight, this is the source of the honest
constant 72 in the selected-mass chain.
-/

def actualGPrimeLabelFirstThreeShiftCGridLeftTube
    {radius : NNReal} {iota : Type u} [DecidableEq iota]
    {fineLabel : Type v} [DecidableEq fineLabel]
    (N : CanonicalNormNonconcentrationData iota)
    (D : CoarseRectangleIncidenceData (point := Real × Real)
      (radius := radius) (iota := iota) fineLabel)
    (keep : iota -> fineLabel -> Prop) (left right : iota)
    (ballRadius : Real)
    (omega : (N.family -> Fin 1) × (N.family -> Fin 1))
    (gridLabel : Fin 3) (eta globalDelta tGlobal : Real)
    (a : ActualGPrimeLabelFirstSurvivor
      N D keep left right ballRadius omega) : Tube radius :=
  traceTranslateTube
    (threeShiftCGridNormalizeTube gridLabel
      (D.fine.tubes (actualGPrimeLabelFirstLeftIndex
        N D keep left right ballRadius omega a)))
    (eta *
      (actualY1PaperFineCNormalizedChoiceLambda
          (radius : Real) globalDelta tGlobal (4 * ballRadius) *
        actualY1PaperFineCNormalizedChoiceLocalDelta
          (radius : Real) globalDelta tGlobal (4 * ballRadius)))

def actualGPrimeLabelFirstThreeShiftCGridRightTube
    {radius : NNReal} {iota : Type u} [DecidableEq iota]
    {fineLabel : Type v} [DecidableEq fineLabel]
    (N : CanonicalNormNonconcentrationData iota)
    (D : CoarseRectangleIncidenceData (point := Real × Real)
      (radius := radius) (iota := iota) fineLabel)
    (keep : iota -> fineLabel -> Prop) (left right : iota)
    (ballRadius : Real)
    (omega : (N.family -> Fin 1) × (N.family -> Fin 1))
    (gridLabel : Fin 3)
    (a : ActualGPrimeLabelFirstSurvivor
      N D keep left right ballRadius omega) : Tube radius :=
  threeShiftCGridNormalizeTube gridLabel
    (D.fine.tubes (actualGPrimeLabelFirstRightIndex
      N D keep left right ballRadius omega a))

structure ActualGPrimeLabelFirstThreeShiftCGridPaperFineUniformPackage
    {radius : NNReal} {iota : Type u} [DecidableEq iota]
    {fineLabel : Type v} [DecidableEq fineLabel]
    (fine : UniformTubeFamily radius iota)
    (N : CanonicalNormNonconcentrationData iota)
    (D : CoarseRectangleIncidenceData (point := Real × Real)
      (radius := radius) (iota := iota) fineLabel)
    (keep : iota -> fineLabel -> Prop) (left right : iota)
    (ballRadius : Real)
    (omega : (N.family -> Fin 1) × (N.family -> Fin 1))
    (f : Real -> Real) (outerA outerB globalDelta tGlobal : Real) where
  gridSelection : ActualRetainedY1ThreeShiftCGridSelection D
    (Finset.univ : Finset (ActualGPrimeLabelFirstSurvivor
      N D keep left right ballRadius omega))
    (actualGPrimeLabelFirstLeftIndex
      N D keep left right ballRadius omega)
    (actualGPrimeLabelFirstRightIndex
      N D keep left right ballRadius omega)
    (actualGPrimeLabelFirstLabel
      N D keep left right ballRadius omega)
    keep (4 * ballRadius)
  gridLabel : Fin 3
  gridLabel_eq : gridLabel = gridSelection.gridLabel
  shiftLabel : Fin 3
  eta : Real
  selected : Finset (ActualGPrimeLabelFirstSurvivor
    N D keep left right ballRadius omega)
  data : forall a, a ∈ selected ->
    PerturbationReadyPairLocalActualLensRectangleData
      (actualGPrimeLabelFirstThreeShiftCGridLeftTube N D keep left right
        ballRadius omega gridLabel eta globalDelta tGlobal a)
      (actualGPrimeLabelFirstThreeShiftCGridRightTube N D keep left right
        ballRadius omega gridLabel a)
      f (D.fineRectangleAt (actualGPrimeLabelFirstLabel
        N D keep left right ballRadius omega a)) outerA outerB
      (actualY1PaperFineCNormalizedChoiceLocalDelta
        (radius : Real) globalDelta tGlobal (4 * ballRadius))
      (4 * ballRadius)
      (actualY1PaperFineCNormalizedChoiceLambda
        (radius : Real) globalDelta tGlobal (4 * ballRadius))
      (2 * actualY1PaperFineCNormalizedChoiceLambda
        (radius : Real) globalDelta tGlobal (4 * ballRadius))
  eta_eq : eta = threeShiftValue shiftLabel
  eta_mem : eta ∈ ({(-1 : Real), 0, 1} : Set Real)
  grid_selected_nonempty : gridSelection.selected.Nonempty
  grid_selected_subset :
    gridSelection.selected ⊆
      (Finset.univ : Finset (ActualGPrimeLabelFirstSurvivor
        N D keep left right ballRadius omega))
  grid_cardinal_retention :
    (Finset.univ : Finset (ActualGPrimeLabelFirstSurvivor
      N D keep left right ballRadius omega)).card <=
      3 * gridSelection.selected.card
  selected_nonempty : selected.Nonempty
  selected_subset_grid : selected ⊆ gridSelection.selected
  selected_subset :
    selected ⊆
      (Finset.univ : Finset (ActualGPrimeLabelFirstSurvivor
        N D keep left right ballRadius omega))
  nineShift_cardinal_retention :
    (Finset.univ : Finset (ActualGPrimeLabelFirstSurvivor
      N D keep left right ballRadius omega)).card <= 9 * selected.card
  final_common_c : forall a, a ∈ selected ->
    tubeGraphC
        (actualGPrimeLabelFirstThreeShiftCGridLeftTube N D keep left right
          ballRadius omega gridLabel eta globalDelta tGlobal a) =
      tubeGraphC
        (actualGPrimeLabelFirstThreeShiftCGridRightTube N D keep left right
          ballRadius omega gridLabel a)
  final_coefficient_strict : forall a, a ∈ selected ->
    4 * ballRadius < tubePairCoefficientDistance
      (actualGPrimeLabelFirstThreeShiftCGridLeftTube N D keep left right
        ballRadius omega gridLabel eta globalDelta tGlobal a)
      (actualGPrimeLabelFirstThreeShiftCGridRightTube N D keep left right
        ballRadius omega gridLabel a)
  raw_right_c_gap : forall a, a ∈ selected ->
    |tubeGraphC
        (D.fine.tubes (actualGPrimeLabelFirstRightIndex
          N D keep left right ballRadius omega a)) -
      tubeGraphC
        (actualGPrimeLabelFirstThreeShiftCGridRightTube N D keep left right
          ballRadius omega gridLabel a)| <= (radius : Real)
  label_survival :
    ((actualGPrimeBilateralRetainedFineLabels
      N D keep left right ballRadius).card : Real) / 8 <=
      ((twoSidedZeroColorSurvivors 1 1
        (fun r : actualGPrimeBilateralRetainedFineLabels
            N D keep left right ballRadius =>
          actualGPrimeRetainedFineMetricNeighbors
            N D keep left ballRadius r.1)
        (fun r : actualGPrimeBilateralRetainedFineLabels
            N D keep left right ballRadius =>
          actualGPrimeRetainedFineMetricNeighbors
            N D keep right ballRadius r.1)
        omega).card : Real)
  sample_load : twoSidedZeroColorLoad 1 1 omega <=
    7 * ((N.family.card : Real) / (1 : Real) +
      (N.family.card : Real) / (1 : Real))
  retained_tube_card_le_load :
    ((survivorRetainedPairTubeFamily 1 1
      (fun r : actualGPrimeBilateralRetainedFineLabels
          N D keep left right ballRadius =>
        actualGPrimeRetainedFineMetricNeighbors
          N D keep left ballRadius r.1)
      (fun r : actualGPrimeBilateralRetainedFineLabels
          N D keep left right ballRadius =>
        actualGPrimeRetainedFineMetricNeighbors
          N D keep right ballRadius r.1)
      omega (fun i : N.family => D.fine.tubes i.1)
        (fun i : N.family => D.fine.tubes i.1)).card : Real) <=
      twoSidedZeroColorLoad 1 1 omega
  left_retained : forall a, a ∈ selected ->
    (actualGPrimeLabelFirstLeftIndex
        N D keep left right ballRadius omega a,
      actualGPrimeLabelFirstLabel
        N D keep left right ballRadius omega a) ∈ D.retainedGoodPairs keep
  right_retained : forall a, a ∈ selected ->
    (actualGPrimeLabelFirstRightIndex
        N D keep left right ballRadius omega a,
      actualGPrimeLabelFirstLabel
        N D keep left right ballRadius omega a) ∈ D.retainedGoodPairs keep
  fine_subset_coarse : forall a, a ∈ selected ->
    (D.fineRectangleAt (actualGPrimeLabelFirstLabel
      N D keep left right ballRadius omega a)).carrier (radius : Real) ⊆
      (D.coarseRectangleAt (actualGPrimeLabelFirstLabel
        N D keep left right ballRadius omega a)).carrier globalDelta

/-- The package's final left endpoint is definitionally the left endpoint used
by the restricted canonical C-fibre partition, at the package's fixed trace
shift. -/
theorem ActualGPrimeLabelFirstThreeShiftCGridPaperFineUniformPackage.leftTube_eq_restricted
    {radius : NNReal} {iota : Type u} [DecidableEq iota]
    {fineLabel : Type v} [DecidableEq fineLabel]
    (fine : UniformTubeFamily radius iota)
    (N : CanonicalNormNonconcentrationData iota)
    (D : CoarseRectangleIncidenceData (point := Real × Real)
      (radius := radius) (iota := iota) fineLabel)
    (keep : iota -> fineLabel -> Prop) (left right : iota)
    (ballRadius : Real)
    (omega : (N.family -> Fin 1) × (N.family -> Fin 1))
    (f : Real -> Real) (outerA outerB globalDelta tGlobal : Real)
    (P : ActualGPrimeLabelFirstThreeShiftCGridPaperFineUniformPackage fine N D
      keep left right ballRadius omega f outerA outerB globalDelta tGlobal)
    (a : ActualGPrimeLabelFirstSurvivor
      N D keep left right ballRadius omega) :
    actualGPrimeLabelFirstThreeShiftCGridLeftTube N D keep left right
        ballRadius omega P.gridLabel P.eta globalDelta tGlobal a =
      actualThreeShiftCGridRestrictedTraceLeftTube P.gridSelection
        (P.eta *
          (actualY1PaperFineCNormalizedChoiceLambda
              (radius : Real) globalDelta tGlobal (4 * ballRadius) *
            actualY1PaperFineCNormalizedChoiceLocalDelta
              (radius : Real) globalDelta tGlobal (4 * ballRadius))) a := by
  simp only [actualGPrimeLabelFirstThreeShiftCGridLeftTube,
    actualThreeShiftCGridRestrictedTraceLeftTube,
    actualThreeShiftCGridLeftTube, P.gridLabel_eq]

/-- The package's final right endpoint is definitionally the right endpoint
used by the restricted canonical C-fibre partition. -/
theorem ActualGPrimeLabelFirstThreeShiftCGridPaperFineUniformPackage.rightTube_eq_restricted
    {radius : NNReal} {iota : Type u} [DecidableEq iota]
    {fineLabel : Type v} [DecidableEq fineLabel]
    (fine : UniformTubeFamily radius iota)
    (N : CanonicalNormNonconcentrationData iota)
    (D : CoarseRectangleIncidenceData (point := Real × Real)
      (radius := radius) (iota := iota) fineLabel)
    (keep : iota -> fineLabel -> Prop) (left right : iota)
    (ballRadius : Real)
    (omega : (N.family -> Fin 1) × (N.family -> Fin 1))
    (f : Real -> Real) (outerA outerB globalDelta tGlobal : Real)
    (P : ActualGPrimeLabelFirstThreeShiftCGridPaperFineUniformPackage fine N D
      keep left right ballRadius omega f outerA outerB globalDelta tGlobal)
    (a : ActualGPrimeLabelFirstSurvivor
      N D keep left right ballRadius omega) :
    actualGPrimeLabelFirstThreeShiftCGridRightTube N D keep left right
        ballRadius omega P.gridLabel a =
      actualThreeShiftCGridRestrictedRightTube P.gridSelection a := by
  simp only [actualGPrimeLabelFirstThreeShiftCGridRightTube,
    actualThreeShiftCGridRestrictedRightTube,
    actualThreeShiftCGridRightTube, P.gridLabel_eq]

theorem exists_actualGPrimeLabelFirstThreeShiftCGridPaperFineUniformPackage
    {radius : NNReal} {iota : Type u} [DecidableEq iota]
    {fineLabel : Type v} [DecidableEq fineLabel]
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
    (sharp : ActualY1SharpFineScaleNumerics
      (radius : Real) globalDelta tGlobal (outerB - outerA))
    (hparameter : forall z, z ∈ Icc outerA outerB -> |z| <= 1)
    (hft : forall z, z ∈ Icc outerA outerB -> |f z| <= 2)
    (hf1Lower : forall z, z ∈ Icc outerA outerB -> 1 <= |f1 z|)
    (hf1Upper : forall z, z ∈ Icc outerA outerB -> |f1 z| <= 2)
    (hf2 : forall z, z ∈ Icc outerA outerB -> |f2 z| <= 1 / 100)
    (hf2Continuous : ContinuousOn f2 (Icc outerA outerB))
    (N : CanonicalNormNonconcentrationData iota)
    (D : CoarseRectangleIncidenceData (point := Real × Real)
      (radius := radius) (iota := iota) fineLabel)
    (hD : D = y1FineCoarseRectangleData fine Y1 fineLabels pointAt tubeAt
      f f1 f2 hf hf1 (radius : Real)
      (prop41Y1PaperFineT (radius : Real) globalDelta tGlobal)
      globalDelta tGlobal)
    (keep : iota -> fineLabel -> Prop) (left right : iota)
    (ballRadius : Real)
    (hdistance : forall i j, N.distance i j =
      projectedTubePairCoefficientDistance
        (D.fine.tubes i) (D.fine.tubes j))
    (hcross : FiniteFamiliesCrossSeparated N.distance (8 * ballRadius)
      (finiteFamilyMetricBall N.family N.distance ballRadius left)
      (finiteFamilyMetricBall N.family N.distance ballRadius right))
    (omega : (N.family -> Fin 1) × (N.family -> Fin 1))
    (O : ActualGPrimeLabelFirstSampledOutcome
      N D keep left right ballRadius omega)
    (hlabels : (actualGPrimeBilateralRetainedFineLabels
      N D keep left right ballRadius).Nonempty)
    (hsmall : ActualY1PaperFineCNormalizedThreeShiftPairScaleSmallness
      (radius : Real) globalDelta tGlobal (4 * ballRadius)) :
    Nonempty (ActualGPrimeLabelFirstThreeShiftCGridPaperFineUniformPackage
      fine N D keep left right ballRadius omega f outerA outerB
        globalDelta tGlobal) := by
  subst D
  let D := y1FineCoarseRectangleData fine Y1 fineLabels pointAt tubeAt
    f f1 f2 hf hf1 (radius : Real)
    (prop41Y1PaperFineT (radius : Real) globalDelta tGlobal)
    globalDelta tGlobal
  let items : Finset (ActualGPrimeLabelFirstSurvivor
      N D keep left right ballRadius omega) := Finset.univ
  have selection : ActualRetainedY1ApproxCPairSelection D items
      (actualGPrimeLabelFirstLeftIndex
        N D keep left right ballRadius omega)
      (actualGPrimeLabelFirstRightIndex
        N D keep left right ballRadius omega)
      (actualGPrimeLabelFirstLabel
        N D keep left right ballRadius omega)
      keep (4 * ballRadius) (radius : Real) := by
    exact actualGPrimeLabelFirst_actualRetainedY1ApproxCPairSelection
      fine physical E Y1 fineLabels pointAt tubeAt f f1 f2 outerA outerB
      hOuter hf hf1 tGlobal globalDelta facts hpointE
      (radius : Real)
      (prop41Y1PaperFineT (radius : Real) globalDelta tGlobal)
      globalDelta tGlobal N D (by rfl) keep left right ballRadius
      hdistance hcross omega
  have hitems : items.Nonempty := by
    exact O.survivors_nonempty N D keep left right ballRadius omega hlabels
  let scales :=
    actualY1PaperFineCNormalizedAutomaticThreeShiftNumerics_of_pairScaleSmall
      sharp hsmall
  obtain ⟨grid, k, eta, fiber, P, heta, hetaMem, hgridNonempty,
      hgridSubset, hgridCard, hfiber, hfiberGrid, hcardNine, hactual⟩ :=
    exists_uniform_threeShift_perturbationReady_of_actualRetainedY1ThreeShiftCGrid
      fine physical E Y1 fineLabels pointAt centerTube tubeAt f f1 f2
      outerA outerB hOuter hf hf1 tGlobal globalDelta facts pointSource
      hpointE sharp hparameter hft hf1Lower hf1Upper hf2 hf2Continuous
      items
      (actualGPrimeLabelFirstLeftIndex
        N D keep left right ballRadius omega)
      (actualGPrimeLabelFirstRightIndex
        N D keep left right ballRadius omega)
      (actualGPrimeLabelFirstLabel
        N D keep left right ballRadius omega)
      keep scales.choice_scale selection hitems scales.traceQ_one
      scales.lambda_pos scales.rho_le_lambda scales.shift_dominates
      scales.strengthened_scale scales.trace_radius
  have hmaps :=
    actualRetainedY1ThreeShiftCGrid_finalMapFacts D items
      (actualGPrimeLabelFirstLeftIndex
        N D keep left right ballRadius omega)
      (actualGPrimeLabelFirstRightIndex
        N D keep left right ballRadius omega)
      (actualGPrimeLabelFirstLabel
        N D keep left right ballRadius omega)
      keep (4 * ballRadius) grid f outerA outerB
      (actualY1PaperFineCNormalizedChoiceLocalDelta
        (radius : Real) globalDelta tGlobal (4 * ballRadius))
      (actualY1PaperFineCNormalizedChoiceLambda
        (radius : Real) globalDelta tGlobal (4 * ballRadius))
      eta fiber (by
        intro a ha
        simpa only [D, y1FineCoarseRectangleData] using P a ha)
      hfiberGrid
  refine ⟨{
    gridSelection := grid
    gridLabel := grid.gridLabel
    gridLabel_eq := rfl
    shiftLabel := k
    eta := eta
    selected := fiber
    data := ?_
    eta_eq := heta
    eta_mem := hetaMem
    grid_selected_nonempty := hgridNonempty
    grid_selected_subset := hgridSubset
    grid_cardinal_retention := hgridCard
    selected_nonempty := hfiber
    selected_subset_grid := hfiberGrid
    selected_subset := hfiberGrid.trans hgridSubset
    nineShift_cardinal_retention := hcardNine
    final_common_c := ?_
    final_coefficient_strict := ?_
    raw_right_c_gap := ?_
    label_survival := O.survival
    sample_load := O.load
    retained_tube_card_le_load := O.retained_tube_card_le_load
    left_retained := ?_
    right_retained := ?_
    fine_subset_coarse := ?_ }⟩
  · intro a ha
    simpa only [actualGPrimeLabelFirstThreeShiftCGridLeftTube,
      actualGPrimeLabelFirstThreeShiftCGridRightTube, D,
      y1FineCoarseRectangleData] using P a ha
  · intro a ha
    simpa only [actualGPrimeLabelFirstThreeShiftCGridLeftTube,
      actualGPrimeLabelFirstThreeShiftCGridRightTube, D,
      y1FineCoarseRectangleData] using hmaps.1 a ha
  · intro a ha
    simpa only [actualGPrimeLabelFirstThreeShiftCGridLeftTube,
      actualGPrimeLabelFirstThreeShiftCGridRightTube, D,
      y1FineCoarseRectangleData] using hmaps.2.1 a ha
  · intro a ha
    simpa only [actualGPrimeLabelFirstThreeShiftCGridRightTube, D,
      y1FineCoarseRectangleData] using hmaps.2.2 a ha
  · intro a ha
    exact (hactual a ha).1
  · intro a ha
    exact (hactual a ha).2.1
  · intro a ha
    exact (hactual a ha).2.2

#print axioms ActualGPrimeLabelFirstThreeShiftCGridPaperFineUniformPackage
#print axioms exists_actualGPrimeLabelFirstThreeShiftCGridPaperFineUniformPackage
#print axioms ActualGPrimeLabelFirstThreeShiftCGridPaperFineUniformPackage.leftTube_eq_restricted
#print axioms ActualGPrimeLabelFirstThreeShiftCGridPaperFineUniformPackage.rightTube_eq_restricted

end

end FamilyStickyCinematicL32Prop41ActualY1SamplingPaperFineGPrimeLabelFirstThreeShiftCGridUniformPackageV1
