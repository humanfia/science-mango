import FamilyStickyGrounding.Cinematic.FamilyStickyCinematicL32Prop41ActualY1RetainedThreeShiftCGridWeightedTangencyV1
import FamilyStickyGrounding.Cinematic.FamilyStickyCinematicL32Prop41ActualGPrimeLabelFirstWeightedSeparatedSamplingOutcomeV1
import FamilyStickyGrounding.Cinematic.FamilyStickyCinematicL32Prop41ActualY1SamplingPaperFineGPrimeLabelFirstThreeShiftCGridUniformPackageV1
import FamilyStickyGrounding.Cinematic.FamilyStickyCinematicL32Prop41FiniteRandomSamplingWeightedExtractionV1
import FamilyStickyGrounding.Cinematic.FamilyStickyCinematicL32Prop41ENNRealSeventyTwoWeightedRetentionV1

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 4000000

open Set
open scoped BigOperators ENNReal

namespace FamilyStickyCinematicL32Prop41ActualY1SamplingPaperFineGPrimeLabelFirstThreeShiftCGridWeightedUniformPackageV2

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
open FamilyStickyCinematicL32Prop41ActualGPrimeLabelFirstWeightedSamplingV1
open FamilyStickyCinematicL32Prop41ActualGPrimeDegreeRichMassProducerV1
open FamilyStickyCinematicL32Prop41FiniteRichSeparatedPairSelectionV1
open FamilyStickyCinematicL32Prop41ActualGPrimeLabelFirstWeightedSeparatedSamplingOutcomeV1
open FamilyStickyCinematicL32Prop41ActualY1FineCoarseRectangleProducerV1
open FamilyStickyCinematicL32Prop41ActualY1PaperFineCNormalizedThreeShiftScaleProducerV1
open FamilyStickyCinematicL32Prop41ActualY1RetainedThreeShiftCGridCanonicalFibresV1
open FamilyStickyCinematicL32Prop41ActualY1RetainedThreeShiftCGridRestrictedCanonicalFibresV1
open FamilyStickyCinematicL32Prop41ActualY1RetainedThreeShiftCGridSelectionV1
open FamilyStickyCinematicL32Prop41ActualY1RetainedThreeShiftCGridTangencyV1
open FamilyStickyCinematicL32Prop41ActualY1RetainedThreeShiftCGridWeightedSelectionV1
open FamilyStickyCinematicL32Prop41ActualY1RetainedThreeShiftCGridWeightedTangencyV1
open FamilyStickyCinematicL32Prop41ActualY1SamplingPaperFineGPrimeLabelFirstApproxCSelectionV1
open FamilyStickyCinematicL32Prop41ActualY1SamplingPaperFineGPrimeLabelFirstProvenanceV1
open FamilyStickyCinematicL32Prop41ActualY1SamplingPaperFineGPrimeLabelFirstThreeShiftCGridUniformPackageV1
open FamilyStickyCinematicL32Prop41ActualY1SharpFineScaleTangencyV1
open FamilyStickyCinematicL32Prop41CanonicalMaximizerNonconcentrationV1
open FamilyStickyCinematicL32Prop41CanonicalRichSeparatedPairConsumerV1
open FamilyStickyCinematicL32Prop41CoarseRectangleIncidenceDataV1
open FamilyStickyCinematicL32Prop41ENNRealSeventyTwoWeightedRetentionV1
open FamilyStickyCinematicL32Prop41FiniteGeneralPositionExactRootReproductionV1
open FamilyStickyCinematicL32Prop41FiniteRandomSamplingExtractionV1
open FamilyStickyCinematicL32Prop41FiniteRandomSamplingWeightedExtractionV1
open FamilyStickyCinematicL32Prop41SeparatedCoefficientBallPairV1
open FamilyStickyCinematicL32Prop41ThreeShiftPigeonholeV1
open FamilyStickyCinematicL32Prop41WeightedThreeShiftPigeonholeV1
open FamilyStickyCinematicL32ThreeShiftCGridTubeNormalizationV1
open FamilyStickyCinematicL32TubePairTraceV1
open FamilyStickyWZ2TubeCarrierCoordinateAdapterV1

noncomputable section

universe u v

/-!
# Weight-aware actual label-first C-grid package

The random sample, shifted C-grid, and trace-shift choices all use one label
weight.  On survivors that weight is definitionally pulled back along the
label-first map.  The package keeps the old geometry-only grid interface only
on the already selected first-stage carrier; no false cardinal-retention claim
on the original carrier is introduced.
-/

/-- The label weight pulled back to the literal label-first survivor type. -/
def actualGPrimeLabelFirstSurvivorWeightAt
    {radius : NNReal} {iota : Type u} [DecidableEq iota]
    {fineLabel : Type v} [DecidableEq fineLabel]
    (N : CanonicalNormNonconcentrationData iota)
    (D : CoarseRectangleIncidenceData (point := Real × Real)
      (radius := radius) (iota := iota) fineLabel)
    (keep : iota -> fineLabel -> Prop) (left right : iota)
    (ballRadius : Real)
    (omega : (N.family -> Fin 1) × (N.family -> Fin 1))
    (labelWeight : fineLabel -> ENNReal) :
    ActualGPrimeLabelFirstSurvivor N D keep left right ballRadius omega ->
      ENNReal :=
  fun a => labelWeight
    (actualGPrimeLabelFirstLabel N D keep left right ballRadius omega a)


/-- V2 package with honest weighted retention.  The geometry-only grid
interface lives on weightedGridSelection.selected; the two equality fields
make that restriction explicit to downstream users. -/
structure ActualGPrimeLabelFirstThreeShiftCGridPaperFineWeightedUniformPackageV2
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
    (f : Real -> Real) (outerA outerB globalDelta tGlobal : Real) where
  weightedGridSelection : ActualRetainedY1WeightedThreeShiftCGridSelection D
    (Finset.univ : Finset (ActualGPrimeLabelFirstSurvivor
      N D keep left right ballRadius omega))
    (actualGPrimeLabelFirstLeftIndex N D keep left right ballRadius omega)
    (actualGPrimeLabelFirstRightIndex N D keep left right ballRadius omega)
    (actualGPrimeLabelFirstLabel N D keep left right ballRadius omega)
    keep (4 * ballRadius)
    (actualGPrimeLabelFirstSurvivorWeightAt N D keep left right ballRadius omega
      labelWeight)
  gridSelection : ActualRetainedY1ThreeShiftCGridSelection D
    weightedGridSelection.selected
    (actualGPrimeLabelFirstLeftIndex N D keep left right ballRadius omega)
    (actualGPrimeLabelFirstRightIndex N D keep left right ballRadius omega)
    (actualGPrimeLabelFirstLabel N D keep left right ballRadius omega)
    keep (4 * ballRadius)
  gridSelection_eq :
    gridSelection = weightedGridSelection.toOrdinaryOnSelected
  gridLabel : Fin 3
  gridLabel_eq : gridLabel = gridSelection.gridLabel
  weightedGridLabel_eq : gridLabel = weightedGridSelection.gridLabel
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
  label_injective : Function.Injective
    (actualGPrimeLabelFirstLabel N D keep left right ballRadius omega)
  grid_selected_nonempty : weightedGridSelection.selected.Nonempty
  grid_selected_subset : weightedGridSelection.selected ⊆
    (Finset.univ : Finset (ActualGPrimeLabelFirstSurvivor
      N D keep left right ballRadius omega))
  grid_weight_retention :
    finiteENNRealWeight
        (Finset.univ : Finset (ActualGPrimeLabelFirstSurvivor
          N D keep left right ballRadius omega))
        (actualGPrimeLabelFirstSurvivorWeightAt N D keep left right ballRadius
          omega labelWeight) <=
      3 * finiteENNRealWeight weightedGridSelection.selected
        (actualGPrimeLabelFirstSurvivorWeightAt N D keep left right ballRadius
          omega labelWeight)
  selected_nonempty : selected.Nonempty
  selected_subset_grid : selected ⊆ gridSelection.selected
  selected_subset_weightedGrid : selected ⊆ weightedGridSelection.selected
  selected_subset : selected ⊆
    (Finset.univ : Finset (ActualGPrimeLabelFirstSurvivor
      N D keep left right ballRadius omega))
  trace_weight_retention :
    finiteENNRealWeight weightedGridSelection.selected
        (actualGPrimeLabelFirstSurvivorWeightAt N D keep left right ballRadius
          omega labelWeight) <=
      3 * finiteENNRealWeight selected
        (actualGPrimeLabelFirstSurvivorWeightAt N D keep left right ballRadius
          omega labelWeight)
  nineShift_weight_retention :
    finiteENNRealWeight
        (Finset.univ : Finset (ActualGPrimeLabelFirstSurvivor
          N D keep left right ballRadius omega))
        (actualGPrimeLabelFirstSurvivorWeightAt N D keep left right ballRadius
          omega labelWeight) <=
      9 * finiteENNRealWeight selected
        (actualGPrimeLabelFirstSurvivorWeightAt N D keep left right ballRadius
          omega labelWeight)
  sample_weight_survival :
    (∑ r ∈ actualGPrimeBilateralRetainedFineLabels
        N D keep left right ballRadius, labelWeight r) / 8 <=
      ∑ a : ActualGPrimeLabelFirstSurvivor
          N D keep left right ballRadius omega,
        labelWeight (actualGPrimeLabelFirstLabel
          N D keep left right ballRadius omega a)
  seventyTwo_weight_retention :
    (∑ r ∈ actualGPrimeBilateralRetainedFineLabels
        N D keep left right ballRadius, labelWeight r) <=
      72 * ∑ a ∈ selected,
        labelWeight (actualGPrimeLabelFirstLabel
          N D keep left right ballRadius omega a)
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
    (actualGPrimeLabelFirstLeftIndex N D keep left right ballRadius omega a,
      actualGPrimeLabelFirstLabel N D keep left right ballRadius omega a) ∈
        D.retainedGoodPairs keep
  right_retained : forall a, a ∈ selected ->
    (actualGPrimeLabelFirstRightIndex N D keep left right ballRadius omega a,
      actualGPrimeLabelFirstLabel N D keep left right ballRadius omega a) ∈
        D.retainedGoodPairs keep
  fine_subset_coarse : forall a, a ∈ selected ->
    (D.fineRectangleAt (actualGPrimeLabelFirstLabel
      N D keep left right ballRadius omega a)).carrier (radius : Real) ⊆
      (D.coarseRectangleAt (actualGPrimeLabelFirstLabel
        N D keep left right ballRadius omega a)).carrier globalDelta


/-- The final left endpoint is the restricted canonical-fibre endpoint for
the fixed trace shift stored by the package. -/
theorem ActualGPrimeLabelFirstThreeShiftCGridPaperFineWeightedUniformPackageV2.leftTube_eq_restricted
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

/-- The final right endpoint is the restricted canonical-fibre endpoint. -/
theorem ActualGPrimeLabelFirstThreeShiftCGridPaperFineWeightedUniformPackageV2.rightTube_eq_restricted
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
    (a : ActualGPrimeLabelFirstSurvivor
      N D keep left right ballRadius omega) :
    actualGPrimeLabelFirstThreeShiftCGridRightTube N D keep left right
        ballRadius omega P.gridLabel a =
      actualThreeShiftCGridRestrictedRightTube P.gridSelection a := by
  simp only [actualGPrimeLabelFirstThreeShiftCGridRightTube,
    actualThreeShiftCGridRestrictedRightTube,
    actualThreeShiftCGridRightTube, P.gridLabel_eq]


/-- Consume an already chosen weighted G-prime centre pair and random outcome,
then make the grid and trace choices against the same pulled-back label weight. -/
theorem exists_actualGPrimeLabelFirstThreeShiftCGridPaperFineWeightedUniformPackageV2_of_sampledOutcome
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
    (keep : iota -> fineLabel -> Prop) (ballRadius : Real)
    (degreeLower : Nat) (labelWeight : fineLabel -> ENNReal)
    (hdistance : forall i j, N.distance i j =
      projectedTubePairCoefficientDistance
        (D.fine.tubes i) (D.fine.tubes j))
    (Q : ActualGPrimeWeightedFineSeparatedSampledOutcome
      N D keep ballRadius degreeLower labelWeight)
    (hsmall : ActualY1PaperFineCNormalizedThreeShiftPairScaleSmallness
      (radius : Real) globalDelta tGlobal (4 * ballRadius)) :
    Nonempty
      (ActualGPrimeLabelFirstThreeShiftCGridPaperFineWeightedUniformPackageV2
        fine N D keep Q.pair.left Q.pair.right ballRadius Q.omega labelWeight
          f outerA outerB globalDelta tGlobal) := by
  subst D
  let D := y1FineCoarseRectangleData fine Y1 fineLabels pointAt tubeAt
    f f1 f2 hf hf1 (radius : Real)
    (prop41Y1PaperFineT (radius : Real) globalDelta tGlobal)
    globalDelta tGlobal
  let items : Finset (ActualGPrimeLabelFirstSurvivor
      N D keep Q.pair.left Q.pair.right ballRadius Q.omega) := Finset.univ
  let labelAt :=
    actualGPrimeLabelFirstLabel
      N D keep Q.pair.left Q.pair.right ballRadius Q.omega
  let weight : ActualGPrimeLabelFirstSurvivor
      N D keep Q.pair.left Q.pair.right ballRadius Q.omega -> ENNReal :=
    actualGPrimeLabelFirstSurvivorWeightAt
      N D keep Q.pair.left Q.pair.right ballRadius Q.omega labelWeight
  have selection : ActualRetainedY1ApproxCPairSelection D items
      (actualGPrimeLabelFirstLeftIndex
        N D keep Q.pair.left Q.pair.right ballRadius Q.omega)
      (actualGPrimeLabelFirstRightIndex
        N D keep Q.pair.left Q.pair.right ballRadius Q.omega)
      labelAt keep (4 * ballRadius) (radius : Real) := by
    exact actualGPrimeLabelFirst_actualRetainedY1ApproxCPairSelection
      fine physical E Y1 fineLabels pointAt tubeAt f f1 f2 outerA outerB
      hOuter hf hf1 tGlobal globalDelta facts hpointE
      (radius : Real)
      (prop41Y1PaperFineT (radius : Real) globalDelta tGlobal)
      globalDelta tGlobal N D (by rfl) keep Q.pair.left Q.pair.right
      ballRadius hdistance Q.pair.cross_separated Q.omega
  have hitems : items.Nonempty := Q.survivors_nonempty
  let scales :=
    actualY1PaperFineCNormalizedAutomaticThreeShiftNumerics_of_pairScaleSmall
      sharp hsmall
  obtain ⟨weightedGrid, k, eta, fiber, P, heta, hetaMem,
      hgridNonempty, hgridSubset, hgridWeight, hfiber, hfiberGrid,
      htraceWeight, hnine, hactual⟩ :=
    exists_uniform_threeShift_weighted_perturbationReady_of_actualRetainedY1ThreeShiftCGrid
      fine physical E Y1 fineLabels pointAt centerTube tubeAt f f1 f2
      outerA outerB hOuter hf hf1 tGlobal globalDelta facts pointSource
      hpointE sharp hparameter hft hf1Lower hf1Upper hf2 hf2Continuous
      items
      (actualGPrimeLabelFirstLeftIndex
        N D keep Q.pair.left Q.pair.right ballRadius Q.omega)
      (actualGPrimeLabelFirstRightIndex
        N D keep Q.pair.left Q.pair.right ballRadius Q.omega)
      labelAt keep scales.choice_scale selection hitems scales.traceQ_one
      scales.lambda_pos scales.rho_le_lambda scales.shift_dominates
      scales.strengthened_scale scales.trace_radius weight
  let grid : ActualRetainedY1ThreeShiftCGridSelection D weightedGrid.selected
      (actualGPrimeLabelFirstLeftIndex
        N D keep Q.pair.left Q.pair.right ballRadius Q.omega)
      (actualGPrimeLabelFirstRightIndex
        N D keep Q.pair.left Q.pair.right ballRadius Q.omega)
      labelAt keep (4 * ballRadius) :=
    weightedGrid.toOrdinaryOnSelected
  have hmaps :=
    actualRetainedY1ThreeShiftCGrid_finalMapFacts D weightedGrid.selected
      (actualGPrimeLabelFirstLeftIndex
        N D keep Q.pair.left Q.pair.right ballRadius Q.omega)
      (actualGPrimeLabelFirstRightIndex
        N D keep Q.pair.left Q.pair.right ballRadius Q.omega)
      labelAt keep (4 * ballRadius) grid f outerA outerB
      (actualY1PaperFineCNormalizedChoiceLocalDelta
        (radius : Real) globalDelta tGlobal (4 * ballRadius))
      (actualY1PaperFineCNormalizedChoiceLambda
        (radius : Real) globalDelta tGlobal (4 * ballRadius))
      eta fiber (by
        intro a ha
        simpa only [D, y1FineCoarseRectangleData, labelAt, grid,
          ActualRetainedY1WeightedThreeShiftCGridSelection.toOrdinaryOnSelected]
          using P a ha)
      (by
        intro a ha
        simpa only [grid,
          ActualRetainedY1WeightedThreeShiftCGridSelection.toOrdinaryOnSelected]
          using hfiberGrid ha)
  have hlabelInjective : Function.Injective labelAt := by
    intro a b hab
    apply Subtype.ext
    apply Subtype.ext
    exact hab
  have hseventyTwo :
      (∑ r ∈ actualGPrimeBilateralRetainedFineLabels
          N D keep Q.pair.left Q.pair.right ballRadius, labelWeight r) <=
        72 * ∑ a ∈ fiber, labelWeight (labelAt a) := by
    apply fintypeLabelWeight_le_seventyTwo_mul_of_eighth_nine
      (actualGPrimeBilateralRetainedFineLabels
        N D keep Q.pair.left Q.pair.right ballRadius)
      fiber labelWeight labelAt Q.sampled.weighted_survival
    simpa only [finiteENNRealWeight, weight,
      actualGPrimeLabelFirstSurvivorWeightAt, items,
      Finset.sum_const_zero, Finset.sum_filter, Finset.mem_univ, if_true]
      using hnine
  refine ⟨{
    weightedGridSelection := weightedGrid
    gridSelection := grid
    gridSelection_eq := rfl
    gridLabel := weightedGrid.gridLabel
    gridLabel_eq := rfl
    weightedGridLabel_eq := rfl
    shiftLabel := k
    eta := eta
    selected := fiber
    data := ?_
    eta_eq := heta
    eta_mem := hetaMem
    label_injective := ?_
    grid_selected_nonempty := hgridNonempty
    grid_selected_subset := hgridSubset
    grid_weight_retention := hgridWeight
    selected_nonempty := hfiber
    selected_subset_grid := ?_
    selected_subset_weightedGrid := hfiberGrid
    selected_subset := hfiberGrid.trans hgridSubset
    trace_weight_retention := htraceWeight
    nineShift_weight_retention := hnine
    sample_weight_survival := Q.sampled.weighted_survival
    seventyTwo_weight_retention := hseventyTwo
    final_common_c := ?_
    final_coefficient_strict := ?_
    raw_right_c_gap := ?_
    sample_load := Q.sampled.load
    retained_tube_card_le_load := Q.sampled.retained_tube_card_le_load
    left_retained := ?_
    right_retained := ?_
    fine_subset_coarse := ?_ }⟩
  · intro a ha
    simpa only [actualGPrimeLabelFirstThreeShiftCGridLeftTube,
      actualGPrimeLabelFirstThreeShiftCGridRightTube, D,
      y1FineCoarseRectangleData, labelAt] using P a ha
  · simpa only [labelAt] using hlabelInjective
  · intro a ha
    simpa only [grid,
      ActualRetainedY1WeightedThreeShiftCGridSelection.toOrdinaryOnSelected]
      using hfiberGrid ha
  · intro a ha
    simpa only [actualGPrimeLabelFirstThreeShiftCGridLeftTube,
      actualGPrimeLabelFirstThreeShiftCGridRightTube, D,
      y1FineCoarseRectangleData, labelAt, grid,
      ActualRetainedY1WeightedThreeShiftCGridSelection.toOrdinaryOnSelected]
      using hmaps.1 a ha
  · intro a ha
    simpa only [actualGPrimeLabelFirstThreeShiftCGridLeftTube,
      actualGPrimeLabelFirstThreeShiftCGridRightTube, D,
      y1FineCoarseRectangleData, labelAt, grid,
      ActualRetainedY1WeightedThreeShiftCGridSelection.toOrdinaryOnSelected]
      using hmaps.2.1 a ha
  · intro a ha
    simpa only [actualGPrimeLabelFirstThreeShiftCGridRightTube, D,
      y1FineCoarseRectangleData, labelAt, grid,
      ActualRetainedY1WeightedThreeShiftCGridSelection.toOrdinaryOnSelected]
      using hmaps.2.2 a ha
  · intro a ha
    exact (hactual a ha).1
  · intro a ha
    exact (hactual a ha).2.1
  · intro a ha
    exact (hactual a ha).2.2


/-- Compose upstream weighted G-prime averaging and random-sampling loss with
the honest factor-nine grid-plus-trace retention. -/
theorem ActualGPrimeLabelFirstThreeShiftCGridPaperFineWeightedUniformPackageV2.source_mul_gap_le_seventyTwo_pairCount_mul_selectedWeight
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
        f outerA outerB globalDelta tGlobal) :
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
            Q.pair.right ballRadius Q.omega a)) := by
  have hnine :
      actualGPrimeLabelFirstSurvivorWeight N D keep Q.pair.left Q.pair.right
          ballRadius Q.omega labelWeight <=
        9 * ∑ a ∈ P.selected,
          labelWeight (actualGPrimeLabelFirstLabel N D keep Q.pair.left
            Q.pair.right ballRadius Q.omega a) := by
    simpa only [actualGPrimeLabelFirstSurvivorWeight,
      finiteENNRealWeight, actualGPrimeLabelFirstSurvivorWeightAt,
      Finset.sum_filter, Finset.mem_univ, if_true]
      using P.nineShift_weight_retention
  calc
    (∑ r ∈ D.fineLabels, labelWeight r) *
          ((degreeLower *
            (degreeLower - automaticCanonicalNearCap N ballRadius) : Nat) :
              ENNReal) <=
        8 *
          ((richSeparatedCenterPairs N.family
            (canonicalTenRadiusSeparated N ballRadius)
            (fun _ _ => True)).card : ENNReal) *
          actualGPrimeLabelFirstSurvivorWeight N D keep Q.pair.left
            Q.pair.right ballRadius Q.omega labelWeight :=
      Q.source_mul_gap_le_eight_pairCount_mul_survivorWeight
    _ <= 8 *
          ((richSeparatedCenterPairs N.family
            (canonicalTenRadiusSeparated N ballRadius)
            (fun _ _ => True)).card : ENNReal) *
          (9 * ∑ a ∈ P.selected,
            labelWeight (actualGPrimeLabelFirstLabel N D keep Q.pair.left
              Q.pair.right ballRadius Q.omega a)) := by
      gcongr
    _ = 72 *
          ((richSeparatedCenterPairs N.family
            (canonicalTenRadiusSeparated N ballRadius)
            (fun _ _ => True)).card : ENNReal) *
          (∑ a ∈ P.selected,
            labelWeight (actualGPrimeLabelFirstLabel N D keep Q.pair.left
              Q.pair.right ballRadius Q.omega a)) := by ring

#print axioms actualGPrimeLabelFirstSurvivorWeightAt
#print axioms ActualGPrimeLabelFirstThreeShiftCGridPaperFineWeightedUniformPackageV2
#print axioms ActualGPrimeLabelFirstThreeShiftCGridPaperFineWeightedUniformPackageV2.leftTube_eq_restricted
#print axioms ActualGPrimeLabelFirstThreeShiftCGridPaperFineWeightedUniformPackageV2.rightTube_eq_restricted
#print axioms exists_actualGPrimeLabelFirstThreeShiftCGridPaperFineWeightedUniformPackageV2_of_sampledOutcome
#print axioms ActualGPrimeLabelFirstThreeShiftCGridPaperFineWeightedUniformPackageV2.source_mul_gap_le_seventyTwo_pairCount_mul_selectedWeight

end

end FamilyStickyCinematicL32Prop41ActualY1SamplingPaperFineGPrimeLabelFirstThreeShiftCGridWeightedUniformPackageV2
