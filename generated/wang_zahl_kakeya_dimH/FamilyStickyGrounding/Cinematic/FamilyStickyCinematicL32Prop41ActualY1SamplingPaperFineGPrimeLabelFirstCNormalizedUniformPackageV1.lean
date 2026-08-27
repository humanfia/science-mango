import FamilyStickyGrounding.Cinematic.FamilyStickyCinematicL32Prop41ActualY1RetainedCNormalizedThreeShiftPerturbationReadyV1

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 4000000

open Set

namespace FamilyStickyCinematicL32Prop41ActualY1SamplingPaperFineGPrimeLabelFirstCNormalizedUniformPackageV1

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
open FamilyStickyCinematicL32Prop41ActualTubeCNormalizationV1
open FamilyStickyCinematicL32Prop41ActualY1FineCoarseRectangleProducerV1
open FamilyStickyCinematicL32Prop41ActualY1PaperFineCNormalizedThreeShiftScaleProducerV1
open FamilyStickyCinematicL32Prop41ActualY1RetainedCNormalizedThreeShiftPerturbationReadyV1
open FamilyStickyCinematicL32Prop41ActualY1SamplingPaperFineGPrimeLabelFirstApproxCSelectionV1
open FamilyStickyCinematicL32Prop41ActualY1SamplingPaperFineGPrimeLabelFirstProvenanceV1
open FamilyStickyCinematicL32Prop41ActualY1SharpFineScaleTangencyV1
open FamilyStickyCinematicL32Prop41CanonicalMaximizerNonconcentrationV1
open FamilyStickyCinematicL32Prop41CoarseRectangleIncidenceDataV1
open FamilyStickyCinematicL32Prop41FiniteGeneralPositionExactRootReproductionV1
open FamilyStickyCinematicL32Prop41FiniteRandomSamplingExtractionV1
open FamilyStickyCinematicL32Prop41SeparatedCoefficientBallPairV1
open FamilyStickyCinematicL32Prop41ThreeShiftPigeonholeV1

noncomputable section

universe u v

/-!
# Callback-free paper-fine package on the label-first G-prime carrier

The left retained tube is replaced by the honest graph-coordinate tube with
the right retained tube's C coordinate.  The reduced (a,b,d) separation is
unchanged, while the ordinary same-label active bucket proves the required
one-radius C gap.  Consequently this package has literal common C but no
fixed-C provenance input.
-/

structure ActualGPrimeLabelFirstCNormalizedPaperFineUniformPackage
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
  shiftLabel : Fin 3
  eta : Real
  selected : Finset (ActualGPrimeLabelFirstSurvivor
    N D keep left right ballRadius omega)
  data : forall a, a ∈ selected ->
    PerturbationReadyPairLocalActualLensRectangleData
      (traceTranslateTube
        (normalizeTubeCTo
          (fine.tubes (actualGPrimeLabelFirstLeftIndex
            N D keep left right ballRadius omega a))
          (fine.tubes (actualGPrimeLabelFirstRightIndex
            N D keep left right ballRadius omega a)))
        (eta *
          (actualY1PaperFineCNormalizedChoiceLambda
              (radius : Real) globalDelta tGlobal (4 * ballRadius) *
            actualY1PaperFineCNormalizedChoiceLocalDelta
              (radius : Real) globalDelta tGlobal (4 * ballRadius))))
      (fine.tubes (actualGPrimeLabelFirstRightIndex
        N D keep left right ballRadius omega a))
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
  selected_nonempty : selected.Nonempty
  selected_subset : selected ⊆
    (Finset.univ : Finset (ActualGPrimeLabelFirstSurvivor
      N D keep left right ballRadius omega))
  threeShift_cardinal_retention :
    (Finset.univ : Finset (ActualGPrimeLabelFirstSurvivor
      N D keep left right ballRadius omega)).card <= 3 * selected.card
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

theorem exists_actualGPrimeLabelFirstCNormalizedPaperFineUniformPackage
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
    Nonempty (ActualGPrimeLabelFirstCNormalizedPaperFineUniformPackage
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
  obtain ⟨k, eta, fiber, P, heta, hetaMem, hfiber, hsubset, hcard,
      hactual⟩ :=
    exists_uniform_threeShift_perturbationReady_of_actualRetainedY1ApproxCPairs
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
  refine ⟨{
    shiftLabel := k
    eta := eta
    selected := fiber
    data := P
    eta_eq := heta
    eta_mem := hetaMem
    selected_nonempty := hfiber
    selected_subset := hsubset
    threeShift_cardinal_retention := hcard
    label_survival := O.survival
    sample_load := O.load
    retained_tube_card_le_load := O.retained_tube_card_le_load
    left_retained := ?_
    right_retained := ?_
    fine_subset_coarse := ?_ }⟩
  · intro a ha
    exact (hactual a ha).1
  · intro a ha
    exact (hactual a ha).2.1
  · intro a ha
    exact (hactual a ha).2.2

#print axioms ActualGPrimeLabelFirstCNormalizedPaperFineUniformPackage
#print axioms exists_actualGPrimeLabelFirstCNormalizedPaperFineUniformPackage

end

end FamilyStickyCinematicL32Prop41ActualY1SamplingPaperFineGPrimeLabelFirstCNormalizedUniformPackageV1
