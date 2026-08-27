import FamilyStickyGrounding.Cinematic.FamilyStickyCinematicL32Prop41ActualY1PaperFineCNormalizedSelectedCountingNumericsV1
import FamilyStickyGrounding.Cinematic.FamilyStickyCinematicL32Prop41ActualY1SamplingPaperFineGPrimeLabelFirstThreeShiftCGridWeightedUniformPackageV2
import FamilyStickyGrounding.Cinematic.FamilyStickyCinematicL32Prop41ActualY1SamplingPaperFineGPrimeLabelFirstThreeShiftCGridRestrictedEndpointC2BallV1
import FamilyStickyGrounding.Cinematic.FamilyStickyCinematicL32Prop41ActualY1SamplingPaperFineGPrimeLabelFirstThreeShiftCGridRightCLocalCoverFiniteOccupiedCodeCurvatureDataV1
import FamilyStickyGrounding.Cinematic.FamilyStickyCinematicL32Prop41ThirdStageSelectedSubfamilyAutomaticOutcomeGeneralScalesV1
import Mathlib.Tactic

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 500000

open Set

namespace FamilyStickyCinematicL32Prop41ActualY1SamplingPaperFineGPrimeLabelFirstThreeShiftCGridThirdStageSelectedSampledLensV2

open Submission.Kakeya.ConvexGeometry
open Submission.Kakeya.Uniformity
open FamilyStickyWZ2TubeCarrierCoordinateAdapterV1
open FamilyStickyCinematicL32ActualTubeCoefficientDistancesV1
open FamilyStickyCinematicL32FiniteNestedValueFibresExternalPivotThirdStageV1
open FamilyStickyCinematicL32FiniteNestedValueFibresThirdStageAtScalesV1
open FamilyStickyCinematicL32FiniteValueFibresV1
open FamilyStickyCinematicL32FiniteValuePairCarrierV1
open FamilyStickyCinematicL32CurvilinearRectanglePointMultiplicityV1
open FamilyStickyCinematicL32Lemma316AutomaticCompactC2GreedySelectionTwoCenterV1
open FamilyStickyCinematicL32FiniteProjectedShadingMultiplicitySliceV1
open FamilyStickyCinematicL32Prop41ActualGlobalNormCoarseFiberV1
open FamilyStickyCinematicL32Prop41CanonicalMaximizerNonconcentrationV1
open FamilyStickyCinematicL32Prop41ActualY1FineCoarseRectangleProducerV1
open FamilyStickyCinematicL32Prop41ActualY1GridRightCLocalCoverSelectedGenericV1
open FamilyStickyCinematicL32Prop41ActualY1PaperFineCNormalizedSelectedCountingNumericsV1
open FamilyStickyCinematicL32Prop41ActualY1PaperFineCNormalizedThreeShiftScaleProducerV1
open FamilyStickyCinematicL32Prop41ActualY1RetainedThreeShiftCGridCanonicalFibresV1
open FamilyStickyCinematicL32Prop41ActualY1RetainedThreeShiftCGridRestrictedCanonicalFibresV1
open FamilyStickyCinematicL32Prop41ActualY1RightCLocalCoverSelectedGenericV1
open FamilyStickyCinematicL32Prop41ActualY1SamplingPaperFineGPrimeLabelFirstProvenanceV1
open FamilyStickyCinematicL32Prop41ActualY1SamplingPaperFineGPrimeLabelFirstThreeShiftCGridRestrictedCoefficientBallV1
open FamilyStickyCinematicL32Prop41ActualY1SamplingPaperFineGPrimeLabelFirstThreeShiftCGridRestrictedEndpointC2BallV1
open FamilyStickyCinematicL32Prop41ActualY1SamplingPaperFineGPrimeLabelFirstThreeShiftCGridRightCLocalCoverFiniteOccupiedCodeCurvatureDataV1
open FamilyStickyCinematicL32Prop41ActualY1SamplingPaperFineGPrimeLabelFirstThreeShiftCGridUniformPackageV1
open FamilyStickyCinematicL32Prop41ActualY1SamplingPaperFineGPrimeLabelFirstThreeShiftCGridWeightedUniformPackageV2
open FamilyStickyCinematicL32Prop41ActualY1SharpFineScaleTangencyV1
open FamilyStickyCinematicL32Prop41CoarseRectangleIncidenceDataV1
open FamilyStickyCinematicL32Prop41ExactLocalRectangleRestrictionV1
open FamilyStickyCinematicL32Prop41FiniteGeneralPositionExactRootReproductionV1
open FamilyStickyCinematicL32Prop41FiniteGeneralPositionPairReindexV1
open FamilyStickyCinematicL32Prop41SampledLensCardinalityAssemblyV1
open FamilyStickyCinematicL32Prop41SelectedSubfamilyTwoScaleAutomaticOutcomeFromCurveBudgetRepoV2V1
open FamilyStickyCinematicL32Prop41SharpCommonCReferenceV1
open FamilyStickyCinematicL32Prop41ThirdStageSelectedSubfamilyAutomaticOutcomeGeneralScalesV1
open FamilyStickyCinematicL32TubePairTraceV1

noncomputable section

local instance tubeDecidableEq {radius : NNReal} :
    DecidableEq (Tube radius) := Classical.decEq _

universe u v w

section Tagged

variable {radius : NNReal} {iota : Type u} [DecidableEq iota]
variable {fineLabel : Type v} [DecidableEq fineLabel]
variable (fine : UniformTubeFamily radius iota)
variable (physical : FiniteProjectedShading (Real × Real) iota)
variable (tGlobal : Real) (globalCenter : Tube radius)
variable (N : CanonicalNormNonconcentrationData iota)
variable (D : CoarseRectangleIncidenceData (point := Real × Real)
  (radius := radius) (iota := iota) fineLabel)
variable (keep : iota -> fineLabel -> Prop) (left right : iota)
variable (ballRadius : Real)
variable (omega : (N.family -> Fin 1) × (N.family -> Fin 1))
variable (labelWeight : fineLabel -> ENNReal)
variable (f : Real -> Real) (outerA outerB globalDelta : Real)

private abbrev Survivor := ActualGPrimeLabelFirstSurvivor
  N D keep left right ballRadius omega

variable
  (P : ActualGPrimeLabelFirstThreeShiftCGridPaperFineWeightedUniformPackageV2 fine N D
    keep left right ballRadius omega labelWeight f outerA outerB globalDelta tGlobal)

/-- The literal trace shift used by the final package endpoints. -/
def actualGPrimeLabelFirstThreeShiftCGridFinalTraceShift : Real :=
  P.eta *
    (actualY1PaperFineCNormalizedChoiceLambda
        (radius : Real) globalDelta tGlobal (4 * ballRadius) *
      actualY1PaperFineCNormalizedChoiceLocalDelta
        (radius : Real) globalDelta tGlobal (4 * ballRadius))

/-- Forget a local-cover code tag and use the final package left endpoint. -/
def actualGPrimeLabelFirstThreeShiftCGridTaggedLeftTube
    {code : Type w} :
    CodeSelectedCandidate code
      (Survivor N D keep left right ballRadius omega) -> Tube radius :=
  fun q =>
    actualGPrimeLabelFirstThreeShiftCGridLeftTube N D keep left right
      ballRadius omega P.gridLabel P.eta globalDelta tGlobal q.2

/-- Forget a local-cover code tag and use the final package right endpoint. -/
def actualGPrimeLabelFirstThreeShiftCGridTaggedRightTube
    {code : Type w} :
    CodeSelectedCandidate code
      (Survivor N D keep left right ballRadius omega) -> Tube radius :=
  fun q =>
    actualGPrimeLabelFirstThreeShiftCGridRightTube N D keep left right
      ballRadius omega P.gridLabel q.2

/-- The third-stage source is the exact-local restriction already used by
the occupied-code local-compact producer. -/
def actualGPrimeLabelFirstThreeShiftCGridTaggedLocalRectangle
    {code : Type w} :
    CodeSelectedCandidate code
      (Survivor N D keep left right ballRadius omega) -> C2GraphRectangle :=
  codeSelectedRectangleAt
    (actualGPrimeThreeShiftCGridLocalCompactRectangleAt N D keep left right
      ballRadius omega globalDelta tGlobal)

/-- Any tagged subfamily whose underlying pairs stay in P.selected and
whose final right endpoint has value c lies in the genuine restricted
outer C fibre. -/
theorem actualGPrimeLabelFirstThreeShiftCGrid_taggedRetainedPairTubeFamily_subset_restricted
    {code : Type w} [Fintype code] [DecidableEq code]
    (selectedAt : code ->
      Finset (Survivor N D keep left right ballRadius omega))
    (c : Real)
    (hselectedAt : forall k a, a ∈ selectedAt k -> a ∈ P.selected)
    (hfixedC : forall k a, a ∈ selectedAt k ->
      tubeGraphC
          (actualGPrimeLabelFirstThreeShiftCGridRightTube N D keep left right
            ballRadius omega P.gridLabel a) = c)
    (tagged : Finset (CodeSelectedCandidate code
      (Survivor N D keep left right ballRadius omega)))
    (htagged : tagged ⊆
      codeSelectedCandidates (Finset.univ : Finset code) selectedAt) :
    retainedPairTubeFamily tagged
        (actualGPrimeLabelFirstThreeShiftCGridTaggedLeftTube
          (P := P))
        (actualGPrimeLabelFirstThreeShiftCGridTaggedRightTube
          (P := P)) ⊆
      actualThreeShiftCGridRestrictedTubeFamilyAt P.gridSelection P.selected
        (actualGPrimeLabelFirstThreeShiftCGridFinalTraceShift
          (P := P)) c := by
  intro V hV
  simp only [retainedPairTubeFamily, Finset.mem_union,
    Finset.mem_image] at hV
  rcases hV with ⟨q, hq, rfl⟩ | ⟨q, hq, rfl⟩
  · have hqVertices := htagged hq
    have hqData :=
      (mem_codeSelectedCandidates_iff
        (Finset.univ : Finset code) selectedAt q).mp hqVertices
    have hqSelected := hselectedAt q.1 q.2 hqData.2
    have hrightC : tubeGraphC
        (actualThreeShiftCGridRestrictedRightTube P.gridSelection q.2) = c := by
      simpa only [actualThreeShiftCGridRestrictedRightTube,
        actualThreeShiftCGridRightTube,
        actualGPrimeLabelFirstThreeShiftCGridRightTube, P.gridLabel_eq] using
        hfixedC q.1 q.2 hqData.2
    have hvalue : actualThreeShiftCGridRestrictedValueAt P.gridSelection
        (actualGPrimeLabelFirstThreeShiftCGridFinalTraceShift
          (P := P)) q.2 = c := by
      rw [← actualThreeShiftCGridRestrictedRightTube_graphC_eq_valueAt
        P.gridSelection P.selected_subset_grid
          (actualGPrimeLabelFirstThreeShiftCGridFinalTraceShift
          (P := P)) hqSelected]
      exact hrightC
    have hfiber : q.2 ∈ actualThreeShiftCGridRestrictedFiber
        P.gridSelection P.selected
          (actualGPrimeLabelFirstThreeShiftCGridFinalTraceShift
          (P := P)) c := by
      exact (mem_finiteValueFiber_iff P.selected
        (actualThreeShiftCGridRestrictedValueAt P.gridSelection
          (actualGPrimeLabelFirstThreeShiftCGridFinalTraceShift
          (P := P))) c q.2).mpr ⟨hqSelected, hvalue⟩
    simp only [actualThreeShiftCGridRestrictedTubeFamilyAt,
      finiteValuePairCarrierAt, finitePairCarrier, Finset.mem_union,
      Finset.mem_image]
    exact Or.inl ⟨q.2, hfiber, (ActualGPrimeLabelFirstThreeShiftCGridPaperFineWeightedUniformPackageV2.leftTube_eq_restricted fine N D keep left right ballRadius omega labelWeight f outerA outerB globalDelta tGlobal P q.2).symm⟩
  · have hqVertices := htagged hq
    have hqData :=
      (mem_codeSelectedCandidates_iff
        (Finset.univ : Finset code) selectedAt q).mp hqVertices
    have hqSelected := hselectedAt q.1 q.2 hqData.2
    have hrightC : tubeGraphC
        (actualThreeShiftCGridRestrictedRightTube P.gridSelection q.2) = c := by
      simpa only [actualThreeShiftCGridRestrictedRightTube,
        actualThreeShiftCGridRightTube,
        actualGPrimeLabelFirstThreeShiftCGridRightTube, P.gridLabel_eq] using
        hfixedC q.1 q.2 hqData.2
    have hvalue : actualThreeShiftCGridRestrictedValueAt P.gridSelection
        (actualGPrimeLabelFirstThreeShiftCGridFinalTraceShift
          (P := P)) q.2 = c := by
      rw [← actualThreeShiftCGridRestrictedRightTube_graphC_eq_valueAt
        P.gridSelection P.selected_subset_grid
          (actualGPrimeLabelFirstThreeShiftCGridFinalTraceShift
          (P := P)) hqSelected]
      exact hrightC
    have hfiber : q.2 ∈ actualThreeShiftCGridRestrictedFiber
        P.gridSelection P.selected
          (actualGPrimeLabelFirstThreeShiftCGridFinalTraceShift
          (P := P)) c := by
      exact (mem_finiteValueFiber_iff P.selected
        (actualThreeShiftCGridRestrictedValueAt P.gridSelection
          (actualGPrimeLabelFirstThreeShiftCGridFinalTraceShift
          (P := P))) c q.2).mpr ⟨hqSelected, hvalue⟩
    simp only [actualThreeShiftCGridRestrictedTubeFamilyAt,
      finiteValuePairCarrierAt, finitePairCarrier, Finset.mem_union,
      Finset.mem_image]
    exact Or.inr ⟨q.2, hfiber, (ActualGPrimeLabelFirstThreeShiftCGridPaperFineWeightedUniformPackageV2.rightTube_eq_restricted fine N D keep left right ballRadius omega labelWeight f outerA outerB globalDelta tGlobal P q.2).symm⟩

/-- Actual post-third-stage sampled-lens bound in one normalized-C fibre.

The third-stage outcome is supplied by the independent occupied-code
producer. The only transport fields are literal underlying membership and
fixed-C facts for its code-local selected sets. The six-radius selected
smallness is explicit: it is not derivable from the old five-radius
condition. -/
theorem actualGPrimeLabelFirstThreeShiftCGrid_thirdStageSelected_card_le_sampledLensBound
    {code : Type w} [Fintype code] [DecidableEq code]
    (selectedAt : code ->
      Finset (Survivor N D keep left right ballRadius omega))
    (c referenceScale : Real)
    (weight : CodeSelectedCandidate code
      (Survivor N D keep left right ballRadius omega) -> ENNReal)
    (thirdPacking : ENNReal)
    (f1 f2 : Real -> Real)
    (hOuter : outerA <= outerB)
    (hfDeriv : forall z, HasDerivAt f (f1 z) z)
    (hf1Deriv : forall z, HasDerivAt f1 (f2 z) z)
    (Q : FiniteThirdStageGreedyOutcome
      (codeSelectedCandidates (Finset.univ : Finset code) selectedAt)
      (compactC2ComparableAtScales
        (actualGPrimeLabelFirstThreeShiftCGridTaggedLocalRectangle
          (N := N) (D := D) (keep := keep) (left := left) (right := right)
          (ballRadius := ballRadius) (omega := omega)
          (globalDelta := globalDelta) (tGlobal := tGlobal))
        (Icc outerA outerB)
        (globalCenterFixedCommonCReference globalCenter c f f1 f2
          hfDeriv hf1Deriv outerA outerB hOuter)
        (actualY1PaperFineCNormalizedChoiceLocalDelta
          (radius : Real) globalDelta tGlobal (4 * ballRadius))
        (4 * ballRadius) referenceScale
        (actualY1PaperFineCNormalizedSelectedAutomaticComparisonLambda
          (radius : Real) globalDelta tGlobal (4 * ballRadius)))
      weight thirdPacking)
    (hvertices :
      (codeSelectedCandidates (Finset.univ : Finset code)
        selectedAt).Nonempty)
    (hselectedAt : forall k a, a ∈ selectedAt k -> a ∈ P.selected)
    (hfixedC : forall k a, a ∈ selectedAt k ->
      tubeGraphC
          (actualGPrimeLabelFirstThreeShiftCGridRightTube N D keep left right
            ballRadius omega P.gridLabel a) = c)
    (hDfine : D.fine = fine)
    (hfamily : N.family =
      actualGlobalNormIndexFamily fine physical tGlobal globalCenter)
    (sharp : ActualY1SharpFineScaleNumerics
      (radius : Real) globalDelta tGlobal (outerB - outerA))
    (hthree : ActualY1PaperFineCNormalizedThreeShiftPairScaleSmallness
      (radius : Real) globalDelta tGlobal (4 * ballRadius))
    (hcount : ActualY1PaperFineCNormalizedSelectedCountingSmallness
      (radius : Real) globalDelta tGlobal (4 * ballRadius))
    (hparameter : forall z, z ∈ Icc outerA outerB -> |z| <= 1)
    (hfunction : forall z, z ∈ Icc outerA outerB -> |f z| <= 2)
    (hfirstLower : forall z, z ∈ Icc outerA outerB -> 1 <= |f1 z|)
    (hfirstUpper : forall z, z ∈ Icc outerA outerB -> |f1 z| <= 2)
    (hsecond : forall z, z ∈ Icc outerA outerB -> |f2 z| <= 1 / 100)
    (hsecondContinuous : ContinuousOn f2 (Icc outerA outerB))
    (hreferenceMargin :
      max ((401 / 100 : Real) *
          actualGPrimeLabelFirstThreeShiftCGridRestrictedCoefficientRadius
            tGlobal
              (actualGPrimeLabelFirstThreeShiftCGridFinalTraceShift
          (P := P)))
        (2 *
            actualGPrimeLabelFirstThreeShiftCGridRestrictedCoefficientRadius
              tGlobal
                (actualGPrimeLabelFirstThreeShiftCGridFinalTraceShift
          (P := P)) + 0) <
        3 * referenceScale) :
    (Q.selected.card : Real) <=
      sampledLensBound
        (selectedSubfamilyAutomaticDepthFromCurveBudget
          (actualThreeShiftCGridRestrictedGlobalTubeFamily P.gridSelection
            P.selected
              (actualGPrimeLabelFirstThreeShiftCGridFinalTraceShift
          (P := P))).card)
        ((actualThreeShiftCGridRestrictedTubeFamilyAt P.gridSelection
          P.selected
            (actualGPrimeLabelFirstThreeShiftCGridFinalTraceShift
          (P := P)) c).card : Real) := by
  let shift :=
    actualGPrimeLabelFirstThreeShiftCGridFinalTraceShift
          (P := P)
  let taggedLeft :=
    actualGPrimeLabelFirstThreeShiftCGridTaggedLeftTube
          (P := P) (code := code)
  let taggedRight :=
    actualGPrimeLabelFirstThreeShiftCGridTaggedRightTube
          (P := P) (code := code)
  let taggedSource :=
    actualGPrimeLabelFirstThreeShiftCGridTaggedLocalRectangle
          (N := N) (D := D) (keep := keep) (left := left) (right := right)
          (ballRadius := ballRadius) (omega := omega)
          (globalDelta := globalDelta) (tGlobal := tGlobal) (code := code)
  let outerFamily :=
    actualThreeShiftCGridRestrictedTubeFamilyAt P.gridSelection P.selected
      shift c
  let globalFamily :=
    actualThreeShiftCGridRestrictedGlobalTubeFamily P.gridSelection P.selected
      shift
  have hendpointOuter :
      retainedPairTubeFamily Q.selected taggedLeft taggedRight ⊆
        outerFamily := by
    exact
      actualGPrimeLabelFirstThreeShiftCGrid_taggedRetainedPairTubeFamily_subset_restricted
        fine tGlobal N D keep left right ballRadius omega labelWeight f outerA outerB
          globalDelta P selectedAt c hselectedAt hfixedC Q.selected
            Q.selected_subset
  have houterGlobal : outerFamily ⊆ globalFamily := by
    exact
      actualGPrimeLabelFirstThreeShiftCGridRestrictedTubeFamilyAt_subset_global
        (N := N) (D := D) (keep := keep) (left := left) (right := right)
          (ballRadius := ballRadius) (omega := omega)
          (P := P.gridSelection) P.selected shift c
  have hendpointGlobal :
      retainedPairTubeFamily Q.selected taggedLeft taggedRight ⊆
        globalFamily :=
    fun _ hV => houterGlobal (hendpointOuter hV)
  have hcommon : forall V,
      V ∈ retainedPairTubeFamily Q.selected taggedLeft taggedRight ->
        tubeGraphC V = c := by
    intro V hV
    exact
      actualGPrimeLabelFirstThreeShiftCGridRestrictedTubeFamilyAt_graphC
        (N := N) (D := D) (keep := keep) (left := left) (right := right)
          (ballRadius := ballRadius) (omega := omega)
          (P := P.gridSelection) P.selected_subset_grid shift c
            (hendpointOuter hV)
  have hball : forall V,
      V ∈ retainedPairTubeFamily Q.selected taggedLeft taggedRight ->
        tubePairCoefficientDistance V globalCenter <=
          actualGPrimeLabelFirstThreeShiftCGridRestrictedCoefficientRadius
            tGlobal shift := by
    intro V hV
    exact
      actualGPrimeLabelFirstThreeShiftCGridRestrictedGlobalTubeFamily_distance_le
        fine physical tGlobal globalCenter N D keep left right ballRadius
          omega P.gridSelection hDfine hfamily P.selected shift V
            (hendpointGlobal hV)
  have hcurveBudget :
      (retainedPairTubeFamily Q.selected taggedLeft taggedRight).card <=
        globalFamily.card :=
    Finset.card_le_card hendpointGlobal
  have hdata : forall q, q ∈ Q.selected ->
      PerturbationReadyPairLocalActualLensRectangleData
        (taggedLeft q) (taggedRight q) f (taggedSource q) outerA outerB
        (actualY1PaperFineCNormalizedChoiceLocalDelta
          (radius : Real) globalDelta tGlobal (4 * ballRadius))
        (4 * ballRadius)
        (actualY1PaperFineCNormalizedChoiceLambda
          (radius : Real) globalDelta tGlobal (4 * ballRadius))
        (2 * actualY1PaperFineCNormalizedChoiceLambda
          (radius : Real) globalDelta tGlobal (4 * ballRadius)) := by
    intro q hq
    have hqVertices := Q.selected_subset hq
    have hqData :=
      (mem_codeSelectedCandidates_iff
        (Finset.univ : Finset code) selectedAt q).mp hqVertices
    have hqSelected := hselectedAt q.1 q.2 hqData.2
    have hlocal := FamilyStickyCinematicL32Prop41ExactLocalRectangleRestrictionV1.PerturbationReadyPairLocalActualLensRectangleData.toExactLocalRectangle (P.data q.2 hqSelected)
    simpa only [taggedLeft, taggedRight, taggedSource,
      actualGPrimeLabelFirstThreeShiftCGridTaggedLeftTube,
      actualGPrimeLabelFirstThreeShiftCGridTaggedRightTube,
      actualGPrimeLabelFirstThreeShiftCGridTaggedLocalRectangle,
      codeSelectedRectangleAt,
      actualGPrimeThreeShiftCGridLocalCompactRectangleAt,
      actualY1GridRightCLocalCoverExactLocalRectangle,
      actualY1RightCLocalCoverExactLocalRectangle] using hlocal
  let numerics :=
    actualY1PaperFineCNormalizedSelectedCountingNumerics_of_pairScaleSmall
      sharp hthree hcount
  have hraw :
      (Q.selected.card : Real) <=
        sampledLensBound
          (selectedSubfamilyAutomaticDepthFromCurveBudget globalFamily.card)
          ((retainedPairTubeFamily Q.selected taggedLeft
            taggedRight).card : Real) := by
    exact
      thirdStageSelected_card_le_sampledLensBoundAtScales_of_scalars_curveBudget
        (codeSelectedCandidates (Finset.univ : Finset code) selectedAt)
        taggedLeft taggedRight taggedSource globalCenter c
        (actualGPrimeLabelFirstThreeShiftCGridRestrictedCoefficientRadius
          tGlobal shift)
        globalFamily.card f f1 f2 outerA outerB
        (actualY1PaperFineCNormalizedChoiceLocalDelta
          (radius : Real) globalDelta tGlobal (4 * ballRadius))
        (4 * ballRadius) referenceScale
        (actualY1PaperFineCNormalizedChoiceLambda
          (radius : Real) globalDelta tGlobal (4 * ballRadius))
        (2 * actualY1PaperFineCNormalizedChoiceLambda
          (radius : Real) globalDelta tGlobal (4 * ballRadius))
        (actualY1PaperFineCNormalizedSelectedAutomaticComparisonLambda
          (radius : Real) globalDelta tGlobal (4 * ballRadius))
        weight thirdPacking hOuter hfDeriv hf1Deriv
        numerics.interval_strict numerics.delta_pos numerics.localScale_pos
        numerics.lambda1_ge_one numerics.interval_width numerics.small_scale
        hparameter hfunction hfirstLower hfirstUpper hsecond
        hsecondContinuous Q hvertices hcommon hball hcurveBudget
        hreferenceMargin numerics.comparison_enlarges
        numerics.localization_scale hdata
  calc
    (Q.selected.card : Real) <=
        sampledLensBound
          (selectedSubfamilyAutomaticDepthFromCurveBudget globalFamily.card)
          ((retainedPairTubeFamily Q.selected taggedLeft
            taggedRight).card : Real) := hraw
    _ <= sampledLensBound
        (selectedSubfamilyAutomaticDepthFromCurveBudget globalFamily.card)
        (outerFamily.card : Real) := by
      apply sampledLensBound_mono_curveCount
      · exact selectedSubfamilyAutomaticDepthFromCurveBudget_nonneg
          globalFamily.card
      · positivity
      · exact_mod_cast Finset.card_le_card hendpointOuter

#print axioms actualGPrimeLabelFirstThreeShiftCGridFinalTraceShift
#print axioms actualGPrimeLabelFirstThreeShiftCGridTaggedLeftTube
#print axioms actualGPrimeLabelFirstThreeShiftCGridTaggedRightTube
#print axioms actualGPrimeLabelFirstThreeShiftCGridTaggedLocalRectangle
#print axioms actualGPrimeLabelFirstThreeShiftCGrid_taggedRetainedPairTubeFamily_subset_restricted
#print axioms actualGPrimeLabelFirstThreeShiftCGrid_thirdStageSelected_card_le_sampledLensBound

end Tagged

end

end FamilyStickyCinematicL32Prop41ActualY1SamplingPaperFineGPrimeLabelFirstThreeShiftCGridThirdStageSelectedSampledLensV2
