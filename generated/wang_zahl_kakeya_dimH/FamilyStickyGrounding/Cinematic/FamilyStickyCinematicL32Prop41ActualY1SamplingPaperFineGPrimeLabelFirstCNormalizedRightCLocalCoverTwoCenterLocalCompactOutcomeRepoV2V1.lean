import FamilyStickyGrounding.Cinematic.FamilyStickyCinematicL32Lemma312TwoCenterAutomaticCurvatureRatioV1
import FamilyStickyGrounding.Cinematic.FamilyStickyCinematicL32Lemma55FirstHitOwnerClusterVolumeCapTwoCenterLocalCompactV1
import FamilyStickyGrounding.Cinematic.FamilyStickyCinematicL32Prop41ActualY1SamplingPaperFineGPrimeLabelFirstCNormalizedRightCLocalCoverTwoCenterBridgeV1
import FamilyStickyGrounding.Cinematic.FamilyStickyCinematicL32Prop41AutomaticComparisonLambdaV1
import FamilyStickyGrounding.Cinematic.FamilyStickyCinematicL32Prop41ExactLocalRectangleRestrictionV1
import Mathlib.Tactic

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 8000000

open Set MeasureTheory
open scoped BigOperators ENNReal Interval

namespace FamilyStickyCinematicL32Prop41ActualY1SamplingPaperFineGPrimeLabelFirstCNormalizedRightCLocalCoverTwoCenterLocalCompactOutcomeRepoV2V1

open Submission.Kakeya.ConvexGeometry
open Submission.Kakeya.Uniformity
open FamilyStickyWZ2TubeCarrierCoordinateAdapterV1
open FamilyStickyCinematicL32ActualProjectedCenteredHalfPointSourceV1
open FamilyStickyCinematicL32ActualProjectedCenteredHalfY1ActiveGeometryV1
open FamilyStickyCinematicL32CenteredFractionIntervalsV1
open FamilyStickyCinematicL32CurvilinearRectanglePointMultiplicityV1
open FamilyStickyCinematicL32FiniteProjectedShadingMultiplicitySliceV1
open FamilyStickyCinematicL32Lemma312PivotCenteredContainerTwoCenterV1
open FamilyStickyCinematicL32Lemma312PivotCenteredContainerV1
open FamilyStickyCinematicL32Lemma312TwoCenterAutomaticCurvatureRatioV1
open FamilyStickyCinematicL32Lemma316CompactC2GreedySelectionV1
open FamilyStickyCinematicL32Lemma55E2FineRectangleFirstHitY2V1
open FamilyStickyCinematicL32Lemma55FirstHitOwnerClusterVolumeCapTwoCenterLocalCompactV1
open FamilyStickyCinematicL32Lemma55Lemma316TwoStageGreedyClusteringAtScalesTwoCenterV1
open FamilyStickyCinematicL32Lemma55Lemma316TwoStageGreedyClusteringAtScalesTwoCenterLocalCompactV1
open FamilyStickyCinematicL32Prop41ActualY1FineCoarseRectangleProducerV1
open FamilyStickyCinematicL32Prop41ActualY1PaperFineCNormalizedThreeShiftScaleProducerV1
open FamilyStickyCinematicL32Prop41ActualY1PaperFineThreeShiftScaleProducerV1
open FamilyStickyCinematicL32Prop41ActualY1RightCLocalCoverSelectedGenericV1
open FamilyStickyCinematicL32Prop41ActualY1SamplingPaperFineGPrimeLabelFirstCNormalizedRightCLocalCoverBallAdapterV1
open FamilyStickyCinematicL32Prop41ActualY1SamplingPaperFineGPrimeLabelFirstCNormalizedRightCLocalCoverTwoCenterBridgeV1
open FamilyStickyCinematicL32Prop41ActualY1SamplingPaperFineGPrimeLabelFirstCNormalizedUniformPackageV1
open FamilyStickyCinematicL32Prop41ActualY1SamplingPaperFineGPrimeLabelFirstProvenanceV1
open FamilyStickyCinematicL32Prop41ActualY1SharpFineScaleTangencyV1
open FamilyStickyCinematicL32Prop41AutomaticComparisonLambdaV1
open FamilyStickyCinematicL32Prop41CanonicalMaximizerNonconcentrationV1
open FamilyStickyCinematicL32Prop41CoarseRectangleIncidenceDataV1
open FamilyStickyCinematicL32Prop41ExactLocalRectangleRestrictionV1
open FamilyStickyCinematicL32Prop41SharpCommonCReferenceV1
open FamilyStickyCinematicL32Prop41TangencyProductToScaleV1
open FamilyStickyCinematicL32ThinReferenceCompactDomainC2BallV1

noncomputable section

universe u v

local instance c2GraphRectangleDecidableEq : DecidableEq C2GraphRectangle :=
  Classical.decEq _

local instance tubeDecidableEq {radius : NNReal} : DecidableEq (Tube radius) :=
  Classical.decEq _

/-!
# C-normalized actual local-compact two-center outcome on one joint fibre

The joint key is (right graph-C, source-cover code).  The local compact-C2
first stage retains an honest pivot-centered owner container, while the
second stage is Pairwise at the independent global reference.  First-hit
mass is capped by the exact dilation area.  No per-code sampled-lens or
global two-sided-load bound is asserted here.
-/

/-- The normalized analogue of the canonical comparison enlargement. -/
def actualY1PaperFineCNormalizedAutomaticComparisonLambda
    {radius : NNReal} (globalDelta tGlobal pairScale : Real) : Real :=
  prop41AutomaticComparisonLambda
    (2 * actualY1PaperFineCNormalizedChoiceLambda
      (radius : Real) globalDelta tGlobal pairScale)
    (actualY1PaperFineCNormalizedChoiceLocalDelta
      (radius : Real) globalDelta tGlobal pairScale)
    pairScale

/-- Normalized paper smallness makes the automatic comparison enlargement
at least 100, as required by the local-compact selector. -/
theorem actualY1PaperFineCNormalizedAutomaticComparisonLambda_ge_hundred
    {radius : NNReal} {globalDelta tGlobal outerWidth pairScale : Real}
    (sharp : ActualY1SharpFineScaleNumerics
      (radius : Real) globalDelta tGlobal outerWidth)
    (hsmall : ActualY1PaperFineCNormalizedThreeShiftPairScaleSmallness
      (radius : Real) globalDelta tGlobal pairScale) :
    100 <= actualY1PaperFineCNormalizedAutomaticComparisonLambda
      (radius := radius) globalDelta tGlobal pairScale := by
  have scales :=
    actualY1PaperFineCNormalizedAutomaticThreeShiftNumerics_of_pairScaleSmall
      sharp hsmall
  have hq : 1 <=
      actualY1PaperFineCNormalizedChoiceTraceQ
        (radius : Real) globalDelta tGlobal pairScale :=
    scales.traceQ_one
  have hqSq : 1 <=
      (actualY1PaperFineCNormalizedChoiceTraceQ
        (radius : Real) globalDelta tGlobal pairScale) ^ 2 := by
    nlinarith [sq_nonneg
      (actualY1PaperFineCNormalizedChoiceTraceQ
        (radius : Real) globalDelta tGlobal pairScale - 1)]
  have hfactor : 2 <= prop41TangencyScaleFactor
      (actualY1PaperFineCNormalizedChoiceTraceQ
        (radius : Real) globalDelta tGlobal pairScale) := by
    rw [prop41TangencyScaleFactor]
    apply (le_div_iff₀ prop41TangencyProductCoefficient_pos).2
    have hc : prop41TangencyProductCoefficient <= 1 := by
      norm_num [prop41TangencyProductCoefficient]
    nlinarith
  have hlambda : 40 <=
      actualY1PaperFineCNormalizedChoiceLambda
        (radius : Real) globalDelta tGlobal pairScale := by
    rw [actualY1PaperFineCNormalizedChoiceLambda]
    nlinarith
  have hterm : 0 <=
      (pairScale /
          actualY1PaperFineCNormalizedChoiceLocalDelta
            (radius : Real) globalDelta tGlobal pairScale) *
        (4 *
          FamilyStickyCinematicL32Prop41ActualPairRectangleLensLocalizationV1.prop41ActualPairLocalizationRadius
              (4 * (2 * actualY1PaperFineCNormalizedChoiceLambda
                (radius : Real) globalDelta tGlobal pairScale))
              (actualY1PaperFineCNormalizedChoiceLocalDelta
                (radius : Real) globalDelta tGlobal pairScale)
              pairScale) ^ 2 := by
    exact mul_nonneg
      (div_nonneg (le_of_lt scales.choice_scale.pairScale_pos)
        (le_of_lt scales.choice_scale.localDelta_pos))
      (sq_nonneg _)
  unfold actualY1PaperFineCNormalizedAutomaticComparisonLambda
  unfold prop41AutomaticComparisonLambda
  nlinarith

/-- Deduplicated selected exact-local rectangles, ready for a same-right-C
aggregation layer. -/
noncomputable def actualGPrimeCNormalizedSelectedRectangleImage
    {radius : NNReal} {iota : Type u} [DecidableEq iota]
    {fineLabel : Type v} [DecidableEq fineLabel]
    (N : CanonicalNormNonconcentrationData iota)
    (D : CoarseRectangleIncidenceData (point := Real × Real)
      (radius := radius) (iota := iota) fineLabel)
    (keep : iota -> fineLabel -> Prop) (left right : iota)
    (ballRadius : Real)
    (omega : (N.family -> Fin 1) × (N.family -> Fin 1))
    (globalDelta tGlobal : Real)
    (selected : Finset (ActualGPrimeLabelFirstSurvivor
      N D keep left right ballRadius omega)) : Finset C2GraphRectangle :=
  selected.image
    (actualGPrimeCNormalizedRightCLocalCoverExactLocalRectangle N D keep
      left right ballRadius omega globalDelta tGlobal)

/-- Deduplicated pair-normalized left tubes.  No global load bound is claimed
for this image because normalization is pair-dependent. -/
noncomputable def actualGPrimeCNormalizedSelectedLeftTubeImage
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
    (P : ActualGPrimeLabelFirstCNormalizedPaperFineUniformPackage fine N D
      keep left right ballRadius omega f outerA outerB globalDelta tGlobal)
    (selected : Finset (ActualGPrimeLabelFirstSurvivor
      N D keep left right ballRadius omega)) : Finset (Tube radius) :=
  selected.image
    (actualGPrimeCNormalizedLeftTube fine N D keep left right ballRadius omega
      f outerA outerB globalDelta tGlobal P)

/-- Deduplicated ordinary right tubes, the canonical carrier for later
same-right-C union and cross-C disjointness. -/
noncomputable def actualGPrimeCNormalizedSelectedRightTubeImage
    {radius : NNReal} {iota : Type u} [DecidableEq iota]
    {fineLabel : Type v} [DecidableEq fineLabel]
    (fine : UniformTubeFamily radius iota)
    (N : CanonicalNormNonconcentrationData iota)
    (D : CoarseRectangleIncidenceData (point := Real × Real)
      (radius := radius) (iota := iota) fineLabel)
    (keep : iota -> fineLabel -> Prop) (left right : iota)
    (ballRadius : Real)
    (omega : (N.family -> Fin 1) × (N.family -> Fin 1))
    (selected : Finset (ActualGPrimeLabelFirstSurvivor
      N D keep left right ballRadius omega)) : Finset (Tube radius) :=
  selected.image (fun a =>
    fine.tubes (actualGPrimeCNormalizedRightIndex
      N D keep left right ballRadius omega a))

/-- All three deduplicated selected images have cardinality at most the
selected survivor family. -/
theorem actualGPrimeCNormalizedSelectedImages_card_le
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
    (P : ActualGPrimeLabelFirstCNormalizedPaperFineUniformPackage fine N D
      keep left right ballRadius omega f outerA outerB globalDelta tGlobal)
    (selected : Finset (ActualGPrimeLabelFirstSurvivor
      N D keep left right ballRadius omega)) :
    (actualGPrimeCNormalizedSelectedRectangleImage N D keep left right
      ballRadius omega globalDelta tGlobal selected).card <= selected.card ∧
    (actualGPrimeCNormalizedSelectedLeftTubeImage fine N D keep left right
      ballRadius omega f outerA outerB globalDelta tGlobal P selected).card <=
        selected.card ∧
    (actualGPrimeCNormalizedSelectedRightTubeImage fine N D keep left right
      ballRadius omega selected).card <= selected.card := by
  exact ⟨Finset.card_image_le, Finset.card_image_le, Finset.card_image_le⟩

/-- Per occupied joint value, construct the local-compact/global-AtScales
selector and connect its first-hit owner masses to the explicit dilation
area.  The sole continuum input is a measurable source covered by this
fibre's exact-local rectangles. -/
theorem exists_actualGPrimeCNormalizedRightCLocalCoverFiber_twoCenter_localCompact
    {radius : NNReal} {iota : Type u} [DecidableEq iota]
    {fineLabel : Type v} [DecidableEq fineLabel]
    (fine : UniformTubeFamily radius iota)
    (physical : FiniteProjectedShading (Real × Real) iota)
    (E : Set (Real × Real))
    (Y1 : FiniteProjectedShading (Real × Real) iota)
    (fineLabels : Finset fineLabel) (pointAt : fineLabel -> Real × Real)
    (globalCenter : Tube radius)
    (tubeAt : Real × Real -> Tube radius)
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
    (P : ActualGPrimeLabelFirstCNormalizedPaperFineUniformPackage fine N D
      keep left right ballRadius omega f outerA outerB globalDelta tGlobal)
    (c : Real) (coverCenter : Tube radius)
    (hvalue : (c, coverCenter) ∈
      actualGPrimeCNormalizedRightCLocalCoverValues fine N D keep left right
        ballRadius omega f outerA outerB globalDelta tGlobal P pointAt tubeAt)
    (sourceSet : Set (Real × Real)) (hsource : MeasurableSet sourceSet)
    (hcover : forall x, x ∈ sourceSet ->
      exists a, a ∈
        actualGPrimeCNormalizedRightCLocalCoverUnderlyingFiber fine N D keep
          left right ballRadius omega f outerA outerB globalDelta tGlobal P
            pointAt tubeAt (c, coverCenter) ∧
        x ∈ (actualGPrimeCNormalizedRightCLocalCoverExactLocalRectangle N D
          keep left right ballRadius omega globalDelta tGlobal a).carrier
            (actualY1PaperFineCNormalizedChoiceLocalDelta
              (radius : Real) globalDelta tGlobal (4 * ballRadius)))
    (sharp : ActualY1SharpFineScaleNumerics
      (radius : Real) globalDelta tGlobal (outerB - outerA))
    (hsmall : ActualY1PaperFineCNormalizedThreeShiftPairScaleSmallness
      (radius : Real) globalDelta tGlobal (4 * ballRadius))
    (referenceScale : Real)
    (hparameter : forall z, z ∈ Icc outerA outerB -> |z| <= 1)
    (hfunction : forall z, z ∈ Icc outerA outerB -> |f z| <= 2)
    (hfirst : forall z, z ∈ Icc outerA outerB -> |f1 z| <= 2)
    (hsecond : forall z, z ∈ Icc outerA outerB -> |f2 z| <= 1 / 100) :
    let fiber :=
      actualGPrimeCNormalizedRightCLocalCoverUnderlyingFiber fine N D keep
        left right ballRadius omega f outerA outerB globalDelta tGlobal P
          pointAt tubeAt (c, coverCenter)
    let rectangleAt :=
      actualGPrimeCNormalizedRightCLocalCoverExactLocalRectangle N D keep
        left right ballRadius omega globalDelta tGlobal
    let delta := actualY1PaperFineCNormalizedChoiceLocalDelta
      (radius : Real) globalDelta tGlobal (4 * ballRadius)
    let localScale := 4 * ballRadius
    let localCenter := globalCenterFixedCommonCReference coverCenter c
      f f1 f2 hfDeriv hf1Deriv outerA outerB hOuter
    let referenceCenter := globalCenterFixedCommonCReference globalCenter c
      f f1 f2 hfDeriv hf1Deriv outerA outerB hOuter
    let domain := Icc outerA outerB
    let comparisonLambda :=
      actualY1PaperFineCNormalizedAutomaticComparisonLambda
        (radius := radius) globalDelta tGlobal (4 * ballRadius)
    let centerGap := (401 / 100 : Real) * (ballRadius + 6 * tGlobal)
    let curvatureRatio := twoCenterAutomaticCurvatureRatio
      localScale centerGap referenceScale
    let packingBound := pyzClosedNeighbourBound
      (pyzLemma312TwoScalePackingLambda comparisonLambda curvatureRatio)
    let area :=
      ENNReal.ofReal (2 * (pyzLemma312PackingLambda 100 * delta)) *
        ENNReal.ofReal
          (Real.sqrt
            (pyzLemma312PackingLambda 100 * delta / localScale))
    let weight := fun a =>
      volume (firstHitFineRectangleY2
        sourceSet fiber rectangleAt delta a)
    exists C :
      CompactC2TwoStageAtScalesTwoCenterLocalCompactOutcome fiber rectangleAt
        domain localCenter referenceCenter delta localScale referenceScale
          comparisonLambda curvatureRatio centerGap weight,
      C.selected.Nonempty ∧
      C.selected ⊆ fiber ∧
      (forall a, a ∈ C.selected ->
        tubeGraphC
            (actualGPrimeCNormalizedLeftTube fine N D keep left right
              ballRadius omega f outerA outerB globalDelta tGlobal P a) = c ∧
          tubeGraphC
            (fine.tubes (actualGPrimeCNormalizedRightIndex N D keep left
              right ballRadius omega a)) = c) ∧
      fiber.card =
        ∑ b ∈ C.pivots, ownerClusterCard fiber C.owner b ∧
      (C.pivots.card : ENNReal) <=
        packingBound * (C.selected.card : ENNReal) ∧
      volume sourceSet <= packingBound *
        ∑ b ∈ C.selected, ownerClusterMass fiber C.owner weight b ∧
      (forall b, b ∈ C.selected ->
        ownerClusterMass fiber C.owner weight b <= area) ∧
      volume sourceSet <=
        packingBound * (C.selected.card : ENNReal) * area := by
  dsimp only
  let fiber :=
    actualGPrimeCNormalizedRightCLocalCoverUnderlyingFiber fine N D keep
      left right ballRadius omega f outerA outerB globalDelta tGlobal P
        pointAt tubeAt (c, coverCenter)
  let rectangleAt :=
    actualGPrimeCNormalizedRightCLocalCoverExactLocalRectangle N D keep
      left right ballRadius omega globalDelta tGlobal
  let delta := actualY1PaperFineCNormalizedChoiceLocalDelta
    (radius : Real) globalDelta tGlobal (4 * ballRadius)
  let localScale := 4 * ballRadius
  let localCenter := globalCenterFixedCommonCReference coverCenter c
    f f1 f2 hfDeriv hf1Deriv outerA outerB hOuter
  let referenceCenter := globalCenterFixedCommonCReference globalCenter c
    f f1 f2 hfDeriv hf1Deriv outerA outerB hOuter
  let domain := Icc outerA outerB
  let comparisonLambda :=
    actualY1PaperFineCNormalizedAutomaticComparisonLambda
      (radius := radius) globalDelta tGlobal (4 * ballRadius)
  let centerGap := (401 / 100 : Real) * (ballRadius + 6 * tGlobal)
  let curvatureRatio := twoCenterAutomaticCurvatureRatio
    localScale centerGap referenceScale
  let packingBound := pyzClosedNeighbourBound
    (pyzLemma312TwoScalePackingLambda comparisonLambda curvatureRatio)
  let area :=
    ENNReal.ofReal (2 * (pyzLemma312PackingLambda 100 * delta)) *
      ENNReal.ofReal
        (Real.sqrt
          (pyzLemma312PackingLambda 100 * delta / localScale))
  let weight := fun a =>
    volume (firstHitFineRectangleY2 sourceSet fiber rectangleAt delta a)
  have hfiberSubset : fiber ⊆ P.selected := by
    simpa only [fiber] using
      actualGPrimeCNormalizedRightCLocalCoverUnderlyingFiber_subset fine N D
        keep left right ballRadius omega f outerA outerB globalDelta tGlobal P
          pointAt tubeAt (c, coverCenter)
  have hfiberNonempty : fiber.Nonempty := by
    simpa only [fiber] using
      actualGPrimeCNormalizedRightCLocalCoverUnderlyingFiber_nonempty fine N D
        keep left right ballRadius omega f outerA outerB globalDelta tGlobal P
          pointAt tubeAt (c, coverCenter) hvalue
  have hrawFiberNonempty :=
    actualY1RightCLocalCoverFiber_nonempty fine P.selected
      (actualGPrimeCNormalizedLabelAt N D keep left right ballRadius omega)
      (actualGPrimeCNormalizedRightIndex N D keep left right ballRadius omega)
      pointAt tubeAt ballRadius (c, coverCenter) hvalue
  have scales :=
    actualY1PaperFineCNormalizedAutomaticThreeShiftNumerics_of_pairScaleSmall
      sharp hsmall
  have hlocal : 0 < localScale := by
    simpa only [localScale] using scales.choice_scale.pairScale_pos
  have hdelta : 0 < delta := by
    simpa only [delta] using scales.choice_scale.localDelta_pos
  have hcomparison : 100 <= comparisonLambda := by
    simpa only [comparisonLambda] using
      actualY1PaperFineCNormalizedAutomaticComparisonLambda_ge_hundred
        sharp hsmall
  have hquarterSubset : centeredFractionIcc outerA outerB (1 / 4 : Real) ⊆
      Icc outerA outerB := by
    intro z hz
    rcases hz with ⟨hzLeft, hzRight⟩
    constructor <;>
      simp only [centeredFractionLeft, centeredFractionRight] at * <;>
      linarith
  have hbase : forall a, a ∈ fiber ->
      (rectangleAt a).rectangle.base ⊆ domain := by
    intro a ha z hz
    let Q := PerturbationReadyPairLocalActualLensRectangleData.toExactLocalRectangle
      (actualGPrimeCNormalizedSelected_data fine N D keep left right
        ballRadius omega f outerA outerB globalDelta tGlobal P a
          (hfiberSubset ha))
    have hleftOuter := hquarterSubset Q.data.left_mem_quarter
    have hrightOuter := hquarterSubset Q.data.right_mem_quarter
    exact ⟨hleftOuter.1.trans hz.1, hz.2.trans hrightOuter.2⟩
  have hsegment : forall a, a ∈ fiber ->
      forall b, b ∈ fiber ->
      forall x, x ∈ (rectangleAt a).rectangle.base ->
      forall y, y ∈ (rectangleAt b).rectangle.base ->
        [[x, y]] ⊆ domain := by
    intro a ha b hb x hx y hy
    exact uIcc_subset_Icc (hbase a ha hx) (hbase b hb hy)
  have hball : forall a, a ∈ fiber ->
      InPointwiseC2BallOn domain localCenter
        (rectangleAt a) (3 * localScale) := by
    intro a ha
    rcases Finset.mem_image.mp ha with ⟨b, hb, rfl⟩
    simpa only [domain, localCenter, rectangleAt, localScale] using
      actualGPrimeCNormalizedRightCLocalCoverFiber_hballLocal fine physical E
        Y1 fineLabels pointAt tubeAt f f1 f2 outerA outerB hOuter hfDeriv
          hf1Deriv tGlobal globalDelta facts hpointE N D hD keep left right
            ballRadius omega P sharp hsmall hparameter hfunction hfirst
              hsecond c coverCenter b hb
  have hcenterSecond : forall z, z ∈ domain ->
      |localCenter.second z - referenceCenter.second z| <= centerGap := by
    simpa only [domain, localCenter, referenceCenter, centerGap] using
      actualGPrimeCNormalizedRightCLocalCoverFiber_second_bridge fine E Y1
        fineLabels pointAt globalCenter tubeAt f f1 f2 outerA outerB hOuter
          hfDeriv hf1Deriv tGlobal pointSource hpointE (radius : Real)
            (prop41Y1PaperFineT (radius : Real) globalDelta tGlobal)
              globalDelta tGlobal N D hD keep left right ballRadius
                (by
                  dsimp only [localScale] at hlocal
                  nlinarith)
                omega globalDelta P c coverCenter hrawFiberNonempty hparameter
                  hfunction hfirst hsecond
  obtain ⟨C⟩ :=
    exists_compactC2_twoStage_greedy_clusteringAtScales_twoCenter_localCompact
      fiber rectangleAt domain localCenter referenceCenter
        (delta := delta) (localScale := localScale)
        (referenceScale := referenceScale)
        (comparisonLambda := comparisonLambda)
        (curvatureRatio := curvatureRatio) (centerGap := centerGap)
        weight hdelta hlocal hcomparison
        (twoCenterAutomaticCurvatureRatio_nonneg hlocal)
        (twoCenterAutomaticCurvatureRatio_budget hlocal)
        (by
          intro a _ha
          simp only [rectangleAt,
            actualGPrimeCNormalizedRightCLocalCoverExactLocalRectangle,
            actualY1RightCLocalCoverExactLocalRectangle,
            exactLocalC2GraphRectangle_length, delta, localScale])
        hbase hball hcenterSecond hsegment
  have hselectedSubsetFiber : C.selected ⊆ fiber :=
    C.selected_subset_pivots.trans C.pivots_subset
  have hcommon : forall a, a ∈ C.selected ->
      tubeGraphC
          (actualGPrimeCNormalizedLeftTube fine N D keep left right
            ballRadius omega f outerA outerB globalDelta tGlobal P a) = c ∧
        tubeGraphC
          (fine.tubes (actualGPrimeCNormalizedRightIndex N D keep left right
            ballRadius omega a)) = c := by
    intro a ha
    have hafiber := hselectedSubsetFiber ha
    constructor
    · exact
        actualGPrimeCNormalizedRightCLocalCoverUnderlyingFiber_leftGraphC
          fine N D keep left right ballRadius omega f outerA outerB
            globalDelta tGlobal P pointAt tubeAt c coverCenter a hafiber
    · exact actualY1RightCLocalCoverUnderlyingFiber_rightGraphC fine P.selected
        (actualGPrimeCNormalizedLabelAt N D keep left right ballRadius omega)
        (actualGPrimeCNormalizedRightIndex N D keep left right ballRadius omega)
        pointAt tubeAt ballRadius c coverCenter a hafiber
  have hmass :
      (∑ a ∈ fiber,
        volume (firstHitFineRectangleY2
          sourceSet fiber rectangleAt delta a)) = volume sourceSet :=
    sum_measure_firstHitFineRectangleY2_eq_source volume sourceSet fiber
      rectangleAt delta hsource hcover
  have hrawMass : volume sourceSet <= packingBound *
      ∑ b ∈ C.selected, ownerClusterMass fiber C.owner weight b := by
    calc
      volume sourceSet =
          ∑ a ∈ fiber,
            volume (firstHitFineRectangleY2
              sourceSet fiber rectangleAt delta a) := hmass.symm
      _ <= packingBound *
          ∑ b ∈ C.selected, ownerClusterMass fiber C.owner weight b := by
        simpa only [packingBound, weight] using
          C.raw_mass_le_selected_cluster_mass
  have hownerCap : forall b, b ∈ C.selected ->
      ownerClusterMass fiber C.owner weight b <= area := by
    intro b _hb
    simpa only [weight, area] using
      firstHitY2_ownerClusterMass_le_explicitDilationArea_twoCenterLocalCompact
        sourceSet fiber rectangleAt domain localCenter referenceCenter delta
          localScale referenceScale comparisonLambda curvatureRatio centerGap
            C hsource b
  have hvolumeCap : volume sourceSet <=
      packingBound * (C.selected.card : ENNReal) * area := by
    simpa only [packingBound, area, weight] using
      volume_source_le_neighbourBound_mul_selectedCard_mul_dilationArea_twoCenterLocalCompact
        sourceSet fiber rectangleAt domain localCenter referenceCenter delta
          localScale referenceScale comparisonLambda curvatureRatio centerGap
            C hsource hcover
  refine ⟨C, C.selected_nonempty hfiberNonempty, hselectedSubsetFiber,
    hcommon, C.card_partition, ?_, hrawMass, hownerCap, hvolumeCap⟩
  simpa only [packingBound] using C.pivot_card_le

#print axioms actualY1PaperFineCNormalizedAutomaticComparisonLambda_ge_hundred
#print axioms actualGPrimeCNormalizedSelectedImages_card_le
#print axioms exists_actualGPrimeCNormalizedRightCLocalCoverFiber_twoCenter_localCompact

end

end FamilyStickyCinematicL32Prop41ActualY1SamplingPaperFineGPrimeLabelFirstCNormalizedRightCLocalCoverTwoCenterLocalCompactOutcomeRepoV2V1
