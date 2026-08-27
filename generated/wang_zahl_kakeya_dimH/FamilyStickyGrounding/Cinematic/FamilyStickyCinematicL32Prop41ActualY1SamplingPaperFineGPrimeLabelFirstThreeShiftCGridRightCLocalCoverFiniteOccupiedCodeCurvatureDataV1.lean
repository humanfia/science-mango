import FamilyStickyGrounding.Cinematic.FamilyStickyCinematicL32FiniteOccupiedCodeLocalCompactThirdStageV1
import FamilyStickyGrounding.Cinematic.FamilyStickyCinematicL32Lemma312TwoCenterAutomaticCurvatureRatioV1
import FamilyStickyGrounding.Cinematic.FamilyStickyCinematicL32Prop41ActualY1SamplingPaperFineGPrimeLabelFirstCNormalizedRightCLocalCoverTwoCenterLocalCompactOutcomeRepoV2V1
import FamilyStickyGrounding.Cinematic.FamilyStickyCinematicL32Prop41ActualY1SamplingPaperFineGPrimeLabelFirstThreeShiftCGridRightCLocalCoverFixedCCodePackingAdapterV1
import Mathlib.Tactic

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 8000000

open Set
open scoped ENNReal Interval

namespace FamilyStickyCinematicL32Prop41ActualY1SamplingPaperFineGPrimeLabelFirstThreeShiftCGridRightCLocalCoverFiniteOccupiedCodeCurvatureDataV1

open Submission.Kakeya.ConvexGeometry
open Submission.Kakeya.Uniformity
open FamilyStickyWZ2TubeCarrierCoordinateAdapterV1
open FamilyStickyCinematicL32ActualProjectedCenteredHalfPointSourceV1
open FamilyStickyCinematicL32ActualProjectedCenteredHalfY1ActiveGeometryV1
open FamilyStickyCinematicL32CenteredFractionIntervalsV1
open FamilyStickyCinematicL32CurvilinearRectanglePointMultiplicityV1
open FamilyStickyCinematicL32FiniteOccupiedCodeLocalCompactThirdStageV1
open FamilyStickyCinematicL32FiniteProjectedShadingMultiplicitySliceV1
open FamilyStickyCinematicL32Lemma312TwoCenterAutomaticCurvatureRatioV1
open FamilyStickyCinematicL32Lemma315ExternalContainerCurvatureRatioNumericsV1
open FamilyStickyCinematicL32Prop41ActualY1FineCoarseRectangleProducerV1
open FamilyStickyCinematicL32Prop41ActualY1GridRightCLocalCoverSelectedGenericV1
open FamilyStickyCinematicL32Prop41ActualY1GridRightCLocalCoverFixedCCodePackingV1
open FamilyStickyCinematicL32Prop41ActualY1PaperFineCNormalizedThreeShiftScaleProducerV1
open FamilyStickyCinematicL32Prop41ActualY1RightCLocalCoverSelectedGenericV1
open FamilyStickyCinematicL32Prop41ActualY1SamplingPaperFineGPrimeLabelFirstCNormalizedRightCLocalCoverTwoCenterLocalCompactOutcomeRepoV2V1
open FamilyStickyCinematicL32Prop41ActualY1SamplingPaperFineGPrimeLabelFirstProvenanceV1
open FamilyStickyCinematicL32Prop41ActualY1SamplingPaperFineGPrimeLabelFirstThreeShiftCGridRightCLocalCoverFixedCCodePackingAdapterV1
open FamilyStickyCinematicL32Prop41ActualY1SamplingPaperFineGPrimeLabelFirstThreeShiftCGridRightCLocalCoverTwoCenterBridgeV1
open FamilyStickyCinematicL32Prop41ActualY1SamplingPaperFineGPrimeLabelFirstThreeShiftCGridUniformPackageV1
open FamilyStickyCinematicL32Prop41ActualY1SharpFineScaleTangencyV1
open FamilyStickyCinematicL32Prop41CanonicalMaximizerNonconcentrationV1
open FamilyStickyCinematicL32Prop41CoarseRectangleIncidenceDataV1
open FamilyStickyCinematicL32Prop41ExactLocalRectangleRestrictionV1
open FamilyStickyCinematicL32Prop41GlobalScaleNearFiberPackingV1
open FamilyStickyCinematicL32Prop41SharpCommonCReferenceV1
open FamilyStickyCinematicL32ThinReferenceCompactDomainC2BallV1
open FamilyStickyCinematicL32TubePairTraceV1

noncomputable section

local instance c2GraphRectangleDecidableEq : DecidableEq C2GraphRectangle :=
  Classical.decEq _

local instance tubeDecidableEq {radius : NNReal} :
    DecidableEq (Tube radius) := Classical.decEq _

universe u v

/-!
# Curvature data over all occupied source-cover codes in one grid C fibre

The outer key `c` remains the literal normalized endpoint C.  Inside that
outer fibre, codes are the canonical source-cover centres.  The raw item
fibres therefore partition selected pairs, whereas code cardinality is
controlled by the single global maximal source cover.
-/

/-- Occupied source-cover codes at one fixed normalized C, as a finite type. -/
abbrev ActualGPrimeThreeShiftCGridFixedCCode
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
    (pointAt : fineLabel -> Real × Real)
    (tubeAt : Real × Real -> Tube radius) (c : Real) :=
  {coverCenter : Tube radius //
    coverCenter ∈
      actualGPrimeThreeShiftCGridRightCLocalCoverSourceCodesAtC fine N D keep
        left right ballRadius omega f outerA outerB globalDelta tGlobal P
          pointAt tubeAt c}

/-- The underlying selected-item fibre at an occupied source-cover code. -/
noncomputable def actualGPrimeThreeShiftCGridFixedCRawAt
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
    (pointAt : fineLabel -> Real × Real)
    (tubeAt : Real × Real -> Tube radius) (c : Real) :
    ActualGPrimeThreeShiftCGridFixedCCode fine N D keep left right ballRadius
      omega f outerA outerB globalDelta tGlobal P pointAt tubeAt c ->
      Finset (ActualGPrimeLabelFirstSurvivor
        N D keep left right ballRadius omega) :=
  fun k => actualY1GridRightCLocalCoverUnderlyingFiber P.selected
    (actualGPrimeLabelFirstLabel N D keep left right ballRadius omega)
    (actualGPrimeLabelFirstThreeShiftCGridRightTube N D keep left right
      ballRadius omega P.gridLabel)
    pointAt tubeAt ballRadius (c, k.1)

/-- The package source rectangle, restricted at the C-normalized local
delta and the fixed local scale `4 * ballRadius`. -/
def actualGPrimeThreeShiftCGridLocalCompactRectangleAt
    {radius : NNReal} {iota : Type u} [DecidableEq iota]
    {fineLabel : Type v} [DecidableEq fineLabel]
    (N : CanonicalNormNonconcentrationData iota)
    (D : CoarseRectangleIncidenceData (point := Real × Real)
      (radius := radius) (iota := iota) fineLabel)
    (keep : iota -> fineLabel -> Prop) (left right : iota)
    (ballRadius : Real)
    (omega : (N.family -> Fin 1) × (N.family -> Fin 1))
    (globalDelta tGlobal : Real) :
    ActualGPrimeLabelFirstSurvivor N D keep left right ballRadius omega ->
      C2GraphRectangle :=
  actualY1GridRightCLocalCoverExactLocalRectangle D
    (actualGPrimeLabelFirstLabel N D keep left right ballRadius omega)
    (actualY1PaperFineCNormalizedChoiceLocalDelta
      (radius : Real) globalDelta tGlobal (4 * ballRadius))
    (4 * ballRadius)

/-- Local common-C reference attached to one source-cover code. -/
def actualGPrimeThreeShiftCGridFixedCLocalCenterAt
    {radius : NNReal} {iota : Type u} [DecidableEq iota]
    {fineLabel : Type v} [DecidableEq fineLabel]
    (fine : UniformTubeFamily radius iota)
    (N : CanonicalNormNonconcentrationData iota)
    (D : CoarseRectangleIncidenceData (point := Real × Real)
      (radius := radius) (iota := iota) fineLabel)
    (keep : iota -> fineLabel -> Prop) (left right : iota)
    (ballRadius : Real)
    (omega : (N.family -> Fin 1) × (N.family -> Fin 1))
    (f f1 f2 : Real -> Real) (outerA outerB : Real) (hOuter : outerA <= outerB)
    (hfDeriv : forall z, HasDerivAt f (f1 z) z)
    (hf1Deriv : forall z, HasDerivAt f1 (f2 z) z)
    (globalDelta tGlobal : Real)
    (P : ActualGPrimeLabelFirstThreeShiftCGridPaperFineUniformPackage fine N D
      keep left right ballRadius omega f outerA outerB globalDelta tGlobal)
    (pointAt : fineLabel -> Real × Real)
    (tubeAt : Real × Real -> Tube radius) (c : Real) :
    ActualGPrimeThreeShiftCGridFixedCCode fine N D keep left right ballRadius
      omega f outerA outerB globalDelta tGlobal P pointAt tubeAt c ->
      C2GraphRectangle :=
  fun k => globalCenterFixedCommonCReference k.1 c f f1 f2 hfDeriv
    hf1Deriv outerA outerB hOuter

/-- The package-specific finite occupied-code curvature datum consumed by
the canonical three-stage local-compact selector. -/
theorem actualGPrimeThreeShiftCGridRightCLocalCover_finiteOccupiedCodeLocalCompactCurvatureData
    {radius : NNReal} {iota : Type u} [DecidableEq iota]
    {fineLabel : Type v} [DecidableEq fineLabel]
    (fine : UniformTubeFamily radius iota)
    (physical : FiniteProjectedShading (Real × Real) iota)
    (E : Set (Real × Real))
    (Y1 : FiniteProjectedShading (Real × Real) iota)
    (fineLabels : Finset fineLabel) (pointAt : fineLabel -> Real × Real)
    (globalCenter : Tube radius) (tubeAt : Real × Real -> Tube radius)
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
    (P : ActualGPrimeLabelFirstThreeShiftCGridPaperFineUniformPackage fine N D
      keep left right ballRadius omega f outerA outerB globalDelta tGlobal)
    (c : Real)
    (sharp : ActualY1SharpFineScaleNumerics
      (radius : Real) globalDelta tGlobal (outerB - outerA))
    (hsmall : ActualY1PaperFineCNormalizedThreeShiftPairScaleSmallness
      (radius : Real) globalDelta tGlobal (4 * ballRadius))
    (referenceScale : Real) (hreferenceScale : 0 <= referenceScale)
    (hparameter : forall z, z ∈ Icc outerA outerB -> |z| <= 1)
    (hfunction : forall z, z ∈ Icc outerA outerB -> |f z| <= 2)
    (hfirst : forall z, z ∈ Icc outerA outerB -> |f1 z| <= 2)
    (hsecond : forall z, z ∈ Icc outerA outerB -> |f2 z| <= 1 / 100) :
    FiniteOccupiedCodeLocalCompactCurvatureData
      (actualGPrimeThreeShiftCGridFixedCRawAt fine N D keep left right
        ballRadius omega f outerA outerB globalDelta tGlobal P pointAt tubeAt c)
      (actualGPrimeThreeShiftCGridLocalCompactRectangleAt N D keep left right
        ballRadius omega globalDelta tGlobal)
      (Icc outerA outerB)
      (actualGPrimeThreeShiftCGridFixedCLocalCenterAt fine N D keep left right
        ballRadius omega f f1 f2 outerA outerB hOuter hfDeriv hf1Deriv
          globalDelta tGlobal P pointAt tubeAt c)
      (globalCenterFixedCommonCReference globalCenter c f f1 f2 hfDeriv
        hf1Deriv outerA outerB hOuter)
      (actualY1PaperFineCNormalizedChoiceLocalDelta
        (radius : Real) globalDelta tGlobal (4 * ballRadius))
      (4 * ballRadius) referenceScale
      (actualY1PaperFineCNormalizedAutomaticComparisonLambda
        (radius := radius) globalDelta tGlobal (4 * ballRadius))
      (twoCenterAutomaticCurvatureRatio (4 * ballRadius)
        ((401 / 100 : Real) * (ballRadius + 6 * tGlobal)) referenceScale)
      ((401 / 100 : Real) * (ballRadius + 6 * tGlobal))
      (twoCenterAutomaticCurvatureRatio (4 * ballRadius)
        ((401 / 100 : Real) * (ballRadius + 6 * tGlobal)) referenceScale)
      (projectedCoefficientPackingCap ballRadius
        (2 * (ballRadius + 6 * tGlobal)) : ENNReal) := by
  let rawAt := actualGPrimeThreeShiftCGridFixedCRawAt fine N D keep left right
    ballRadius omega f outerA outerB globalDelta tGlobal P pointAt tubeAt c
  let rectangleAt := actualGPrimeThreeShiftCGridLocalCompactRectangleAt N D
    keep left right ballRadius omega globalDelta tGlobal
  let localCenterAt := actualGPrimeThreeShiftCGridFixedCLocalCenterAt fine N D
    keep left right ballRadius omega f f1 f2 outerA outerB hOuter hfDeriv
      hf1Deriv globalDelta tGlobal P pointAt tubeAt c
  let delta := actualY1PaperFineCNormalizedChoiceLocalDelta
    (radius : Real) globalDelta tGlobal (4 * ballRadius)
  let localScale := 4 * ballRadius
  let comparisonLambda :=
    actualY1PaperFineCNormalizedAutomaticComparisonLambda
      (radius := radius) globalDelta tGlobal (4 * ballRadius)
  let centerGap := (401 / 100 : Real) * (ballRadius + 6 * tGlobal)
  let curvatureRatio := twoCenterAutomaticCurvatureRatio
    localScale centerGap referenceScale
  let codeBound : ENNReal := projectedCoefficientPackingCap ballRadius
    (2 * (ballRadius + 6 * tGlobal))
  have scales :=
    actualY1PaperFineCNormalizedAutomaticThreeShiftNumerics_of_pairScaleSmall
      sharp hsmall
  have hlocal : 0 < localScale := by
    simpa only [localScale] using scales.choice_scale.pairScale_pos
  have hballRadius : 0 < ballRadius := by
    dsimp only [localScale] at hlocal
    nlinarith
  have hdelta : 0 < delta := by
    simpa only [delta] using scales.choice_scale.localDelta_pos
  have hcomparison : 100 <= comparisonLambda := by
    simpa only [comparisonLambda] using
      actualY1PaperFineCNormalizedAutomaticComparisonLambda_ge_hundred
        sharp hsmall
  have hcurvature : 0 <= curvatureRatio := by
    exact twoCenterAutomaticCurvatureRatio_nonneg hlocal
  have hratio : 3 * localScale + centerGap + 3 * referenceScale <=
      curvatureRatio * localScale := by
    exact twoCenterAutomaticCurvatureRatio_budget hlocal
  have hcenterGap : 0 <= centerGap := by
    dsimp only [centerGap]
    exact mul_nonneg (by norm_num) (by nlinarith [hballRadius, sharp.tGlobal_pos])
  have hcodeNat :
      (actualGPrimeThreeShiftCGridRightCLocalCoverSourceCodesAtC fine N D keep
        left right ballRadius omega f outerA outerB globalDelta tGlobal P
          pointAt tubeAt c).card <
        projectedCoefficientPackingCap ballRadius
          (2 * (ballRadius + 6 * tGlobal)) := by
    exact
      actualGPrimeThreeShiftCGridRightCLocalCoverSourceCodesAtC_card_lt_packingCap
        fine E Y1 fineLabels pointAt globalCenter tubeAt f f1 f2 outerA
          outerB hfDeriv hf1Deriv tGlobal pointSource hpointE (radius : Real)
            (prop41Y1PaperFineT (radius : Real) globalDelta tGlobal)
              globalDelta tGlobal N D hD keep left right ballRadius
                hballRadius omega globalDelta P (by
                  nlinarith [sharp.tGlobal_pos]) c
  have hquarterSubset : centeredFractionIcc outerA outerB (1 / 4 : Real) ⊆
      Icc outerA outerB := by
    intro z hz
    rcases hz with ⟨hzLeft, hzRight⟩
    constructor <;>
      simp only [centeredFractionLeft, centeredFractionRight] at * <;>
      linarith
  have hrawSubset : forall k, rawAt k ⊆ P.selected := by
    intro k
    simpa only [rawAt, actualGPrimeThreeShiftCGridFixedCRawAt] using
      actualY1GridRightCLocalCoverUnderlyingFiber_subset P.selected
        (actualGPrimeLabelFirstLabel N D keep left right ballRadius omega)
        (actualGPrimeLabelFirstThreeShiftCGridRightTube N D keep left right
          ballRadius omega P.gridLabel)
        pointAt tubeAt ballRadius (c, k.1)
  have hDfine : D.fine = fine := by
    simp only [hD, y1FineCoarseRectangleData]
  have hbase : forall k, forall b, b ∈ rawAt k ->
      (rectangleAt b).rectangle.base ⊆ Icc outerA outerB := by
    intro k b hb z hz
    let Q :=
      PerturbationReadyPairLocalActualLensRectangleData.toExactLocalRectangle
        (P.data b (hrawSubset k hb))
    have hleftOuter := hquarterSubset Q.data.left_mem_quarter
    have hrightOuter := hquarterSubset Q.data.right_mem_quarter
    exact ⟨hleftOuter.1.trans hz.1, hz.2.trans hrightOuter.2⟩
  refine {
    code_card := ?_
    delta_pos := hdelta
    localScale_pos := hlocal
    comparisonLambda_ge := hcomparison
    curvatureRatio_nonneg := hcurvature
    scale_ratio := hratio
    centerGap_nonneg := hcenterGap
    externalRatio_nonneg := hcurvature
    external_gap := ?_
    length := ?_
    base := hbase
    local_ball := ?_
    center_second := ?_
    segment_domain := ?_ }
  · change (Fintype.card
      (ActualGPrimeThreeShiftCGridFixedCCode fine N D keep left right
        ballRadius omega f outerA outerB globalDelta tGlobal P pointAt tubeAt
          c) : ENNReal) <= codeBound
    rw [show Fintype.card
        (ActualGPrimeThreeShiftCGridFixedCCode fine N D keep left right
          ballRadius omega f outerA outerB globalDelta tGlobal P pointAt
            tubeAt c) =
          (actualGPrimeThreeShiftCGridRightCLocalCoverSourceCodesAtC fine N D
            keep left right ballRadius omega f outerA outerB globalDelta
              tGlobal P pointAt tubeAt c).card by
        exact Fintype.card_coe _]
    dsimp only [codeBound]
    exact_mod_cast hcodeNat.le
  · exact six_mul_t_add_two_mul_centerGap_le_two_mul_ratio_mul_t
      hreferenceScale hratio
  · intro k b _hb
    simp only [actualGPrimeThreeShiftCGridLocalCompactRectangleAt,
      actualY1GridRightCLocalCoverExactLocalRectangle,
      actualY1RightCLocalCoverExactLocalRectangle,
      exactLocalC2GraphRectangle_length]
  · intro k b hb
    rcases Finset.mem_image.mp hb with ⟨a, ha, rfl⟩
    simpa only [rawAt, localCenterAt, rectangleAt, localScale,
      actualGPrimeThreeShiftCGridFixedCRawAt,
      actualGPrimeThreeShiftCGridFixedCLocalCenterAt,
      actualGPrimeThreeShiftCGridLocalCompactRectangleAt] using
      actualY1GridRightCLocalCoverFiber_hballLocal fine physical E Y1
        fineLabels pointAt tubeAt f f1 f2 outerA outerB hOuter hfDeriv
          hf1Deriv tGlobal globalDelta facts hpointE (radius : Real)
            (prop41Y1PaperFineT (radius : Real) globalDelta tGlobal)
              globalDelta tGlobal D hD keep P.selected
                (actualGPrimeLabelFirstLabel N D keep left right ballRadius
                  omega)
                (actualGPrimeLabelFirstRightIndex N D keep left right
                  ballRadius omega)
                (actualGPrimeLabelFirstThreeShiftCGridRightTube N D keep left
                  right ballRadius omega P.gridLabel)
                P.right_retained (fun a ha => by
                  have hgap := P.raw_right_c_gap a ha
                  rw [hDfine] at hgap
                  exact hgap) delta ballRadius
                  hballRadius
                  (three_halves_radius_le_eight_ballRadius_of_cNormalizedThreeShiftSmall
                    sharp hsmall)
                  hparameter hfunction hfirst hsecond c k.1 a ha
  · intro k z hz
    have hvalue : (c, k.1) ∈
        actualGPrimeThreeShiftCGridRightCLocalCoverValues fine N D keep left
          right ballRadius omega f outerA outerB globalDelta tGlobal P
            pointAt tubeAt := by
      exact
        (mem_actualY1GridRightCLocalCoverSourceCodesAtC_iff P.selected
          (actualGPrimeLabelFirstLabel N D keep left right ballRadius omega)
          (actualGPrimeLabelFirstThreeShiftCGridRightTube N D keep left right
            ballRadius omega P.gridLabel)
          pointAt tubeAt ballRadius c k.1).mp k.2
    have hfiber :
        (actualGPrimeThreeShiftCGridRightCLocalCoverFiber fine N D keep left
          right ballRadius omega f outerA outerB globalDelta tGlobal P
            pointAt tubeAt (c, k.1)).Nonempty := by
      simpa only [actualGPrimeThreeShiftCGridRightCLocalCoverFiber] using
        actualY1GridRightCLocalCoverFiber_nonempty P.selected
          (actualGPrimeLabelFirstLabel N D keep left right ballRadius omega)
          (actualGPrimeLabelFirstThreeShiftCGridRightTube N D keep left right
            ballRadius omega P.gridLabel)
          pointAt tubeAt ballRadius (c, k.1) hvalue
    simpa only [localCenterAt, centerGap,
      actualGPrimeThreeShiftCGridFixedCLocalCenterAt] using
      actualGPrimeThreeShiftCGridRightCLocalCoverFiber_second_bridge fine E Y1
        fineLabels pointAt globalCenter tubeAt f f1 f2 outerA outerB hOuter
          hfDeriv hf1Deriv tGlobal pointSource hpointE (radius : Real)
            (prop41Y1PaperFineT (radius : Real) globalDelta tGlobal)
              globalDelta tGlobal N D hD keep left right ballRadius
                hballRadius omega globalDelta P c k.1 hfiber hparameter
                  hfunction hfirst hsecond z hz
  · intro kp p hp k b hb x hx y hy
    exact uIcc_subset_Icc (hbase kp p hp hx) (hbase k b hb hy)

#print axioms actualGPrimeThreeShiftCGridRightCLocalCover_finiteOccupiedCodeLocalCompactCurvatureData

end

end FamilyStickyCinematicL32Prop41ActualY1SamplingPaperFineGPrimeLabelFirstThreeShiftCGridRightCLocalCoverFiniteOccupiedCodeCurvatureDataV1
