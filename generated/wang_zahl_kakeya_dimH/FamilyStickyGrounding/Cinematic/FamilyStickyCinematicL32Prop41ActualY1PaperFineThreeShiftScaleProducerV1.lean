import FamilyStickyGrounding.Cinematic.FamilyStickyCinematicL32Prop41ActualY1RetainedThreeShiftPerturbationReadyV1

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 2000000

namespace FamilyStickyCinematicL32Prop41ActualY1PaperFineThreeShiftScaleProducerV1

open Set
open Submission.Kakeya.ConvexGeometry
open Submission.Kakeya.Uniformity
open FamilyStickyCinematicL32ActualTubeConstantShiftV1
open FamilyStickyCinematicL32ActualProjectedCenteredHalfPointSourceV1
open FamilyStickyCinematicL32ActualProjectedCenteredHalfY1ActiveGeometryV1
open FamilyStickyCinematicL32FiniteProjectedShadingMultiplicitySliceV1
open FamilyStickyCinematicL32Prop41ActualChoiceOfShiftPairLocalBridgeV1
open FamilyStickyCinematicL32Prop41ActualY1FineCoarseRectangleProducerV1
open FamilyStickyCinematicL32Prop41ActualY1RetainedThreeShiftPerturbationReadyV1
open FamilyStickyCinematicL32Prop41ActualY1SharpFineScaleTangencyV1
open FamilyStickyCinematicL32Prop41CoarseRectangleIncidenceDataV1
open FamilyStickyCinematicL32Prop41FiniteGeneralPositionExactRootReproductionV1
open FamilyStickyCinematicL32Prop41TangencyProductToScaleV1
open FamilyStickyCinematicL32Prop41ThreeShiftPigeonholeV1

noncomputable section

universe u v w

/-!
# Automatic scalar choices for the actual Y1 three-shift lane

The paper fine rectangle has thickness `fineDelta` and squared horizontal
scale `fineDelta / fineT`.  A choice-of-shift rectangle with coefficient
scale `pairScale` therefore needs
`localDelta / pairScale <= fineDelta / fineT`.  At the same time, upgrading
the proved `5 * fineDelta` tangency requires
`5 * fineDelta <= rho * localDelta`.

The harmonic choice below pays both constraints without a case split and
loses at most a factor two from their largest possible common scale.  It
makes all `rho`, `q`, and `lambda` bookkeeping automatic.  The one honest
remaining hypothesis is a small-radius comparison with `pairScale`; the
strong paper-shaped version has `pairScale` itself on the right-hand side.
-/

/-- Positive denominator shared by all automatic choices. -/
def actualY1PaperFineChoiceDenominator
    (fineDelta globalDelta tGlobal pairScale : Real) : Real :=
  prop41Y1PaperFineT fineDelta globalDelta tGlobal + pairScale

/-- Harmonic local thickness simultaneously adapted to the literal paper
fine rectangle and the selected pair coefficient scale. -/
def actualY1PaperFineChoiceLocalDelta
    (fineDelta globalDelta tGlobal pairScale : Real) : Real :=
  fineDelta * pairScale /
    actualY1PaperFineChoiceDenominator fineDelta globalDelta tGlobal pairScale

/-- Minimal tangency enlargement for the harmonic local thickness. -/
def actualY1PaperFineChoiceRho
    (fineDelta globalDelta tGlobal pairScale : Real) : Real :=
  5 * actualY1PaperFineChoiceDenominator
    fineDelta globalDelta tGlobal pairScale / pairScale

/-- Trace tolerance exactly twice the tangency enlargement. -/
def actualY1PaperFineChoiceTraceQ
    (fineDelta globalDelta tGlobal pairScale : Real) : Real :=
  2 * actualY1PaperFineChoiceRho
    fineDelta globalDelta tGlobal pairScale

/-- Shift enlargement with a factor-two strict margin over the required
`10 * prop41TangencyScaleFactor q`. -/
def actualY1PaperFineChoiceLambda
    (fineDelta globalDelta tGlobal pairScale : Real) : Real :=
  20 * prop41TangencyScaleFactor
    (actualY1PaperFineChoiceTraceQ
      fineDelta globalDelta tGlobal pairScale)

/-- The exact denominator-free radius condition for the harmonic choices.
It is equivalent to the downstream strengthened-scale inequality after
cancelling the positive `pairScale` and common denominator. -/
def ActualY1PaperFineThreeShiftRadiusSmallness
    (fineDelta globalDelta tGlobal pairScale : Real) : Prop :=
  46080 *
      (10 * prop41TangencyScaleFactor
          (actualY1PaperFineChoiceTraceQ
            fineDelta globalDelta tGlobal pairScale) +
        actualY1PaperFineChoiceLambda
          fineDelta globalDelta tGlobal pairScale) * fineDelta <
    actualY1PaperFineChoiceDenominator
      fineDelta globalDelta tGlobal pairScale

/-- A simpler and stronger paper-shaped input: the fine radius, after all
fixed three-shift losses, is smaller than the selected pair scale itself.
Unlike the downstream condition, this has no `localDelta` or division on
the right-hand side. -/
def ActualY1PaperFineThreeShiftPairScaleSmallness
    (fineDelta globalDelta tGlobal pairScale : Real) : Prop :=
  46080 *
      (10 * prop41TangencyScaleFactor
          (actualY1PaperFineChoiceTraceQ
            fineDelta globalDelta tGlobal pairScale) +
        actualY1PaperFineChoiceLambda
          fineDelta globalDelta tGlobal pairScale) * fineDelta <
    pairScale

/-- All scalar facts consumed by
`exists_uniform_threeShift_perturbationReady_of_actualRetainedY1Pairs`, for
the literal automatic choices above. -/
structure ActualY1PaperFineAutomaticThreeShiftNumerics
    (fineDelta globalDelta tGlobal pairScale : Real) : Prop where
  choice_scale : ActualY1PaperFineChoiceScaleNumerics
    fineDelta globalDelta tGlobal
    (actualY1PaperFineChoiceLocalDelta
      fineDelta globalDelta tGlobal pairScale)
    pairScale
    (actualY1PaperFineChoiceRho
      fineDelta globalDelta tGlobal pairScale)
  traceQ_one : 1 <= actualY1PaperFineChoiceTraceQ
    fineDelta globalDelta tGlobal pairScale
  lambda_pos : 0 < actualY1PaperFineChoiceLambda
    fineDelta globalDelta tGlobal pairScale
  rho_le_lambda : actualY1PaperFineChoiceRho
      fineDelta globalDelta tGlobal pairScale <=
    actualY1PaperFineChoiceLambda
      fineDelta globalDelta tGlobal pairScale
  shift_dominates :
    10 * prop41TangencyScaleFactor
        (actualY1PaperFineChoiceTraceQ
          fineDelta globalDelta tGlobal pairScale) <
      actualY1PaperFineChoiceLambda
        fineDelta globalDelta tGlobal pairScale
  strengthened_scale :
    (10 * prop41TangencyScaleFactor
          (actualY1PaperFineChoiceTraceQ
            fineDelta globalDelta tGlobal pairScale) +
        actualY1PaperFineChoiceLambda
          fineDelta globalDelta tGlobal pairScale) *
        actualY1PaperFineChoiceLocalDelta
          fineDelta globalDelta tGlobal pairScale <
      pairScale / 46080
  trace_radius :
    2 * (actualY1PaperFineChoiceRho
          fineDelta globalDelta tGlobal pairScale *
        actualY1PaperFineChoiceLocalDelta
          fineDelta globalDelta tGlobal pairScale) <=
      actualY1PaperFineChoiceTraceQ
          fineDelta globalDelta tGlobal pairScale *
        actualY1PaperFineChoiceLocalDelta
          fineDelta globalDelta tGlobal pairScale

theorem actualY1PaperFineChoiceDenominator_pos
    {fineDelta globalDelta tGlobal outerWidth pairScale : Real}
    (N : ActualY1SharpFineScaleNumerics
      fineDelta globalDelta tGlobal outerWidth)
    (hpairScale : 0 < pairScale) :
    0 < actualY1PaperFineChoiceDenominator
      fineDelta globalDelta tGlobal pairScale := by
  exact add_pos (prop41Y1PaperFineT_pos N) hpairScale

theorem prop41TangencyScaleFactor_pos_of_pos
    {q : Real} (hq : 0 < q) :
    0 < prop41TangencyScaleFactor q := by
  rw [prop41TangencyScaleFactor]
  exact div_pos (mul_pos (by norm_num) (sq_pos_of_pos hq))
    prop41TangencyProductCoefficient_pos

theorem q_le_prop41TangencyScaleFactor_of_one_le
    {q : Real} (hq : 1 <= q) :
    q <= prop41TangencyScaleFactor q := by
  have hqNonneg : 0 <= q := by linarith
  have hcoefficientLeOne :
      prop41TangencyProductCoefficient <= 1 := by
    norm_num [prop41TangencyProductCoefficient]
  have hqMul : q * prop41TangencyProductCoefficient <= q := by
    nlinarith [mul_nonneg hqNonneg
      (sub_nonneg.mpr hcoefficientLeOne)]
  have hqSquare : q <= q ^ 2 := by nlinarith
  rw [prop41TangencyScaleFactor]
  apply (le_div_iff₀ prop41TangencyProductCoefficient_pos).2
  calc
    q * prop41TangencyProductCoefficient <= q := hqMul
    _ <= q ^ 2 := hqSquare
    _ <= 20000 * q ^ 2 := by nlinarith [sq_nonneg q]

theorem actualY1PaperFineChoiceLocalDelta_pos
    {fineDelta globalDelta tGlobal outerWidth pairScale : Real}
    (N : ActualY1SharpFineScaleNumerics
      fineDelta globalDelta tGlobal outerWidth)
    (hpairScale : 0 < pairScale) :
    0 < actualY1PaperFineChoiceLocalDelta
      fineDelta globalDelta tGlobal pairScale := by
  exact div_pos (mul_pos N.fineDelta_pos hpairScale)
    (actualY1PaperFineChoiceDenominator_pos N hpairScale)

theorem actualY1PaperFineChoiceLocalDelta_le_fineDelta
    {fineDelta globalDelta tGlobal outerWidth pairScale : Real}
    (N : ActualY1SharpFineScaleNumerics
      fineDelta globalDelta tGlobal outerWidth)
    (hpairScale : 0 < pairScale) :
    actualY1PaperFineChoiceLocalDelta
        fineDelta globalDelta tGlobal pairScale <= fineDelta := by
  rw [actualY1PaperFineChoiceLocalDelta]
  apply (div_le_iff₀
    (actualY1PaperFineChoiceDenominator_pos N hpairScale)).2
  rw [actualY1PaperFineChoiceDenominator]
  nlinarith [mul_pos N.fineDelta_pos (prop41Y1PaperFineT_pos N)]

theorem actualY1PaperFineChoice_retainedTangencyBudget
    {fineDelta globalDelta tGlobal outerWidth pairScale : Real}
    (N : ActualY1SharpFineScaleNumerics
      fineDelta globalDelta tGlobal outerWidth)
    (hpairScale : 0 < pairScale) :
    5 * fineDelta <=
      actualY1PaperFineChoiceRho
          fineDelta globalDelta tGlobal pairScale *
        actualY1PaperFineChoiceLocalDelta
          fineDelta globalDelta tGlobal pairScale := by
  have hdenominator :=
    actualY1PaperFineChoiceDenominator_pos N hpairScale
  have heq :
      actualY1PaperFineChoiceRho
          fineDelta globalDelta tGlobal pairScale *
        actualY1PaperFineChoiceLocalDelta
          fineDelta globalDelta tGlobal pairScale =
      5 * fineDelta := by
    unfold actualY1PaperFineChoiceRho
      actualY1PaperFineChoiceLocalDelta
    field_simp [ne_of_gt hpairScale, ne_of_gt hdenominator]
  rw [heq]

theorem actualY1PaperFineChoice_rectangleRatio
    {fineDelta globalDelta tGlobal outerWidth pairScale : Real}
    (N : ActualY1SharpFineScaleNumerics
      fineDelta globalDelta tGlobal outerWidth)
    (hpairScale : 0 < pairScale) :
    actualY1PaperFineChoiceLocalDelta
          fineDelta globalDelta tGlobal pairScale / pairScale <=
      fineDelta / prop41Y1PaperFineT fineDelta globalDelta tGlobal := by
  have hdenominator :=
    actualY1PaperFineChoiceDenominator_pos N hpairScale
  have hfineT := prop41Y1PaperFineT_pos N
  have hcancel :
      actualY1PaperFineChoiceLocalDelta
          fineDelta globalDelta tGlobal pairScale / pairScale =
        fineDelta /
          actualY1PaperFineChoiceDenominator
            fineDelta globalDelta tGlobal pairScale := by
    unfold actualY1PaperFineChoiceLocalDelta
    field_simp [ne_of_gt hpairScale]
  rw [hcancel]
  apply (div_le_div_iff₀ hdenominator hfineT).2
  rw [actualY1PaperFineChoiceDenominator]
  nlinarith [mul_pos N.fineDelta_pos hpairScale]

theorem actualY1PaperFineChoiceRho_pos
    {fineDelta globalDelta tGlobal outerWidth pairScale : Real}
    (N : ActualY1SharpFineScaleNumerics
      fineDelta globalDelta tGlobal outerWidth)
    (hpairScale : 0 < pairScale) :
    0 < actualY1PaperFineChoiceRho
      fineDelta globalDelta tGlobal pairScale := by
  exact div_pos
    (mul_pos (by norm_num)
      (actualY1PaperFineChoiceDenominator_pos N hpairScale))
    hpairScale

theorem five_le_actualY1PaperFineChoiceRho
    {fineDelta globalDelta tGlobal outerWidth pairScale : Real}
    (N : ActualY1SharpFineScaleNumerics
      fineDelta globalDelta tGlobal outerWidth)
    (hpairScale : 0 < pairScale) :
    5 <= actualY1PaperFineChoiceRho
      fineDelta globalDelta tGlobal pairScale := by
  rw [actualY1PaperFineChoiceRho]
  apply (le_div_iff₀ hpairScale).2
  rw [actualY1PaperFineChoiceDenominator]
  nlinarith [prop41Y1PaperFineT_pos N]

theorem actualY1PaperFineChoiceTraceQ_one
    {fineDelta globalDelta tGlobal outerWidth pairScale : Real}
    (N : ActualY1SharpFineScaleNumerics
      fineDelta globalDelta tGlobal outerWidth)
    (hpairScale : 0 < pairScale) :
    1 <= actualY1PaperFineChoiceTraceQ
      fineDelta globalDelta tGlobal pairScale := by
  rw [actualY1PaperFineChoiceTraceQ]
  nlinarith [five_le_actualY1PaperFineChoiceRho N hpairScale]

theorem actualY1PaperFineChoiceLambda_pos
    {fineDelta globalDelta tGlobal outerWidth pairScale : Real}
    (N : ActualY1SharpFineScaleNumerics
      fineDelta globalDelta tGlobal outerWidth)
    (hpairScale : 0 < pairScale) :
    0 < actualY1PaperFineChoiceLambda
      fineDelta globalDelta tGlobal pairScale := by
  rw [actualY1PaperFineChoiceLambda]
  exact mul_pos (by norm_num)
    (prop41TangencyScaleFactor_pos_of_pos
      (lt_of_lt_of_le (by norm_num)
        (actualY1PaperFineChoiceTraceQ_one N hpairScale)))

theorem actualY1PaperFineChoiceRho_le_lambda
    {fineDelta globalDelta tGlobal outerWidth pairScale : Real}
    (N : ActualY1SharpFineScaleNumerics
      fineDelta globalDelta tGlobal outerWidth)
    (hpairScale : 0 < pairScale) :
    actualY1PaperFineChoiceRho
        fineDelta globalDelta tGlobal pairScale <=
      actualY1PaperFineChoiceLambda
        fineDelta globalDelta tGlobal pairScale := by
  have hrhoPos := actualY1PaperFineChoiceRho_pos N hpairScale
  have hqOne := actualY1PaperFineChoiceTraceQ_one N hpairScale
  have hqFactor := q_le_prop41TangencyScaleFactor_of_one_le hqOne
  have hfactorPos := prop41TangencyScaleFactor_pos_of_pos
    (lt_of_lt_of_le (by norm_num) hqOne)
  have hrhoLeQ : actualY1PaperFineChoiceRho
      fineDelta globalDelta tGlobal pairScale <=
      actualY1PaperFineChoiceTraceQ
        fineDelta globalDelta tGlobal pairScale := by
    rw [actualY1PaperFineChoiceTraceQ]
    linarith
  rw [actualY1PaperFineChoiceLambda]
  nlinarith

theorem actualY1PaperFineChoice_shiftDominates
    {fineDelta globalDelta tGlobal outerWidth pairScale : Real}
    (N : ActualY1SharpFineScaleNumerics
      fineDelta globalDelta tGlobal outerWidth)
    (hpairScale : 0 < pairScale) :
    10 * prop41TangencyScaleFactor
          (actualY1PaperFineChoiceTraceQ
            fineDelta globalDelta tGlobal pairScale) <
      actualY1PaperFineChoiceLambda
        fineDelta globalDelta tGlobal pairScale := by
  rw [actualY1PaperFineChoiceLambda]
  have hfactorPos := prop41TangencyScaleFactor_pos_of_pos
    (lt_of_lt_of_le (by norm_num)
      (actualY1PaperFineChoiceTraceQ_one N hpairScale))
  nlinarith

theorem actualY1PaperFineChoice_traceRadius
    (fineDelta globalDelta tGlobal pairScale : Real) :
    2 * (actualY1PaperFineChoiceRho
          fineDelta globalDelta tGlobal pairScale *
        actualY1PaperFineChoiceLocalDelta
          fineDelta globalDelta tGlobal pairScale) <=
      actualY1PaperFineChoiceTraceQ
          fineDelta globalDelta tGlobal pairScale *
        actualY1PaperFineChoiceLocalDelta
          fineDelta globalDelta tGlobal pairScale := by
  rw [actualY1PaperFineChoiceTraceQ, mul_assoc]

theorem actualY1PaperFineChoice_strengthenedScale
    {fineDelta globalDelta tGlobal outerWidth pairScale : Real}
    (N : ActualY1SharpFineScaleNumerics
      fineDelta globalDelta tGlobal outerWidth)
    (hpairScale : 0 < pairScale)
    (hsmall : ActualY1PaperFineThreeShiftRadiusSmallness
      fineDelta globalDelta tGlobal pairScale) :
    (10 * prop41TangencyScaleFactor
          (actualY1PaperFineChoiceTraceQ
            fineDelta globalDelta tGlobal pairScale) +
        actualY1PaperFineChoiceLambda
          fineDelta globalDelta tGlobal pairScale) *
        actualY1PaperFineChoiceLocalDelta
          fineDelta globalDelta tGlobal pairScale <
      pairScale / 46080 := by
  have hdenominator :=
    actualY1PaperFineChoiceDenominator_pos N hpairScale
  change 46080 *
      (10 * prop41TangencyScaleFactor
          (actualY1PaperFineChoiceTraceQ
            fineDelta globalDelta tGlobal pairScale) +
        actualY1PaperFineChoiceLambda
          fineDelta globalDelta tGlobal pairScale) * fineDelta <
      actualY1PaperFineChoiceDenominator
        fineDelta globalDelta tGlobal pairScale at hsmall
  rw [actualY1PaperFineChoiceLocalDelta]
  apply (lt_div_iff₀ (by norm_num : (0 : Real) < 46080)).2
  calc
    (10 * prop41TangencyScaleFactor
          (actualY1PaperFineChoiceTraceQ
            fineDelta globalDelta tGlobal pairScale) +
        actualY1PaperFineChoiceLambda
          fineDelta globalDelta tGlobal pairScale) *
          (fineDelta * pairScale /
            actualY1PaperFineChoiceDenominator
              fineDelta globalDelta tGlobal pairScale) * 46080 =
        (46080 *
          (10 * prop41TangencyScaleFactor
              (actualY1PaperFineChoiceTraceQ
                fineDelta globalDelta tGlobal pairScale) +
            actualY1PaperFineChoiceLambda
              fineDelta globalDelta tGlobal pairScale) * fineDelta) *
            pairScale /
          actualY1PaperFineChoiceDenominator
            fineDelta globalDelta tGlobal pairScale := by ring
    _ < actualY1PaperFineChoiceDenominator
          fineDelta globalDelta tGlobal pairScale * pairScale /
        actualY1PaperFineChoiceDenominator
          fineDelta globalDelta tGlobal pairScale :=
      (div_lt_div_iff_of_pos_right hdenominator).2
        (mul_lt_mul_of_pos_right hsmall hpairScale)
    _ = pairScale := by
      field_simp [ne_of_gt hdenominator]

theorem ActualY1PaperFineThreeShiftPairScaleSmallness.pairScale_pos
    {fineDelta globalDelta tGlobal outerWidth pairScale : Real}
    (N : ActualY1SharpFineScaleNumerics
      fineDelta globalDelta tGlobal outerWidth)
    (hsmall : ActualY1PaperFineThreeShiftPairScaleSmallness
      fineDelta globalDelta tGlobal pairScale) :
    0 < pairScale := by
  have hfactorNonneg :
      0 <= prop41TangencyScaleFactor
        (actualY1PaperFineChoiceTraceQ
          fineDelta globalDelta tGlobal pairScale) := by
    rw [prop41TangencyScaleFactor]
    exact div_nonneg (mul_nonneg (by norm_num) (sq_nonneg _))
      prop41TangencyProductCoefficient_pos.le
  have hlambdaNonneg :
      0 <= actualY1PaperFineChoiceLambda
        fineDelta globalDelta tGlobal pairScale := by
    rw [actualY1PaperFineChoiceLambda]
    positivity
  change 46080 *
      (10 * prop41TangencyScaleFactor
          (actualY1PaperFineChoiceTraceQ
            fineDelta globalDelta tGlobal pairScale) +
        actualY1PaperFineChoiceLambda
          fineDelta globalDelta tGlobal pairScale) * fineDelta <
      pairScale at hsmall
  have hleftNonneg : 0 <= 46080 *
      (10 * prop41TangencyScaleFactor
          (actualY1PaperFineChoiceTraceQ
            fineDelta globalDelta tGlobal pairScale) +
        actualY1PaperFineChoiceLambda
          fineDelta globalDelta tGlobal pairScale) * fineDelta := by
    exact mul_nonneg
      (mul_nonneg (by norm_num)
        (add_nonneg
          (mul_nonneg (by norm_num) hfactorNonneg)
          hlambdaNonneg))
      N.fineDelta_pos.le
  linarith

theorem ActualY1PaperFineThreeShiftPairScaleSmallness.toRadiusSmallness
    {fineDelta globalDelta tGlobal outerWidth pairScale : Real}
    (N : ActualY1SharpFineScaleNumerics
      fineDelta globalDelta tGlobal outerWidth)
    (hsmall : ActualY1PaperFineThreeShiftPairScaleSmallness
      fineDelta globalDelta tGlobal pairScale) :
    ActualY1PaperFineThreeShiftRadiusSmallness
      fineDelta globalDelta tGlobal pairScale := by
  have hpairScale := hsmall.pairScale_pos N
  change 46080 *
      (10 * prop41TangencyScaleFactor
          (actualY1PaperFineChoiceTraceQ
            fineDelta globalDelta tGlobal pairScale) +
        actualY1PaperFineChoiceLambda
          fineDelta globalDelta tGlobal pairScale) * fineDelta <
      pairScale at hsmall
  change 46080 *
      (10 * prop41TangencyScaleFactor
          (actualY1PaperFineChoiceTraceQ
            fineDelta globalDelta tGlobal pairScale) +
        actualY1PaperFineChoiceLambda
          fineDelta globalDelta tGlobal pairScale) * fineDelta <
      actualY1PaperFineChoiceDenominator
        fineDelta globalDelta tGlobal pairScale
  rw [actualY1PaperFineChoiceDenominator]
  exact hsmall.trans (lt_add_of_pos_left _ (prop41Y1PaperFineT_pos N))

/-- General scalar producer from the exact one-line harmonic radius input. -/
theorem actualY1PaperFineAutomaticThreeShiftNumerics_of_radiusSmall
    {fineDelta globalDelta tGlobal outerWidth pairScale : Real}
    (N : ActualY1SharpFineScaleNumerics
      fineDelta globalDelta tGlobal outerWidth)
    (hpairScale : 0 < pairScale)
    (hsmall : ActualY1PaperFineThreeShiftRadiusSmallness
      fineDelta globalDelta tGlobal pairScale) :
    ActualY1PaperFineAutomaticThreeShiftNumerics
      fineDelta globalDelta tGlobal pairScale := by
  exact {
    choice_scale := {
      localDelta_pos := actualY1PaperFineChoiceLocalDelta_pos N hpairScale
      pairScale_pos := hpairScale
      localDelta_le_fineDelta :=
        actualY1PaperFineChoiceLocalDelta_le_fineDelta N hpairScale
      retained_tangency_budget :=
        actualY1PaperFineChoice_retainedTangencyBudget N hpairScale
      rectangle_ratio :=
        actualY1PaperFineChoice_rectangleRatio N hpairScale
    }
    traceQ_one := actualY1PaperFineChoiceTraceQ_one N hpairScale
    lambda_pos := actualY1PaperFineChoiceLambda_pos N hpairScale
    rho_le_lambda :=
      actualY1PaperFineChoiceRho_le_lambda N hpairScale
    shift_dominates :=
      actualY1PaperFineChoice_shiftDominates N hpairScale
    strengthened_scale :=
      actualY1PaperFineChoice_strengthenedScale N hpairScale hsmall
    trace_radius := actualY1PaperFineChoice_traceRadius
      fineDelta globalDelta tGlobal pairScale
  }

/-- Paper-shaped scalar producer.  The single small-radius hypothesis also
forces `pairScale > 0`, so no redundant positivity premise remains. -/
theorem actualY1PaperFineAutomaticThreeShiftNumerics_of_pairScaleSmall
    {fineDelta globalDelta tGlobal outerWidth pairScale : Real}
    (N : ActualY1SharpFineScaleNumerics
      fineDelta globalDelta tGlobal outerWidth)
    (hsmall : ActualY1PaperFineThreeShiftPairScaleSmallness
      fineDelta globalDelta tGlobal pairScale) :
    ActualY1PaperFineAutomaticThreeShiftNumerics
      fineDelta globalDelta tGlobal pairScale := by
  exact actualY1PaperFineAutomaticThreeShiftNumerics_of_radiusSmall N
    (hsmall.pairScale_pos N) (hsmall.toRadiusSmallness N)


/-- Fully automatic scalar specialization of the retained-`Y1` three-shift
endpoint.  Compared with
`exists_uniform_threeShift_perturbationReady_of_actualRetainedY1Pairs`, the
six separate `rho/q/lambda/small-scale` premises and the choice-scale record
are replaced by one paper-shaped pair-scale smallness hypothesis. -/
theorem exists_uniform_threeShift_perturbationReady_of_actualRetainedY1Pairs_of_pairScaleSmall
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
    (pairScale : Real)
    (selection : ActualRetainedY1PairSelection
      (y1FineCoarseRectangleData fine Y1 fineLabels pointAt tubeAt
        f f1 f2 hf hf1 (radius : Real)
        (prop41Y1PaperFineT (radius : Real) globalDelta tGlobal)
        globalDelta tGlobal)
      items leftIndex rightIndex labelAt keep pairScale)
    (hitems : items.Nonempty)
    (hsmall : ActualY1PaperFineThreeShiftPairScaleSmallness
      (radius : Real) globalDelta tGlobal pairScale) :
    let localDelta := actualY1PaperFineChoiceLocalDelta
      (radius : Real) globalDelta tGlobal pairScale
    let lambda := actualY1PaperFineChoiceLambda
      (radius : Real) globalDelta tGlobal pairScale
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
  let scales :=
    actualY1PaperFineAutomaticThreeShiftNumerics_of_pairScaleSmall N hsmall
  exact exists_uniform_threeShift_perturbationReady_of_actualRetainedY1Pairs
    fine physical E Y1 fineLabels pointAt centerTube tubeAt f f1 f2 outerA
    outerB hOuter hf hf1 tGlobal globalDelta facts pointSource hpointE N
    hparameter hft hf1Lower hf1Upper hf2 hf2Continuous items leftIndex
    rightIndex labelAt keep scales.choice_scale selection hitems
    scales.traceQ_one scales.lambda_pos scales.rho_le_lambda
    scales.shift_dominates scales.strengthened_scale scales.trace_radius


#print axioms actualY1PaperFineChoiceDenominator_pos
#print axioms q_le_prop41TangencyScaleFactor_of_one_le
#print axioms actualY1PaperFineChoice_retainedTangencyBudget
#print axioms actualY1PaperFineChoice_rectangleRatio
#print axioms actualY1PaperFineChoice_strengthenedScale
#print axioms ActualY1PaperFineThreeShiftPairScaleSmallness.pairScale_pos
#print axioms ActualY1PaperFineThreeShiftPairScaleSmallness.toRadiusSmallness
#print axioms actualY1PaperFineAutomaticThreeShiftNumerics_of_radiusSmall
#print axioms actualY1PaperFineAutomaticThreeShiftNumerics_of_pairScaleSmall
#print axioms exists_uniform_threeShift_perturbationReady_of_actualRetainedY1Pairs_of_pairScaleSmall


end

end FamilyStickyCinematicL32Prop41ActualY1PaperFineThreeShiftScaleProducerV1
