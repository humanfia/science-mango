import FamilyStickyGrounding.Cinematic.FamilyStickyCinematicL32Prop41ActualY1PaperFineThreeShiftScaleProducerV1

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 2000000

namespace FamilyStickyCinematicL32Prop41ActualY1PaperFineCNormalizedThreeShiftScaleProducerV1

open FamilyStickyCinematicL32Prop41ActualY1PaperFineThreeShiftScaleProducerV1
open FamilyStickyCinematicL32Prop41ActualY1RetainedThreeShiftPerturbationReadyV1
open FamilyStickyCinematicL32Prop41ActualY1SharpFineScaleTangencyV1
open FamilyStickyCinematicL32Prop41TangencyProductToScaleV1

noncomputable section

/-!
# Automatic six-radius choices for the C-normalized three-shift lane

Replacing the left tube's graph `c` coordinate costs at most one additional
`fineDelta` in the cinematic trace neighborhood.  Thus the retained tangency
budget is `6 * fineDelta`, rather than the former `5 * fineDelta` budget.

The harmonic local thickness is unchanged.  We replace only

* `rho` by `6 * denominator / pairScale`,
* `traceQ` by `2 * rho`, and
* `lambda` by `20 * prop41TangencyScaleFactor traceQ`.

All conclusions below are elementary scalar consequences of those literal
definitions.  In particular, this module has no fixed-`C` provenance input.
-/

/-- The same positive harmonic denominator used in the five-radius lane. -/
def actualY1PaperFineCNormalizedChoiceDenominator
    (fineDelta globalDelta tGlobal pairScale : Real) : Real :=
  actualY1PaperFineChoiceDenominator
    fineDelta globalDelta tGlobal pairScale

/-- The harmonic local thickness is unchanged by graph-`c` normalization. -/
def actualY1PaperFineCNormalizedChoiceLocalDelta
    (fineDelta globalDelta tGlobal pairScale : Real) : Real :=
  fineDelta * pairScale /
    actualY1PaperFineCNormalizedChoiceDenominator
      fineDelta globalDelta tGlobal pairScale

/-- Tangency enlargement paying the full `6 * fineDelta` budget. -/
def actualY1PaperFineCNormalizedChoiceRho
    (fineDelta globalDelta tGlobal pairScale : Real) : Real :=
  6 * actualY1PaperFineCNormalizedChoiceDenominator
    fineDelta globalDelta tGlobal pairScale / pairScale

/-- Trace tolerance exactly twice the C-normalized enlargement. -/
def actualY1PaperFineCNormalizedChoiceTraceQ
    (fineDelta globalDelta tGlobal pairScale : Real) : Real :=
  2 * actualY1PaperFineCNormalizedChoiceRho
    fineDelta globalDelta tGlobal pairScale

/-- Shift enlargement with the same strict factor-two margin. -/
def actualY1PaperFineCNormalizedChoiceLambda
    (fineDelta globalDelta tGlobal pairScale : Real) : Real :=
  20 * prop41TangencyScaleFactor
    (actualY1PaperFineCNormalizedChoiceTraceQ
      fineDelta globalDelta tGlobal pairScale)

/-- Exact denominator-form smallness condition for the six-radius choices. -/
def ActualY1PaperFineCNormalizedThreeShiftRadiusSmallness
    (fineDelta globalDelta tGlobal pairScale : Real) : Prop :=
  46080 *
      (10 * prop41TangencyScaleFactor
          (actualY1PaperFineCNormalizedChoiceTraceQ
            fineDelta globalDelta tGlobal pairScale) +
        actualY1PaperFineCNormalizedChoiceLambda
          fineDelta globalDelta tGlobal pairScale) * fineDelta <
    actualY1PaperFineCNormalizedChoiceDenominator
      fineDelta globalDelta tGlobal pairScale

/-- Strong paper-shaped smallness condition with `pairScale` on the right. -/
def ActualY1PaperFineCNormalizedThreeShiftPairScaleSmallness
    (fineDelta globalDelta tGlobal pairScale : Real) : Prop :=
  46080 *
      (10 * prop41TangencyScaleFactor
          (actualY1PaperFineCNormalizedChoiceTraceQ
            fineDelta globalDelta tGlobal pairScale) +
        actualY1PaperFineCNormalizedChoiceLambda
          fineDelta globalDelta tGlobal pairScale) * fineDelta <
    pairScale

/-- Scale facts for the C-normalized lane.  The six-radius tangency budget is
a literal field, rather than being hidden behind the former five-radius
record. -/
structure ActualY1PaperFineCNormalizedChoiceScaleNumerics
    (fineDelta globalDelta tGlobal localDelta pairScale rho : Real) : Prop where
  localDelta_pos : 0 < localDelta
  pairScale_pos : 0 < pairScale
  localDelta_le_fineDelta : localDelta <= fineDelta
  normalized_tangency_budget : 6 * fineDelta <= rho * localDelta
  rectangle_ratio :
    localDelta / pairScale <=
      fineDelta / prop41Y1PaperFineT fineDelta globalDelta tGlobal

/-- Complete scalar package consumed by the C-normalized uniform producer. -/
structure ActualY1PaperFineCNormalizedAutomaticThreeShiftNumerics
    (fineDelta globalDelta tGlobal pairScale : Real) : Prop where
  choice_scale : ActualY1PaperFineCNormalizedChoiceScaleNumerics
    fineDelta globalDelta tGlobal
    (actualY1PaperFineCNormalizedChoiceLocalDelta
      fineDelta globalDelta tGlobal pairScale)
    pairScale
    (actualY1PaperFineCNormalizedChoiceRho
      fineDelta globalDelta tGlobal pairScale)
  traceQ_one : 1 <= actualY1PaperFineCNormalizedChoiceTraceQ
    fineDelta globalDelta tGlobal pairScale
  lambda_pos : 0 < actualY1PaperFineCNormalizedChoiceLambda
    fineDelta globalDelta tGlobal pairScale
  rho_le_lambda : actualY1PaperFineCNormalizedChoiceRho
      fineDelta globalDelta tGlobal pairScale <=
    actualY1PaperFineCNormalizedChoiceLambda
      fineDelta globalDelta tGlobal pairScale
  shift_dominates :
    10 * prop41TangencyScaleFactor
        (actualY1PaperFineCNormalizedChoiceTraceQ
          fineDelta globalDelta tGlobal pairScale) <
      actualY1PaperFineCNormalizedChoiceLambda
        fineDelta globalDelta tGlobal pairScale
  strengthened_scale :
    (10 * prop41TangencyScaleFactor
          (actualY1PaperFineCNormalizedChoiceTraceQ
            fineDelta globalDelta tGlobal pairScale) +
        actualY1PaperFineCNormalizedChoiceLambda
          fineDelta globalDelta tGlobal pairScale) *
        actualY1PaperFineCNormalizedChoiceLocalDelta
          fineDelta globalDelta tGlobal pairScale <
      pairScale / 46080
  trace_radius :
    2 * (actualY1PaperFineCNormalizedChoiceRho
          fineDelta globalDelta tGlobal pairScale *
        actualY1PaperFineCNormalizedChoiceLocalDelta
          fineDelta globalDelta tGlobal pairScale) <=
      actualY1PaperFineCNormalizedChoiceTraceQ
          fineDelta globalDelta tGlobal pairScale *
        actualY1PaperFineCNormalizedChoiceLocalDelta
          fineDelta globalDelta tGlobal pairScale

theorem actualY1PaperFineCNormalizedChoiceDenominator_pos
    {fineDelta globalDelta tGlobal outerWidth pairScale : Real}
    (N : ActualY1SharpFineScaleNumerics
      fineDelta globalDelta tGlobal outerWidth)
    (hpairScale : 0 < pairScale) :
    0 < actualY1PaperFineCNormalizedChoiceDenominator
      fineDelta globalDelta tGlobal pairScale := by
  exact actualY1PaperFineChoiceDenominator_pos N hpairScale

theorem actualY1PaperFineCNormalizedChoiceLocalDelta_pos
    {fineDelta globalDelta tGlobal outerWidth pairScale : Real}
    (N : ActualY1SharpFineScaleNumerics
      fineDelta globalDelta tGlobal outerWidth)
    (hpairScale : 0 < pairScale) :
    0 < actualY1PaperFineCNormalizedChoiceLocalDelta
      fineDelta globalDelta tGlobal pairScale := by
  exact div_pos (mul_pos N.fineDelta_pos hpairScale)
    (actualY1PaperFineCNormalizedChoiceDenominator_pos N hpairScale)

theorem actualY1PaperFineCNormalizedChoiceLocalDelta_le_fineDelta
    {fineDelta globalDelta tGlobal outerWidth pairScale : Real}
    (N : ActualY1SharpFineScaleNumerics
      fineDelta globalDelta tGlobal outerWidth)
    (hpairScale : 0 < pairScale) :
    actualY1PaperFineCNormalizedChoiceLocalDelta
        fineDelta globalDelta tGlobal pairScale <= fineDelta := by
  rw [actualY1PaperFineCNormalizedChoiceLocalDelta]
  apply (div_le_iff₀
    (actualY1PaperFineCNormalizedChoiceDenominator_pos N hpairScale)).2
  rw [actualY1PaperFineCNormalizedChoiceDenominator,
    actualY1PaperFineChoiceDenominator]
  nlinarith [mul_pos N.fineDelta_pos (prop41Y1PaperFineT_pos N)]

/-- Exact cancellation behind the six-radius tangency budget. -/
theorem actualY1PaperFineCNormalizedChoice_rho_mul_localDelta
    {fineDelta globalDelta tGlobal outerWidth pairScale : Real}
    (N : ActualY1SharpFineScaleNumerics
      fineDelta globalDelta tGlobal outerWidth)
    (hpairScale : 0 < pairScale) :
    actualY1PaperFineCNormalizedChoiceRho
          fineDelta globalDelta tGlobal pairScale *
        actualY1PaperFineCNormalizedChoiceLocalDelta
          fineDelta globalDelta tGlobal pairScale =
      6 * fineDelta := by
  have hdenominator :=
    actualY1PaperFineCNormalizedChoiceDenominator_pos N hpairScale
  unfold actualY1PaperFineCNormalizedChoiceRho
    actualY1PaperFineCNormalizedChoiceLocalDelta
  field_simp [ne_of_gt hpairScale, ne_of_gt hdenominator]

theorem actualY1PaperFineCNormalizedChoice_normalizedTangencyBudget
    {fineDelta globalDelta tGlobal outerWidth pairScale : Real}
    (N : ActualY1SharpFineScaleNumerics
      fineDelta globalDelta tGlobal outerWidth)
    (hpairScale : 0 < pairScale) :
    6 * fineDelta <=
      actualY1PaperFineCNormalizedChoiceRho
          fineDelta globalDelta tGlobal pairScale *
        actualY1PaperFineCNormalizedChoiceLocalDelta
          fineDelta globalDelta tGlobal pairScale := by
  rw [actualY1PaperFineCNormalizedChoice_rho_mul_localDelta N hpairScale]

theorem actualY1PaperFineCNormalizedChoice_rectangleRatio
    {fineDelta globalDelta tGlobal outerWidth pairScale : Real}
    (N : ActualY1SharpFineScaleNumerics
      fineDelta globalDelta tGlobal outerWidth)
    (hpairScale : 0 < pairScale) :
    actualY1PaperFineCNormalizedChoiceLocalDelta
          fineDelta globalDelta tGlobal pairScale / pairScale <=
      fineDelta / prop41Y1PaperFineT fineDelta globalDelta tGlobal := by
  simpa [actualY1PaperFineCNormalizedChoiceLocalDelta,
    actualY1PaperFineCNormalizedChoiceDenominator,
    actualY1PaperFineChoiceLocalDelta] using
      (actualY1PaperFineChoice_rectangleRatio N hpairScale)

theorem actualY1PaperFineCNormalizedChoiceRho_pos
    {fineDelta globalDelta tGlobal outerWidth pairScale : Real}
    (N : ActualY1SharpFineScaleNumerics
      fineDelta globalDelta tGlobal outerWidth)
    (hpairScale : 0 < pairScale) :
    0 < actualY1PaperFineCNormalizedChoiceRho
      fineDelta globalDelta tGlobal pairScale := by
  exact div_pos
    (mul_pos (by norm_num)
      (actualY1PaperFineCNormalizedChoiceDenominator_pos N hpairScale))
    hpairScale

theorem six_le_actualY1PaperFineCNormalizedChoiceRho
    {fineDelta globalDelta tGlobal outerWidth pairScale : Real}
    (N : ActualY1SharpFineScaleNumerics
      fineDelta globalDelta tGlobal outerWidth)
    (hpairScale : 0 < pairScale) :
    6 <= actualY1PaperFineCNormalizedChoiceRho
      fineDelta globalDelta tGlobal pairScale := by
  rw [actualY1PaperFineCNormalizedChoiceRho]
  apply (le_div_iff₀ hpairScale).2
  rw [actualY1PaperFineCNormalizedChoiceDenominator,
    actualY1PaperFineChoiceDenominator]
  nlinarith [prop41Y1PaperFineT_pos N]

theorem actualY1PaperFineCNormalizedChoiceTraceQ_one
    {fineDelta globalDelta tGlobal outerWidth pairScale : Real}
    (N : ActualY1SharpFineScaleNumerics
      fineDelta globalDelta tGlobal outerWidth)
    (hpairScale : 0 < pairScale) :
    1 <= actualY1PaperFineCNormalizedChoiceTraceQ
      fineDelta globalDelta tGlobal pairScale := by
  rw [actualY1PaperFineCNormalizedChoiceTraceQ]
  nlinarith [six_le_actualY1PaperFineCNormalizedChoiceRho N hpairScale]

theorem actualY1PaperFineCNormalizedChoiceLambda_pos
    {fineDelta globalDelta tGlobal outerWidth pairScale : Real}
    (N : ActualY1SharpFineScaleNumerics
      fineDelta globalDelta tGlobal outerWidth)
    (hpairScale : 0 < pairScale) :
    0 < actualY1PaperFineCNormalizedChoiceLambda
      fineDelta globalDelta tGlobal pairScale := by
  rw [actualY1PaperFineCNormalizedChoiceLambda]
  exact mul_pos (by norm_num)
    (prop41TangencyScaleFactor_pos_of_pos
      (lt_of_lt_of_le (by norm_num)
        (actualY1PaperFineCNormalizedChoiceTraceQ_one N hpairScale)))

theorem actualY1PaperFineCNormalizedChoiceRho_le_lambda
    {fineDelta globalDelta tGlobal outerWidth pairScale : Real}
    (N : ActualY1SharpFineScaleNumerics
      fineDelta globalDelta tGlobal outerWidth)
    (hpairScale : 0 < pairScale) :
    actualY1PaperFineCNormalizedChoiceRho
        fineDelta globalDelta tGlobal pairScale <=
      actualY1PaperFineCNormalizedChoiceLambda
        fineDelta globalDelta tGlobal pairScale := by
  have hrhoPos :=
    actualY1PaperFineCNormalizedChoiceRho_pos N hpairScale
  have hqOne :=
    actualY1PaperFineCNormalizedChoiceTraceQ_one N hpairScale
  have hqFactor := q_le_prop41TangencyScaleFactor_of_one_le hqOne
  have hfactorPos := prop41TangencyScaleFactor_pos_of_pos
    (lt_of_lt_of_le (by norm_num) hqOne)
  have hrhoLeQ : actualY1PaperFineCNormalizedChoiceRho
      fineDelta globalDelta tGlobal pairScale <=
      actualY1PaperFineCNormalizedChoiceTraceQ
        fineDelta globalDelta tGlobal pairScale := by
    rw [actualY1PaperFineCNormalizedChoiceTraceQ]
    linarith
  rw [actualY1PaperFineCNormalizedChoiceLambda]
  nlinarith

theorem actualY1PaperFineCNormalizedChoice_shiftDominates
    {fineDelta globalDelta tGlobal outerWidth pairScale : Real}
    (N : ActualY1SharpFineScaleNumerics
      fineDelta globalDelta tGlobal outerWidth)
    (hpairScale : 0 < pairScale) :
    10 * prop41TangencyScaleFactor
          (actualY1PaperFineCNormalizedChoiceTraceQ
            fineDelta globalDelta tGlobal pairScale) <
      actualY1PaperFineCNormalizedChoiceLambda
        fineDelta globalDelta tGlobal pairScale := by
  rw [actualY1PaperFineCNormalizedChoiceLambda]
  have hfactorPos := prop41TangencyScaleFactor_pos_of_pos
    (lt_of_lt_of_le (by norm_num)
      (actualY1PaperFineCNormalizedChoiceTraceQ_one N hpairScale))
  nlinarith

theorem actualY1PaperFineCNormalizedChoice_traceRadius
    (fineDelta globalDelta tGlobal pairScale : Real) :
    2 * (actualY1PaperFineCNormalizedChoiceRho
          fineDelta globalDelta tGlobal pairScale *
        actualY1PaperFineCNormalizedChoiceLocalDelta
          fineDelta globalDelta tGlobal pairScale) <=
      actualY1PaperFineCNormalizedChoiceTraceQ
          fineDelta globalDelta tGlobal pairScale *
        actualY1PaperFineCNormalizedChoiceLocalDelta
          fineDelta globalDelta tGlobal pairScale := by
  rw [actualY1PaperFineCNormalizedChoiceTraceQ, mul_assoc]

theorem actualY1PaperFineCNormalizedChoice_strengthenedScale
    {fineDelta globalDelta tGlobal outerWidth pairScale : Real}
    (N : ActualY1SharpFineScaleNumerics
      fineDelta globalDelta tGlobal outerWidth)
    (hpairScale : 0 < pairScale)
    (hsmall : ActualY1PaperFineCNormalizedThreeShiftRadiusSmallness
      fineDelta globalDelta tGlobal pairScale) :
    (10 * prop41TangencyScaleFactor
          (actualY1PaperFineCNormalizedChoiceTraceQ
            fineDelta globalDelta tGlobal pairScale) +
        actualY1PaperFineCNormalizedChoiceLambda
          fineDelta globalDelta tGlobal pairScale) *
        actualY1PaperFineCNormalizedChoiceLocalDelta
          fineDelta globalDelta tGlobal pairScale <
      pairScale / 46080 := by
  have hdenominator :=
    actualY1PaperFineCNormalizedChoiceDenominator_pos N hpairScale
  change 46080 *
      (10 * prop41TangencyScaleFactor
          (actualY1PaperFineCNormalizedChoiceTraceQ
            fineDelta globalDelta tGlobal pairScale) +
        actualY1PaperFineCNormalizedChoiceLambda
          fineDelta globalDelta tGlobal pairScale) * fineDelta <
      actualY1PaperFineCNormalizedChoiceDenominator
        fineDelta globalDelta tGlobal pairScale at hsmall
  rw [actualY1PaperFineCNormalizedChoiceLocalDelta]
  apply (lt_div_iff₀ (by norm_num : (0 : Real) < 46080)).2
  calc
    (10 * prop41TangencyScaleFactor
          (actualY1PaperFineCNormalizedChoiceTraceQ
            fineDelta globalDelta tGlobal pairScale) +
        actualY1PaperFineCNormalizedChoiceLambda
          fineDelta globalDelta tGlobal pairScale) *
          (fineDelta * pairScale /
            actualY1PaperFineCNormalizedChoiceDenominator
              fineDelta globalDelta tGlobal pairScale) * 46080 =
        (46080 *
          (10 * prop41TangencyScaleFactor
              (actualY1PaperFineCNormalizedChoiceTraceQ
                fineDelta globalDelta tGlobal pairScale) +
            actualY1PaperFineCNormalizedChoiceLambda
              fineDelta globalDelta tGlobal pairScale) * fineDelta) *
            pairScale /
          actualY1PaperFineCNormalizedChoiceDenominator
            fineDelta globalDelta tGlobal pairScale := by ring
    _ < actualY1PaperFineCNormalizedChoiceDenominator
          fineDelta globalDelta tGlobal pairScale * pairScale /
        actualY1PaperFineCNormalizedChoiceDenominator
          fineDelta globalDelta tGlobal pairScale :=
      (div_lt_div_iff_of_pos_right hdenominator).2
        (mul_lt_mul_of_pos_right hsmall hpairScale)
    _ = pairScale := by
      field_simp [ne_of_gt hdenominator]

theorem ActualY1PaperFineCNormalizedThreeShiftPairScaleSmallness.pairScale_pos
    {fineDelta globalDelta tGlobal outerWidth pairScale : Real}
    (N : ActualY1SharpFineScaleNumerics
      fineDelta globalDelta tGlobal outerWidth)
    (hsmall : ActualY1PaperFineCNormalizedThreeShiftPairScaleSmallness
      fineDelta globalDelta tGlobal pairScale) :
    0 < pairScale := by
  have hfactorNonneg :
      0 <= prop41TangencyScaleFactor
        (actualY1PaperFineCNormalizedChoiceTraceQ
          fineDelta globalDelta tGlobal pairScale) := by
    rw [prop41TangencyScaleFactor]
    exact div_nonneg (mul_nonneg (by norm_num) (sq_nonneg _))
      prop41TangencyProductCoefficient_pos.le
  have hlambdaNonneg :
      0 <= actualY1PaperFineCNormalizedChoiceLambda
        fineDelta globalDelta tGlobal pairScale := by
    rw [actualY1PaperFineCNormalizedChoiceLambda]
    positivity
  change 46080 *
      (10 * prop41TangencyScaleFactor
          (actualY1PaperFineCNormalizedChoiceTraceQ
            fineDelta globalDelta tGlobal pairScale) +
        actualY1PaperFineCNormalizedChoiceLambda
          fineDelta globalDelta tGlobal pairScale) * fineDelta <
      pairScale at hsmall
  have hleftNonneg : 0 <= 46080 *
      (10 * prop41TangencyScaleFactor
          (actualY1PaperFineCNormalizedChoiceTraceQ
            fineDelta globalDelta tGlobal pairScale) +
        actualY1PaperFineCNormalizedChoiceLambda
          fineDelta globalDelta tGlobal pairScale) * fineDelta := by
    exact mul_nonneg
      (mul_nonneg (by norm_num)
        (add_nonneg
          (mul_nonneg (by norm_num) hfactorNonneg)
          hlambdaNonneg))
      N.fineDelta_pos.le
  linarith

theorem ActualY1PaperFineCNormalizedThreeShiftPairScaleSmallness.toRadiusSmallness
    {fineDelta globalDelta tGlobal outerWidth pairScale : Real}
    (N : ActualY1SharpFineScaleNumerics
      fineDelta globalDelta tGlobal outerWidth)
    (hsmall : ActualY1PaperFineCNormalizedThreeShiftPairScaleSmallness
      fineDelta globalDelta tGlobal pairScale) :
    ActualY1PaperFineCNormalizedThreeShiftRadiusSmallness
      fineDelta globalDelta tGlobal pairScale := by
  have hpairScale := hsmall.pairScale_pos N
  change 46080 *
      (10 * prop41TangencyScaleFactor
          (actualY1PaperFineCNormalizedChoiceTraceQ
            fineDelta globalDelta tGlobal pairScale) +
        actualY1PaperFineCNormalizedChoiceLambda
          fineDelta globalDelta tGlobal pairScale) * fineDelta <
      pairScale at hsmall
  change 46080 *
      (10 * prop41TangencyScaleFactor
          (actualY1PaperFineCNormalizedChoiceTraceQ
            fineDelta globalDelta tGlobal pairScale) +
        actualY1PaperFineCNormalizedChoiceLambda
          fineDelta globalDelta tGlobal pairScale) * fineDelta <
      actualY1PaperFineCNormalizedChoiceDenominator
        fineDelta globalDelta tGlobal pairScale
  rw [actualY1PaperFineCNormalizedChoiceDenominator,
    actualY1PaperFineChoiceDenominator]
  exact hsmall.trans (lt_add_of_pos_left _ (prop41Y1PaperFineT_pos N))

/-- A six-budget choice record can feed the old five-budget numerical API
when a downstream lemma has not yet been specialized to C normalization. -/
theorem ActualY1PaperFineCNormalizedChoiceScaleNumerics.toFiveBudget
    {fineDelta globalDelta tGlobal localDelta pairScale rho : Real}
    (S : ActualY1PaperFineCNormalizedChoiceScaleNumerics
      fineDelta globalDelta tGlobal localDelta pairScale rho)
    (hfineDelta : 0 <= fineDelta) :
    ActualY1PaperFineChoiceScaleNumerics
      fineDelta globalDelta tGlobal localDelta pairScale rho := by
  exact {
    localDelta_pos := S.localDelta_pos
    pairScale_pos := S.pairScale_pos
    localDelta_le_fineDelta := S.localDelta_le_fineDelta
    retained_tangency_budget := by
      calc
        5 * fineDelta <= 6 * fineDelta := by linarith
        _ <= rho * localDelta := S.normalized_tangency_budget
    rectangle_ratio := S.rectangle_ratio
  }

/-- General scalar producer from the exact denominator-form smallness input. -/
theorem actualY1PaperFineCNormalizedAutomaticThreeShiftNumerics_of_radiusSmall
    {fineDelta globalDelta tGlobal outerWidth pairScale : Real}
    (N : ActualY1SharpFineScaleNumerics
      fineDelta globalDelta tGlobal outerWidth)
    (hpairScale : 0 < pairScale)
    (hsmall : ActualY1PaperFineCNormalizedThreeShiftRadiusSmallness
      fineDelta globalDelta tGlobal pairScale) :
    ActualY1PaperFineCNormalizedAutomaticThreeShiftNumerics
      fineDelta globalDelta tGlobal pairScale := by
  exact {
    choice_scale := {
      localDelta_pos :=
        actualY1PaperFineCNormalizedChoiceLocalDelta_pos N hpairScale
      pairScale_pos := hpairScale
      localDelta_le_fineDelta :=
        actualY1PaperFineCNormalizedChoiceLocalDelta_le_fineDelta N hpairScale
      normalized_tangency_budget :=
        actualY1PaperFineCNormalizedChoice_normalizedTangencyBudget
          N hpairScale
      rectangle_ratio :=
        actualY1PaperFineCNormalizedChoice_rectangleRatio N hpairScale
    }
    traceQ_one :=
      actualY1PaperFineCNormalizedChoiceTraceQ_one N hpairScale
    lambda_pos :=
      actualY1PaperFineCNormalizedChoiceLambda_pos N hpairScale
    rho_le_lambda :=
      actualY1PaperFineCNormalizedChoiceRho_le_lambda N hpairScale
    shift_dominates :=
      actualY1PaperFineCNormalizedChoice_shiftDominates N hpairScale
    strengthened_scale :=
      actualY1PaperFineCNormalizedChoice_strengthenedScale
        N hpairScale hsmall
    trace_radius := actualY1PaperFineCNormalizedChoice_traceRadius
      fineDelta globalDelta tGlobal pairScale
  }

/-- Paper-shaped producer: the smallness input itself forces positive
`pairScale`, so no separate positivity premise is needed. -/
theorem actualY1PaperFineCNormalizedAutomaticThreeShiftNumerics_of_pairScaleSmall
    {fineDelta globalDelta tGlobal outerWidth pairScale : Real}
    (N : ActualY1SharpFineScaleNumerics
      fineDelta globalDelta tGlobal outerWidth)
    (hsmall : ActualY1PaperFineCNormalizedThreeShiftPairScaleSmallness
      fineDelta globalDelta tGlobal pairScale) :
    ActualY1PaperFineCNormalizedAutomaticThreeShiftNumerics
      fineDelta globalDelta tGlobal pairScale := by
  exact actualY1PaperFineCNormalizedAutomaticThreeShiftNumerics_of_radiusSmall
    N (hsmall.pairScale_pos N) (hsmall.toRadiusSmallness N)

#print axioms actualY1PaperFineCNormalizedChoiceDenominator_pos
#print axioms actualY1PaperFineCNormalizedChoice_rho_mul_localDelta
#print axioms actualY1PaperFineCNormalizedChoice_normalizedTangencyBudget
#print axioms actualY1PaperFineCNormalizedChoice_rectangleRatio
#print axioms actualY1PaperFineCNormalizedChoiceRho_le_lambda
#print axioms actualY1PaperFineCNormalizedChoice_strengthenedScale
#print axioms ActualY1PaperFineCNormalizedThreeShiftPairScaleSmallness.pairScale_pos
#print axioms ActualY1PaperFineCNormalizedThreeShiftPairScaleSmallness.toRadiusSmallness
#print axioms ActualY1PaperFineCNormalizedChoiceScaleNumerics.toFiveBudget
#print axioms actualY1PaperFineCNormalizedAutomaticThreeShiftNumerics_of_radiusSmall
#print axioms actualY1PaperFineCNormalizedAutomaticThreeShiftNumerics_of_pairScaleSmall

end

end FamilyStickyCinematicL32Prop41ActualY1PaperFineCNormalizedThreeShiftScaleProducerV1
