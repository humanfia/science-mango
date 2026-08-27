import FamilyStickyGrounding.Cinematic.FamilyStickyCinematicL32Prop41ActualY1FineCoarseTangencyBranchV1

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 2000000

open Set
open scoped Interval

/-!
# Prop. 4.1: actual Y1 tangency at the paper fine scale

This module replaces the crude low-coefficient propagation estimate by the
two-regime estimate in PYZ Lemma 3.8(2c).  The split is made at the attained
tangency cost `Delta₀ = d / 1200`, rather than at `d = t / 2`.

In the sharp-curvature regime a critical point localizes the physical
parameter and gives an `O (sqrt (t * globalDelta))` point-slope estimate.
In the complementary regime the coefficient distance itself is
`O globalDelta`, which gives the same estimate by the normalized jet bound.
The explicit paper-scale choice `C_R = 10^8` then pays for propagation over
the canonical fine interval without an assumed scalar budget.
-/

namespace FamilyStickyCinematicL32Prop41ActualY1SharpFineScaleTangencyV1

open FamilyStickyCinematicL32Prop41ActualY1FineCoarseTangencyBranchV1

noncomputable section

/-- A deliberately explicit square-root factor for the Prop. 4.1 fine scale. -/
def prop41Y1FineRootFactor : ℝ := 10000

/-- The corresponding paper constant `C_R` in
`fineT = C_R * t * globalDelta / fineDelta`. -/
def prop41Y1RectangleFactor : ℝ := prop41Y1FineRootFactor ^ 2

/-- The uniform actual point-slope constant proved below. -/
def prop41Y1SharpSlopeConstant : ℝ := 10000

/-- The exact fine parameter used by the sharpened actual Y1 endpoint. -/
def prop41Y1PaperFineT
    (fineDelta globalDelta tGlobal : ℝ) : ℝ :=
  prop41Y1RectangleFactor * tGlobal * globalDelta / fineDelta

/-- Minimal scale data needed by the sharpened actual Y1 argument.

Unlike `ActualY1FineCoarseTangencyNumerics`, this structure has no assumed
propagation budget.  The budget is derived from the explicit paper scale. -/
structure ActualY1SharpFineScaleNumerics
    (fineDelta globalDelta tGlobal outerWidth : ℝ) : Prop where
  fineDelta_pos : 0 < fineDelta
  globalDelta_pos : 0 < globalDelta
  tGlobal_pos : 0 < tGlobal
  outerWidth_lower : 1 / 2 ≤ outerWidth
  fineDelta_le_globalDelta : fineDelta ≤ globalDelta
  prop41_smallScale : 2 * globalDelta - fineDelta < tGlobal / 2400

theorem prop41Y1FineRootFactor_pos :
    0 < prop41Y1FineRootFactor := by
  norm_num [prop41Y1FineRootFactor]

theorem prop41Y1RectangleFactor_pos :
    0 < prop41Y1RectangleFactor := by
  norm_num [prop41Y1RectangleFactor, prop41Y1FineRootFactor]

theorem prop41Y1SharpSlopeConstant_eq :
    prop41Y1SharpSlopeConstant = prop41Y1FineRootFactor := by
  rfl

theorem prop41Y1PaperFineT_pos
    {fineDelta globalDelta tGlobal outerWidth : ℝ}
    (N : ActualY1SharpFineScaleNumerics
      fineDelta globalDelta tGlobal outerWidth) :
    0 < prop41Y1PaperFineT fineDelta globalDelta tGlobal := by
  unfold prop41Y1PaperFineT
  exact div_pos
    (mul_pos (mul_pos prop41Y1RectangleFactor_pos N.tGlobal_pos)
      N.globalDelta_pos)
    N.fineDelta_pos

theorem ActualY1SharpFineScaleNumerics.globalDelta_lt_tGlobal_div :
    ∀ {fineDelta globalDelta tGlobal outerWidth : ℝ},
      ActualY1SharpFineScaleNumerics
        fineDelta globalDelta tGlobal outerWidth →
      globalDelta < tGlobal / 2400 := by
  intro fineDelta globalDelta tGlobal outerWidth N
  have hleft : globalDelta ≤ 2 * globalDelta - fineDelta := by
    linarith [N.fineDelta_le_globalDelta]
  exact lt_of_le_of_lt hleft N.prop41_smallScale

theorem ActualY1SharpFineScaleNumerics.globalDelta_le_tGlobal :
    ∀ {fineDelta globalDelta tGlobal outerWidth : ℝ},
      ActualY1SharpFineScaleNumerics
        fineDelta globalDelta tGlobal outerWidth →
      globalDelta ≤ tGlobal := by
  intro fineDelta globalDelta tGlobal outerWidth N
  have h := N.globalDelta_lt_tGlobal_div
  nlinarith [N.tGlobal_pos]

theorem prop41Y1PaperFineHalfWidth_eq
    {fineDelta globalDelta tGlobal outerWidth : ℝ}
    (N : ActualY1SharpFineScaleNumerics
      fineDelta globalDelta tGlobal outerWidth) :
    Real.sqrt
          (fineDelta /
            prop41Y1PaperFineT fineDelta globalDelta tGlobal) /
        2 =
      fineDelta /
        (2 * prop41Y1FineRootFactor *
          Real.sqrt (tGlobal * globalDelta)) := by
  have hprodPos : 0 < tGlobal * globalDelta :=
    mul_pos N.tGlobal_pos N.globalDelta_pos
  have hsqrtPos : 0 < Real.sqrt (tGlobal * globalDelta) :=
    Real.sqrt_pos.2 hprodPos
  have hsqrtSq :
      (Real.sqrt (tGlobal * globalDelta)) ^ 2 =
        tGlobal * globalDelta :=
    Real.sq_sqrt hprodPos.le
  have hratio :
      fineDelta /
          prop41Y1PaperFineT fineDelta globalDelta tGlobal =
        (fineDelta /
          (prop41Y1FineRootFactor *
            Real.sqrt (tGlobal * globalDelta))) ^ 2 := by
    unfold prop41Y1PaperFineT prop41Y1RectangleFactor
    field_simp [ne_of_gt N.fineDelta_pos, ne_of_gt N.globalDelta_pos,
      ne_of_gt N.tGlobal_pos, ne_of_gt hsqrtPos,
      ne_of_gt prop41Y1FineRootFactor_pos]
    nlinarith
  rw [hratio, Real.sqrt_sq_eq_abs]
  rw [abs_of_pos]
  · ring
  · exact div_pos N.fineDelta_pos
      (mul_pos prop41Y1FineRootFactor_pos hsqrtPos)

theorem prop41Y1PaperFine_baseScale_le_coarseBaseScale
    {fineDelta globalDelta tGlobal outerWidth : ℝ}
    (N : ActualY1SharpFineScaleNumerics
      fineDelta globalDelta tGlobal outerWidth) :
    fineDelta /
        prop41Y1PaperFineT fineDelta globalDelta tGlobal ≤
      globalDelta / tGlobal := by
  rw [show fineDelta /
          prop41Y1PaperFineT fineDelta globalDelta tGlobal =
        (fineDelta /
          (prop41Y1FineRootFactor *
            Real.sqrt (tGlobal * globalDelta))) ^ 2 by
    have hhalf := prop41Y1PaperFineHalfWidth_eq N
    have hprodPos : 0 < tGlobal * globalDelta :=
      mul_pos N.tGlobal_pos N.globalDelta_pos
    have hsqrtPos : 0 < Real.sqrt (tGlobal * globalDelta) :=
      Real.sqrt_pos.2 hprodPos
    have hsqrtSq :
        (Real.sqrt (tGlobal * globalDelta)) ^ 2 =
          tGlobal * globalDelta :=
      Real.sq_sqrt hprodPos.le
    unfold prop41Y1PaperFineT prop41Y1RectangleFactor
    field_simp [ne_of_gt N.fineDelta_pos, ne_of_gt N.globalDelta_pos,
      ne_of_gt N.tGlobal_pos, ne_of_gt hsqrtPos,
      ne_of_gt prop41Y1FineRootFactor_pos]
    nlinarith]
  have hrootOne : 1 ≤ prop41Y1FineRootFactor := by
    norm_num [prop41Y1FineRootFactor]
  have hsq :
      fineDelta ^ 2 ≤
        prop41Y1FineRootFactor ^ 2 * globalDelta ^ 2 := by
    have hfdNonneg := N.fineDelta_pos.le
    have hgdNonneg := N.globalDelta_pos.le
    have hfdSq : fineDelta ^ 2 ≤ globalDelta ^ 2 :=
      (sq_le_sq₀ hfdNonneg hgdNonneg).2 N.fineDelta_le_globalDelta
    calc
      fineDelta ^ 2 ≤ globalDelta ^ 2 := hfdSq
      _ ≤ prop41Y1FineRootFactor ^ 2 * globalDelta ^ 2 := by
        have hfactor : 1 ≤ prop41Y1FineRootFactor ^ 2 := by
          norm_num [prop41Y1FineRootFactor]
        simpa only [one_mul] using
          mul_le_mul_of_nonneg_right hfactor (sq_nonneg globalDelta)
  have hsqrtSq :
      (Real.sqrt (tGlobal * globalDelta)) ^ 2 =
        tGlobal * globalDelta :=
    Real.sq_sqrt (mul_nonneg N.tGlobal_pos.le N.globalDelta_pos.le)
  rw [div_pow]
  apply (div_le_iff₀
    (sq_pos_of_pos (mul_pos prop41Y1FineRootFactor_pos
      (Real.sqrt_pos.2
        (mul_pos N.tGlobal_pos N.globalDelta_pos))))).2
  calc
    fineDelta ^ 2 ≤
        prop41Y1FineRootFactor ^ 2 * globalDelta ^ 2 := hsq
    _ = globalDelta / tGlobal *
        (prop41Y1FineRootFactor *
          Real.sqrt (tGlobal * globalDelta)) ^ 2 := by
      rw [mul_pow, hsqrtSq]
      field_simp [ne_of_gt N.tGlobal_pos]

theorem prop41Y1PaperFine_canonicalMargin
    {fineDelta globalDelta tGlobal outerWidth : ℝ}
    (N : ActualY1SharpFineScaleNumerics
      fineDelta globalDelta tGlobal outerWidth) :
    Real.sqrt
          (fineDelta /
            prop41Y1PaperFineT fineDelta globalDelta tGlobal) /
        2 ≤
      3 * outerWidth / 32 := by
  have hsqrt :
      Real.sqrt
          (fineDelta /
            prop41Y1PaperFineT fineDelta globalDelta tGlobal) ≤
        Real.sqrt (globalDelta / tGlobal) :=
    Real.sqrt_le_sqrt
      (prop41Y1PaperFine_baseScale_le_coarseBaseScale N)
  have hcoarse :=
    coarse_canonicalMargin_of_prop41_smallScale
      N.globalDelta_pos N.tGlobal_pos N.outerWidth_lower
      N.fineDelta_le_globalDelta N.prop41_smallScale
  linarith

theorem prop41Y1PaperFine_propagation_budget
    {fineDelta globalDelta tGlobal outerWidth : ℝ}
    (N : ActualY1SharpFineScaleNumerics
      fineDelta globalDelta tGlobal outerWidth) :
    (prop41Y1SharpSlopeConstant *
          Real.sqrt (tGlobal * globalDelta) +
        30 * tGlobal *
          (Real.sqrt
            (fineDelta /
              prop41Y1PaperFineT fineDelta globalDelta tGlobal) /
            2)) *
        (Real.sqrt
          (fineDelta /
            prop41Y1PaperFineT fineDelta globalDelta tGlobal) /
          2) ≤
      2 * fineDelta := by
  rw [prop41Y1PaperFineHalfWidth_eq N]
  have hsqrtPos :
      0 < Real.sqrt (tGlobal * globalDelta) :=
    Real.sqrt_pos.2 (mul_pos N.tGlobal_pos N.globalDelta_pos)
  have hsqrtSq :
      (Real.sqrt (tGlobal * globalDelta)) ^ 2 =
        tGlobal * globalDelta :=
    Real.sq_sqrt (mul_nonneg N.tGlobal_pos.le N.globalDelta_pos.le)
  have hfdSq :
      fineDelta ^ 2 ≤ fineDelta * globalDelta := by
    nlinarith [N.fineDelta_pos, N.fineDelta_le_globalDelta]
  have hfdSqT :
      tGlobal * fineDelta ^ 2 ≤
        tGlobal * (fineDelta * globalDelta) :=
    mul_le_mul_of_nonneg_left hfdSq N.tGlobal_pos.le
  rw [prop41Y1SharpSlopeConstant_eq]
  have hcross :
      tGlobal * fineDelta * fineDelta ≤
        fineDelta * (Real.sqrt (tGlobal * globalDelta)) ^ 2 := by
    calc
      tGlobal * fineDelta * fineDelta ≤
          tGlobal * (fineDelta * globalDelta) := by convert hfdSqT using 1 ; ring
      _ = fineDelta * (Real.sqrt (tGlobal * globalDelta)) ^ 2 := by
        rw [hsqrtSq]
        ring
  have hcrossPow :
      tGlobal * fineDelta ^ 2 ≤
        fineDelta * (Real.sqrt (tGlobal * globalDelta)) ^ 2 := by
    simpa only [pow_two, mul_assoc] using hcross
  have hlinear :
      prop41Y1FineRootFactor *
          Real.sqrt (tGlobal * globalDelta) *
          (fineDelta /
            (2 * prop41Y1FineRootFactor *
              Real.sqrt (tGlobal * globalDelta))) =
        fineDelta / 2 := by
    field_simp [ne_of_gt hsqrtPos, ne_of_gt prop41Y1FineRootFactor_pos]
  have hquadratic :
      30 * tGlobal *
          (fineDelta /
            (2 * prop41Y1FineRootFactor *
              Real.sqrt (tGlobal * globalDelta))) *
          (fineDelta /
            (2 * prop41Y1FineRootFactor *
              Real.sqrt (tGlobal * globalDelta))) ≤
        fineDelta / 2 := by
    field_simp [ne_of_gt hsqrtPos, ne_of_gt prop41Y1FineRootFactor_pos]
    norm_num [prop41Y1FineRootFactor] at *
    have hA :
        0 ≤ fineDelta * (Real.sqrt (tGlobal * globalDelta)) ^ 2 :=
      mul_nonneg N.fineDelta_pos.le (sq_nonneg _)
    nlinarith only [hcrossPow, hA]
  nlinarith [hlinear, hquadratic, N.fineDelta_pos]

end
end FamilyStickyCinematicL32Prop41ActualY1SharpFineScaleTangencyV1
