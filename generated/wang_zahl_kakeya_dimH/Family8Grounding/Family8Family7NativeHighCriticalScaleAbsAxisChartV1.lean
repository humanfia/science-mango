import Family8Grounding.Family8Family7NativeHighCriticalScaleAffineMapV1
import Mathlib.Tactic

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 2000000

open Set MeasureTheory
open scoped ENNReal NNReal

namespace Family8Family7NativeHighCriticalScaleAbsAxisChartV1

open LeanEval.Analysis.WangZahlKakeya
open Submission.Kakeya.ConvexGeometry
open Family8ContractedJohnActualTubeProxyV1
open Family8Family7NativeHighCriticalScaleAffineMapV1
open Family8SelectedParentPlankFineProxyCarrierV3
open FamilyStickyCinematicL32ActualTubeCoefficientDistancesV1
open FamilyStickyWZ2ProjectionSliceRetentionV1

noncomputable section

/-!
# Sign-free critical-scale axis and chart estimates

The actual `WZL3` source records an absolute final-coordinate chart.  These
lemmas give the sign-free form of the concrete critical-scale estimates.
-/

theorem abs_projectedTubeGraphC_le_two_of_abs_final_half
    {radius : NNReal} (T : Tube radius)
    (hchart : (1 / 2 : Real) ≤ |T.axis.direction 2|) :
    |projectedTubeGraphC T| ≤ 2 := by
  have hzpos : 0 < |T.axis.direction 2| := by linarith
  have hx : |T.axis.direction 0| ≤ 1 := by
    calc
      |T.axis.direction 0| ≤ ‖T.axis.direction‖ := by
        simpa only [Real.norm_eq_abs] using
          PiLp.norm_apply_le T.axis.direction (0 : Fin 3)
      _ = 1 := T.axis.norm_direction
  unfold projectedTubeGraphC
  rw [abs_div]
  apply (div_le_iff₀ hzpos).2
  nlinarith

theorem abs_projectedTubeGraphD_le_two_of_abs_final_half
    {radius : NNReal} (T : Tube radius)
    (hchart : (1 / 2 : Real) ≤ |T.axis.direction 2|) :
    |projectedTubeGraphD T| ≤ 2 := by
  have hzpos : 0 < |T.axis.direction 2| := by linarith
  have hy : |T.axis.direction 1| ≤ 1 := by
    calc
      |T.axis.direction 1| ≤ ‖T.axis.direction‖ := by
        simpa only [Real.norm_eq_abs] using
          PiLp.norm_apply_le T.axis.direction (1 : Fin 3)
      _ = 1 := T.axis.norm_direction
  unfold projectedTubeGraphD
  rw [abs_div]
  apply (div_le_iff₀ hzpos).2
  nlinarith

theorem abs_affineImageAxisVector_criticalScale_zero_le_abs
    {radius : NNReal} (t : Real) (ht : 0 < t)
    (a0 b0 c0 d0 : Real) (T : Tube radius)
    (hvertical : T.axis.direction 2 ≠ 0)
    (hC : |projectedTubeGraphC T - c0| ≤ t) :
    |(affineImageAxisVector
      (criticalScaleAffineEquiv t ht a0 b0 c0 d0) T) 0| ≤
        |T.axis.direction 2| / 16 := by
  rw [affineImageAxisVector_criticalScale_apply_zero]
  have hid : T.axis.direction 0 - c0 * T.axis.direction 2 =
      T.axis.direction 2 * (projectedTubeGraphC T - c0) := by
    unfold projectedTubeGraphC
    field_simp [hvertical]
  rw [hid, abs_div, abs_mul,
    abs_of_pos (mul_pos (by norm_num) ht)]
  calc
    |T.axis.direction 2| * |projectedTubeGraphC T - c0| /
          (16 * t) ≤ |T.axis.direction 2| * t / (16 * t) := by
      gcongr
    _ = |T.axis.direction 2| / 16 := by
      field_simp [ht.ne']

theorem abs_affineImageAxisVector_criticalScale_one_le_abs
    {radius : NNReal} (t : Real) (ht : 0 < t)
    (a0 b0 c0 d0 : Real) (T : Tube radius)
    (hvertical : T.axis.direction 2 ≠ 0)
    (hD : |projectedTubeGraphD T - d0| ≤ t) :
    |(affineImageAxisVector
      (criticalScaleAffineEquiv t ht a0 b0 c0 d0) T) 1| ≤
        |T.axis.direction 2| / 16 := by
  rw [affineImageAxisVector_criticalScale_apply_one]
  have hid : T.axis.direction 1 - d0 * T.axis.direction 2 =
      T.axis.direction 2 * (projectedTubeGraphD T - d0) := by
    unfold projectedTubeGraphD
    field_simp [hvertical]
  rw [hid, abs_div, abs_mul,
    abs_of_pos (mul_pos (by norm_num) ht)]
  calc
    |T.axis.direction 2| * |projectedTubeGraphD T - d0| /
          (16 * t) ≤ |T.axis.direction 2| * t / (16 * t) := by
      gcongr
    _ = |T.axis.direction 2| / 16 := by
      field_simp [ht.ne']

theorem criticalScale_axisLength_le_one_of_graph_gaps_abs
    {radius : NNReal} (t : Real) (ht : 0 < t)
    (a0 b0 c0 d0 : Real) (T : Tube radius)
    (hvertical : T.axis.direction 2 ≠ 0)
    (hC : |projectedTubeGraphC T - c0| ≤ t)
    (hD : |projectedTubeGraphD T - d0| ≤ t) :
    ‖affineImageAxisVector
      (criticalScaleAffineEquiv t ht a0 b0 c0 d0) T‖ ≤ 1 := by
  let w := affineImageAxisVector
    (criticalScaleAffineEquiv t ht a0 b0 c0 d0) T
  have h0 : |w 0| ≤ |T.axis.direction 2| / 16 :=
    abs_affineImageAxisVector_criticalScale_zero_le_abs
      t ht a0 b0 c0 d0 T hvertical hC
  have h1 : |w 1| ≤ |T.axis.direction 2| / 16 :=
    abs_affineImageAxisVector_criticalScale_one_le_abs
      t ht a0 b0 c0 d0 T hvertical hD
  have h2 : w 2 = T.axis.direction 2 / 16 :=
    affineImageAxisVector_criticalScale_apply_two
      t ht a0 b0 c0 d0 T
  have hzle : |T.axis.direction 2| ≤ 1 := by
    calc
      |T.axis.direction 2| ≤ ‖T.axis.direction‖ := by
        simpa only [Real.norm_eq_abs] using
          PiLp.norm_apply_le T.axis.direction (2 : Fin 3)
      _ = 1 := T.axis.norm_direction
  have h0sq : (w 0) ^ 2 ≤ (|T.axis.direction 2| / 16) ^ 2 := by
    have hs := (sq_le_sq₀ (abs_nonneg (w 0))
      (div_nonneg (abs_nonneg _) (by norm_num))).2 h0
    simpa only [sq_abs] using hs
  have h1sq : (w 1) ^ 2 ≤ (|T.axis.direction 2| / 16) ^ 2 := by
    have hs := (sq_le_sq₀ (abs_nonneg (w 1))
      (div_nonneg (abs_nonneg _) (by norm_num))).2 h1
    simpa only [sq_abs] using hs
  have hzsq : (T.axis.direction 2) ^ 2 ≤ 1 := by
    have hs := (sq_le_sq₀ (abs_nonneg (T.axis.direction 2))
      (by norm_num : (0 : Real) ≤ 1)).2 hzle
    simpa only [sq_abs, one_pow] using hs
  have habsq : (|T.axis.direction 2| / 16) ^ 2 =
      (T.axis.direction 2) ^ 2 / 256 := by
    rw [div_pow, sq_abs]
    norm_num
  rw [habsq] at h0sq h1sq
  change ‖w‖ ≤ 1
  apply (sq_le_sq₀ (norm_nonneg w) (by norm_num)).mp
  rw [EuclideanSpace.real_norm_sq_eq, Fin.sum_univ_three, h2]
  norm_num at ⊢
  nlinarith [sq_nonneg (T.axis.direction 2)]

theorem criticalScale_axisDirection_final_half_of_graph_gaps_abs
    {radius : NNReal} (t : Real) (ht : 0 < t)
    (a0 b0 c0 d0 : Real) (T : Tube radius)
    (hvertical : T.axis.direction 2 ≠ 0)
    (hC : |projectedTubeGraphC T - c0| ≤ t)
    (hD : |projectedTubeGraphD T - d0| ≤ t) :
    (1 / 2 : Real) ≤
      |(affineImageUnitExtensionAxis
        (criticalScaleAffineEquiv t ht a0 b0 c0 d0) T).direction 2| := by
  let e := criticalScaleAffineEquiv t ht a0 b0 c0 d0
  let w := affineImageAxisVector e T
  have h0 : |w 0| ≤ |T.axis.direction 2| / 16 :=
    abs_affineImageAxisVector_criticalScale_zero_le_abs
      t ht a0 b0 c0 d0 T hvertical hC
  have h1 : |w 1| ≤ |T.axis.direction 2| / 16 :=
    abs_affineImageAxisVector_criticalScale_one_le_abs
      t ht a0 b0 c0 d0 T hvertical hD
  have h2 : w 2 = T.axis.direction 2 / 16 :=
    affineImageAxisVector_criticalScale_apply_two
      t ht a0 b0 c0 d0 T
  have h0sq : (w 0) ^ 2 ≤ (|T.axis.direction 2| / 16) ^ 2 := by
    have hs := (sq_le_sq₀ (abs_nonneg (w 0))
      (div_nonneg (abs_nonneg _) (by norm_num))).2 h0
    simpa only [sq_abs] using hs
  have h1sq : (w 1) ^ 2 ≤ (|T.axis.direction 2| / 16) ^ 2 := by
    have hs := (sq_le_sq₀ (abs_nonneg (w 1))
      (div_nonneg (abs_nonneg _) (by norm_num))).2 h1
    simpa only [sq_abs] using hs
  have hw2ne : w 2 ≠ 0 := by
    rw [h2]
    exact div_ne_zero hvertical (by norm_num)
  have hwne : w ≠ 0 := by
    intro hw
    apply hw2ne
    simpa using congrArg (fun v : Space => v 2) hw
  have hnormpos : 0 < ‖w‖ := norm_pos_iff.mpr hwne
  have hnorm : ‖w‖ ≤ 2 * |w 2| := by
    apply (sq_le_sq₀ (norm_nonneg w)
      (mul_nonneg (by norm_num) (abs_nonneg _))).mp
    rw [EuclideanSpace.real_norm_sq_eq, Fin.sum_univ_three, h2,
      abs_div, abs_of_pos (by norm_num : (0 : Real) < 16)]
    nlinarith [sq_nonneg (T.axis.direction 2),
      sq_abs (T.axis.direction 2)]
  have hhalf : ‖w‖ / 2 ≤ |w 2| := by nlinarith
  change (1 / 2 : Real) ≤ |(affineImageUnitExtensionAxis e T).direction 2|
  rw [affineImageUnitExtensionAxis_direction, affineImageAxisDirection]
  change (1 / 2 : Real) ≤ |‖w‖⁻¹ * w 2|
  rw [abs_mul, abs_of_pos (inv_pos.mpr hnormpos)]
  calc
    (1 / 2 : Real) = ‖w‖⁻¹ * (‖w‖ / 2) := by
      field_simp [hnormpos.ne']
    _ ≤ ‖w‖⁻¹ * |w 2| :=
      mul_le_mul_of_nonneg_left hhalf (inv_nonneg.mpr hnormpos.le)

#print axioms abs_projectedTubeGraphC_le_two_of_abs_final_half
#print axioms abs_projectedTubeGraphD_le_two_of_abs_final_half
#print axioms abs_affineImageAxisVector_criticalScale_zero_le_abs
#print axioms abs_affineImageAxisVector_criticalScale_one_le_abs
#print axioms criticalScale_axisLength_le_one_of_graph_gaps_abs
#print axioms criticalScale_axisDirection_final_half_of_graph_gaps_abs

end

end Family8Family7NativeHighCriticalScaleAbsAxisChartV1
