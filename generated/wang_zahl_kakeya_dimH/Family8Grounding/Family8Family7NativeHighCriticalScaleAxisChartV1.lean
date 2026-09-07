import Family8Grounding.Family8Family7NativeHighCriticalScaleAffineMapV1
import Mathlib.Tactic

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 1000000

open Set MeasureTheory
open scoped ENNReal NNReal

namespace Family8Family7NativeHighCriticalScaleAxisChartV1

open LeanEval.Analysis.WangZahlKakeya
open Submission.Kakeya.ConvexGeometry
open Family8ContractedJohnActualTubeProxyV1
open Family8Family7NativeHighCriticalBallDatumV1
open Family8Family7NativeHighCriticalBallRestrictedSourceV1
open Family8Family7NativeHighCriticalBallAffineProxyV1
open Family8Family7NativeHighCriticalScaleAffineMapV1
open Family8SelectedParentPlankFineProxyDatumV1
open FamilyStickyCinematicL32ActualTubeCoefficientDistancesV1
open FamilyStickyCinematicL32PyzActualNormFirstAllCenterMassWeightedBranchTypesV5C
open FamilyStickyCinematicL32Prop41CanonicalMaximizerNonconcentrationV1

noncomputable section

universe u

/-!
# Axis and chart control for the concrete critical-scale map

The reduced metric controls the `D` slope and the native common bucket
controls the omitted `C` slope.  After centering at the canonical critical
tube, both normalized slopes have absolute value at most one.  The common
factor `1/16` then makes the transformed axis shorter than one, while its
unit extension keeps final coordinate at least `1/2`.
-/

theorem direction_zero_sub_mul_eq_graphC_sub
    {radius : NNReal} (T : Tube radius) (c0 : Real)
    (hforward : 0 < T.axis.direction 2) :
    T.axis.direction 0 - c0 * T.axis.direction 2 =
      T.axis.direction 2 * (projectedTubeGraphC T - c0) := by
  unfold projectedTubeGraphC
  field_simp [hforward.ne']

theorem direction_one_sub_mul_eq_graphD_sub
    {radius : NNReal} (T : Tube radius) (d0 : Real)
    (hforward : 0 < T.axis.direction 2) :
    T.axis.direction 1 - d0 * T.axis.direction 2 =
      T.axis.direction 2 * (projectedTubeGraphD T - d0) := by
  unfold projectedTubeGraphD
  field_simp [hforward.ne']

theorem abs_affineImageAxisVector_criticalScale_zero_le
    {radius : NNReal} (t : Real) (ht : 0 < t)
    (a0 b0 c0 d0 : Real) (T : Tube radius)
    (hforward : 0 < T.axis.direction 2)
    (hC : |projectedTubeGraphC T - c0| ≤ t) :
    |(affineImageAxisVector
      (criticalScaleAffineEquiv t ht a0 b0 c0 d0) T) 0| ≤
        T.axis.direction 2 / 16 := by
  rw [affineImageAxisVector_criticalScale_apply_zero,
    direction_zero_sub_mul_eq_graphC_sub T c0 hforward,
    abs_div, abs_mul, abs_of_pos hforward,
    abs_of_pos (mul_pos (by norm_num) ht)]
  apply (div_le_iff₀ (mul_pos (by norm_num) ht)).2
  have hmul := mul_le_mul_of_nonneg_left hC hforward.le
  convert hmul using 1
  all_goals field_simp [ht.ne']

theorem abs_affineImageAxisVector_criticalScale_one_le
    {radius : NNReal} (t : Real) (ht : 0 < t)
    (a0 b0 c0 d0 : Real) (T : Tube radius)
    (hforward : 0 < T.axis.direction 2)
    (hD : |projectedTubeGraphD T - d0| ≤ t) :
    |(affineImageAxisVector
      (criticalScaleAffineEquiv t ht a0 b0 c0 d0) T) 1| ≤
        T.axis.direction 2 / 16 := by
  rw [affineImageAxisVector_criticalScale_apply_one,
    direction_one_sub_mul_eq_graphD_sub T d0 hforward,
    abs_div, abs_mul, abs_of_pos hforward,
    abs_of_pos (mul_pos (by norm_num) ht)]
  apply (div_le_iff₀ (mul_pos (by norm_num) ht)).2
  have hmul := mul_le_mul_of_nonneg_left hD hforward.le
  convert hmul using 1
  all_goals field_simp [ht.ne']

theorem criticalScale_axisLength_le_one_of_graph_gaps
    {radius : NNReal} (t : Real) (ht : 0 < t)
    (a0 b0 c0 d0 : Real) (T : Tube radius)
    (hforward : 0 < T.axis.direction 2)
    (hC : |projectedTubeGraphC T - c0| ≤ t)
    (hD : |projectedTubeGraphD T - d0| ≤ t) :
    ‖affineImageAxisVector
      (criticalScaleAffineEquiv t ht a0 b0 c0 d0) T‖ ≤ 1 := by
  let w := affineImageAxisVector
    (criticalScaleAffineEquiv t ht a0 b0 c0 d0) T
  have h0 : |w 0| ≤ T.axis.direction 2 / 16 :=
    abs_affineImageAxisVector_criticalScale_zero_le
      t ht a0 b0 c0 d0 T hforward hC
  have h1 : |w 1| ≤ T.axis.direction 2 / 16 :=
    abs_affineImageAxisVector_criticalScale_one_le
      t ht a0 b0 c0 d0 T hforward hD
  have h2 : w 2 = T.axis.direction 2 / 16 := by
    exact affineImageAxisVector_criticalScale_apply_two
      t ht a0 b0 c0 d0 T
  have hzle : T.axis.direction 2 ≤ 1 := by
    calc
      T.axis.direction 2 ≤ |T.axis.direction 2| := le_abs_self _
      _ ≤ ‖T.axis.direction‖ := by
        simpa only [Real.norm_eq_abs] using
          PiLp.norm_apply_le T.axis.direction (2 : Fin 3)
      _ = 1 := T.axis.norm_direction
  have h0sq : (w 0) ^ 2 ≤ (T.axis.direction 2 / 16) ^ 2 := by
    have hs := (sq_le_sq₀ (abs_nonneg (w 0))
      (div_nonneg hforward.le (by norm_num))).2 h0
    simpa only [sq_abs] using hs
  have h1sq : (w 1) ^ 2 ≤ (T.axis.direction 2 / 16) ^ 2 := by
    have hs := (sq_le_sq₀ (abs_nonneg (w 1))
      (div_nonneg hforward.le (by norm_num))).2 h1
    simpa only [sq_abs] using hs
  change ‖w‖ ≤ 1
  apply (sq_le_sq₀ (norm_nonneg w) (by norm_num)).mp
  rw [EuclideanSpace.real_norm_sq_eq, Fin.sum_univ_three]
  rw [h2]
  norm_num at h0sq h1sq ⊢
  nlinarith [sq_nonneg (T.axis.direction 2)]

theorem criticalScale_axisDirection_final_half_of_graph_gaps
    {radius : NNReal} (t : Real) (ht : 0 < t)
    (a0 b0 c0 d0 : Real) (T : Tube radius)
    (hforward : 0 < T.axis.direction 2)
    (hC : |projectedTubeGraphC T - c0| ≤ t)
    (hD : |projectedTubeGraphD T - d0| ≤ t) :
    (1 / 2 : Real) ≤
      |(affineImageUnitExtensionAxis
        (criticalScaleAffineEquiv t ht a0 b0 c0 d0) T).direction 2| := by
  let e := criticalScaleAffineEquiv t ht a0 b0 c0 d0
  let w := affineImageAxisVector e T
  have h0 : |w 0| ≤ T.axis.direction 2 / 16 := by
    exact abs_affineImageAxisVector_criticalScale_zero_le
      t ht a0 b0 c0 d0 T hforward hC
  have h1 : |w 1| ≤ T.axis.direction 2 / 16 := by
    exact abs_affineImageAxisVector_criticalScale_one_le
      t ht a0 b0 c0 d0 T hforward hD
  have h2 : w 2 = T.axis.direction 2 / 16 := by
    exact affineImageAxisVector_criticalScale_apply_two
      t ht a0 b0 c0 d0 T
  have hw2pos : 0 < w 2 := by rw [h2]; positivity
  have h0sq : (w 0) ^ 2 ≤ (T.axis.direction 2 / 16) ^ 2 := by
    have hs := (sq_le_sq₀ (abs_nonneg (w 0))
      (div_nonneg hforward.le (by norm_num))).2 h0
    simpa only [sq_abs] using hs
  have h1sq : (w 1) ^ 2 ≤ (T.axis.direction 2 / 16) ^ 2 := by
    have hs := (sq_le_sq₀ (abs_nonneg (w 1))
      (div_nonneg hforward.le (by norm_num))).2 h1
    simpa only [sq_abs] using hs
  have hnorm : ‖w‖ ≤ 2 * w 2 := by
    apply (sq_le_sq₀ (norm_nonneg w) (mul_nonneg (by norm_num)
      hw2pos.le)).mp
    rw [EuclideanSpace.real_norm_sq_eq, Fin.sum_univ_three]
    rw [h2]
    nlinarith [sq_nonneg (T.axis.direction 2)]
  have hwne : w ≠ 0 := by
    intro hw
    have hzero : w 2 = 0 := by
      simpa using congrArg (fun v : Space => v 2) hw
    exact hw2pos.ne' hzero
  have hnormpos : 0 < ‖w‖ := norm_pos_iff.mpr hwne
  have hhalf : ‖w‖ / 2 ≤ w 2 := by nlinarith
  change (1 / 2 : Real) ≤
    |(affineImageUnitExtensionAxis e T).direction 2|
  rw [affineImageUnitExtensionAxis_direction, affineImageAxisDirection]
  change (1 / 2 : Real) ≤ |‖w‖⁻¹ * w 2|
  rw [abs_mul, abs_of_pos (inv_pos.mpr hnormpos), abs_of_pos hw2pos]
  calc
    (1 / 2 : Real) = ‖w‖⁻¹ * (‖w‖ / 2) := by
      field_simp [hnormpos.ne']
    _ ≤ ‖w‖⁻¹ * w 2 :=
      mul_le_mul_of_nonneg_left hhalf (inv_nonneg.mpr hnormpos.le)

#print axioms direction_zero_sub_mul_eq_graphC_sub
#print axioms direction_one_sub_mul_eq_graphD_sub
#print axioms abs_affineImageAxisVector_criticalScale_zero_le
#print axioms abs_affineImageAxisVector_criticalScale_one_le
#print axioms criticalScale_axisLength_le_one_of_graph_gaps
#print axioms criticalScale_axisDirection_final_half_of_graph_gaps

end

end Family8Family7NativeHighCriticalScaleAxisChartV1
