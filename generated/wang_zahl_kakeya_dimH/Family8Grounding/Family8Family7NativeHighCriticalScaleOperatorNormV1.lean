import Family8Grounding.Family8Family7NativeHighCriticalScaleAxisChartV1
import Mathlib.Tactic

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 1000000

open Set MeasureTheory
open scoped ENNReal NNReal

namespace Family8Family7NativeHighCriticalScaleOperatorNormV1

open LeanEval.Analysis.WangZahlKakeya
open Submission.Kakeya.ConvexGeometry
open Family8Family7NativeHighCriticalScaleAffineMapV1
open Family8SelectedParentPlankFineProxyCarrierV3
open FamilyStickyCinematicL32ActualTubeCoefficientDistancesV1
open FamilyStickyWZ2ProjectionSliceRetentionV1

noncomputable section

/-!
# Operator norm of the concrete critical-scale normalization

The original L3 chart bounds both reference graph slopes by 2.
Coordinatewise estimates and the true critical-scale ceiling t ≤ 16 then
give the uniform operator bound 2/t.
-/

theorem norm_point3_le_abs_add_abs_add_abs (x y z : Real) :
    ‖point3 x y z‖ ≤ |x| + |y| + |z| := by
  apply (sq_le_sq₀ (norm_nonneg _) (by positivity)).mp
  rw [EuclideanSpace.real_norm_sq_eq, Fin.sum_univ_three]
  change x ^ 2 + y ^ 2 + z ^ 2 ≤ (|x| + |y| + |z|) ^ 2
  nlinarith [abs_nonneg x, abs_nonneg y, abs_nonneg z,
    sq_abs x, sq_abs y, sq_abs z]

theorem abs_projectedTubeGraphC_le_two_of_final_half
    {radius : NNReal} (T : Tube radius)
    (hforward : (1 / 2 : Real) ≤ T.axis.direction 2) :
    |projectedTubeGraphC T| ≤ 2 := by
  have hzpos : 0 < T.axis.direction 2 := by linarith
  have hx : |T.axis.direction 0| ≤ 1 := by
    calc
      |T.axis.direction 0| ≤ ‖T.axis.direction‖ := by
        simpa only [Real.norm_eq_abs] using
          PiLp.norm_apply_le T.axis.direction (0 : Fin 3)
      _ = 1 := T.axis.norm_direction
  unfold projectedTubeGraphC
  rw [abs_div, abs_of_pos hzpos]
  apply (div_le_iff₀ hzpos).2
  nlinarith

theorem abs_projectedTubeGraphD_le_two_of_final_half
    {radius : NNReal} (T : Tube radius)
    (hforward : (1 / 2 : Real) ≤ T.axis.direction 2) :
    |projectedTubeGraphD T| ≤ 2 := by
  have hzpos : 0 < T.axis.direction 2 := by linarith
  have hy : |T.axis.direction 1| ≤ 1 := by
    calc
      |T.axis.direction 1| ≤ ‖T.axis.direction‖ := by
        simpa only [Real.norm_eq_abs] using
          PiLp.norm_apply_le T.axis.direction (1 : Fin 3)
      _ = 1 := T.axis.norm_direction
  unfold projectedTubeGraphD
  rw [abs_div, abs_of_pos hzpos]
  apply (div_le_iff₀ hzpos).2
  nlinarith

theorem norm_criticalScaleLinearEquiv_le_two_div
    (t : Real) (ht : 0 < t) (c0 d0 : Real)
    (htUpper : t ≤ 16) (hc0 : |c0| ≤ 2) (hd0 : |d0| ≤ 2)
    (p : Space) :
    ‖criticalScaleLinearEquiv t ht c0 d0 p‖ ≤
      (2 / t) * ‖p‖ := by
  have hp0 : |p 0| ≤ ‖p‖ := by
    simpa only [Real.norm_eq_abs] using PiLp.norm_apply_le p (0 : Fin 3)
  have hp1 : |p 1| ≤ ‖p‖ := by
    simpa only [Real.norm_eq_abs] using PiLp.norm_apply_le p (1 : Fin 3)
  have hp2 : |p 2| ≤ ‖p‖ := by
    simpa only [Real.norm_eq_abs] using PiLp.norm_apply_le p (2 : Fin 3)
  have hnum0 : |p 0 - c0 * p 2| ≤ 3 * ‖p‖ := by
    calc
      |p 0 - c0 * p 2| ≤ |p 0| + |c0 * p 2| := by
        simpa using abs_sub_le (p 0) 0 (c0 * p 2)
      _ = |p 0| + |c0| * |p 2| := by rw [abs_mul]
      _ ≤ ‖p‖ + 2 * ‖p‖ := by gcongr
      _ = 3 * ‖p‖ := by ring
  have hnum1 : |p 1 - d0 * p 2| ≤ 3 * ‖p‖ := by
    calc
      |p 1 - d0 * p 2| ≤ |p 1| + |d0 * p 2| := by
        simpa using abs_sub_le (p 1) 0 (d0 * p 2)
      _ = |p 1| + |d0| * |p 2| := by rw [abs_mul]
      _ ≤ ‖p‖ + 2 * ‖p‖ := by gcongr
      _ = 3 * ‖p‖ := by ring
  have hden : 0 < 16 * t := mul_pos (by norm_num) ht
  have hx :
      |(p 0 - c0 * p 2) / (16 * t)| ≤
        (3 / (16 * t)) * ‖p‖ := by
    rw [abs_div, abs_of_pos hden]
    apply (div_le_iff₀ hden).2
    calc
      |p 0 - c0 * p 2| ≤ 3 * ‖p‖ := hnum0
      _ = (3 / (16 * t)) * ‖p‖ * (16 * t) := by
        field_simp [ht.ne']
  have hy :
      |(p 1 - d0 * p 2) / (16 * t)| ≤
        (3 / (16 * t)) * ‖p‖ := by
    rw [abs_div, abs_of_pos hden]
    apply (div_le_iff₀ hden).2
    calc
      |p 1 - d0 * p 2| ≤ 3 * ‖p‖ := hnum1
      _ = (3 / (16 * t)) * ‖p‖ * (16 * t) := by
        field_simp [ht.ne']
  have hz : |p 2 / 16| ≤ (1 / 16 : Real) * ‖p‖ := by
    rw [abs_div, abs_of_pos (by norm_num : (0 : Real) < 16)]
    apply (div_le_iff₀ (by norm_num : (0 : Real) < 16)).2
    calc
      |p 2| ≤ ‖p‖ := hp2
      _ = (1 / 16 : Real) * ‖p‖ * 16 := by ring
  have hcoeff :
      6 / (16 * t) + (1 / 16 : Real) ≤ 2 / t := by
    calc
      6 / (16 * t) + (1 / 16 : Real) =
          (6 + t) / (16 * t) := by field_simp [ht.ne']
      _ ≤ 32 / (16 * t) := by
        apply div_le_div_of_nonneg_right
        · nlinarith
        · exact hden.le
      _ = 2 / t := by field_simp [ht.ne']; norm_num
  calc
    ‖criticalScaleLinearEquiv t ht c0 d0 p‖ =
        ‖point3
          ((p 0 - c0 * p 2) / (16 * t))
          ((p 1 - d0 * p 2) / (16 * t))
          (p 2 / 16)‖ := rfl
    _ ≤ |(p 0 - c0 * p 2) / (16 * t)| +
          |(p 1 - d0 * p 2) / (16 * t)| +
          |p 2 / 16| :=
      norm_point3_le_abs_add_abs_add_abs _ _ _
    _ ≤ (3 / (16 * t)) * ‖p‖ +
          (3 / (16 * t)) * ‖p‖ +
          (1 / 16 : Real) * ‖p‖ := by gcongr
    _ = (6 / (16 * t) + (1 / 16 : Real)) * ‖p‖ := by ring
    _ ≤ (2 / t) * ‖p‖ :=
      mul_le_mul_of_nonneg_right hcoeff (norm_nonneg p)

theorem affineLinearOperatorNorm_criticalScaleAffineEquiv_le_two_div
    (t : Real) (ht : 0 < t) (a0 b0 c0 d0 : Real)
    (htUpper : t ≤ 16) (hc0 : |c0| ≤ 2) (hd0 : |d0| ≤ 2) :
    affineLinearOperatorNorm
      (criticalScaleAffineEquiv t ht a0 b0 c0 d0) ≤ 2 / t := by
  unfold affineLinearOperatorNorm
  apply ContinuousLinearMap.opNorm_le_bound _ (by positivity)
  intro p
  change ‖criticalScaleLinearEquiv t ht c0 d0 p‖ ≤ (2 / t) * ‖p‖
  exact norm_criticalScaleLinearEquiv_le_two_div
    t ht c0 d0 htUpper hc0 hd0 p

#print axioms norm_point3_le_abs_add_abs_add_abs
#print axioms abs_projectedTubeGraphC_le_two_of_final_half
#print axioms abs_projectedTubeGraphD_le_two_of_final_half
#print axioms norm_criticalScaleLinearEquiv_le_two_div
#print axioms
  affineLinearOperatorNorm_criticalScaleAffineEquiv_le_two_div

end

end Family8Family7NativeHighCriticalScaleOperatorNormV1
