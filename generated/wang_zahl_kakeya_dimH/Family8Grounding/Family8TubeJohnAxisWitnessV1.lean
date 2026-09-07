import Family8Grounding.Family8Def212ConvexWolffAtEveryScaleV2
import Submission.Kakeya.ConvexFactoring.TubeFrameBoxDimensions

set_option autoImplicit false
set_option warningAsError true

open Set
open scoped NNReal InnerProductSpace

namespace Family8TubeJohnAxisWitnessV1

open LeanEval.Analysis.WangZahlKakeya
open Submission.Kakeya.ConvexGeometry
open Family8Def212ConvexWolffAtEveryScaleV2

noncomputable section

/-!
# An explicit John-axis witness for a positive tube

For `0 < rho <= 1/2`, use the tube midpoint, an orthonormal frame whose last
vector is the tube direction, and semiaxes `rho, rho, 1/2`.  This construction
uses the capsule geometry of the tube directly and does not invoke a general
John theorem.
-/

/-- The semiaxes of the explicit midpoint ellipsoid. -/
def tubeJohnRadii (rho : NNReal) : Fin 3 -> NNReal :=
  ![rho, rho, (2 : NNReal)⁻¹]

/-- Every positive tube of radius at most `1/2` has an explicit factor-three
John-axis witness. -/
theorem Tube.johnAxisWitness_of_pos_le_half
    {rho : NNReal} (T : Tube rho) (hrho : 0 < rho)
    (hrhoHalf : rho <= (2 : NNReal)⁻¹) :
    Nonempty (JohnAxisWitness T.body) := by
  obtain ⟨frame, hframe⟩ := T.exists_alignedFrame
  let center : Space := tubeCenter T
  let radius : Fin 3 -> NNReal := tubeJohnRadii rho
  have hrhoReal : 0 < (rho : Real) := NNReal.coe_pos.mpr hrho
  have hrho0 : (rho : Real) ≠ 0 := hrhoReal.ne'
  have hrhoHalfReal : (rho : Real) <= (2 : Real)⁻¹ := by
    exact_mod_cast hrhoHalf
  refine ⟨
    { center := center
      frame := frame
      radius := radius
      inner := ?_
      outer := ?_ }⟩
  · intro x hx
    rcases hx with ⟨z, hz, rfl⟩
    rw [Fin.sum_univ_three] at hz
    norm_num at hz
    have hz2sq : (z 2) ^ 2 <= 1 := by
      nlinarith [sq_nonneg (z 0), sq_nonneg (z 1)]
    have hz2lo : -1 <= z 2 := by nlinarith [sq_nonneg (z 2 + 1)]
    have hz2hi : z 2 <= 1 := by nlinarith [sq_nonneg (z 2 - 1)]
    let t : Real := (2 : Real)⁻¹ + z 2 / 2
    have ht : t ∈ Set.Icc (0 : Real) 1 := by
      constructor <;> dsimp only [t] <;> norm_num at * <;> linarith
    apply Metric.mem_cthickening_of_dist_le
      (center + ∑ i, (z i * (radius i : Real)) • frame i)
      (T.axis.base + t • T.axis.direction) (rho : Real)
      T.axis.carrier (T.axis.mem_carrier_of_mem_Icc ht)
    have hvec :
        center + ∑ i, (z i * (radius i : Real)) • frame i -
            (T.axis.base + t • T.axis.direction) =
          (z 0 * (rho : Real)) • frame 0 +
            (z 1 * (rho : Real)) • frame 1 := by
      rw [Fin.sum_univ_three]
      dsimp only [center, tubeCenter, t]
      simp [radius, tubeJohnRadii]
      rw [hframe]
      module
    rw [dist_eq_norm, hvec]
    apply (sq_le_sq₀ (norm_nonneg _) (NNReal.zero_le_coe)).mp
    have hnormSq :
        ‖(z 0 * (rho : Real)) • frame 0 +
            (z 1 * (rho : Real)) • frame 1‖ ^ 2 =
          (rho : Real) ^ 2 * ((z 0) ^ 2 + (z 1) ^ 2) := by
      rw [← real_inner_self_eq_norm_sq]
      simp only [inner_add_left, inner_add_right, real_inner_smul_left,
        real_inner_smul_right, frame.inner_eq_ite]
      norm_num
      ring
    rw [hnormSq]
    have hz01 : (z 0) ^ 2 + (z 1) ^ 2 <= 1 := by
      nlinarith [sq_nonneg (z 2)]
    calc
      (rho : Real) ^ 2 * ((z 0) ^ 2 + (z 1) ^ 2) <=
          (rho : Real) ^ 2 * 1 := by gcongr
      _ = (rho : Real) ^ 2 := by ring
  · intro x hx
    rw [Tube.coe_body] at hx
    rw [Tube.carrier,
      T.axis.isCompact_carrier.cthickening_eq_biUnion_closedBall
        (show 0 <= (rho : Real) by positivity)] at hx
    simp only [Set.mem_iUnion, Metric.mem_closedBall] at hx
    obtain ⟨y, hy, hxy⟩ := hx
    rw [T.axis.carrier_eq_image] at hy
    obtain ⟨t, ht, rfl⟩ := hy
    let q : Space := T.axis.base + t • T.axis.direction
    let e : Space := x - q
    let d : Fin 3 -> Real := fun i => ⟪frame i, x - center⟫_Real
    let z : Fin 3 -> Real := fun i =>
      if i = 2 then 2 * d i else d i / (rho : Real)
    have heNorm : ‖e‖ <= (rho : Real) := by
      simpa only [e, q, dist_eq_norm, norm_sub_rev] using hxy
    have heNormSq : ‖e‖ ^ 2 <= (rho : Real) ^ 2 := by
      nlinarith [norm_nonneg e]
    have hparseval := frame.sum_sq_inner_right e
    rw [Fin.sum_univ_three] at hparseval
    have hdtrans (i : Fin 3) (hi : i ≠ 2) :
        d i = ⟪frame i, e⟫_Real := by
      dsimp only [d, e, q, center, tubeCenter]
      rw [inner_sub_right, inner_sub_right, inner_add_right,
        inner_add_right, real_inner_smul_right, real_inner_smul_right,
        ← hframe, frame.inner_eq_zero hi]
      ring
    have htransNum : (d 0) ^ 2 + (d 1) ^ 2 <= (rho : Real) ^ 2 := by
      rw [hdtrans 0 (by decide), hdtrans 1 (by decide)]
      nlinarith [sq_nonneg ⟪frame 2, e⟫_Real]
    have htrans :
        (d 0 / (rho : Real)) ^ 2 + (d 1 / (rho : Real)) ^ 2 <= 1 := by
      rw [div_pow, div_pow, ← add_div]
      apply (div_le_iff₀ (sq_pos_of_pos hrhoReal)).2
      simpa only [one_mul] using htransNum
    have htcenter : |t - (2 : Real)⁻¹| <= (2 : Real)⁻¹ := by
      rw [abs_le]
      constructor <;> norm_num at * <;> linarith [ht.1, ht.2]
    have heInner : |⟪frame 2, e⟫_Real| <= (rho : Real) := by
      have h := abs_real_inner_le_norm (frame 2) e
      rw [frame.norm_eq_one, one_mul] at h
      exact h.trans heNorm
    have hd2eq : d 2 = (t - (2 : Real)⁻¹) + ⟪frame 2, e⟫_Real := by
      dsimp only [d, e, q, center, tubeCenter]
      rw [inner_sub_right, inner_sub_right, inner_add_right,
        inner_add_right, real_inner_smul_right, real_inner_smul_right,
        hframe, real_inner_self_eq_norm_sq, T.axis.norm_direction]
      norm_num
      ring
    have hd2abs : |d 2| <= 1 := by
      rw [hd2eq]
      calc
        |(t - (2 : Real)⁻¹) + ⟪frame 2, e⟫_Real| <=
            |t - (2 : Real)⁻¹| + |⟪frame 2, e⟫_Real| := abs_add_le _ _
        _ <= (2 : Real)⁻¹ + (rho : Real) := add_le_add htcenter heInner
        _ <= 1 := by linarith
    have hd2sq : (2 * d 2) ^ 2 <= 4 := by
      have hbounds := abs_le.mp hd2abs
      nlinarith
    have hz0 : z 0 = d 0 / (rho : Real) := by simp [z]
    have hz1 : z 1 = d 1 / (rho : Real) := by simp [z]
    have hz2 : z 2 = 2 * d 2 := by simp [z]
    have hzsum : ∑ i, (z i) ^ 2 <= (3 : Real) ^ 2 := by
      rw [Fin.sum_univ_three, hz0, hz1, hz2]
      norm_num
      nlinarith [htrans, hd2sq]
    have hzmul (i : Fin 3) : z i * (radius i : Real) = d i := by
      fin_cases i
      · simp [z, radius, tubeJohnRadii, hrho0]
      · simp [z, radius, tubeJohnRadii, hrho0]
      · simp [z, radius, tubeJohnRadii]
        ring
    refine ⟨z, hzsum, ?_⟩
    have hsum : ∑ i, d i • frame i = x - center := by
      simpa only [d] using frame.sum_repr' (x - center)
    calc
      x = center + (x - center) := by abel
      _ = center + ∑ i, d i • frame i := by rw [hsum]
      _ = center + ∑ i, (z i * (radius i : Real)) • frame i := by
        congr 2
        funext i
        rw [hzmul i]

#print axioms Tube.johnAxisWitness_of_pos_le_half

end
end Family8TubeJohnAxisWitnessV1
