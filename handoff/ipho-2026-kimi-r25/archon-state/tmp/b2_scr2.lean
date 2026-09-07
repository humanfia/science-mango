import Mathlib

open Real Filter InnerProductGeometry
open scoped InnerProductSpace RealInnerProductSpace Topology

namespace Scratch2

abbrev Plane : Type := EuclideanSpace ℝ (Fin 2)

def planeWedge (x y : Plane) : ℝ := x 0 * y 1 - x 1 * y 0

lemma inner_eq_coords (x y : Plane) : ⟪x, y⟫_ℝ = x 0 * y 0 + x 1 * y 1 := by
  rw [PiLp.inner_apply, Fin.sum_univ_two]
  simp [RCLike.inner_apply]
  ring

lemma norm_sq_eq_coords (x : Plane) : ‖x‖ ^ 2 = (x 0) ^ 2 + (x 1) ^ 2 := by
  rw [EuclideanSpace.norm_eq, Real.sq_sqrt (by positivity), Fin.sum_univ_two]
  simp [sq_abs]

lemma planeWedge_sq_add_inner_sq (x y : Plane) :
    planeWedge x y ^ 2 + ⟪x, y⟫_ℝ ^ 2 = ‖x‖ ^ 2 * ‖y‖ ^ 2 := by
  rw [inner_eq_coords, norm_sq_eq_coords, norm_sq_eq_coords]
  simp only [planeWedge]
  ring

lemma inner_mul_inner_planeWedge (e x y : Plane) :
    ⟪e, e⟫_ℝ * ⟪x, y⟫_ℝ = ⟪e, x⟫_ℝ * ⟪e, y⟫_ℝ + planeWedge e x * planeWedge e y := by
  rw [inner_eq_coords, inner_eq_coords, inner_eq_coords, inner_eq_coords]
  simp only [planeWedge]
  ring

lemma planeWedge_smul_left (a : ℝ) (x y : Plane) : planeWedge (a • x) y = a * planeWedge x y := by
  simp only [planeWedge, PiLp.smul_apply, smul_eq_mul]
  ring

lemma planeWedge_smul_right (a : ℝ) (x y : Plane) : planeWedge x (a • y) = a * planeWedge x y := by
  simp only [planeWedge, PiLp.smul_apply, smul_eq_mul]
  ring

lemma planeWedge_neg_left (x y : Plane) : planeWedge (-x) y = -planeWedge x y := by
  simpa using planeWedge_smul_left (-1) x y

lemma planeWedge_self (x : Plane) : planeWedge x x = 0 := by
  simp only [planeWedge]; ring

lemma planeWedge_comm (x y : Plane) : planeWedge x y = -planeWedge y x := by
  simp only [planeWedge]; ring

def planeRot (x : Plane) : Plane := ![-x 1, x 0]

lemma inner_planeRot_left (x y : Plane) : ⟪planeRot x, y⟫_ℝ = planeWedge x y := by
  rw [inner_eq_coords]
  simp only [planeWedge, planeRot, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons]
  ring

lemma norm_planeRot (x : Plane) : ‖planeRot x‖ = ‖x‖ := by
  have h1 : ‖planeRot x‖ ^ 2 = ‖x‖ ^ 2 := by
    rw [norm_sq_eq_coords, norm_sq_eq_coords]
    simp only [planeRot, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons]
    ring
  have h2 : |‖planeRot x‖| = |‖x‖| := (sq_eq_sq_iff_abs_eq_abs _ _).mp h1
  rwa [abs_of_nonneg (norm_nonneg _), abs_of_nonneg (norm_nonneg _)] at h2

lemma planeWedge_self_planeRot (e : Plane) (he : ‖e‖ = 1) : planeWedge e (planeRot e) = 1 := by
  have hee : (e 0) ^ 2 + (e 1) ^ 2 = 1 := by
    have h := norm_sq_eq_coords e
    rw [he] at h
    linarith [h]
  simp only [planeWedge, planeRot, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons]
  linear_combination hee

end Scratch2
