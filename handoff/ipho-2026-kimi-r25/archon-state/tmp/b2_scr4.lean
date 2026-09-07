import Mathlib

open Real Filter InnerProductGeometry
open scoped InnerProductSpace RealInnerProductSpace Topology

abbrev Plane : Type := EuclideanSpace ℝ (Fin 2)

def planeWedge (x y : Plane) : ℝ := x 0 * y 1 - x 1 * y 0

def planeRot (x : Plane) : Plane :=
  (-x 1) • EuclideanSpace.single (0 : Fin 2) (1 : ℝ) + (x 0) • EuclideanSpace.single (1 : Fin 2) (1 : ℝ)

lemma planeRot_zero (x : Plane) : planeRot x 0 = -x 1 := by
  simp [planeRot]

lemma planeRot_one (x : Plane) : planeRot x 1 = x 0 := by
  simp [planeRot]

lemma inner_eq_coords (x y : Plane) : ⟪x, y⟫_ℝ = x 0 * y 0 + x 1 * y 1 := by
  rw [PiLp.inner_apply, Fin.sum_univ_two]
  simp [RCLike.inner_apply]
  ring

lemma inner_planeRot_left (x y : Plane) : ⟪planeRot x, y⟫_ℝ = planeWedge x y := by
  rw [inner_eq_coords, planeRot_zero, planeRot_one]
  simp only [planeWedge]
  ring

example (r : ℝ → Plane) (e v : Plane) (t : ℝ) (hr : HasDerivAt r v t) :
    HasDerivAt (fun s => planeWedge e (r s)) (planeWedge e v) t := by
  have h1 := HasDerivAt.inner (𝕜 := ℝ) (hasDerivAt_const t (planeRot e)) hr
  simp only [inner_zero_left, add_zero] at h1
  simpa only [inner_planeRot_left] using h1

lemma norm_sq_eq_coords (x : Plane) : ‖x‖ ^ 2 = (x 0) ^ 2 + (x 1) ^ 2 := by
  rw [EuclideanSpace.norm_eq, Real.sq_sqrt (by positivity), Fin.sum_univ_two]
  simp [sq_abs]

lemma norm_planeRot (x : Plane) : ‖planeRot x‖ = ‖x‖ := by
  have h1 : ‖planeRot x‖ ^ 2 = ‖x‖ ^ 2 := by
    rw [norm_sq_eq_coords, norm_sq_eq_coords, planeRot_zero, planeRot_one]
    ring
  have h2 : |‖planeRot x‖| = |‖x‖| := (sq_eq_sq_iff_abs_eq_abs _ _).mp h1
  rwa [abs_of_nonneg (norm_nonneg _), abs_of_nonneg (norm_nonneg _)] at h2

example (r : ℝ → Plane) (v : Plane) (t : ℝ) (hr : HasDerivAt r v t) :
    HasDerivAt (fun s => ‖r s‖ ^ 2) (2 * ⟪r t, v⟫_ℝ) t :=
  hr.norm_sq

example (x : Plane) : ⟪x, x⟫_ℝ = 0 ↔ x = 0 := inner_self_eq_zero
