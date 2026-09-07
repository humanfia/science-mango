import Mathlib

open Real Filter InnerProductGeometry
open scoped InnerProductSpace RealInnerProductSpace Topology

abbrev Plane : Type := EuclideanSpace ℝ (Fin 2)

def planeWedge (x y : Plane) : ℝ := x 0 * y 1 - x 1 * y 0

-- variant A
def planeRot (x : Plane) : Plane := fun i => ![-x 1, x 0] i

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

-- differentiability via HasDerivAt.inner
example (r : ℝ → Plane) (v : Plane) (t : ℝ) (hr : HasDerivAt r (v) t) :
    HasDerivAt (fun s => planeWedge (r s) v) (planeWedge v v) t := by
  sorry

example (r : ℝ → Plane) (e v : Plane) (t : ℝ) (hr : HasDerivAt r v t) :
    HasDerivAt (fun s => planeWedge e (r s)) (planeWedge e v) t := by
  have h1 : HasDerivAt (fun s => ⟪planeRot e, r s⟫_ℝ) (⟪planeRot e, v⟫_ℝ + ⟪(0:Plane), r t⟫_ℝ) t :=
    HasDerivAt.inner (𝕜 := ℝ) (hasDerivAt_const t (planeRot e)) hr
  simp only [inner_zero_left, add_zero] at h1
  simpa only [inner_planeRot_left] using h1

-- norm_sq derivative
example (r : ℝ → Plane) (v : Plane) (t : ℝ) (hr : HasDerivAt r v t) :
    HasDerivAt (fun s => ‖r s‖ ^ 2) (2 * ⟪r t, v⟫_ℝ) t :=
  hr.norm_sq
