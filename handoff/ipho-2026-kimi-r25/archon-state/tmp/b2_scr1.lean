import Mathlib

open Real Filter InnerProductGeometry
open scoped InnerProductSpace RealInnerProductSpace Topology

namespace Scratch

abbrev Plane : Type := EuclideanSpace ℝ (Fin 2)

def planeWedge (x y : Plane) : ℝ := x 0 * y 1 - x 1 * y 0

-- test: reduce inner to coordinates
example (x y : Plane) : ⟪x, y⟫_ℝ = x 0 * y 0 + x 1 * y 1 := by
  rw [PiLp.inner_apply, Fin.sum_univ_two]
  simp [RCLike.inner_apply]

-- test: reduce norm squared to coordinates
example (x : Plane) : ‖x‖ ^ 2 = (x 0) ^ 2 + (x 1) ^ 2 := by
  rw [EuclideanSpace.norm_eq]
  rw [Real.sq_sqrt (by positivity), Fin.sum_univ_two]
  simp [sq_abs]

-- master identity
example (x y : Plane) : planeWedge x y ^ 2 + ⟪x, y⟫_ℝ ^ 2 = ‖x‖ ^ 2 * ‖y‖ ^ 2 := by
  have h1 : ∀ a b : Plane, ⟪a, b⟫_ℝ = a 0 * b 0 + a 1 * b 1 := by
    intro a b
    rw [PiLp.inner_apply, Fin.sum_univ_two]
    simp [RCLike.inner_apply]
  have h2 : ∀ a : Plane, ‖a‖ ^ 2 = (a 0) ^ 2 + (a 1) ^ 2 := by
    intro a
    rw [EuclideanSpace.norm_eq, Real.sq_sqrt (by positivity), Fin.sum_univ_two]
    simp [sq_abs]
  rw [h1 x y, h2 x, h2 y, planeWedge]
  ring

end Scratch
