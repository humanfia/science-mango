import Submission.Kakeya.ConvexFactoring.DeterminantAngleBridge
import Mathlib.Tactic

set_option autoImplicit false
set_option warningAsError true

open scoped InnerProductSpace Matrix

namespace Family8FiniteRandomRigidMotionPaperTransverseCoordinateAngleV1

open LeanEval.Analysis.WangZahlKakeya

noncomputable section

/-!
# Transverse frame coordinates from the unoriented sine angle

The random-motion conflict geometry is unoriented: reversing a unit axis does
not change its tube.  Consequently transverse coordinates must be controlled
by the sine of the angle, not by the oriented distance between directions.
-/

/-- In an orthonormal frame whose last vector is `u`, either transverse
coordinate of another unit vector `v` is at most `sin(angle u v)`. -/
theorem abs_inner_frame_le_sin_angle_of_ne_two
    (frame : OrthonormalBasis (Fin 3) Real Space)
    (u v : Space)
    (hframe : frame 2 = u)
    (hu : ‖u‖ = 1) (hv : ‖v‖ = 1)
    (k : Fin 3) (hk : k ≠ 2) :
    |⟪frame k, v⟫_ℝ| ≤
      Real.sin (InnerProductGeometry.angle u v) := by
  apply (sq_le_sq₀ (abs_nonneg _)
    (InnerProductGeometry.sin_angle_nonneg u v)).mp
  rw [sq_abs]
  have hparseval := frame.sum_sq_inner_right v
  rw [Fin.sum_univ_three, hv] at hparseval
  have hlast :
      ⟪frame 2, v⟫_ℝ =
        Real.cos (InnerProductGeometry.angle u v) := by
    rw [hframe]
    exact InnerProductGeometry.inner_eq_cos_angle_of_norm_eq_one hu hv
  have htrig := Real.sin_sq_add_cos_sq
    (InnerProductGeometry.angle u v)
  rw [hlast] at hparseval
  norm_num at hparseval
  fin_cases k
  · change ⟪frame 0, v⟫_ℝ ^ 2 ≤
      Real.sin (InnerProductGeometry.angle u v) ^ 2
    nlinarith [sq_nonneg ⟪frame 1, v⟫_ℝ]
  · change ⟪frame 1, v⟫_ℝ ^ 2 ≤
      Real.sin (InnerProductGeometry.angle u v) ^ 2
    nlinarith [sq_nonneg ⟪frame 0, v⟫_ℝ]
  · exact (hk rfl).elim

#print axioms abs_inner_frame_le_sin_angle_of_ne_two

end
end Family8FiniteRandomRigidMotionPaperTransverseCoordinateAngleV1
