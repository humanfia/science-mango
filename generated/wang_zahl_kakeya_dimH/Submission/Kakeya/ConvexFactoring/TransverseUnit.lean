import Submission.Kakeya.ConvexFactoring.CertifiedSlabOverlap

open scoped ENNReal NNReal Pointwise InnerProductSpace Matrix
open MeasureTheory

namespace Submission.Kakeya.ConvexGeometry

open LeanEval.Analysis.WangZahlKakeya

noncomputable section

/-- The Euclidean cross product transported to `Space`. -/
def transverseVector (u v : Space) : Space :=
  WithLp.toLp 2 (WithLp.ofLp u ⨯₃ WithLp.ofLp v)

/-- The normalized transverse direction. -/
def transverseUnit (u v : Space) : Space :=
  ‖transverseVector u v‖⁻¹ • transverseVector u v

theorem norm_transverseVector (u v : Space) :
    ‖transverseVector u v‖ =
      ‖u‖ * ‖v‖ * Real.sin (InnerProductGeometry.angle u v) := by
  exact InnerProductGeometry.norm_ofLp_crossProduct u v

theorem inner_transverseVector_left (u v : Space) :
    ⟪transverseVector u v, u⟫_ℝ = 0 := by
  rw [real_inner_comm]
  simp [transverseVector, EuclideanSpace.inner_eq_star_dotProduct, dotProduct_comm]

theorem inner_transverseVector_right (u v : Space) :
    ⟪transverseVector u v, v⟫_ℝ = 0 := by
  rw [real_inner_comm]
  simp [transverseVector, EuclideanSpace.inner_eq_star_dotProduct, dotProduct_comm]

theorem norm_transverseUnit_of_unit
    (u v : Space) (hu : ‖u‖ = 1) (hv : ‖v‖ = 1)
    (hangle : 0 < Real.sin (InnerProductGeometry.angle u v)) :
    ‖transverseUnit u v‖ = 1 := by
  have hnorm : ‖transverseVector u v‖ =
      Real.sin (InnerProductGeometry.angle u v) := by
    rw [norm_transverseVector, hu, hv, one_mul, one_mul]
  have hne : ‖transverseVector u v‖ ≠ 0 := by
    rw [hnorm]
    exact ne_of_gt hangle
  rw [transverseUnit, norm_smul, Real.norm_eq_abs, abs_inv, abs_norm]
  exact inv_mul_cancel₀ hne

theorem inner_transverseUnit_left (u v : Space) :
    ⟪transverseUnit u v, u⟫_ℝ = 0 := by
  rw [transverseUnit, real_inner_smul_left, inner_transverseVector_left, mul_zero]

theorem inner_transverseUnit_right (u v : Space) :
    ⟪transverseUnit u v, v⟫_ℝ = 0 := by
  rw [transverseUnit, real_inner_smul_left, inner_transverseVector_right, mul_zero]

/-- Certified slab overlap needs no externally supplied longitudinal vector:
positive angular sine constructs one canonically by the cross product. -/
theorem SlabDimensionsCertificate.volume_inter_body_le_sin_angle_auto
    {C₀ C₁ θ₀ θ₁ : ℝ≥0} {K₀ K₁ : ConvexBody Space}
    (cert₀ : SlabDimensionsCertificate C₀ θ₀ K₀)
    (cert₁ : SlabDimensionsCertificate C₁ θ₁ K₁)
    (hangle : 0 < Real.sin
      (InnerProductGeometry.angle (cert₀.box.frame 0) (cert₁.box.frame 0))) :
    volume ((K₀ : Set Space) ∩ (K₁ : Set Space)) ≤
      ENNReal.ofReal
          ((Real.sin (InnerProductGeometry.angle
            (cert₀.box.frame 0) (cert₁.box.frame 0)))⁻¹) *
        2 * (θ₀ : ℝ≥0∞) * (θ₁ : ℝ≥0∞) := by
  let e := transverseUnit (cert₀.box.frame 0) (cert₁.box.frame 0)
  apply cert₀.volume_inter_body_le_sin_angle cert₁ e
  · exact norm_transverseUnit_of_unit _ _
      (cert₀.box.frame.norm_eq_one 0) (cert₁.box.frame.norm_eq_one 0) hangle
  · exact inner_transverseUnit_left _ _
  · exact inner_transverseUnit_right _ _
  · exact hangle

end

end Submission.Kakeya.ConvexGeometry
