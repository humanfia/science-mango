import Family8Grounding.Family8FiniteRandomRigidMotionPaperConflictOverlapLowerV1
import Submission.Kakeya.ConvexFactoring.TransverseUnit
import Submission.Kakeya.ConvexFactoring.DeterminantAngleBridge

open Set MeasureTheory
open scoped ENNReal NNReal Pointwise InnerProductSpace Matrix

namespace Family8FiniteRandomRigidMotionPaperTubeSlabGeometryV1

open LeanEval.Analysis.WangZahlKakeya
open Submission.Kakeya.ConvexGeometry
open Submission.Kakeya.ConvexGeometry.TransverseCoordinateOverlap

noncomputable section

set_option autoImplicit false
set_option warningAsError true

/-!
# Three thin slabs for a pair of tubes

For a transverse pair of unit tube directions, the normalized cross product
is a common thin normal.  Crossing that normal once more with each tube
direction supplies the other two thin normals.  Their coordinate determinant
has absolute value exactly the sine of the original tube angle.  This is the
geometric input behind the `rho^3 / sin(angle)` overlap estimate.
-/

/-- Any unit vector perpendicular to a tube axis gives a radius-width slab
containing the whole metric tube. -/
theorem Tube.carrier_subset_affineSlab_of_inner_direction_eq_zero
    {rho : NNReal} (T : Tube rho) (n : Space)
    (hn : ‖n‖ = 1) (horth : ⟪n, T.axis.direction⟫_ℝ = 0) :
    T.carrier ⊆ affineSlab n
      ⟪n, T.axis.base + (2 : Real)⁻¹ • T.axis.direction⟫_ℝ rho := by
  intro x hx
  rw [Tube.carrier,
    T.axis.isCompact_carrier.cthickening_eq_biUnion_closedBall
      (show 0 ≤ (rho : Real) by positivity)] at hx
  simp only [mem_iUnion, Metric.mem_closedBall] at hx
  obtain ⟨y, hy, hxy⟩ := hx
  rw [T.axis.carrier_eq_image] at hy
  obtain ⟨t, _ht, rfl⟩ := hy
  change |⟪n, x⟫_ℝ -
      ⟪n, T.axis.base + (2 : Real)⁻¹ • T.axis.direction⟫_ℝ| ≤
    (rho : Real)
  have hcenter :
      ⟪n, T.axis.base + t • T.axis.direction⟫_ℝ =
        ⟪n, T.axis.base + (2 : Real)⁻¹ • T.axis.direction⟫_ℝ := by
    rw [inner_add_right, inner_add_right,
      inner_smul_right, inner_smul_right, horth]
    ring
  rw [← hcenter]
  exact (abs_inner_sub_inner_le_dist_of_norm_eq_one n x
    (T.axis.base + t • T.axis.direction) hn).trans hxy

/-- The common unit normal to two positively transverse tube directions. -/
def commonTubeNormal {rho : NNReal} (T U : Tube rho) : Space :=
  transverseUnit T.axis.direction U.axis.direction

/-- The second thin normal for the left tube. -/
def leftTubeNormal {rho : NNReal} (T U : Tube rho) : Space :=
  transverseVector (commonTubeNormal T U) T.axis.direction

/-- The second thin normal for the right tube. -/
def rightTubeNormal {rho : NNReal} (T U : Tube rho) : Space :=
  transverseVector (commonTubeNormal T U) U.axis.direction

theorem norm_commonTubeNormal {rho : NNReal} (T U : Tube rho)
    (hangle : 0 < Real.sin (InnerProductGeometry.angle
      T.axis.direction U.axis.direction)) :
    ‖commonTubeNormal T U‖ = 1 := by
  exact norm_transverseUnit_of_unit _ _
    T.axis.norm_direction U.axis.norm_direction hangle

theorem inner_commonTubeNormal_left {rho : NNReal} (T U : Tube rho) :
    ⟪commonTubeNormal T U, T.axis.direction⟫_ℝ = 0 := by
  exact inner_transverseUnit_left _ _

theorem inner_commonTubeNormal_right {rho : NNReal} (T U : Tube rho) :
    ⟪commonTubeNormal T U, U.axis.direction⟫_ℝ = 0 := by
  exact inner_transverseUnit_right _ _

private theorem sin_angle_eq_one_of_unit_inner_eq_zero
    (a b : Space) (_ha : ‖a‖ = 1) (_hb : ‖b‖ = 1)
    (hab : ⟪a, b⟫_ℝ = 0) :
    Real.sin (InnerProductGeometry.angle a b) = 1 := by
  have hang : InnerProductGeometry.angle a b = Real.pi / 2 :=
    (InnerProductGeometry.inner_eq_zero_iff_angle_eq_pi_div_two a b).mp hab
  rw [hang, Real.sin_pi_div_two]

theorem norm_leftTubeNormal {rho : NNReal} (T U : Tube rho)
    (hangle : 0 < Real.sin (InnerProductGeometry.angle
      T.axis.direction U.axis.direction)) :
    ‖leftTubeNormal T U‖ = 1 := by
  rw [leftTubeNormal, norm_transverseVector,
    norm_commonTubeNormal T U hangle, T.axis.norm_direction]
  rw [sin_angle_eq_one_of_unit_inner_eq_zero
    (commonTubeNormal T U) T.axis.direction
    (norm_commonTubeNormal T U hangle) T.axis.norm_direction
    (inner_commonTubeNormal_left T U)]
  norm_num

theorem norm_rightTubeNormal {rho : NNReal} (T U : Tube rho)
    (hangle : 0 < Real.sin (InnerProductGeometry.angle
      T.axis.direction U.axis.direction)) :
    ‖rightTubeNormal T U‖ = 1 := by
  rw [rightTubeNormal, norm_transverseVector,
    norm_commonTubeNormal T U hangle, U.axis.norm_direction]
  rw [sin_angle_eq_one_of_unit_inner_eq_zero
    (commonTubeNormal T U) U.axis.direction
    (norm_commonTubeNormal T U hangle) U.axis.norm_direction
    (inner_commonTubeNormal_right T U)]
  norm_num

theorem inner_commonTubeNormal_leftTubeNormal {rho : NNReal}
    (T U : Tube rho) :
    ⟪commonTubeNormal T U, leftTubeNormal T U⟫_ℝ = 0 := by
  rw [real_inner_comm]
  exact inner_transverseVector_left _ _

theorem inner_commonTubeNormal_rightTubeNormal {rho : NNReal}
    (T U : Tube rho) :
    ⟪commonTubeNormal T U, rightTubeNormal T U⟫_ℝ = 0 := by
  rw [real_inner_comm]
  exact inner_transverseVector_left _ _

theorem inner_leftTubeNormal_axis {rho : NNReal} (T U : Tube rho) :
    ⟪leftTubeNormal T U, T.axis.direction⟫_ℝ = 0 := by
  exact inner_transverseVector_right _ _

theorem inner_rightTubeNormal_axis {rho : NNReal} (T U : Tube rho) :
    ⟪rightTubeNormal T U, U.axis.direction⟫_ℝ = 0 := by
  exact inner_transverseVector_right _ _

/-- Crossing both tube directions by the same unit normal preserves their
inner product. -/
theorem inner_leftTubeNormal_rightTubeNormal {rho : NNReal}
    (T U : Tube rho)
    (hangle : 0 < Real.sin (InnerProductGeometry.angle
      T.axis.direction U.axis.direction)) :
    ⟪leftTubeNormal T U, rightTubeNormal T U⟫_ℝ =
      ⟪T.axis.direction, U.axis.direction⟫_ℝ := by
  have hee : ⟪commonTubeNormal T U, commonTubeNormal T U⟫_ℝ = 1 := by
    rw [real_inner_self_eq_norm_sq, norm_commonTubeNormal T U hangle]
    norm_num
  have hev : ⟪commonTubeNormal T U, U.axis.direction⟫_ℝ = 0 :=
    inner_commonTubeNormal_right T U
  have hue : ⟪T.axis.direction, commonTubeNormal T U⟫_ℝ = 0 := by
    rw [real_inner_comm]
    exact inner_commonTubeNormal_left T U
  have hee' : (commonTubeNormal T U).ofLp ⬝ᵥ (commonTubeNormal T U).ofLp = 1 := by
    simpa only [EuclideanSpace.inner_eq_star_dotProduct, star_trivial] using hee
  have hev' : U.axis.direction.ofLp ⬝ᵥ (commonTubeNormal T U).ofLp = 0 := by
    simpa only [EuclideanSpace.inner_eq_star_dotProduct, star_trivial] using hev
  have hue' : (commonTubeNormal T U).ofLp ⬝ᵥ T.axis.direction.ofLp = 0 := by
    simpa only [EuclideanSpace.inner_eq_star_dotProduct, star_trivial] using hue
  simp only [leftTubeNormal, rightTubeNormal, transverseVector,
    EuclideanSpace.inner_eq_star_dotProduct, star_trivial]
  rw [cross_dot_cross, hee', hue', hev']
  ring

/-- The three thin slab normals have determinant equal in absolute value to
the sine of the original tube-axis angle. -/
theorem abs_det_common_left_right_eq_sin_angle {rho : NNReal}
    (T U : Tube rho)
    (hangle : 0 < Real.sin (InnerProductGeometry.angle
      T.axis.direction U.axis.direction)) :
    |LinearMap.det (innerCoordinateMap
      ![commonTubeNormal T U, leftTubeNormal T U, rightTubeNormal T U])| =
      Real.sin (InnerProductGeometry.angle
        T.axis.direction U.axis.direction) := by
  have hdetAngle := abs_det_innerCoordinateMap_eq_sin_angle
    (commonTubeNormal T U) (leftTubeNormal T U) (rightTubeNormal T U)
    (norm_commonTubeNormal T U hangle)
    (norm_leftTubeNormal T U hangle) (norm_rightTubeNormal T U hangle)
    (inner_commonTubeNormal_leftTubeNormal T U)
    (inner_commonTubeNormal_rightTubeNormal T U)
  rw [hdetAngle]
  have hcos :
      Real.cos (InnerProductGeometry.angle
          (leftTubeNormal T U) (rightTubeNormal T U)) =
        Real.cos (InnerProductGeometry.angle
          T.axis.direction U.axis.direction) := by
    rw [← InnerProductGeometry.inner_eq_cos_angle_of_norm_eq_one
        (norm_leftTubeNormal T U hangle) (norm_rightTubeNormal T U hangle),
      ← InnerProductGeometry.inner_eq_cos_angle_of_norm_eq_one
        T.axis.norm_direction U.axis.norm_direction]
    exact inner_leftTubeNormal_rightTubeNormal T U hangle
  have hsinLeft := InnerProductGeometry.sin_angle_nonneg
    (leftTubeNormal T U) (rightTubeNormal T U)
  have hsinRight := InnerProductGeometry.sin_angle_nonneg
    T.axis.direction U.axis.direction
  have htrigLeft := Real.sin_sq_add_cos_sq
    (InnerProductGeometry.angle (leftTubeNormal T U) (rightTubeNormal T U))
  have htrigRight := Real.sin_sq_add_cos_sq
    (InnerProductGeometry.angle T.axis.direction U.axis.direction)
  apply (sq_eq_sq₀ hsinLeft hsinRight).mp
  rw [hcos] at htrigLeft
  nlinarith [htrigLeft, htrigRight]

#print axioms Tube.carrier_subset_affineSlab_of_inner_direction_eq_zero
#print axioms abs_det_common_left_right_eq_sin_angle

end
end Family8FiniteRandomRigidMotionPaperTubeSlabGeometryV1
