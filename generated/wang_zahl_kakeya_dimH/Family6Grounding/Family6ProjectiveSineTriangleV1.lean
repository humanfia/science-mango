import Mathlib.Geometry.Euclidean.Angle.Unoriented.TriangleInequality

set_option autoImplicit false

open Set
open scoped Real InnerProductSpace

namespace Family6ProjectiveSineTriangleV1

open InnerProductGeometry

noncomputable section

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]

/-- Flip a vector, when necessary, so that its angle with the reference
vector is at most `π / 2`.  Sines of all relevant angles are unchanged. -/
def projectiveOrient (x y : V) : V :=
  if angle x y ≤ Real.pi / 2 then x else -x

theorem angle_projectiveOrient_le_pi_div_two (x y : V) :
    angle (projectiveOrient x y) y ≤ Real.pi / 2 := by
  unfold projectiveOrient
  split_ifs with h
  · exact h
  · rw [angle_neg_left]
    have hpi := angle_le_pi x y
    linarith

theorem sin_angle_projectiveOrient (x y : V) :
    Real.sin (angle (projectiveOrient x y) y) =
      Real.sin (angle x y) := by
  unfold projectiveOrient
  split_ifs with h
  · rfl
  · rw [angle_neg_left, Real.sin_pi_sub]

theorem sin_angle_projectiveOrient_pair (x y z : V) :
    Real.sin (angle (projectiveOrient x y) (projectiveOrient z y)) =
      Real.sin (angle x z) := by
  by_cases hx : angle x y ≤ Real.pi / 2
  · by_cases hz : angle z y ≤ Real.pi / 2
    · simp [projectiveOrient, hx, hz]
    · simp [projectiveOrient, hx, hz, angle_neg_right, Real.sin_pi_sub]
  · by_cases hz : angle z y ≤ Real.pi / 2
    · simp [projectiveOrient, hx, hz, angle_neg_left, Real.sin_pi_sub]
    · simp [projectiveOrient, hx, hz, angle_neg_neg]

/-- Elementary scalar core: if `α` and `β` are acute and `γ ≤ α + β`,
then `sin γ ≤ sin α + sin β`. -/
theorem sin_le_sin_add_sin_of_acute
    (alpha beta gamma : Real)
    (halpha0 : 0 ≤ alpha) (hbeta0 : 0 ≤ beta) (hgamma0 : 0 ≤ gamma)
    (halpha : alpha ≤ Real.pi / 2) (hbeta : beta ≤ Real.pi / 2)
    (hgamma : gamma ≤ alpha + beta) :
    Real.sin gamma ≤ Real.sin alpha + Real.sin beta := by
  have hhalf_le_pi : Real.pi / 2 ≤ Real.pi := by
    linarith [Real.pi_pos]
  have hsinalpha : 0 ≤ Real.sin alpha :=
    Real.sin_nonneg_of_nonneg_of_le_pi halpha0 (halpha.trans hhalf_le_pi)
  have hsinbeta : 0 ≤ Real.sin beta :=
    Real.sin_nonneg_of_nonneg_of_le_pi hbeta0 (hbeta.trans hhalf_le_pi)
  by_cases hsum : alpha + beta ≤ Real.pi / 2
  · have hsin_gamma_sum : Real.sin gamma ≤ Real.sin (alpha + beta) :=
      Real.sin_le_sin_of_le_of_le_pi_div_two
        (by linarith [Real.pi_pos]) hsum hgamma
    have hleft : Real.sin alpha * Real.cos beta ≤ Real.sin alpha := by
      simpa using mul_le_mul_of_nonneg_left (Real.cos_le_one beta) hsinalpha
    have hright : Real.cos alpha * Real.sin beta ≤ Real.sin beta := by
      simpa using mul_le_mul_of_nonneg_right (Real.cos_le_one alpha) hsinbeta
    calc
      Real.sin gamma ≤ Real.sin (alpha + beta) := hsin_gamma_sum
      _ = Real.sin alpha * Real.cos beta +
          Real.cos alpha * Real.sin beta := Real.sin_add alpha beta
      _ ≤ Real.sin alpha + Real.sin beta := add_le_add hleft hright
  · have hbetaLower : Real.pi / 2 - alpha ≤ beta := by
      linarith
    have hsinComplement : Real.cos alpha ≤ Real.sin beta := by
      rw [← Real.sin_pi_div_two_sub alpha]
      exact Real.sin_le_sin_of_le_of_le_pi_div_two
        (by linarith [Real.pi_pos]) hbeta hbetaLower
    have hcosalpha : 0 ≤ Real.cos alpha :=
      Real.cos_nonneg_of_neg_pi_div_two_le_of_le
        (by linarith [Real.pi_pos]) halpha
    have hone : 1 ≤ Real.sin alpha + Real.cos alpha := by
      nlinarith [Real.sin_sq_add_cos_sq alpha,
        mul_nonneg hsinalpha hcosalpha]
    have hone' : 1 ≤ Real.sin alpha + Real.sin beta := by
      linarith
    exact (Real.sin_le_one gamma).trans hone'

/-- The sine of the unoriented angle is the projective-line gap metric, so
it satisfies the triangle inequality even when frame normals are reversed. -/
theorem sin_angle_triangle_projective (x y z : V) :
    Real.sin (angle x z) ≤
      Real.sin (angle x y) + Real.sin (angle y z) := by
  let x' := projectiveOrient x y
  let z' := projectiveOrient z y
  have hxacute : angle x' y ≤ Real.pi / 2 := by
    exact angle_projectiveOrient_le_pi_div_two x y
  have hzacute : angle z' y ≤ Real.pi / 2 := by
    exact angle_projectiveOrient_le_pi_div_two z y
  have htriangle : angle x' z' ≤ angle x' y + angle z' y := by
    simpa only [angle_comm y z'] using angle_le_angle_add_angle x' y z'
  have hscalar : Real.sin (angle x' z') ≤
      Real.sin (angle x' y) + Real.sin (angle z' y) :=
    sin_le_sin_add_sin_of_acute
      (angle x' y) (angle z' y) (angle x' z')
      (angle_nonneg _ _) (angle_nonneg _ _) (angle_nonneg _ _)
      hxacute hzacute htriangle
  calc
    Real.sin (angle x z) = Real.sin (angle x' z') := by
      exact (sin_angle_projectiveOrient_pair x y z).symm
    _ ≤ Real.sin (angle x' y) + Real.sin (angle z' y) := hscalar
    _ = Real.sin (angle x y) + Real.sin (angle y z) := by
      rw [sin_angle_projectiveOrient x y,
        sin_angle_projectiveOrient z y, angle_comm z y]

#print axioms sin_angle_triangle_projective

end
end Family6ProjectiveSineTriangleV1
