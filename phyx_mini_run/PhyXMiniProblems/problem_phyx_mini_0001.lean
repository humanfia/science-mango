import Mathlib.Analysis.SpecialFunctions.Trigonometric.Angle
import Mathlib.Geometry.Euclidean.Angle.Unoriented.Basic
import Mathlib.Analysis.InnerProductSpace.PiL2
import Physlib.Optics.Basic

namespace PhyXMiniProblems.ProblemPhyXMini0001

noncomputable section

/-- The optical media on the two sides of the depicted interface. -/
inductive OpticalMedium where
  | air
  | water
  deriving DecidableEq, Repr

/-- The two directed portions of the single light ray shown in the figure. -/
inductive RaySegment where
  | incident
  | refracted
  deriving DecidableEq, Repr

/-- The medium occupied by each portion of the ray. -/
def RaySegment.medium : RaySegment → OpticalMedium
  | .incident => .air
  | .refracted => .water

/-- The Euclidean plane containing the refraction diagram. -/
abbrev DiagramPlane := EuclideanSpace ℝ (Fin 2)

/--
Physical data read from the air--water refraction diagram.

The interface and its normal are represented by nonzero perpendicular
directions. Each ray segment has a nonzero direction, and its physical angle
to the normal is tied to Mathlib's undirected Euclidean vector angle.
Refractive indices are dimensionless scalar readouts attached to typed media.
-/
structure AirWaterRefractionSetup where
  interfacePoint : DiagramPlane
  interfaceDirection : DiagramPlane
  normalDirection : DiagramPlane
  rayDirection : RaySegment → DiagramPlane
  interfaceDirection_ne_zero : interfaceDirection ≠ 0
  normalDirection_ne_zero : normalDirection ≠ 0
  rayDirection_ne_zero : ∀ ray, rayDirection ray ≠ 0
  normal_perpendicular_interface :
    inner ℝ normalDirection interfaceDirection = 0
  angleToNormal : RaySegment → Real.Angle
  angleToNormal_geometry : ∀ ray,
    angleToNormal ray =
      (InnerProductGeometry.angle (rayDirection ray) normalDirection : Real.Angle)
  refractiveIndexDimensionless : OpticalMedium → ℝ

/-- Convert a numerical degree readout into a physical angle. -/
def degrees (value : ℝ) : Real.Angle :=
  ((value * Real.pi / 180 : ℝ) : Real.Angle)

/-- Express the acute representative of a physical angle in degrees. -/
def degreeReadout (angle : Real.Angle) : ℝ :=
  angle.toReal * 180 / Real.pi

/-- The angle labelled `θ₁` between the incident ray and the normal. -/
def thetaOne (setup : AirWaterRefractionSetup) : Real.Angle :=
  setup.angleToNormal .incident

/-- The requested angle `θ₂` between the refracted ray and the normal. -/
def thetaTwo (setup : AirWaterRefractionSetup) : Real.Angle :=
  setup.angleToNormal .refracted

/-- All dimensionless refractive-index readouts in the setup are positive. -/
def HasPositiveRefractiveIndices (setup : AirWaterRefractionSetup) : Prop :=
  ∀ medium, 0 < setup.refractiveIndexDimensionless medium

/-- Snell's law at the depicted air--water interface. -/
def SatisfiesSnellsLaw (setup : AirWaterRefractionSetup) : Prop :=
  setup.refractiveIndexDimensionless .air * Real.Angle.sin (thetaOne setup) =
    setup.refractiveIndexDimensionless .water * Real.Angle.sin (thetaTwo setup)

/-- Select the acute physical branch for an angle measured from the normal. -/
def IsPhysicalRefractionAngle (angle : Real.Angle) : Prop :=
  0 ≤ angle.toReal ∧ angle.toReal ≤ Real.pi / 2

/-- The four numerical answer choices printed with the problem. -/
inductive AnswerChoice where
  | A
  | B
  | C
  | D
  deriving DecidableEq, Repr

/-- Answer-choice degree readouts, in their printed order. -/
def answerInDegrees : AnswerChoice → ℝ
  | .A => 22.7
  | .B => 31.4
  | .C => 32.0
  | .D => 33.5

/--
A one-decimal-place answer choice matches an angle when the degree readout is
within half of one tenth of a degree.
-/
def MatchesAnswerToNearestTenth
    (angle : Real.Angle) (choice : AnswerChoice) : Prop :=
  |degreeReadout angle - answerInDegrees choice| ≤ 0.05

/--
For a `45.0°` ray incident from air into water, Snell's law makes the
refracted angle `θ₂` match choice C, `32.0°`, to the displayed one-decimal
precision.

Blueprint: `thm:physics:phyx_mini_0001:target`.
-/
theorem thetaTwo_matches_choice_C
    (setup : AirWaterRefractionSetup)
    (h_indices_positive : HasPositiveRefractiveIndices setup)
    (h_air_index : setup.refractiveIndexDimensionless .air = 1.000)
    (h_water_index : setup.refractiveIndexDimensionless .water = 1.333)
    (h_thetaOne : thetaOne setup = degrees 45.0)
    (h_snell : SatisfiesSnellsLaw setup)
    (h_thetaTwo_physical : IsPhysicalRefractionAngle (thetaTwo setup)) :
    MatchesAnswerToNearestTenth (thetaTwo setup) .C := by
  have sin_lt_local {x : ℝ} (hx : 0 < x) : Real.sin x < x := by
    rcases lt_or_ge 1 x with hx_one | hx_one
    · exact (Real.sin_le_one x).trans_lt hx_one
    have hx_abs : |x| = x := abs_of_nonneg hx.le
    have h_bound :=
      le_of_abs_le (Real.sin_bound (show |x| ≤ 1 by rwa [hx_abs]))
    rw [sub_le_iff_le_add', hx_abs] at h_bound
    apply h_bound.trans_lt
    rw [sub_add, sub_lt_self_iff, sub_pos, div_eq_mul_inv (x ^ 3)]
    refine mul_lt_mul' ?_ (by norm_num) (by norm_num) (pow_pos hx 3)
    apply pow_le_pow_of_le_one hx.le hx_one
    simp

  have h_series_upper :
      Real.sqrtTwoAddSeries 0 4 ≤ (1447 : ℝ) / 727 := by
    have h₁ : √(2 : ℝ) ≤ (338 : ℝ) / 239 := by
      have hsq := Real.sq_sqrt (show (0 : ℝ) ≤ 2 by norm_num)
      have hnonneg := Real.sqrt_nonneg (2 : ℝ)
      nlinarith only [hsq, hnonneg]
    have h₂ : √(2 + √(2 : ℝ)) ≤ (704 : ℝ) / 381 := by
      have hsq :=
        Real.sq_sqrt (show (0 : ℝ) ≤ 2 + √(2 : ℝ) by positivity)
      have hnonneg := Real.sqrt_nonneg (2 + √(2 : ℝ))
      nlinarith only [h₁, hsq, hnonneg]
    have h₃ :
        √(2 + √(2 + √(2 : ℝ))) ≤ (1940 : ℝ) / 989 := by
      have hsq :=
        Real.sq_sqrt
          (show (0 : ℝ) ≤ 2 + √(2 + √(2 : ℝ)) by positivity)
      have hnonneg := Real.sqrt_nonneg (2 + √(2 + √(2 : ℝ)))
      nlinarith only [h₂, hsq, hnonneg]
    have h₄ :
        √(2 + √(2 + √(2 + √(2 : ℝ)))) ≤ (1447 : ℝ) / 727 := by
      have hsq :=
        Real.sq_sqrt
          (show (0 : ℝ) ≤ 2 + √(2 + √(2 + √(2 : ℝ))) by
            positivity)
      have hnonneg :=
        Real.sqrt_nonneg (2 + √(2 + √(2 + √(2 : ℝ))))
      nlinarith only [h₃, hsq, hnonneg]
    norm_num [Real.sqrtTwoAddSeries]
    exact h₄

  have h_series_lower :
      (412 : ℝ) / 207 ≤ Real.sqrtTwoAddSeries 0 4 := by
    have h₁ : (41 : ℝ) / 29 ≤ √(2 : ℝ) := by
      have hsq := Real.sq_sqrt (show (0 : ℝ) ≤ 2 by norm_num)
      have hnonneg := Real.sqrt_nonneg (2 : ℝ)
      nlinarith only [hsq, hnonneg]
    have h₂ : (109 : ℝ) / 59 ≤ √(2 + √(2 : ℝ)) := by
      have hsq :=
        Real.sq_sqrt (show (0 : ℝ) ≤ 2 + √(2 : ℝ) by positivity)
      have hnonneg := Real.sqrt_nonneg (2 + √(2 : ℝ))
      nlinarith only [h₁, hsq, hnonneg]
    have h₃ :
        (865 : ℝ) / 441 ≤ √(2 + √(2 + √(2 : ℝ))) := by
      have hsq :=
        Real.sq_sqrt
          (show (0 : ℝ) ≤ 2 + √(2 + √(2 : ℝ)) by positivity)
      have hnonneg := Real.sqrt_nonneg (2 + √(2 + √(2 : ℝ)))
      nlinarith only [h₂, hsq, hnonneg]
    have h₄ :
        (412 : ℝ) / 207 ≤
          √(2 + √(2 + √(2 + √(2 : ℝ)))) := by
      have hsq :=
        Real.sq_sqrt
          (show (0 : ℝ) ≤ 2 + √(2 + √(2 + √(2 : ℝ))) by
            positivity)
      have hnonneg :=
        Real.sqrt_nonneg (2 + √(2 + √(2 + √(2 : ℝ))))
      nlinarith only [h₃, hsq, hnonneg]
    norm_num [Real.sqrtTwoAddSeries]
    exact h₄

  have h_pi_lower : (3.14 : ℝ) < Real.pi := by
    have h_sin_lower :
        (3.14 : ℝ) / 64 < Real.sin (Real.pi / 64) := by
      rw [show (64 : ℝ) = 2 ^ (4 + 2) by norm_num,
        Real.sin_pi_over_two_pow_succ]
      have hrad : 0 ≤ 2 - Real.sqrtTwoAddSeries 0 4 :=
        sub_nonneg.mpr (Real.sqrtTwoAddSeries_lt_two 4).le
      have hsq := Real.sq_sqrt hrad
      have hnonneg :=
        Real.sqrt_nonneg (2 - Real.sqrtTwoAddSeries 0 4)
      nlinarith only [h_series_upper, hsq, hnonneg]
    have h_sin_upper :=
      sin_lt_local (show 0 < Real.pi / 64 by positivity)
    nlinarith only [h_sin_lower, h_sin_upper]

  have h_pi_upper : Real.pi < (3.15 : ℝ) := by
    have h_sin_upper :
        Real.sin (Real.pi / 64) < (0.04916 : ℝ) := by
      rw [show (64 : ℝ) = 2 ^ (4 + 2) by norm_num,
        Real.sin_pi_over_two_pow_succ]
      have hrad : 0 ≤ 2 - Real.sqrtTwoAddSeries 0 4 :=
        sub_nonneg.mpr (Real.sqrtTwoAddSeries_lt_two 4).le
      have hsq := Real.sq_sqrt hrad
      have hnonneg :=
        Real.sqrt_nonneg (2 - Real.sqrtTwoAddSeries 0 4)
      nlinarith only [h_series_lower, hsq, hnonneg]
    let x : ℝ := Real.pi / 64
    have hx_pos : 0 < x := by
      dsimp [x]
      positivity
    have hx_le : x ≤ (1 : ℝ) / 16 := by
      dsimp [x]
      nlinarith only [Real.pi_le_four]
    have hx_abs : |x| = x := abs_of_pos hx_pos
    have h_bound :=
      neg_le_of_abs_le
        (Real.sin_bound (x := x) (by rw [hx_abs]; linarith only [hx_le]))
    rw [hx_abs] at h_bound
    have hx3 : x ^ 3 ≤ ((1 : ℝ) / 16) ^ 3 :=
      pow_le_pow_left₀ hx_pos.le hx_le 3
    have hx4 : x ^ 4 ≤ ((1 : ℝ) / 16) ^ 4 :=
      pow_le_pow_left₀ hx_pos.le hx_le 4
    have h_sin_x : Real.sin x < (0.04916 : ℝ) := by
      simpa [x] using h_sin_upper
    dsimp [x] at h_bound hx3 hx4 h_sin_x ⊢
    nlinarith only [h_bound, hx3, hx4, h_sin_x]

  have h_sin_theta :
      Real.sin (thetaTwo setup).toReal = 500 * √2 / 1333 := by
    rw [Real.Angle.sin_toReal]
    unfold SatisfiesSnellsLaw at h_snell
    rw [h_air_index, h_water_index, h_thetaOne] at h_snell
    norm_num [degrees, Real.Angle.sin_coe] at h_snell
    have h_angle : (45 : ℝ) * Real.pi / 180 = Real.pi / 4 := by
      ring
    rw [h_angle, Real.sin_pi_div_four] at h_snell
    nlinarith only [h_snell]

  have h_sqrt_two_lower : (1.4142 : ℝ) < √2 := by
    rw [Real.lt_sqrt (by norm_num)]
    norm_num
  have h_sqrt_two_upper : √2 < (1.4143 : ℝ) := by
    rw [Real.sqrt_lt' (by norm_num)]
    norm_num
  have h_sqrt_three_lower : (1.732 : ℝ) < √3 := by
    rw [Real.lt_sqrt (by norm_num)]
    norm_num
  have h_sqrt_three_upper : √3 < (1.733 : ℝ) := by
    rw [Real.sqrt_lt' (by norm_num)]
    norm_num

  let deltaLower : ℝ := 13 * Real.pi / 1200
  have h_deltaLower_pos : 0 < deltaLower := by
    dsimp [deltaLower]
    positivity
  have h_deltaLower_lt : deltaLower < (0.0342 : ℝ) := by
    dsimp [deltaLower]
    nlinarith only [h_pi_upper]
  have h_sin_deltaLower_lt :
      Real.sin deltaLower < (0.0342 : ℝ) :=
    (sin_lt_local h_deltaLower_pos).trans h_deltaLower_lt
  have h_sin_deltaLower_pos : 0 < Real.sin deltaLower := by
    apply Real.sin_pos_of_pos_of_lt_pi h_deltaLower_pos
    dsimp [deltaLower]
    nlinarith only [Real.pi_pos]
  have h_product_lower_upper :
      √3 * Real.sin deltaLower < (1.733 : ℝ) * 0.0342 := by
    exact mul_lt_mul h_sqrt_three_upper h_sin_deltaLower_lt.le
      h_sin_deltaLower_pos (by norm_num)
  have h_boundary_lower_sin :
      Real.sin ((31.95 : ℝ) * Real.pi / 180) <
        500 * √2 / 1333 := by
    have h_angle :
        (31.95 : ℝ) * Real.pi / 180 =
          Real.pi / 6 + deltaLower := by
      dsimp [deltaLower]
      ring
    rw [h_angle, Real.sin_add, Real.sin_pi_div_six,
      Real.cos_pi_div_six]
    have h_cos := Real.cos_le_one deltaLower
    nlinarith only
      [h_product_lower_upper, h_cos, h_sqrt_two_lower]

  let deltaUpper : ℝ := 41 * Real.pi / 3600
  have h_deltaUpper_pos : 0 < deltaUpper := by
    dsimp [deltaUpper]
    positivity
  have h_deltaUpper_lower : (0.03576 : ℝ) < deltaUpper := by
    dsimp [deltaUpper]
    nlinarith only [h_pi_lower]
  have h_deltaUpper_upper : deltaUpper < (0.035875 : ℝ) := by
    dsimp [deltaUpper]
    nlinarith only [h_pi_upper]
  have h_deltaUpper_abs : |deltaUpper| = deltaUpper :=
    abs_of_pos h_deltaUpper_pos
  have h_deltaUpper_sq :
      deltaUpper ^ 2 ≤ (0.035875 : ℝ) ^ 2 :=
    pow_le_pow_left₀ h_deltaUpper_pos.le h_deltaUpper_upper.le 2
  have h_deltaUpper_cube :
      deltaUpper ^ 3 ≤ (0.035875 : ℝ) ^ 3 :=
    pow_le_pow_left₀ h_deltaUpper_pos.le h_deltaUpper_upper.le 3
  have h_deltaUpper_fourth :
      deltaUpper ^ 4 ≤ (0.035875 : ℝ) ^ 4 :=
    pow_le_pow_left₀ h_deltaUpper_pos.le h_deltaUpper_upper.le 4
  have h_deltaUpper_le_one : |deltaUpper| ≤ 1 := by
    rw [h_deltaUpper_abs]
    linarith only [h_deltaUpper_upper]
  have h_sin_deltaUpper_lower :
      (0.03575 : ℝ) < Real.sin deltaUpper := by
    have h_bound :=
      neg_le_of_abs_le (Real.sin_bound h_deltaUpper_le_one)
    rw [h_deltaUpper_abs] at h_bound
    nlinarith only
      [h_bound, h_deltaUpper_lower, h_deltaUpper_cube,
        h_deltaUpper_fourth]
  have h_cos_deltaUpper_lower :
      (0.99935 : ℝ) < Real.cos deltaUpper := by
    have h_bound :=
      neg_le_of_abs_le (Real.cos_bound h_deltaUpper_le_one)
    rw [h_deltaUpper_abs] at h_bound
    nlinarith only
      [h_bound, h_deltaUpper_sq, h_deltaUpper_fourth]
  have h_product_upper_lower :
      (1.732 : ℝ) * 0.03575 <
        √3 * Real.sin deltaUpper := by
    exact mul_lt_mul h_sqrt_three_lower h_sin_deltaUpper_lower.le
      (by norm_num) (Real.sqrt_nonneg 3)
  have h_boundary_upper_sin :
      500 * √2 / 1333 <
        Real.sin ((32.05 : ℝ) * Real.pi / 180) := by
    have h_angle :
        (32.05 : ℝ) * Real.pi / 180 =
          Real.pi / 6 + deltaUpper := by
      dsimp [deltaUpper]
      ring
    rw [h_angle, Real.sin_add, Real.sin_pi_div_six,
      Real.cos_pi_div_six]
    nlinarith only
      [h_product_upper_lower, h_cos_deltaUpper_lower,
        h_sqrt_two_upper]

  rcases h_thetaTwo_physical with ⟨h_theta_nonneg, h_theta_le⟩
  have h_lower_angle_nonneg :
      0 ≤ (31.95 : ℝ) * Real.pi / 180 := by positivity
  have h_lower_angle_le :
      (31.95 : ℝ) * Real.pi / 180 ≤ Real.pi / 2 := by
    nlinarith only [Real.pi_pos]
  have h_upper_angle_nonneg :
      0 ≤ (32.05 : ℝ) * Real.pi / 180 := by positivity
  have h_upper_angle_le :
      (32.05 : ℝ) * Real.pi / 180 ≤ Real.pi / 2 := by
    nlinarith only [Real.pi_pos]

  have h_theta_lower :
      (31.95 : ℝ) * Real.pi / 180 ≤ (thetaTwo setup).toReal := by
    by_contra h_not
    have h_theta_lt :
        (thetaTwo setup).toReal <
          (31.95 : ℝ) * Real.pi / 180 :=
      lt_of_not_ge h_not
    have h_sin_lt :=
      Real.sin_lt_sin_of_lt_of_le_pi_div_two
        (show -(Real.pi / 2) ≤ (thetaTwo setup).toReal by
          nlinarith only [h_theta_nonneg, Real.pi_pos])
        h_lower_angle_le h_theta_lt
    rw [h_sin_theta] at h_sin_lt
    linarith only [h_sin_lt, h_boundary_lower_sin]

  have h_theta_upper :
      (thetaTwo setup).toReal ≤
        (32.05 : ℝ) * Real.pi / 180 := by
    by_contra h_not
    have h_upper_lt :
        (32.05 : ℝ) * Real.pi / 180 <
          (thetaTwo setup).toReal :=
      lt_of_not_ge h_not
    have h_sin_lt :=
      Real.sin_lt_sin_of_lt_of_le_pi_div_two
        (show -(Real.pi / 2) ≤
            (32.05 : ℝ) * Real.pi / 180 by
          nlinarith only [h_upper_angle_nonneg, Real.pi_pos])
        h_theta_le h_upper_lt
    rw [h_sin_theta] at h_sin_lt
    linarith only [h_sin_lt, h_boundary_upper_sin]

  have h_degree_lower :
      (31.95 : ℝ) ≤
        (thetaTwo setup).toReal * 180 / Real.pi := by
    calc
      (31.95 : ℝ) =
          ((31.95 : ℝ) * Real.pi / 180) * (180 / Real.pi) := by
        field_simp [ne_of_gt Real.pi_pos]
      _ ≤ (thetaTwo setup).toReal * (180 / Real.pi) :=
        mul_le_mul_of_nonneg_right h_theta_lower (by positivity)
      _ = (thetaTwo setup).toReal * 180 / Real.pi := by ring
  have h_degree_upper :
      (thetaTwo setup).toReal * 180 / Real.pi ≤
        (32.05 : ℝ) := by
    calc
      (thetaTwo setup).toReal * 180 / Real.pi =
          (thetaTwo setup).toReal * (180 / Real.pi) := by ring
      _ ≤ ((32.05 : ℝ) * Real.pi / 180) * (180 / Real.pi) :=
        mul_le_mul_of_nonneg_right h_theta_upper (by positivity)
      _ = (32.05 : ℝ) := by
        field_simp [ne_of_gt Real.pi_pos]

  unfold MatchesAnswerToNearestTenth degreeReadout answerInDegrees
  rw [abs_le]
  constructor
  · norm_num
    linarith only [h_degree_lower]
  · norm_num
    linarith only [h_degree_upper]

end
end PhyXMiniProblems.ProblemPhyXMini0001
