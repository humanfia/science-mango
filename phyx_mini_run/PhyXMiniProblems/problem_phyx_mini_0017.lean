import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Physlib.Optics.Basic

/-!
# Mirrored right-angle prism

`Physlib.Optics.Basic` is imported as the relevant formal-physics module, but
that module is currently a placeholder and supplies no geometrical-optics law.
Consequently Snell refraction and specular reflection are stated below as local
law predicates on dimensionless refractive-index and radian angle readouts.
-/

namespace PhyXMiniProblems.Problem0017

/-- The two optical media occurring in the diagram. -/
inductive OpticalMedium
  | air
  | prism
  deriving DecidableEq, Repr

/-- The three prism surfaces met or identified by the ray path in the figure. -/
inductive PrismSurface
  | leftFace
  | mirrorBase
  | rightFace
  deriving DecidableEq, Repr

/-- The four directed ray segments drawn in the figure. -/
inductive RaySegment
  | incomingAir
  | insideTowardMirror
  | insideAfterMirror
  | outgoingAir
  deriving DecidableEq, Repr

/-- The answer labels displayed with the problem. -/
inductive AnswerChoice
  | A
  | B
  | C
  | D
  deriving DecidableEq, Repr

/-- Convert a scalar angle readout in degrees to its value in radians. -/
noncomputable def radiansOfDegrees (angleDegrees : ℝ) : ℝ :=
  angleDegrees * Real.pi / 180

/-- Convert a scalar angle readout in radians to its value in degrees. -/
noncomputable def degreesOfRadians (angleRadians : ℝ) : ℝ :=
  angleRadians * 180 / Real.pi

/-- An angle measured from a surface normal is on its physical principal range. -/
def IsPhysicalNormalAngle (angleRadians : ℝ) : Prop :=
  0 ≤ angleRadians ∧ angleRadians ≤ Real.pi / 2

/--
The figure-derived data for the right-angle prism. All angle fields are scalar
readouts in radians; the ray and surface lists retain the labels and order shown
in the diagram.
-/
structure PrismFigureData where
  leftBaseAngleRad : ℝ
  apexAngleRad : ℝ
  rightBaseAngleRad : ℝ
  entryIncidenceAngleRad : ℝ
  baseIsMirrored : Bool
  surfaceSequence : List PrismSurface
  raySequence : List RaySegment

/--
Snell's law for angles measured from the normal when a ray passes from one
optical medium to another. Refractive indices are dimensionless real readouts.
-/
def SnellLaw
    (refractiveIndex : OpticalMedium → ℝ)
    (incidentMedium transmittedMedium : OpticalMedium)
    (incidenceAngleRad refractionAngleRad : ℝ) : Prop :=
  refractiveIndex incidentMedium * Real.sin incidenceAngleRad =
    refractiveIndex transmittedMedium * Real.sin refractionAngleRad

/-- The law of specular reflection at the mirrored base. -/
def SpecularReflectionLaw
    (incidenceAngleRad reflectionAngleRad : ℝ) : Prop :=
  incidenceAngleRad = reflectionAngleRad

/-- The four numerical answer readouts, in degrees. -/
noncomputable def answerAngleDegrees : AnswerChoice → ℝ
  | .A => 883 / 100
  | .B => 1235 / 100
  | .C => 791 / 100
  | .D => 642 / 100

/--
`RoundsToHundredthDegree angle reported` says that the radian-valued physical
angle rounds to the displayed two-decimal degree readout `reported`.
-/
noncomputable def RoundsToHundredthDegree
    (angleRadians reportedDegrees : ℝ) : Prop :=
  abs (degreesOfRadians angleRadians - reportedDegrees) < 1 / 200

/--
For the ray path in the pictured right-angle prism, Snell refraction at the two
faces and specular reflection at the mirrored base make the outgoing angle
with the right-face normal round to answer C, `7.91°`.

Blueprint label: `thm:physics:phyx_mini_0017:target`.
-/
theorem outgoingRayAngle
    (figure : PrismFigureData)
    (refractiveIndex : OpticalMedium → ℝ)
    (entryRefractionAngleRad mirrorIncidenceAngleRad : ℝ)
    (mirrorReflectionAngleRad exitIncidenceAngleRad outgoingAngleRad : ℝ)
    (h_refractiveIndex_pos :
      ∀ medium : OpticalMedium, 0 < refractiveIndex medium)
    (h_air_index : refractiveIndex .air = 1)
    (h_prism_index : refractiveIndex .prism = 3 / 2)
    (h_left_base_angle :
      figure.leftBaseAngleRad = radiansOfDegrees 60)
    (h_right_apex : figure.apexAngleRad = radiansOfDegrees 90)
    (h_triangle_angle_sum :
      figure.leftBaseAngleRad + figure.apexAngleRad +
          figure.rightBaseAngleRad = Real.pi)
    (h_entry_angle :
      figure.entryIncidenceAngleRad = radiansOfDegrees 60)
    (h_base_mirrored : figure.baseIsMirrored = true)
    (h_surface_path :
      figure.surfaceSequence =
        [.leftFace, .mirrorBase, .rightFace])
    (h_ray_path :
      figure.raySequence =
        [.incomingAir, .insideTowardMirror, .insideAfterMirror, .outgoingAir])
    (h_entry_snell :
      SnellLaw refractiveIndex .air .prism
        figure.entryIncidenceAngleRad entryRefractionAngleRad)
    (h_entry_to_mirror_geometry :
      mirrorIncidenceAngleRad =
        figure.leftBaseAngleRad - entryRefractionAngleRad)
    (h_mirror_reflection :
      SpecularReflectionLaw
        mirrorIncidenceAngleRad mirrorReflectionAngleRad)
    (h_mirror_to_exit_geometry :
      exitIncidenceAngleRad =
        figure.rightBaseAngleRad - mirrorReflectionAngleRad)
    (h_exit_snell :
      SnellLaw refractiveIndex .prism .air
        exitIncidenceAngleRad outgoingAngleRad)
    (h_entry_refraction_physical :
      IsPhysicalNormalAngle entryRefractionAngleRad)
    (h_mirror_incidence_physical :
      IsPhysicalNormalAngle mirrorIncidenceAngleRad)
    (h_mirror_reflection_physical :
      IsPhysicalNormalAngle mirrorReflectionAngleRad)
    (h_exit_incidence_physical :
      IsPhysicalNormalAngle exitIncidenceAngleRad)
    (h_outgoing_physical : IsPhysicalNormalAngle outgoingAngleRad) :
    RoundsToHundredthDegree outgoingAngleRad (answerAngleDegrees .C) := by
  have h_left_angle : figure.leftBaseAngleRad = Real.pi / 3 := by
    rw [h_left_base_angle]
    unfold radiansOfDegrees
    ring
  have h_apex_angle : figure.apexAngleRad = Real.pi / 2 := by
    rw [h_right_apex]
    unfold radiansOfDegrees
    ring
  have h_right_angle : figure.rightBaseAngleRad = Real.pi / 6 := by
    rw [h_left_angle, h_apex_angle] at h_triangle_angle_sum
    linarith
  have h_incident_angle : figure.entryIncidenceAngleRad = Real.pi / 3 := by
    rw [h_entry_angle]
    unfold radiansOfDegrees
    ring
  have h_sin_entry :
      Real.sin entryRefractionAngleRad = Real.sqrt 3 / 3 := by
    rw [SnellLaw, h_air_index, h_prism_index, h_incident_angle,
      Real.sin_pi_div_three] at h_entry_snell
    nlinarith
  have h_entry_refraction_nonneg : 0 ≤ entryRefractionAngleRad :=
    h_entry_refraction_physical.1
  have h_entry_refraction_le :
      entryRefractionAngleRad ≤ Real.pi / 2 :=
    h_entry_refraction_physical.2
  have h_cos_entry :
      Real.cos entryRefractionAngleRad = Real.sqrt (2 / 3) := by
    rw [Real.cos_eq_sqrt_one_sub_sin_sq
      (by linarith only [h_entry_refraction_nonneg, Real.pi_pos])
      h_entry_refraction_le, h_sin_entry]
    congr 1
    have h_sqrt_three_sq : (Real.sqrt 3) ^ 2 = (3 : ℝ) :=
      Real.sq_sqrt (by norm_num)
    nlinarith
  have h_exit_angle :
      exitIncidenceAngleRad = entryRefractionAngleRad - Real.pi / 6 := by
    change mirrorIncidenceAngleRad = mirrorReflectionAngleRad at h_mirror_reflection
    rw [h_mirror_to_exit_geometry, h_right_angle,
      ← h_mirror_reflection, h_entry_to_mirror_geometry, h_left_angle]
    ring
  have h_sin_outgoing :
      Real.sin outgoingAngleRad = 3 / 4 * (1 - Real.sqrt (2 / 3)) := by
    rw [SnellLaw, h_prism_index, h_air_index, h_exit_angle,
      Real.sin_sub, h_sin_entry, h_cos_entry, Real.cos_pi_div_six,
      Real.sin_pi_div_six] at h_exit_snell
    have h_sqrt_three_sq : (Real.sqrt 3) ^ 2 = (3 : ℝ) :=
      Real.sq_sqrt (by norm_num)
    nlinarith
  have h_sqrt_two_thirds_sq :
      (Real.sqrt (2 / 3)) ^ 2 = (2 / 3 : ℝ) :=
    Real.sq_sqrt (by norm_num)
  have h_sqrt_two_thirds_nonneg : 0 ≤ Real.sqrt (2 / 3) :=
    Real.sqrt_nonneg _
  have h_sqrt_two_thirds_lower :
      (0.816496 : ℝ) < Real.sqrt (2 / 3) := by
    nlinarith only [h_sqrt_two_thirds_sq, h_sqrt_two_thirds_nonneg]
  have h_sqrt_two_thirds_upper :
      Real.sqrt (2 / 3) < (0.816497 : ℝ) := by
    nlinarith only [h_sqrt_two_thirds_sq, h_sqrt_two_thirds_nonneg]
  have h_sin_outgoing_lower :
      (0.137627 : ℝ) < Real.sin outgoingAngleRad := by
    rw [h_sin_outgoing]
    linarith only [h_sqrt_two_thirds_upper]
  have h_sin_outgoing_upper :
      Real.sin outgoingAngleRad < (0.137628 : ℝ) := by
    rw [h_sin_outgoing]
    linarith only [h_sqrt_two_thirds_lower]
  -- The imported exact half-angle value at `π / 32`, together with
  -- `Real.sin_bound`, supplies the modest decimal bounds on `π` needed below.
  have hr2_sq : (Real.sqrt 2) ^ 2 = (2 : ℝ) :=
    Real.sq_sqrt (by norm_num)
  have hr2_nonneg : 0 ≤ Real.sqrt 2 := Real.sqrt_nonneg _
  have hr2_lower : (1.4142135 : ℝ) < Real.sqrt 2 := by
    nlinarith only [hr2_sq, hr2_nonneg]
  have hr2_upper : Real.sqrt 2 < (1.4142136 : ℝ) := by
    nlinarith only [hr2_sq, hr2_nonneg]
  have hr3_arg : 0 ≤ (2 : ℝ) + Real.sqrt 2 := by positivity
  have hr3_sq :
      (Real.sqrt (2 + Real.sqrt 2)) ^ 2 = 2 + Real.sqrt 2 :=
    Real.sq_sqrt hr3_arg
  have hr3_nonneg : 0 ≤ Real.sqrt (2 + Real.sqrt 2) :=
    Real.sqrt_nonneg _
  have hr3_lower :
      (1.8477590 : ℝ) < Real.sqrt (2 + Real.sqrt 2) := by
    nlinarith only [hr3_sq, hr3_nonneg, hr2_lower]
  have hr3_upper :
      Real.sqrt (2 + Real.sqrt 2) < (1.8477591 : ℝ) := by
    nlinarith only [hr3_sq, hr3_nonneg, hr2_upper]
  have hr4_arg :
      0 ≤ (2 : ℝ) + Real.sqrt (2 + Real.sqrt 2) := by positivity
  have hr4_sq :
      (Real.sqrt (2 + Real.sqrt (2 + Real.sqrt 2))) ^ 2 =
        2 + Real.sqrt (2 + Real.sqrt 2) :=
    Real.sq_sqrt hr4_arg
  have hr4_nonneg :
      0 ≤ Real.sqrt (2 + Real.sqrt (2 + Real.sqrt 2)) :=
    Real.sqrt_nonneg _
  have hr4_lower :
      (1.9615705 : ℝ) <
        Real.sqrt (2 + Real.sqrt (2 + Real.sqrt 2)) := by
    nlinarith only [hr4_sq, hr4_nonneg, hr3_lower]
  have hr4_upper :
      Real.sqrt (2 + Real.sqrt (2 + Real.sqrt 2)) <
        (1.9615706 : ℝ) := by
    nlinarith only [hr4_sq, hr4_nonneg, hr3_upper]
  have hs_arg :
      0 ≤ (2 : ℝ) -
        Real.sqrt (2 + Real.sqrt (2 + Real.sqrt 2)) := by
    linarith only [hr4_upper]
  have hs_sq :
      (Real.sqrt
        (2 - Real.sqrt (2 + Real.sqrt (2 + Real.sqrt 2)))) ^ 2 =
        2 - Real.sqrt (2 + Real.sqrt (2 + Real.sqrt 2)) :=
    Real.sq_sqrt hs_arg
  have hs_nonneg :
      0 ≤ Real.sqrt
        (2 - Real.sqrt (2 + Real.sqrt (2 + Real.sqrt 2))) :=
    Real.sqrt_nonneg _
  have hs_lower :
      (0.196034 : ℝ) <
        Real.sqrt
          (2 - Real.sqrt (2 + Real.sqrt (2 + Real.sqrt 2))) := by
    nlinarith only [hs_sq, hs_nonneg, hr4_upper]
  have hs_upper :
      Real.sqrt
          (2 - Real.sqrt (2 + Real.sqrt (2 + Real.sqrt 2))) <
        (0.196036 : ℝ) := by
    nlinarith only [hs_sq, hs_nonneg, hr4_lower]
  have hsin_pi_div_thirty_two_lower :
      (0.098017 : ℝ) < Real.sin (Real.pi / 32) := by
    rw [Real.sin_pi_div_thirty_two]
    linarith only [hs_lower]
  have hsin_pi_div_thirty_two_upper :
      Real.sin (Real.pi / 32) < (0.098018 : ℝ) := by
    rw [Real.sin_pi_div_thirty_two]
    linarith only [hs_upper]
  clear hr2_sq hr2_nonneg hr2_lower hr2_upper hr3_arg hr3_sq
    hr3_nonneg hr3_lower hr3_upper hr4_arg hr4_sq hr4_nonneg
    hr4_lower hr4_upper hs_arg hs_sq hs_nonneg hs_lower hs_upper
  have hx_nonneg : 0 ≤ Real.pi / 32 := by positivity
  have hx_le_eighth : Real.pi / 32 ≤ (1 / 8 : ℝ) := by
    nlinarith only [Real.pi_le_four]
  have hx_abs : |Real.pi / 32| ≤ 1 := by
    rw [abs_of_nonneg hx_nonneg]
    linarith only [hx_le_eighth]
  have hsin_approx := Real.sin_bound hx_abs
  have hsin_approx_lower := (abs_le.mp hsin_approx).1
  have hsin_approx_upper := (abs_le.mp hsin_approx).2
  rw [abs_of_nonneg hx_nonneg] at hsin_approx_lower hsin_approx_upper
  clear hsin_approx hx_abs
  have hx_cube_nonneg : 0 ≤ (Real.pi / 32) ^ 3 := by positivity
  have hx_cube_le_eighth :
      (Real.pi / 32) ^ 3 ≤ (1 / 8 : ℝ) ^ 3 :=
    pow_le_pow_left₀ hx_nonneg hx_le_eighth 3
  have hx_fourth_le_eighth :
      (Real.pi / 32) ^ 4 ≤ (1 / 8 : ℝ) ^ 4 :=
    pow_le_pow_left₀ hx_nonneg hx_le_eighth 4
  have hpi_lower_coarse : (3.13 : ℝ) < Real.pi := by
    by_contra h
    have hpi_le : Real.pi ≤ (3.13 : ℝ) := le_of_not_gt h
    nlinarith only [hsin_pi_div_thirty_two_lower, hsin_approx_upper,
      hx_cube_nonneg, hx_fourth_le_eighth, hpi_le]
  have hpi_upper_coarse : Real.pi < (3.15 : ℝ) := by
    by_contra h
    have hpi_ge : (3.15 : ℝ) ≤ Real.pi := le_of_not_gt h
    nlinarith only [hsin_pi_div_thirty_two_upper, hsin_approx_lower,
      hx_cube_le_eighth, hx_fourth_le_eighth, hpi_ge]
  have hx_lt_tenth : Real.pi / 32 < (1 / 10 : ℝ) := by
    nlinarith only [hpi_upper_coarse]
  have hx_fourth_le_tenth :
      (Real.pi / 32) ^ 4 ≤ (1 / 10 : ℝ) ^ 4 :=
    pow_le_pow_left₀ hx_nonneg hx_lt_tenth.le 4
  have hx_cube_lower :
      (3.13 / 32 : ℝ) ^ 3 ≤ (Real.pi / 32) ^ 3 := by
    exact pow_le_pow_left₀ (by norm_num)
      (by linarith only [hpi_lower_coarse]) 3
  have hx_cube_upper :
      (Real.pi / 32) ^ 3 ≤ (3.15 / 32 : ℝ) ^ 3 := by
    exact pow_le_pow_left₀ hx_nonneg
      (by linarith only [hpi_upper_coarse]) 3
  have hpi_lower : (3.141 : ℝ) < Real.pi := by
    by_contra h
    have hpi_le : Real.pi ≤ (3.141 : ℝ) := le_of_not_gt h
    nlinarith only [hsin_pi_div_thirty_two_lower, hsin_approx_upper,
      hx_cube_lower, hx_fourth_le_tenth, hpi_le]
  have hpi_upper : Real.pi < (3.142 : ℝ) := by
    by_contra h
    have hpi_ge : (3.142 : ℝ) ≤ Real.pi := le_of_not_gt h
    nlinarith only [hsin_pi_div_thirty_two_upper, hsin_approx_lower,
      hx_cube_upper, hx_fourth_le_tenth, hpi_ge]

  -- Bound the sine at the lower endpoint `7.905°`.
  have h_lower_endpoint_nonneg :
      0 ≤ 527 * Real.pi / 12000 := by positivity
  have h_lower_endpoint_lower :
      (0.1379 : ℝ) < 527 * Real.pi / 12000 := by
    nlinarith only [hpi_lower]
  have h_lower_endpoint_upper :
      527 * Real.pi / 12000 < (0.137987 : ℝ) := by
    nlinarith only [hpi_upper]
  have h_lower_endpoint_abs :
      |527 * Real.pi / 12000| ≤ 1 := by
    rw [abs_of_nonneg h_lower_endpoint_nonneg]
    linarith only [h_lower_endpoint_upper]
  have h_lower_sin_approx :=
    Real.sin_bound h_lower_endpoint_abs
  have h_lower_sin_approx_upper :=
    (abs_le.mp h_lower_sin_approx).2
  rw [abs_of_nonneg h_lower_endpoint_nonneg] at h_lower_sin_approx_upper
  have h_lower_endpoint_cube_lower :
      (0.1379 : ℝ) ^ 3 ≤ (527 * Real.pi / 12000) ^ 3 :=
    pow_le_pow_left₀ (by norm_num) h_lower_endpoint_lower.le 3
  have h_lower_endpoint_fourth_upper :
      (527 * Real.pi / 12000) ^ 4 ≤ (0.137987 : ℝ) ^ 4 :=
    pow_le_pow_left₀ h_lower_endpoint_nonneg h_lower_endpoint_upper.le 4
  have h_lower_endpoint_sin :
      Real.sin (527 * Real.pi / 12000) < (0.137627 : ℝ) := by
    nlinarith only [h_lower_sin_approx_upper,
      h_lower_endpoint_upper, h_lower_endpoint_cube_lower,
      h_lower_endpoint_fourth_upper]

  -- Bound the sine at the upper endpoint `7.915°`.
  have h_upper_endpoint_nonneg :
      0 ≤ 1583 * Real.pi / 36000 := by positivity
  have h_upper_endpoint_lower :
      (0.13811 : ℝ) < 1583 * Real.pi / 36000 := by
    nlinarith only [hpi_lower]
  have h_upper_endpoint_upper :
      1583 * Real.pi / 36000 < (0.139 : ℝ) := by
    nlinarith only [hpi_upper]
  have h_upper_endpoint_abs :
      |1583 * Real.pi / 36000| ≤ 1 := by
    rw [abs_of_nonneg h_upper_endpoint_nonneg]
    linarith only [h_upper_endpoint_upper]
  have h_upper_sin_approx :=
    Real.sin_bound h_upper_endpoint_abs
  have h_upper_sin_approx_lower :=
    (abs_le.mp h_upper_sin_approx).1
  rw [abs_of_nonneg h_upper_endpoint_nonneg] at h_upper_sin_approx_lower
  have h_upper_endpoint_cube_upper :
      (1583 * Real.pi / 36000) ^ 3 ≤ (0.139 : ℝ) ^ 3 :=
    pow_le_pow_left₀ h_upper_endpoint_nonneg h_upper_endpoint_upper.le 3
  have h_upper_endpoint_fourth_upper :
      (1583 * Real.pi / 36000) ^ 4 ≤ (0.139 : ℝ) ^ 4 :=
    pow_le_pow_left₀ h_upper_endpoint_nonneg h_upper_endpoint_upper.le 4
  have h_upper_endpoint_sin :
      (0.137628 : ℝ) <
        Real.sin (1583 * Real.pi / 36000) := by
    nlinarith only [h_upper_sin_approx_lower,
      h_upper_endpoint_lower, h_upper_endpoint_cube_upper,
      h_upper_endpoint_fourth_upper]

  have h_outgoing_nonneg : 0 ≤ outgoingAngleRad :=
    h_outgoing_physical.1
  have h_outgoing_le : outgoingAngleRad ≤ Real.pi / 2 :=
    h_outgoing_physical.2
  have h_lower_endpoint_mem :
      527 * Real.pi / 12000 ∈
        Set.Icc (-(Real.pi / 2)) (Real.pi / 2) := by
    constructor
    · linarith only [h_lower_endpoint_nonneg, Real.pi_pos]
    · linarith only [h_lower_endpoint_upper, Real.one_le_pi_div_two]
  have h_outgoing_mem :
      outgoingAngleRad ∈
        Set.Icc (-(Real.pi / 2)) (Real.pi / 2) := by
    exact ⟨by linarith only [h_outgoing_nonneg, Real.pi_pos],
      h_outgoing_le⟩
  have h_upper_endpoint_mem :
      1583 * Real.pi / 36000 ∈
        Set.Icc (-(Real.pi / 2)) (Real.pi / 2) := by
    constructor
    · linarith only [h_upper_endpoint_nonneg, Real.pi_pos]
    · linarith only [h_upper_endpoint_upper, Real.one_le_pi_div_two]
  have h_angle_lower :
      527 * Real.pi / 12000 < outgoingAngleRad := by
    apply (Real.strictMonoOn_sin.lt_iff_lt
      h_lower_endpoint_mem h_outgoing_mem).mp
    linarith only [h_lower_endpoint_sin, h_sin_outgoing_lower]
  have h_angle_upper :
      outgoingAngleRad < 1583 * Real.pi / 36000 := by
    apply (Real.strictMonoOn_sin.lt_iff_lt
      h_outgoing_mem h_upper_endpoint_mem).mp
    linarith only [h_sin_outgoing_upper, h_upper_endpoint_sin]
  have h_degrees_lower :
      (1581 / 200 : ℝ) < outgoingAngleRad * 180 / Real.pi := by
    apply (lt_div_iff₀ Real.pi_pos).2
    nlinarith only [h_angle_lower]
  have h_degrees_upper :
      outgoingAngleRad * 180 / Real.pi < (1583 / 200 : ℝ) := by
    apply (div_lt_iff₀ Real.pi_pos).2
    nlinarith only [h_angle_upper]
  change |outgoingAngleRad * 180 / Real.pi - 791 / 100| < 1 / 200
  rw [abs_lt]
  constructor <;> nlinarith only [h_degrees_lower, h_degrees_upper]

end PhyXMiniProblems.Problem0017
