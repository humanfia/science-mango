import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Physlib.Units.WithDim.Basic

noncomputable section

namespace PhyXMiniProblems.ProblemPhyXMini0050

/-!
# Refractive index of a 30°-60°-90° prism

The primary image shows a horizontal laser ray entering the vertical face of a
right triangular prism at normal incidence.  The ray remains horizontal inside
the prism and leaves through the sloping face, deflected `22.6°` below its
original direction.  Angles below are dimensionless radian readouts; refractive
indices are unit-independent physical quantities attached to explicitly
distinguished optical regions.
-/

/-- A unit-independent physical scalar, carried by Physlib's identity dimension. -/
abbrev DimensionlessQuantity : Type :=
  Dimensionful (WithDim (1 : Dimension) ℝ)

/-- The real scalar readout of a dimensionless physical quantity. -/
def dimensionlessReadout (quantity : DimensionlessQuantity) : ℝ :=
  (quantity UnitChoices.SI).val

/-- Convert the degree labels printed in the figure to radian values. -/
def radiansOfDegrees (angleDegrees : ℝ) : ℝ :=
  angleDegrees * Real.pi / 180

/-- The two physical regions crossed by the laser beam. -/
inductive OpticalRegion where
  | surroundingAir
  | prismInterior
  deriving DecidableEq, Repr

/-- The three vertices of the triangular prism in the primary image. -/
inductive PrismVertex where
  | top
  | lowerLeft
  | lowerRight
  deriving DecidableEq, Repr

/-- The prism interfaces crossed by the ray, in propagation order. -/
inductive PrismFace where
  | entry
  | exit
  deriving DecidableEq, Repr

/-- The three directed portions of the depicted laser path. -/
inductive RaySegment where
  | incident
  | internal
  | outgoing
  deriving DecidableEq, Repr

/--
The physical and geometrical quantities in the prism experiment.

Directions are oriented radian angles measured counterclockwise from the
rightward horizontal direction.  At each crossed face,
`propagationNormalDirectionRad` chooses the normal pointing into the forward
half-space of the propagating ray.  This makes incidence/refraction angles the
ordinary acute differences from the relevant normal.
-/
structure PrismLaserSetup where
  /-- Unit-independent refractive index of each physical optical region. -/
  refractiveIndex : OpticalRegion → DimensionlessQuantity
  /-- Interior angle at each labeled prism vertex, in radians. -/
  vertexAngleRad : PrismVertex → ℝ
  /-- Oriented propagation direction of each ray segment, in radians. -/
  rayDirectionRad : RaySegment → ℝ
  /-- Forward-facing normal direction at each crossed prism face. -/
  propagationNormalDirectionRad : PrismFace → ℝ
  /-- Magnitude of the beam's final deflection from its incident direction. -/
  deflectionAngleRad : ℝ

/-- The nonnegative angle between a ray segment and a chosen face normal. -/
def angleFromPropagationNormal
    (setup : PrismLaserSetup) (face : PrismFace) (ray : RaySegment) : ℝ :=
  |setup.rayDirectionRad ray - setup.propagationNormalDirectionRad face|

/--
Numerical and directional readouts visible in the primary image: the prism
vertices are `30°`, `90°`, and `60°`, and the outgoing beam is deflected
`22.6°` below the original horizontal laser direction.
-/
structure MatchesFigureReadouts (setup : PrismLaserSetup) : Prop where
  top_vertex : setup.vertexAngleRad .top = radiansOfDegrees 30
  lower_left_vertex : setup.vertexAngleRad .lowerLeft = radiansOfDegrees 90
  lower_right_vertex : setup.vertexAngleRad .lowerRight = radiansOfDegrees 60
  incident_ray_horizontal : setup.rayDirectionRad .incident = radiansOfDegrees 0
  deflection_label : setup.deflectionAngleRad = radiansOfDegrees 22.6

/--
Spatial relations supplied by the right-triangle prism geometry.  The entry
face is vertical, hence its forward normal is horizontal.  Since the sloping
face meets the vertical face at the top vertex, its outward forward normal has
the direction of that `30°` vertex angle in the pictured coordinates.
-/
structure HasDepictedPrismGeometry (setup : PrismLaserSetup) : Prop where
  triangle_angle_sum :
    setup.vertexAngleRad .top + setup.vertexAngleRad .lowerLeft +
        setup.vertexAngleRad .lowerRight = Real.pi
  entry_normal_horizontal :
    setup.propagationNormalDirectionRad .entry = radiansOfDegrees 0
  exit_normal_from_top_angle :
    setup.propagationNormalDirectionRad .exit = setup.vertexAngleRad .top

/--
The depicted propagation path: normal entry produces the horizontal internal
segment, and the exiting segment is clockwise from the incident segment by the
positive deflection shown in the figure.
-/
structure HasDepictedRayPath (setup : PrismLaserSetup) : Prop where
  no_bending_at_normal_entry :
    setup.rayDirectionRad .internal = setup.rayDirectionRad .incident
  outgoing_direction :
    setup.rayDirectionRad .outgoing =
      setup.rayDirectionRad .incident - setup.deflectionAngleRad

/-- The idealized surrounding air has index one, and both indices are positive. -/
structure HasPhysicalRefractiveIndices (setup : PrismLaserSetup) : Prop where
  air_index : dimensionlessReadout (setup.refractiveIndex .surroundingAir) = 1
  air_index_positive :
    0 < dimensionlessReadout (setup.refractiveIndex .surroundingAir)
  prism_index_positive :
    0 < dimensionlessReadout (setup.refractiveIndex .prismInterior)

/--
Snell's law at the entry and exit interfaces.  Every angle is measured from
the local propagation normal, and every refractive index is dimensionless.
-/
structure SatisfiesSnellLawAtPrismFaces (setup : PrismLaserSetup) : Prop where
  entry_face :
    dimensionlessReadout (setup.refractiveIndex .surroundingAir) *
          Real.sin (angleFromPropagationNormal setup .entry .incident) =
      dimensionlessReadout (setup.refractiveIndex .prismInterior) *
          Real.sin (angleFromPropagationNormal setup .entry .internal)
  exit_face :
    dimensionlessReadout (setup.refractiveIndex .prismInterior) *
          Real.sin (angleFromPropagationNormal setup .exit .internal) =
      dimensionlessReadout (setup.refractiveIndex .surroundingAir) *
          Real.sin (angleFromPropagationNormal setup .exit .outgoing)

/-- The four answer labels printed beside the source problem. -/
inductive AnswerChoice where
  | A
  | B
  | C
  | D
  deriving DecidableEq, Repr

/-- The dimensionless refractive-index value displayed by each answer choice. -/
def answerRefractiveIndex : AnswerChoice → ℝ
  | .A => 0.64
  | .B => 1.59
  | .C => 0.89
  | .D => 1.24

/-- Agreement with a refractive index displayed to the nearest hundredth. -/
def MatchesAnswerToNearestHundredth
    (actual : ℝ) (choice : AnswerChoice) : Prop :=
  |actual - answerRefractiveIndex choice| ≤ (1 : ℝ) / 200

/--
The primary-image geometry makes the exit incidence angle `30°` and the exit
refraction angle `30° + 22.6° = 52.6°`, both measured from the exit normal.
-/
lemma exit_interface_angles_from_figure
    (setup : PrismLaserSetup)
    (_figure : MatchesFigureReadouts setup)
    (_prismGeometry : HasDepictedPrismGeometry setup)
    (_rayPath : HasDepictedRayPath setup) :
    angleFromPropagationNormal setup .exit .internal = radiansOfDegrees 30 ∧
      angleFromPropagationNormal setup .exit .outgoing = radiansOfDegrees 52.6 := by
  unfold angleFromPropagationNormal
  rw [_rayPath.no_bending_at_normal_entry, _rayPath.outgoing_direction,
    _figure.incident_ray_horizontal, _figure.deflection_label,
    _prismGeometry.exit_normal_from_top_angle, _figure.top_vertex]
  constructor
  · rw [show radiansOfDegrees 0 - radiansOfDegrees 30 = -(Real.pi / 6) by
      unfold radiansOfDegrees
      ring]
    rw [abs_neg, abs_of_nonneg (by positivity)]
    unfold radiansOfDegrees
    ring
  · rw [show radiansOfDegrees 0 - radiansOfDegrees 22.6 -
        radiansOfDegrees 30 = -(263 * Real.pi / 900) by
      unfold radiansOfDegrees
      ring]
    rw [abs_neg, abs_of_nonneg (by positivity)]
    unfold radiansOfDegrees
    ring

/--
Snell's law at the exit face and the idealized air index determine the exact
symbolic prism index before any decimal rounding is performed.
-/
lemma prism_refractive_index_exact_formula
    (setup : PrismLaserSetup)
    (_figure : MatchesFigureReadouts setup)
    (_prismGeometry : HasDepictedPrismGeometry setup)
    (_rayPath : HasDepictedRayPath setup)
    (_indices : HasPhysicalRefractiveIndices setup)
    (_snell : SatisfiesSnellLawAtPrismFaces setup) :
    dimensionlessReadout (setup.refractiveIndex .prismInterior) =
      Real.sin (radiansOfDegrees 52.6) / Real.sin (radiansOfDegrees 30) := by
  have hangles :=
    exit_interface_angles_from_figure setup _figure _prismGeometry _rayPath
  have hsnell := _snell.exit_face
  rw [hangles.1, hangles.2, _indices.air_index] at hsnell
  have hsin30 : Real.sin (radiansOfDegrees 30) = (1 : ℝ) / 2 := by
    rw [show radiansOfDegrees 30 = Real.pi / 6 by
      unfold radiansOfDegrees
      ring]
    exact Real.sin_pi_div_six
  rw [hsin30] at hsnell ⊢
  linarith

/--
For the pictured `30°-60°-90°` prism, the exact Snell-law expression rounds to
the dimensionless refractive index `1.59`, answer choice B.

This formalizes `thm:physics:phyx_mini_0050:target`.
-/
theorem problem_phyx_mini_0050
    (setup : PrismLaserSetup)
    (_figure : MatchesFigureReadouts setup)
    (_prismGeometry : HasDepictedPrismGeometry setup)
    (_rayPath : HasDepictedRayPath setup)
    (_indices : HasPhysicalRefractiveIndices setup)
    (_snell : SatisfiesSnellLawAtPrismFaces setup) :
    dimensionlessReadout (setup.refractiveIndex .prismInterior) =
        Real.sin (radiansOfDegrees 52.6) / Real.sin (radiansOfDegrees 30) ∧
      MatchesAnswerToNearestHundredth
        (dimensionlessReadout (setup.refractiveIndex .prismInterior)) .B := by
  have hexact :=
    prism_refractive_index_exact_formula setup _figure _prismGeometry _rayPath
      _indices _snell
  constructor
  · exact hexact
  rw [hexact]
  have hsin30 : Real.sin (radiansOfDegrees 30) = (1 : ℝ) / 2 := by
    rw [show radiansOfDegrees 30 = Real.pi / 6 by
      unfold radiansOfDegrees
      ring]
    exact Real.sin_pi_div_six
  rw [hsin30]

  have hpi_ge_three : (3 : ℝ) ≤ Real.pi := by
    by_contra h
    have hpi_lt_three : Real.pi < (3 : ℝ) := lt_of_not_ge h
    have hx_nonneg : 0 ≤ Real.pi / 6 := by positivity
    have hx_lower : (1 : ℝ) / 3 ≤ Real.pi / 6 := by
      nlinarith only [Real.one_le_pi_div_two]
    have hx_upper : Real.pi / 6 ≤ (1 : ℝ) / 2 := by
      linarith
    have hx_abs : |Real.pi / 6| ≤ 1 := by
      rw [abs_of_nonneg hx_nonneg]
      linarith
    have hbound := (abs_le.mp (Real.sin_bound hx_abs)).2
    rw [abs_of_nonneg hx_nonneg, Real.sin_pi_div_six] at hbound
    have hcube_lower : ((1 : ℝ) / 3) ^ 3 ≤ (Real.pi / 6) ^ 3 :=
      pow_le_pow_left₀ (by norm_num) hx_lower 3
    have hfourth_upper : (Real.pi / 6) ^ 4 ≤ ((1 : ℝ) / 2) ^ 4 :=
      pow_le_pow_left₀ hx_nonneg hx_upper 4
    norm_num at hcube_lower hfourth_upper
    nlinarith
  have hpi_lower : (3.1 : ℝ) < Real.pi := by
    by_contra h
    have hpi_upper : Real.pi ≤ (3.1 : ℝ) := le_of_not_gt h
    have hx_nonneg : 0 ≤ Real.pi / 6 := by positivity
    have hx_lower : (1 : ℝ) / 2 ≤ Real.pi / 6 := by
      linarith
    have hx_upper : Real.pi / 6 ≤ (31 : ℝ) / 60 := by
      linarith
    have hx_abs : |Real.pi / 6| ≤ 1 := by
      rw [abs_of_nonneg hx_nonneg]
      linarith
    have hbound := (abs_le.mp (Real.sin_bound hx_abs)).2
    rw [abs_of_nonneg hx_nonneg, Real.sin_pi_div_six] at hbound
    have hcube_lower : ((1 : ℝ) / 2) ^ 3 ≤ (Real.pi / 6) ^ 3 :=
      pow_le_pow_left₀ (by norm_num) hx_lower 3
    have hfourth_upper : (Real.pi / 6) ^ 4 ≤ ((31 : ℝ) / 60) ^ 4 :=
      pow_le_pow_left₀ hx_nonneg hx_upper 4
    norm_num at hcube_lower hfourth_upper
    nlinarith
  have hsqrt_lower : (1.732 : ℝ) < Real.sqrt 3 := by
    rw [Real.lt_sqrt (by norm_num)]
    norm_num
  have hpi_lt_34 : Real.pi < (3.4 : ℝ) := by
    by_contra h
    have hpi_lower' : (3.4 : ℝ) ≤ Real.pi := le_of_not_gt h
    have hx_nonneg : 0 ≤ Real.pi / 6 := by positivity
    have hx_lower : (17 : ℝ) / 30 ≤ Real.pi / 6 := by
      linarith
    have hx_upper : Real.pi / 6 ≤ (2 : ℝ) / 3 := by
      nlinarith only [Real.pi_le_four]
    have hx_abs : |Real.pi / 6| ≤ 1 := by
      rw [abs_of_nonneg hx_nonneg]
      linarith
    have hbound := (abs_le.mp (Real.cos_bound hx_abs)).2
    rw [abs_of_nonneg hx_nonneg, Real.cos_pi_div_six] at hbound
    have hsquare_lower : ((17 : ℝ) / 30) ^ 2 ≤ (Real.pi / 6) ^ 2 :=
      pow_le_pow_left₀ (by norm_num) hx_lower 2
    have hfourth_upper : (Real.pi / 6) ^ 4 ≤ ((2 : ℝ) / 3) ^ 4 :=
      pow_le_pow_left₀ hx_nonneg hx_upper 4
    norm_num at hsquare_lower hfourth_upper
    nlinarith
  have hpi_upper : Real.pi < (3.2 : ℝ) := by
    by_contra h
    have hpi_lower' : (3.2 : ℝ) ≤ Real.pi := le_of_not_gt h
    have hx_nonneg : 0 ≤ Real.pi / 6 := by positivity
    have hx_lower : (8 : ℝ) / 15 ≤ Real.pi / 6 := by
      linarith
    have hx_upper : Real.pi / 6 ≤ (17 : ℝ) / 30 := by
      linarith
    have hx_abs : |Real.pi / 6| ≤ 1 := by
      rw [abs_of_nonneg hx_nonneg]
      linarith
    have hbound := (abs_le.mp (Real.cos_bound hx_abs)).2
    rw [abs_of_nonneg hx_nonneg, Real.cos_pi_div_six] at hbound
    have hsquare_lower : ((8 : ℝ) / 15) ^ 2 ≤ (Real.pi / 6) ^ 2 :=
      pow_le_pow_left₀ (by norm_num) hx_lower 2
    have hfourth_upper : (Real.pi / 6) ^ 4 ≤ ((17 : ℝ) / 30) ^ 4 :=
      pow_le_pow_left₀ hx_nonneg hx_upper 4
    norm_num at hsquare_lower hfourth_upper
    nlinarith

  let delta : ℝ := 37 * Real.pi / 900
  have hdelta_nonneg : 0 ≤ delta := by
    dsimp [delta]
    positivity
  have hdelta_lower : (1147 : ℝ) / 9000 ≤ delta := by
    dsimp [delta]
    nlinarith
  have hdelta_upper : delta ≤ (148 : ℝ) / 1125 := by
    dsimp [delta]
    nlinarith
  have hdelta_abs : |delta| ≤ 1 := by
    rw [abs_of_nonneg hdelta_nonneg]
    linarith
  have hsin_bound := abs_le.mp (Real.sin_bound hdelta_abs)
  have hcos_bound := abs_le.mp (Real.cos_bound hdelta_abs)
  rw [abs_of_nonneg hdelta_nonneg] at hsin_bound hcos_bound
  have hdelta_square_lower :
      ((1147 : ℝ) / 9000) ^ 2 ≤ delta ^ 2 :=
    pow_le_pow_left₀ (by norm_num) hdelta_lower 2
  have hdelta_cube_lower :
      ((1147 : ℝ) / 9000) ^ 3 ≤ delta ^ 3 :=
    pow_le_pow_left₀ (by norm_num) hdelta_lower 3
  have hdelta_square_upper :
      delta ^ 2 ≤ ((148 : ℝ) / 1125) ^ 2 :=
    pow_le_pow_left₀ hdelta_nonneg hdelta_upper 2
  have hdelta_cube_upper :
      delta ^ 3 ≤ ((148 : ℝ) / 1125) ^ 3 :=
    pow_le_pow_left₀ hdelta_nonneg hdelta_upper 3
  have hdelta_fourth_upper :
      delta ^ 4 ≤ ((148 : ℝ) / 1125) ^ 4 :=
    pow_le_pow_left₀ hdelta_nonneg hdelta_upper 4
  have hsin_lower : (0.127 : ℝ) < Real.sin delta := by
    nlinarith only [hsin_bound.1, hdelta_lower, hdelta_cube_upper,
      hdelta_fourth_upper]
  have hsin_upper : Real.sin delta < (0.1313 : ℝ) := by
    nlinarith only [hsin_bound.2, hdelta_upper, hdelta_cube_lower,
      hdelta_fourth_upper]
  have hcos_lower : (0.9913 : ℝ) < Real.cos delta := by
    nlinarith only [hcos_bound.1, hdelta_square_upper,
      hdelta_fourth_upper]
  have hcos_upper : Real.cos delta < (0.992 : ℝ) := by
    nlinarith only [hcos_bound.2, hdelta_square_lower,
      hdelta_fourth_upper]
  have hsqrt_upper : Real.sqrt 3 < (1.733 : ℝ) := by
    rw [Real.sqrt_lt' (by norm_num)]
    norm_num
  have hsqrt_half_lower : (0.866 : ℝ) < Real.sqrt 3 / 2 := by
    linarith
  have hsqrt_half_upper : Real.sqrt 3 / 2 < (0.8665 : ℝ) := by
    linarith
  have hproduct_lower :
      (0.866 : ℝ) * 0.9913 <
        (Real.sqrt 3 / 2) * Real.cos delta :=
    mul_lt_mul hsqrt_half_lower hcos_lower.le (by norm_num)
      (by positivity)
  have hproduct_upper :
      (Real.sqrt 3 / 2) * Real.cos delta <
        (0.8665 : ℝ) * 0.992 :=
    mul_lt_mul hsqrt_half_upper hcos_upper.le
      (by linarith) (by norm_num)
  have hangle :
      radiansOfDegrees 52.6 = Real.pi / 3 - delta := by
    dsimp [radiansOfDegrees, delta]
    ring
  have hsin_formula :
      Real.sin (radiansOfDegrees 52.6) =
        (Real.sqrt 3 / 2) * Real.cos delta -
          (1 / 2) * Real.sin delta := by
    rw [hangle, Real.sin_sub, Real.sin_pi_div_three,
      Real.cos_pi_div_three]
  have htarget_lower :
      (0.7925 : ℝ) < Real.sin (radiansOfDegrees 52.6) := by
    rw [hsin_formula]
    nlinarith only [hproduct_lower, hsin_upper]
  have htarget_upper :
      Real.sin (radiansOfDegrees 52.6) < (0.7975 : ℝ) := by
    rw [hsin_formula]
    nlinarith only [hproduct_upper, hsin_lower]
  unfold MatchesAnswerToNearestHundredth answerRefractiveIndex
  rw [abs_le]
  constructor <;> norm_num at ⊢ <;> linarith

end PhyXMiniProblems.ProblemPhyXMini0050
