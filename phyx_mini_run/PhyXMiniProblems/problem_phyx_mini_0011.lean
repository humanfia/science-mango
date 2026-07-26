import Mathlib.Analysis.SpecialFunctions.Trigonometric.Inverse
import Physlib.Optics.Basic

/- `Physlib.Optics.Basic` is currently a placeholder, so this file states the
Snell-law and critical-transmission interfaces needed by the problem locally. -/

namespace PhyXMiniProblems.ProblemPhyXMini0011

noncomputable section

/-- The optical media named in the scenario.  The requested rotation occurs
while the diamond is immersed in water; `air` records the other ambient medium
mentioned in the problem statement. -/
inductive OpticalMedium where
  | air
  | water
  | diamond
  deriving DecidableEq, Repr

/-- The labeled points in the diamond diagram. -/
inductive FigurePoint where
  | O
  | P
  deriving DecidableEq, Repr

/-- Distinguished planar directions used by the figure readouts. -/
inductive PlanarDirection where
  | horizontal
  | vertical
  | other
  deriving DecidableEq, Repr

/-- The orientation of a rotation axis relative to the printed page. -/
inductive AxisOrientation where
  | inPage
  | perpendicularToPage
  deriving DecidableEq, Repr

/-- A physical rotation axis is specified by its point and spatial
orientation, rather than by a bare scalar. -/
structure RotationAxis where
  passesThrough : FigurePoint
  orientation : AxisOrientation
  deriving DecidableEq, Repr

/-- Scalar readouts and physical labels for one rotated-diamond configuration.

Refractive indices are dimensionless.  Fields ending in `Radians` are measured
angle readouts in radians. -/
structure DiamondRotationSetup where
  refractiveIndex : OpticalMedium → ℝ
  rotationAxis : RotationAxis
  incidentRayDirection : PlanarDirection
  entryFacetInitialDirection : PlanarDirection
  entryExteriorMedium : OpticalMedium
  pExteriorMedium : OpticalMedium
  boundaryInteractionPoint : FigurePoint
  /-- The ray has not transmitted through another facet before reaching `P`. -/
  rayStaysInsideBeforeP : Prop
  /-- Magnitude of the body's rotation about the specified axis. -/
  rotationAngleRadians : ℝ
  /-- Incidence angle of the fixed vertical ray at the rotated entry facet. -/
  entryIncidenceAngleRadians : ℝ
  /-- Refracted angle in the diamond, measured from the entry normal. -/
  entryRefractionAngleRadians : ℝ
  /-- Angle of the facet through `P` from the horizontal dashed line. -/
  pFacetAngleToHorizontalRadians : ℝ
  /-- Incidence angle in the diamond at `P`, measured from the facet normal. -/
  pIncidenceAngleRadians : ℝ
  /-- Transmitted angle in water at `P`, measured from the facet normal. -/
  pTransmissionAngleRadians : ℝ

/-- Convert a numerical degree readout to radians. -/
def degreesToRadians (value : ℝ) : ℝ :=
  value * Real.pi / 180

/-- Convert a radian readout to degrees. -/
def radiansToDegrees (value : ℝ) : ℝ :=
  value * 180 / Real.pi

/-- Refractive indices of every named medium are physically positive. -/
def HasPositiveRefractiveIndices (setup : DiamondRotationSetup) : Prop :=
  ∀ medium, 0 < setup.refractiveIndex medium

/-- Acute representatives are selected for the angles occurring in Snell's
law and at the first-transmission threshold. -/
def HasPhysicalAngleRanges (setup : DiamondRotationSetup) : Prop :=
  setup.rotationAngleRadians ∈ Set.Icc 0 (Real.pi / 2) ∧
  setup.entryIncidenceAngleRadians ∈ Set.Icc 0 (Real.pi / 2) ∧
  setup.entryRefractionAngleRadians ∈ Set.Icc 0 (Real.pi / 2) ∧
  setup.pIncidenceAngleRadians ∈ Set.Icc 0 (Real.pi / 2) ∧
  setup.pTransmissionAngleRadians ∈ Set.Icc 0 (Real.pi / 2)

/-- Figure readouts: rotation is about `O` perpendicular to the page, the
incoming ray remains vertical, the unrotated entry facet is horizontal, both
relevant exterior media are water, the exit point is `P`, and the displayed
facet angle is `35.0°`. -/
def HasFigureReadouts (setup : DiamondRotationSetup) : Prop :=
  setup.rotationAxis.passesThrough = .O ∧
  setup.rotationAxis.orientation = .perpendicularToPage ∧
  setup.incidentRayDirection = .vertical ∧
  setup.entryFacetInitialDirection = .horizontal ∧
  setup.entryExteriorMedium = .water ∧
  setup.pExteriorMedium = .water ∧
  setup.boundaryInteractionPoint = .P ∧
  setup.pFacetAngleToHorizontalRadians = degreesToRadians 35

/-- Standard refractive-index readouts used by the multiple-choice problem. -/
def HasMaterialReadouts (setup : DiamondRotationSetup) : Prop :=
  setup.refractiveIndex .water = 4 / 3 ∧
  setup.refractiveIndex .diamond = 2.42

/-- Co-rotation of the two facet normals gives the planar angle relations for
the fixed vertical incident ray. -/
def HasRotatedRayGeometry (setup : DiamondRotationSetup) : Prop :=
  setup.entryIncidenceAngleRadians = setup.rotationAngleRadians ∧
  setup.pIncidenceAngleRadians =
    setup.pFacetAngleToHorizontalRadians -
      setup.entryRefractionAngleRadians

/-- Snell's law at the water-to-diamond entry facet. -/
def SatisfiesSnellLawAtEntry (setup : DiamondRotationSetup) : Prop :=
  setup.refractiveIndex setup.entryExteriorMedium *
      Real.sin setup.entryIncidenceAngleRadians =
    setup.refractiveIndex .diamond *
      Real.sin setup.entryRefractionAngleRadians

/-- Snell's law at the diamond-to-water facet through `P`. -/
def SatisfiesSnellLawAtP (setup : DiamondRotationSetup) : Prop :=
  setup.refractiveIndex .diamond *
      Real.sin setup.pIncidenceAngleRadians =
    setup.refractiveIndex setup.pExteriorMedium *
      Real.sin setup.pTransmissionAngleRadians

/-- At first transmission through `P`, the ray has remained inside before `P`
and the transmitted ray at `P` is tangent to the facet. -/
def IsAtFirstExitThresholdAtP (setup : DiamondRotationSetup) : Prop :=
  setup.boundaryInteractionPoint = .P ∧
  setup.rayStaysInsideBeforeP ∧
  setup.pTransmissionAngleRadians = Real.pi / 2

/-- Critical incidence angle at the diamond-to-water interface through `P`. -/
def criticalAngleAtPRadians (setup : DiamondRotationSetup) : ℝ :=
  Real.arcsin
    (setup.refractiveIndex setup.pExteriorMedium /
      setup.refractiveIndex .diamond)

/-- Closed-form rotation obtained by combining the facet geometry, critical
angle, and Snell's law at the entry interface. -/
def requiredRotationRadians (setup : DiamondRotationSetup) : ℝ :=
  Real.arcsin
    (setup.refractiveIndex .diamond /
        setup.refractiveIndex setup.entryExteriorMedium *
      Real.sin
        (setup.pFacetAngleToHorizontalRadians -
          criticalAngleAtPRadians setup))

/-- The governing optical laws determine the rotation by the physical closed
form.  This equality is a conclusion, not a setup field or premise. -/
lemma rotationAngle_eq_requiredRotation
    (setup : DiamondRotationSetup)
    (h_indices_positive : HasPositiveRefractiveIndices setup)
    (h_ranges : HasPhysicalAngleRanges setup)
    (h_figure : HasFigureReadouts setup)
    (h_geometry : HasRotatedRayGeometry setup)
    (h_snell_entry : SatisfiesSnellLawAtEntry setup)
    (h_snell_p : SatisfiesSnellLawAtP setup)
    (h_first_exit : IsAtFirstExitThresholdAtP setup) :
    setup.rotationAngleRadians = requiredRotationRadians setup := by
  have _h_figure_readouts : HasFigureReadouts setup := h_figure
  rcases h_ranges with
    ⟨h_rotation_range, h_entry_incidence_range, h_entry_refraction_range,
      h_p_incidence_range, _h_p_transmission_range⟩
  rcases h_geometry with ⟨h_entry_geometry, h_p_geometry⟩
  rcases h_first_exit with ⟨_h_exit_at_p, _h_inside_before_p, h_tangent_at_p⟩
  have h_diamond_pos := h_indices_positive .diamond
  have h_entry_medium_pos :=
    h_indices_positive setup.entryExteriorMedium
  have h_p_sine :
      Real.sin setup.pIncidenceAngleRadians =
        setup.refractiveIndex setup.pExteriorMedium /
          setup.refractiveIndex .diamond := by
    unfold SatisfiesSnellLawAtP at h_snell_p
    rw [h_tangent_at_p, Real.sin_pi_div_two, mul_one] at h_snell_p
    apply (eq_div_iff (ne_of_gt h_diamond_pos)).2
    simpa [mul_comm] using h_snell_p
  have h_p_is_critical :
      criticalAngleAtPRadians setup = setup.pIncidenceAngleRadians := by
    unfold criticalAngleAtPRadians
    rw [← h_p_sine]
    exact Real.arcsin_sin (by
      nlinarith [h_p_incidence_range.1, Real.pi_pos]) h_p_incidence_range.2
  have h_entry_refraction :
      setup.entryRefractionAngleRadians =
        setup.pFacetAngleToHorizontalRadians -
          criticalAngleAtPRadians setup := by
    rw [h_p_is_critical]
    linarith
  have h_rotation_sine :
      Real.sin setup.rotationAngleRadians =
        setup.refractiveIndex .diamond /
            setup.refractiveIndex setup.entryExteriorMedium *
          Real.sin
            (setup.pFacetAngleToHorizontalRadians -
              criticalAngleAtPRadians setup) := by
    rw [← h_entry_refraction]
    unfold SatisfiesSnellLawAtEntry at h_snell_entry
    rw [h_entry_geometry] at h_snell_entry
    field_simp [ne_of_gt h_entry_medium_pos]
    simpa [mul_comm] using h_snell_entry
  unfold requiredRotationRadians
  rw [← h_rotation_sine]
  exact (Real.arcsin_sin (by
    nlinarith [h_rotation_range.1, Real.pi_pos]) h_rotation_range.2).symm

/-- The four displayed answer labels. -/
inductive AnswerChoice where
  | A
  | B
  | C
  | D
  deriving DecidableEq, Repr

/-- Rotation angle printed beside each answer choice, in degrees. -/
def AnswerChoice.rotationDegrees : AnswerChoice → ℝ
  | .A => 1.90
  | .B => 4.12
  | .C => 2.83
  | .D => 3.07

/-- A displayed answer is correct when it is at least as close to the
physically calculated rotation as every other displayed answer. -/
def IsClosestDisplayedAnswer
    (rotationAngleRadians : ℝ) (choice : AnswerChoice) : Prop :=
  ∀ other : AnswerChoice,
    |radiansToDegrees rotationAngleRadians - choice.rotationDegrees| ≤
      |radiansToDegrees rotationAngleRadians - other.rotationDegrees|

/-- For the stated figure and material readouts, Snell's law and first critical
transmission at `P` select answer C, whose displayed rotation is `2.83°`.

Blueprint: `thm:physics:phyx_mini_0011:target`. -/
theorem rotation_angle_matches_choice_C
    (setup : DiamondRotationSetup)
    (h_indices_positive : HasPositiveRefractiveIndices setup)
    (h_material : HasMaterialReadouts setup)
    (h_ranges : HasPhysicalAngleRanges setup)
    (h_figure : HasFigureReadouts setup)
    (h_geometry : HasRotatedRayGeometry setup)
    (h_snell_entry : SatisfiesSnellLawAtEntry setup)
    (h_snell_p : SatisfiesSnellLawAtP setup)
    (h_first_exit : IsAtFirstExitThresholdAtP setup) :
    IsClosestDisplayedAnswer setup.rotationAngleRadians .C := by
  have _h_indices_are_positive : HasPositiveRefractiveIndices setup :=
    h_indices_positive
  rcases h_ranges with
    ⟨h_rotation_range, _h_entry_incidence_range, h_entry_refraction_range,
      h_p_incidence_range, _h_p_transmission_range⟩
  rcases h_material with ⟨h_water_index, h_diamond_index⟩
  rcases h_figure with
    ⟨_h_axis_point, _h_axis_orientation, _h_vertical_ray, _h_horizontal_entry,
      h_entry_water, h_p_water, _h_exit_point, h_p_facet⟩
  rcases h_geometry with ⟨h_entry_geometry, h_p_geometry⟩
  rcases h_first_exit with
    ⟨_h_first_exit_at_p, _h_inside_before_p, h_tangent_at_p⟩
  have h_p_sine :
      Real.sin setup.pIncidenceAngleRadians = (200 : ℝ) / 363 := by
    unfold SatisfiesSnellLawAtP at h_snell_p
    rw [h_p_water, h_tangent_at_p, h_water_index, h_diamond_index,
      Real.sin_pi_div_two, mul_one] at h_snell_p
    norm_num at h_snell_p ⊢
    linarith
  have h_rotation_sine :
      Real.sin setup.rotationAngleRadians =
        (363 : ℝ) / 200 * Real.sin setup.entryRefractionAngleRadians := by
    unfold SatisfiesSnellLawAtEntry at h_snell_entry
    rw [h_entry_water, h_water_index, h_diamond_index, h_entry_geometry] at h_snell_entry
    norm_num at h_snell_entry ⊢
    linarith
  have hr2_sq : (Real.sqrt 2) ^ 2 = (2 : ℝ) :=
    Real.sq_sqrt (by norm_num)
  have hr2_nonneg : 0 ≤ Real.sqrt 2 := Real.sqrt_nonneg _
  have hr2_lower : (1.4142 : ℝ) < Real.sqrt 2 := by
    nlinarith only [hr2_sq, hr2_nonneg]
  have hr2_upper : Real.sqrt 2 < (1.4143 : ℝ) := by
    nlinarith only [hr2_sq, hr2_nonneg]
  have hr3_arg : 0 ≤ (2 : ℝ) + Real.sqrt 2 := by positivity
  have hr3_sq : (Real.sqrt (2 + Real.sqrt 2)) ^ 2 = 2 + Real.sqrt 2 :=
    Real.sq_sqrt hr3_arg
  have hr3_nonneg : 0 ≤ Real.sqrt (2 + Real.sqrt 2) := Real.sqrt_nonneg _
  have hr3_lower : (1.8477 : ℝ) < Real.sqrt (2 + Real.sqrt 2) := by
    nlinarith only [hr2_lower, hr3_sq, hr3_nonneg]
  have hr3_upper : Real.sqrt (2 + Real.sqrt 2) < (1.8478 : ℝ) := by
    nlinarith only [hr2_upper, hr3_sq, hr3_nonneg]
  have hs_arg :
      0 ≤ (2 : ℝ) - Real.sqrt (2 + Real.sqrt 2) := by
    linarith only [hr3_upper]
  have hs_sq :
      (Real.sqrt (2 - Real.sqrt (2 + Real.sqrt 2))) ^ 2 =
        2 - Real.sqrt (2 + Real.sqrt 2) :=
    Real.sq_sqrt hs_arg
  have hs_nonneg :
      0 ≤ Real.sqrt (2 - Real.sqrt (2 + Real.sqrt 2)) :=
    Real.sqrt_nonneg _
  have hs_lower :
      (0.3901 : ℝ) < Real.sqrt (2 - Real.sqrt (2 + Real.sqrt 2)) := by
    nlinarith only [hr3_upper, hs_sq, hs_nonneg]
  have hs_upper :
      Real.sqrt (2 - Real.sqrt (2 + Real.sqrt 2)) <
        (0.3903 : ℝ) := by
    nlinarith only [hr3_lower, hs_sq, hs_nonneg]
  have hsin_pi16_lower : (0.19505 : ℝ) < Real.sin (Real.pi / 16) := by
    rw [Real.sin_pi_div_sixteen]
    linarith
  have hsin_pi16_upper : Real.sin (Real.pi / 16) < (0.19515 : ℝ) := by
    rw [Real.sin_pi_div_sixteen]
    linarith
  have hpi16_nonneg : 0 ≤ Real.pi / 16 := by positivity
  have hpi16_le_quarter : Real.pi / 16 ≤ (1 / 4 : ℝ) := by
    nlinarith only [Real.pi_le_four]
  have hpi16_abs : |Real.pi / 16| ≤ 1 := by
    rw [abs_of_nonneg hpi16_nonneg]
    linarith
  have hsin_pi16_approx := Real.sin_bound hpi16_abs
  have hsin_pi16_approx_lower := (abs_le.mp hsin_pi16_approx).1
  have hsin_pi16_approx_upper := (abs_le.mp hsin_pi16_approx).2
  rw [abs_of_nonneg hpi16_nonneg] at hsin_pi16_approx_lower hsin_pi16_approx_upper
  have hpi_gt_three : (3 : ℝ) < Real.pi := by
    by_contra h
    have hpi_le : Real.pi ≤ (3 : ℝ) := le_of_not_gt h
    have hx_le : Real.pi / 16 ≤ (3 : ℝ) / 16 := by linarith only [hpi_le]
    have hx_fourth_le :
        (Real.pi / 16) ^ 4 ≤ ((3 : ℝ) / 16) ^ 4 :=
      pow_le_pow_left₀ hpi16_nonneg hx_le 4
    have hx_cube_nonneg : 0 ≤ (Real.pi / 16) ^ 3 :=
      pow_nonneg hpi16_nonneg 3
    nlinarith only [hsin_pi16_lower, hsin_pi16_approx_upper,
      hpi16_nonneg, hx_le, hx_cube_nonneg, hx_fourth_le]
  have hpi_lower : (3.135 : ℝ) < Real.pi := by
    by_contra h
    have hpi_le : Real.pi ≤ (3.135 : ℝ) := le_of_not_gt h
    have hx_lower : (3 : ℝ) / 16 ≤ Real.pi / 16 := by
      linarith only [hpi_gt_three]
    have hx_upper : Real.pi / 16 ≤ (49 : ℝ) / 250 := by
      linarith only [hpi_le]
    have hx_cube_lower :
        ((3 : ℝ) / 16) ^ 3 ≤ (Real.pi / 16) ^ 3 :=
      pow_le_pow_left₀ (by norm_num) hx_lower 3
    have hx_fourth_upper :
        (Real.pi / 16) ^ 4 ≤ ((49 : ℝ) / 250) ^ 4 :=
      pow_le_pow_left₀ hpi16_nonneg hx_upper 4
    nlinarith only [hsin_pi16_lower, hsin_pi16_approx_upper, hpi_le,
      hx_cube_lower, hx_fourth_upper]
  have hpi_lt_coarse : Real.pi < (3.2 : ℝ) := by
    by_contra h
    have hpi_ge : (3.2 : ℝ) ≤ Real.pi := le_of_not_gt h
    have hx_lower : (1 : ℝ) / 5 ≤ Real.pi / 16 := by
      linarith only [hpi_ge]
    have hx_cube_upper :
        (Real.pi / 16) ^ 3 ≤ ((1 : ℝ) / 4) ^ 3 :=
      pow_le_pow_left₀ hpi16_nonneg hpi16_le_quarter 3
    have hx_fourth_upper :
        (Real.pi / 16) ^ 4 ≤ ((1 : ℝ) / 4) ^ 4 :=
      pow_le_pow_left₀ hpi16_nonneg hpi16_le_quarter 4
    nlinarith only [hsin_pi16_upper, hsin_pi16_approx_lower, hx_lower,
      hx_cube_upper, hx_fourth_upper]
  have hpi_upper : Real.pi < (3.148 : ℝ) := by
    by_contra h
    have hpi_ge : (3.148 : ℝ) ≤ Real.pi := le_of_not_gt h
    have hx_lower : (787 : ℝ) / 4000 ≤ Real.pi / 16 := by
      linarith only [hpi_ge]
    have hx_upper : Real.pi / 16 ≤ (1 : ℝ) / 5 := by
      linarith only [hpi_lt_coarse]
    have hx_cube_upper :
        (Real.pi / 16) ^ 3 ≤ ((1 : ℝ) / 5) ^ 3 :=
      pow_le_pow_left₀ hpi16_nonneg hx_upper 3
    have hx_fourth_upper :
        (Real.pi / 16) ^ 4 ≤ ((1 : ℝ) / 5) ^ 4 :=
      pow_le_pow_left₀ hpi16_nonneg hx_upper 4
    nlinarith only [hsin_pi16_upper, hsin_pi16_approx_lower, hx_lower,
      hx_cube_upper, hx_fourth_upper]
  have hsqrt3_sq : (Real.sqrt 3) ^ 2 = (3 : ℝ) :=
    Real.sq_sqrt (by norm_num)
  have hsqrt3_nonneg : 0 ≤ Real.sqrt 3 := Real.sqrt_nonneg _
  have hsqrt3_lower : (1732 : ℝ) / 1000 < Real.sqrt 3 := by
    nlinarith only [hsqrt3_sq, hsqrt3_nonneg]
  have hsqrt3_upper : Real.sqrt 3 < (1733 : ℝ) / 1000 := by
    nlinarith only [hsqrt3_sq, hsqrt3_nonneg]
  let deltaLower : ℝ := 17 * Real.pi / 900
  have hdeltaLower_pos : 0 < deltaLower := by
    dsimp [deltaLower]
    positivity
  have hdeltaLower_lower : (59 : ℝ) / 1000 < deltaLower := by
    dsimp [deltaLower]
    nlinarith only [hpi_lower]
  have hdeltaLower_upper : deltaLower < (119 : ℝ) / 2000 := by
    dsimp [deltaLower]
    nlinarith only [hpi_upper]
  have hdeltaLower_abs : |deltaLower| ≤ 1 := by
    rw [abs_of_pos hdeltaLower_pos]
    linarith only [hdeltaLower_upper]
  have hsin_deltaLower := Real.sin_bound hdeltaLower_abs
  have hcos_deltaLower := Real.cos_bound hdeltaLower_abs
  have hsin_deltaLower_upper := (abs_le.mp hsin_deltaLower).2
  have hcos_deltaLower_upper := (abs_le.mp hcos_deltaLower).2
  rw [abs_of_pos hdeltaLower_pos] at hsin_deltaLower_upper hcos_deltaLower_upper
  have hdeltaLower_le_one : deltaLower ≤ 1 := by
    linarith only [hdeltaLower_upper]
  have hdeltaLower_fourth_le_cube :
      deltaLower ^ 4 ≤ deltaLower ^ 3 := by
    calc
      deltaLower ^ 4 = deltaLower ^ 3 * deltaLower := by ring
      _ ≤ deltaLower ^ 3 * 1 :=
        mul_le_mul_of_nonneg_left hdeltaLower_le_one
          (pow_nonneg hdeltaLower_pos.le 3)
      _ = deltaLower ^ 3 := by ring
  have hsin_deltaLower_le :
      Real.sin deltaLower ≤ deltaLower := by
    have hcube_nonneg : 0 ≤ deltaLower ^ 3 :=
      pow_nonneg hdeltaLower_pos.le 3
    nlinarith only [hsin_deltaLower_upper, hdeltaLower_fourth_le_cube,
      hcube_nonneg]
  have hsin_deltaLower_pos : 0 < Real.sin deltaLower :=
    Real.sin_pos_of_pos_of_lt_pi hdeltaLower_pos (by
      linarith only [hdeltaLower_upper, hpi_lower])
  have hsqrt3_sin_deltaLower_le :
      Real.sqrt 3 * Real.sin deltaLower ≤
        (1733 : ℝ) / 1000 * deltaLower := by
    calc
      Real.sqrt 3 * Real.sin deltaLower ≤
          ((1733 : ℝ) / 1000) * Real.sin deltaLower :=
        mul_le_mul_of_nonneg_right hsqrt3_upper.le hsin_deltaLower_pos.le
      _ ≤ (1733 : ℝ) / 1000 * deltaLower :=
        mul_le_mul_of_nonneg_left hsin_deltaLower_le (by norm_num)
  have hdeltaLower_sq_lower :
      ((59 : ℝ) / 1000) ^ 2 < deltaLower ^ 2 := by
    nlinarith only [hdeltaLower_lower, hdeltaLower_pos]
  have hdeltaLower_fourth_upper :
      deltaLower ^ 4 ≤ ((119 : ℝ) / 2000) ^ 4 :=
    pow_le_pow_left₀ hdeltaLower_pos.le hdeltaLower_upper.le 4
  have hsin_334_lower_than_critical :
      Real.sin (167 * Real.pi / 900) < (200 : ℝ) / 363 := by
    have hangle :
        167 * Real.pi / 900 = Real.pi / 6 + deltaLower := by
      dsimp [deltaLower]
      ring
    rw [hangle, Real.sin_add, Real.sin_pi_div_six, Real.cos_pi_div_six]
    nlinarith only [hcos_deltaLower_upper, hsqrt3_sin_deltaLower_le,
      hdeltaLower_sq_lower, hdeltaLower_fourth_upper]
  have h_p_incidence_principal :
      setup.pIncidenceAngleRadians ∈
        Set.Icc (-(Real.pi / 2)) (Real.pi / 2) :=
    ⟨by nlinarith only [h_p_incidence_range.1, Real.pi_pos],
      h_p_incidence_range.2⟩
  have hangle334_principal :
      167 * Real.pi / 900 ∈
        Set.Icc (-(Real.pi / 2)) (Real.pi / 2) := by
    constructor <;> nlinarith only [Real.pi_pos]
  have h_p_incidence_lower :
      167 * Real.pi / 900 < setup.pIncidenceAngleRadians := by
    by_contra h
    have hle :
        setup.pIncidenceAngleRadians ≤ 167 * Real.pi / 900 :=
      le_of_not_gt h
    have hsine_le :=
      Real.strictMonoOn_sin.monotoneOn
        h_p_incidence_principal hangle334_principal hle
    rw [h_p_sine] at hsine_le
    linarith only [hsine_le, hsin_334_lower_than_critical]
  let deltaUpper : ℝ := 7 * Real.pi / 360
  have hdeltaUpper_pos : 0 < deltaUpper := by
    dsimp [deltaUpper]
    positivity
  have hdeltaUpper_lower : (609 : ℝ) / 10000 < deltaUpper := by
    dsimp [deltaUpper]
    nlinarith only [hpi_lower]
  have hdeltaUpper_upper : deltaUpper < (613 : ℝ) / 10000 := by
    dsimp [deltaUpper]
    nlinarith only [hpi_upper]
  have hdeltaUpper_abs : |deltaUpper| ≤ 1 := by
    rw [abs_of_pos hdeltaUpper_pos]
    linarith only [hdeltaUpper_upper]
  have hsin_deltaUpper := Real.sin_bound hdeltaUpper_abs
  have hcos_deltaUpper := Real.cos_bound hdeltaUpper_abs
  have hsin_deltaUpper_lower := (abs_le.mp hsin_deltaUpper).1
  have hcos_deltaUpper_lower := (abs_le.mp hcos_deltaUpper).1
  rw [abs_of_pos hdeltaUpper_pos] at hsin_deltaUpper_lower hcos_deltaUpper_lower
  have hsin_deltaUpper_pos : 0 < Real.sin deltaUpper :=
    Real.sin_pos_of_pos_of_lt_pi hdeltaUpper_pos (by
      linarith only [hdeltaUpper_upper, hpi_lower])
  have hsqrt3_sin_deltaUpper_lower :
      (1732 : ℝ) / 1000 *
          (deltaUpper - deltaUpper ^ 3 / 6 -
            deltaUpper ^ 4 * (5 / 96)) ≤
        Real.sqrt 3 * Real.sin deltaUpper := by
    calc
      (1732 : ℝ) / 1000 *
            (deltaUpper - deltaUpper ^ 3 / 6 -
              deltaUpper ^ 4 * (5 / 96)) ≤
          (1732 : ℝ) / 1000 * Real.sin deltaUpper :=
        mul_le_mul_of_nonneg_left (by
          linarith only [hsin_deltaUpper_lower]) (by norm_num)
      _ ≤ Real.sqrt 3 * Real.sin deltaUpper :=
        mul_le_mul_of_nonneg_right hsqrt3_lower.le hsin_deltaUpper_pos.le
  have hdeltaUpper_sq_upper :
      deltaUpper ^ 2 ≤ ((613 : ℝ) / 10000) ^ 2 :=
    pow_le_pow_left₀ hdeltaUpper_pos.le hdeltaUpper_upper.le 2
  have hdeltaUpper_cube_upper :
      deltaUpper ^ 3 ≤ ((613 : ℝ) / 10000) ^ 3 :=
    pow_le_pow_left₀ hdeltaUpper_pos.le hdeltaUpper_upper.le 3
  have hdeltaUpper_fourth_upper :
      deltaUpper ^ 4 ≤ ((613 : ℝ) / 10000) ^ 4 :=
    pow_le_pow_left₀ hdeltaUpper_pos.le hdeltaUpper_upper.le 4
  have hsin_335_above_critical :
      (200 : ℝ) / 363 < Real.sin (67 * Real.pi / 360) := by
    have hangle :
        67 * Real.pi / 360 = Real.pi / 6 + deltaUpper := by
      dsimp [deltaUpper]
      ring
    rw [hangle, Real.sin_add, Real.sin_pi_div_six, Real.cos_pi_div_six]
    nlinarith only [hcos_deltaUpper_lower,
      hsqrt3_sin_deltaUpper_lower, hdeltaUpper_lower,
      hdeltaUpper_sq_upper, hdeltaUpper_cube_upper,
      hdeltaUpper_fourth_upper]
  have hangle335_principal :
      67 * Real.pi / 360 ∈
        Set.Icc (-(Real.pi / 2)) (Real.pi / 2) := by
    constructor <;> nlinarith only [Real.pi_pos]
  have h_p_incidence_upper :
      setup.pIncidenceAngleRadians < 67 * Real.pi / 360 := by
    by_contra h
    have hle :
        67 * Real.pi / 360 ≤ setup.pIncidenceAngleRadians :=
      le_of_not_gt h
    have hsine_le :=
      Real.strictMonoOn_sin.monotoneOn
        hangle335_principal h_p_incidence_principal hle
    rw [h_p_sine] at hsine_le
    linarith only [hsine_le, hsin_335_above_critical]
  have h_entry_refraction_lower :
      Real.pi / 120 < setup.entryRefractionAngleRadians := by
    rw [h_p_facet] at h_p_geometry
    unfold degreesToRadians at h_p_geometry
    linarith only [h_p_geometry, h_p_incidence_upper]
  have h_entry_refraction_upper :
      setup.entryRefractionAngleRadians < 2 * Real.pi / 225 := by
    rw [h_p_facet] at h_p_geometry
    unfold degreesToRadians at h_p_geometry
    linarith only [h_p_geometry, h_p_incidence_lower]
  have h_entry_refraction_principal :
      setup.entryRefractionAngleRadians ∈
        Set.Icc (-(Real.pi / 2)) (Real.pi / 2) :=
    ⟨by nlinarith only [h_entry_refraction_range.1, Real.pi_pos],
      h_entry_refraction_range.2⟩
  have hpi120_principal :
      Real.pi / 120 ∈ Set.Icc (-(Real.pi / 2)) (Real.pi / 2) := by
    constructor <;> nlinarith only [Real.pi_pos]
  have hsin_refraction_lower :
      Real.sin (Real.pi / 120) <
        Real.sin setup.entryRefractionAngleRadians :=
    Real.strictMonoOn_sin hpi120_principal h_entry_refraction_principal
      h_entry_refraction_lower
  have hpi120_pos : 0 < Real.pi / 120 := by positivity
  have hpi120_lower : (13 : ℝ) / 500 < Real.pi / 120 := by
    nlinarith only [hpi_lower]
  have hpi120_upper : Real.pi / 120 < (27 : ℝ) / 1000 := by
    nlinarith only [hpi_upper]
  have hpi120_abs : |Real.pi / 120| ≤ 1 := by
    rw [abs_of_pos hpi120_pos]
    linarith only [hpi120_upper]
  have hsin_pi120_bound := Real.sin_bound hpi120_abs
  have hsin_pi120_bound_lower := (abs_le.mp hsin_pi120_bound).1
  rw [abs_of_pos hpi120_pos] at hsin_pi120_bound_lower
  have hpi120_cube_upper :
      (Real.pi / 120) ^ 3 ≤ ((27 : ℝ) / 1000) ^ 3 :=
    pow_le_pow_left₀ hpi120_pos.le hpi120_upper.le 3
  have hpi120_fourth_upper :
      (Real.pi / 120) ^ 4 ≤ ((27 : ℝ) / 1000) ^ 4 :=
    pow_le_pow_left₀ hpi120_pos.le hpi120_upper.le 4
  have hsin_pi120_lower :
      (1 : ℝ) / 40 < Real.sin (Real.pi / 120) := by
    nlinarith only [hsin_pi120_bound_lower, hpi120_lower,
      hpi120_cube_upper, hpi120_fourth_upper]
  let lowerChoiceMidpointRadians : ℝ := 473 * Real.pi / 36000
  have hlowerChoice_pos : 0 < lowerChoiceMidpointRadians := by
    dsimp [lowerChoiceMidpointRadians]
    positivity
  have hlowerChoice_upper :
      lowerChoiceMidpointRadians < (21 : ℝ) / 500 := by
    dsimp [lowerChoiceMidpointRadians]
    nlinarith only [hpi_upper]
  have hlowerChoice_abs : |lowerChoiceMidpointRadians| ≤ 1 := by
    rw [abs_of_pos hlowerChoice_pos]
    linarith only [hlowerChoice_upper]
  have hsin_lowerChoice_bound := Real.sin_bound hlowerChoice_abs
  have hsin_lowerChoice_bound_upper :=
    (abs_le.mp hsin_lowerChoice_bound).2
  rw [abs_of_pos hlowerChoice_pos] at hsin_lowerChoice_bound_upper
  have hlowerChoice_le_one : lowerChoiceMidpointRadians ≤ 1 := by
    linarith only [hlowerChoice_upper]
  have hlowerChoice_fourth_le_cube :
      lowerChoiceMidpointRadians ^ 4 ≤
        lowerChoiceMidpointRadians ^ 3 := by
    calc
      lowerChoiceMidpointRadians ^ 4 =
          lowerChoiceMidpointRadians ^ 3 * lowerChoiceMidpointRadians := by
        ring
      _ ≤ lowerChoiceMidpointRadians ^ 3 * 1 :=
        mul_le_mul_of_nonneg_left hlowerChoice_le_one
          (pow_nonneg hlowerChoice_pos.le 3)
      _ = lowerChoiceMidpointRadians ^ 3 := by ring
  have hsin_lowerChoice_le :
      Real.sin lowerChoiceMidpointRadians ≤ lowerChoiceMidpointRadians := by
    have hcube_nonneg : 0 ≤ lowerChoiceMidpointRadians ^ 3 :=
      pow_nonneg hlowerChoice_pos.le 3
    nlinarith only [hsin_lowerChoice_bound_upper,
      hlowerChoice_fourth_le_cube, hcube_nonneg]
  have hsin_lowerChoice_upper :
      Real.sin lowerChoiceMidpointRadians < (21 : ℝ) / 500 :=
    lt_of_le_of_lt hsin_lowerChoice_le hlowerChoice_upper
  have hsin_lowerChoice_lt_rotation :
      Real.sin lowerChoiceMidpointRadians <
        Real.sin setup.rotationAngleRadians := by
    nlinarith only [h_rotation_sine, hsin_refraction_lower,
      hsin_pi120_lower, hsin_lowerChoice_upper]
  have h_rotation_principal :
      setup.rotationAngleRadians ∈
        Set.Icc (-(Real.pi / 2)) (Real.pi / 2) :=
    ⟨by nlinarith only [h_rotation_range.1, Real.pi_pos],
      h_rotation_range.2⟩
  have hlowerChoice_principal :
      lowerChoiceMidpointRadians ∈
        Set.Icc (-(Real.pi / 2)) (Real.pi / 2) := by
    dsimp [lowerChoiceMidpointRadians]
    constructor <;> nlinarith only [Real.pi_pos]
  have h_rotation_lower :
      lowerChoiceMidpointRadians < setup.rotationAngleRadians := by
    by_contra h
    have hle :
        setup.rotationAngleRadians ≤ lowerChoiceMidpointRadians :=
      le_of_not_gt h
    have hsine_le :=
      Real.strictMonoOn_sin.monotoneOn
        h_rotation_principal hlowerChoice_principal hle
    linarith only [hsine_le, hsin_lowerChoice_lt_rotation]
  have h2pi225_principal :
      2 * Real.pi / 225 ∈
        Set.Icc (-(Real.pi / 2)) (Real.pi / 2) := by
    constructor <;> nlinarith only [Real.pi_pos]
  have hsin_refraction_upper :
      Real.sin setup.entryRefractionAngleRadians <
        Real.sin (2 * Real.pi / 225) :=
    Real.strictMonoOn_sin h_entry_refraction_principal h2pi225_principal
      h_entry_refraction_upper
  have h2pi225_pos : 0 < 2 * Real.pi / 225 := by positivity
  have h2pi225_upper : 2 * Real.pi / 225 < (7 : ℝ) / 250 := by
    nlinarith only [hpi_upper]
  have h2pi225_abs : |2 * Real.pi / 225| ≤ 1 := by
    rw [abs_of_pos h2pi225_pos]
    linarith only [h2pi225_upper]
  have hsin_2pi225_bound := Real.sin_bound h2pi225_abs
  have hsin_2pi225_bound_upper := (abs_le.mp hsin_2pi225_bound).2
  rw [abs_of_pos h2pi225_pos] at hsin_2pi225_bound_upper
  have h2pi225_le_one : 2 * Real.pi / 225 ≤ 1 := by
    linarith only [h2pi225_upper]
  have h2pi225_fourth_le_cube :
      (2 * Real.pi / 225) ^ 4 ≤ (2 * Real.pi / 225) ^ 3 := by
    calc
      (2 * Real.pi / 225) ^ 4 =
          (2 * Real.pi / 225) ^ 3 * (2 * Real.pi / 225) := by ring
      _ ≤ (2 * Real.pi / 225) ^ 3 * 1 :=
        mul_le_mul_of_nonneg_left h2pi225_le_one
          (pow_nonneg h2pi225_pos.le 3)
      _ = (2 * Real.pi / 225) ^ 3 := by ring
  have hsin_2pi225_le :
      Real.sin (2 * Real.pi / 225) ≤ 2 * Real.pi / 225 := by
    have hcube_nonneg : 0 ≤ (2 * Real.pi / 225) ^ 3 :=
      pow_nonneg h2pi225_pos.le 3
    nlinarith only [hsin_2pi225_bound_upper,
      h2pi225_fourth_le_cube, hcube_nonneg]
  have hsin_2pi225_upper :
      Real.sin (2 * Real.pi / 225) < (7 : ℝ) / 250 :=
    lt_of_le_of_lt hsin_2pi225_le h2pi225_upper
  let upperChoiceMidpointRadians : ℝ := 59 * Real.pi / 3600
  have hupperChoice_pos : 0 < upperChoiceMidpointRadians := by
    dsimp [upperChoiceMidpointRadians]
    positivity
  have hupperChoice_lower :
      (513 : ℝ) / 10000 < upperChoiceMidpointRadians := by
    dsimp [upperChoiceMidpointRadians]
    nlinarith only [hpi_lower]
  have hupperChoice_upper :
      upperChoiceMidpointRadians < (52 : ℝ) / 1000 := by
    dsimp [upperChoiceMidpointRadians]
    nlinarith only [hpi_upper]
  have hupperChoice_abs : |upperChoiceMidpointRadians| ≤ 1 := by
    rw [abs_of_pos hupperChoice_pos]
    linarith only [hupperChoice_upper]
  have hsin_upperChoice_bound := Real.sin_bound hupperChoice_abs
  have hsin_upperChoice_bound_lower :=
    (abs_le.mp hsin_upperChoice_bound).1
  rw [abs_of_pos hupperChoice_pos] at hsin_upperChoice_bound_lower
  have hupperChoice_cube_upper :
      upperChoiceMidpointRadians ^ 3 ≤ ((52 : ℝ) / 1000) ^ 3 :=
    pow_le_pow_left₀ hupperChoice_pos.le hupperChoice_upper.le 3
  have hupperChoice_fourth_upper :
      upperChoiceMidpointRadians ^ 4 ≤ ((52 : ℝ) / 1000) ^ 4 :=
    pow_le_pow_left₀ hupperChoice_pos.le hupperChoice_upper.le 4
  have hsin_upperChoice_lower :
      (51 : ℝ) / 1000 < Real.sin upperChoiceMidpointRadians := by
    nlinarith only [hsin_upperChoice_bound_lower, hupperChoice_lower,
      hupperChoice_cube_upper, hupperChoice_fourth_upper]
  have hsin_rotation_lt_upperChoice :
      Real.sin setup.rotationAngleRadians <
        Real.sin upperChoiceMidpointRadians := by
    nlinarith only [h_rotation_sine, hsin_refraction_upper,
      hsin_2pi225_upper, hsin_upperChoice_lower]
  have hupperChoice_principal :
      upperChoiceMidpointRadians ∈
        Set.Icc (-(Real.pi / 2)) (Real.pi / 2) := by
    dsimp [upperChoiceMidpointRadians]
    constructor <;> nlinarith only [Real.pi_pos]
  have h_rotation_upper :
      setup.rotationAngleRadians < upperChoiceMidpointRadians := by
    by_contra h
    have hle :
        upperChoiceMidpointRadians ≤ setup.rotationAngleRadians :=
      le_of_not_gt h
    have hsine_le :=
      Real.strictMonoOn_sin.monotoneOn
        hupperChoice_principal h_rotation_principal hle
    linarith only [hsine_le, hsin_rotation_lt_upperChoice]
  have h_degree_lower :
      (2.365 : ℝ) <
        radiansToDegrees setup.rotationAngleRadians := by
    unfold radiansToDegrees
    apply (lt_div_iff₀ Real.pi_pos).2
    dsimp [lowerChoiceMidpointRadians] at h_rotation_lower
    nlinarith only [h_rotation_lower]
  have h_degree_upper :
      radiansToDegrees setup.rotationAngleRadians < (2.95 : ℝ) := by
    unfold radiansToDegrees
    apply (div_lt_iff₀ Real.pi_pos).2
    dsimp [upperChoiceMidpointRadians] at h_rotation_upper
    nlinarith only [h_rotation_upper]
  unfold IsClosestDisplayedAnswer
  intro other
  cases other <;> simp only [AnswerChoice.rotationDegrees]
  · apply sq_le_sq.mp
    nlinarith only [h_degree_lower]
  · apply sq_le_sq.mp
    nlinarith only [h_degree_upper]
  · exact le_rfl
  · apply sq_le_sq.mp
    nlinarith only [h_degree_upper]

end

end PhyXMiniProblems.ProblemPhyXMini0011
