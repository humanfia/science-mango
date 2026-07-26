import Mathlib.Algebra.Order.Round
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Angle
import Physlib.Units.WithDim.Basic

noncomputable section

namespace PhyXMiniProblems.ProblemPhyXMini0080

open Dimension

/-!
# Unit-cell size from first-order x-ray reflection

The primary figure shows a square cross-section of the crystal.  Its horizontal
and vertical nearest-neighbour spacings are both labeled `a₀`; the reflecting
planes run diagonally at `45°` to the top face.  The incident x-ray makes the
given `63.8°` angle with that top face, so its Bragg glancing angle with the
shown planes is `63.8° - 45° = 18.8°`.

Lengths are Physlib dimensionful quantities.  Real scalars occur only as
readouts in a specified length unit or as dimensionless angle data.
-/

/-- A signed physical length whose representations cohere across unit choices. -/
abbrev LengthQuantity : Type := Dimensionful (WithDim L𝓭 ℝ)

/-- Read a physical length as a real scalar in the selected length unit. -/
def lengthValueIn (unit : LengthUnit) (length : LengthQuantity) : ℝ :=
  (length ({ UnitChoices.SI with length := unit } : UnitChoices)).val

/-- The numerical readout of a physical length in nanometres. -/
def nanometersValue (length : LengthQuantity) : ℝ :=
  lengthValueIn LengthUnit.nanometers length

/-- Interpret a scalar angle given in degrees as a Mathlib real angle. -/
def degreesAsAngle (degrees : ℝ) : Real.Angle :=
  ((degrees * Real.pi / 180 : ℝ) : Real.Angle)

/-- The two `a₀` arrows drawn in the square lattice cross-section. -/
inductive UnitCellEdgeLabel where
  | horizontalA0
  | verticalA0
  deriving DecidableEq, Repr

/-- The family of parallel diagonal reflection planes explicitly shown. -/
inductive ReflectionPlaneFamily where
  | shownDiagonal
  deriving DecidableEq, Repr

/-- The monochromatic incident x-ray beam. -/
structure XRayBeam where
  /-- Vacuum wavelength `λ` of the beam. -/
  wavelength : LengthQuantity

/-- Crystal lengths relevant to the depicted square lattice cross-section. -/
structure SquareLatticeCrystal where
  /-- The unknown common horizontal and vertical unit-cell size `a₀`. -/
  unitCellSize : LengthQuantity
  /-- Perpendicular spacing `d` between adjacent shown diagonal planes. -/
  shownPlaneSpacing : LengthQuantity

/-- Geometric quantities and labels read from the primary figure. -/
structure XRayDiffractionFigure where
  /-- Physical lengths attached to the two arrows labeled `a₀`. -/
  labeledCellEdge : UnitCellEdgeLabel → LengthQuantity
  /-- The particular family of parallel lines used as reflection planes. -/
  planeFamily : ReflectionPlaneFamily
  /-- Inclination of the shown reflection planes from the horizontal top face. -/
  planeAngleFromTopFace : Real.Angle
  /-- Inclination of the incident red x-ray from the horizontal top face. -/
  incidentRayAngleFromTopFace : Real.Angle

/-- The observed reflected order and the two angles used in Bragg's law. -/
structure ReflectionObservation where
  /-- Positive diffraction order `n`; the problem states first order. -/
  order : ℕ
  /-- The problem's angle `θ`, measured from the top face. -/
  incidenceAngleFromTopFace : Real.Angle
  /-- Glancing angle between the incident ray and the diagonal reflecting planes. -/
  braggGlancingAngle : Real.Angle

/-- Complete physical setup for the x-ray reflection observation. -/
structure XRayCrystalSetup where
  beam : XRayBeam
  crystal : SquareLatticeCrystal
  figure : XRayDiffractionFigure
  observation : ReflectionObservation

/-
The supplied numerical data.  This includes the wavelength, first-order
observation, and the printed angle, but no readout of the requested `a₀`.
-/
structure HasStatedReadouts (setup : XRayCrystalSetup) : Prop where
  wavelength_nanometers : nanometersValue setup.beam.wavelength = 0.260
  first_order : setup.observation.order = 1
  incidence_angle :
    setup.observation.incidenceAngleFromTopFace = degreesAsAngle 63.8

/-
The geometry visible in the primary figure.  Both labeled arrows denote the
same unit-cell size, and the diagonal plane inclination converts the stated
top-face angle into the glancing angle required by Bragg's law.
-/
structure MatchesShownLatticeFigure (setup : XRayCrystalSetup) : Prop where
  shown_plane_family : setup.figure.planeFamily = .shownDiagonal
  horizontal_label_is_a0 :
    setup.figure.labeledCellEdge .horizontalA0 = setup.crystal.unitCellSize
  vertical_label_is_a0 :
    setup.figure.labeledCellEdge .verticalA0 = setup.crystal.unitCellSize
  ray_angle_matches_observation :
    setup.figure.incidentRayAngleFromTopFace =
      setup.observation.incidenceAngleFromTopFace
  diagonal_plane_inclination :
    setup.figure.planeAngleFromTopFace = degreesAsAngle 45
  glancing_angle_definition :
    setup.observation.braggGlancingAngle =
      setup.observation.incidenceAngleFromTopFace -
        setup.figure.planeAngleFromTopFace

/-
For diagonal planes joining opposite corners of square cells, the perpendicular
interplanar spacing is `d = a₀ / √2`.  The equation is required in every unit
choice and contains no numerical value for `a₀`.
-/
def SatisfiesDiagonalPlaneSpacingLaw (setup : XRayCrystalSetup) : Prop :=
  ∀ units : UnitChoices,
    Real.sqrt 2 * (setup.crystal.shownPlaneSpacing units).val =
      (setup.crystal.unitCellSize units).val

/-
Bragg's reflection law `n λ = 2 d sin φ`, where `φ` is the glancing angle with
the reflecting planes.  Requiring it in every unit choice makes the law
independent of the nanometre readout used in the question.
-/
def SatisfiesBraggReflectionLaw (setup : XRayCrystalSetup) : Prop :=
  ∀ units : UnitChoices,
    (setup.observation.order : ℝ) * (setup.beam.wavelength units).val =
      2 * (setup.crystal.shownPlaneSpacing units).val *
        Real.Angle.sin setup.observation.braggGlancingAngle

/-- Positivity and physical-branch conditions for the depicted observation. -/
structure HasPhysicalDiffractionParameters (setup : XRayCrystalSetup) : Prop where
  wavelength_positive : 0 < nanometersValue setup.beam.wavelength
  unit_cell_size_positive : 0 < nanometersValue setup.crystal.unitCellSize
  plane_spacing_positive : 0 < nanometersValue setup.crystal.shownPlaneSpacing
  glancing_sine_positive :
    0 < Real.Angle.sin setup.observation.braggGlancingAngle

/-- Labels of the four displayed multiple-choice answers. -/
inductive AnswerChoice where
  | A
  | B
  | C
  | D
  deriving DecidableEq, Repr

/-- Unit-cell sizes printed beside the answer choices, in nanometres. -/
def answerUnitCellSizeNanometers : AnswerChoice → ℝ
  | .A => 0.405
  | .B => 0.520
  | .C => 0.570
  | .D => 0.640

/-- A choice is strictly nearer to a length readout than every other choice. -/
def IsClosestAnswer (length : LengthQuantity) (choice : AnswerChoice) : Prop :=
  ∀ other, other ≠ choice →
    abs (nanometersValue length - answerUnitCellSizeNanometers choice) <
      abs (nanometersValue length - answerUnitCellSizeNanometers other)

/-
The top-face angle and the `45°` diagonal-plane inclination determine the
`18.8°` Bragg glancing angle.  This is a geometry consequence, not an assumed
answer for the unit-cell size.
-/
lemma bragg_glancing_angle_eq_eighteen_point_eight_degrees
    (setup : XRayCrystalSetup)
    (h_readouts : HasStatedReadouts setup)
    (h_figure : MatchesShownLatticeFigure setup) :
    setup.observation.braggGlancingAngle = degreesAsAngle 18.8 := by
  rw [h_figure.glancing_angle_definition, h_readouts.incidence_angle,
    h_figure.diagonal_plane_inclination]
  apply Quotient.sound
  use 0
  norm_num [degreesAsAngle]
  ring

/-
Combining first order, the diagonal-plane spacing relation, and Bragg's law
gives the exact formula used to calculate `a₀`.  No answer-choice value occurs
in this intermediate conclusion.
-/
lemma unit_cell_size_nanometers_formula
    (setup : XRayCrystalSetup)
    (h_readouts : HasStatedReadouts setup)
    (h_physical : HasPhysicalDiffractionParameters setup)
    (h_spacing : SatisfiesDiagonalPlaneSpacingLaw setup)
    (h_bragg : SatisfiesBraggReflectionLaw setup) :
    nanometersValue setup.crystal.unitCellSize =
      nanometersValue setup.beam.wavelength /
        (Real.sqrt 2 *
          Real.Angle.sin setup.observation.braggGlancingAngle) := by
  have h_spacing_nm := h_spacing
    ({ UnitChoices.SI with length := LengthUnit.nanometers } : UnitChoices)
  have h_bragg_nm := h_bragg
    ({ UnitChoices.SI with length := LengthUnit.nanometers } : UnitChoices)
  have h_sin_pos := h_physical.glancing_sine_positive
  unfold nanometersValue lengthValueIn
  rw [h_readouts.first_order] at h_bragg_nm
  norm_num at h_bragg_nm
  have h_sqrt_pos : 0 < Real.sqrt 2 := Real.sqrt_pos.2 (by norm_num)
  have h_sqrt_sq : (Real.sqrt 2) ^ 2 = 2 := Real.sq_sqrt (by norm_num)
  apply (eq_div_iff (mul_ne_zero h_sqrt_pos.ne' h_sin_pos.ne')).2
  simp only [UnitChoices.SI_time, UnitChoices.SI_mass,
    UnitChoices.SI_charge, UnitChoices.SI_temperature] at h_spacing_nm ⊢
  rw [← h_spacing_nm, h_bragg_nm]
  calc
    (Real.sqrt 2 *
        (setup.crystal.shownPlaneSpacing
          ({ UnitChoices.SI with length := LengthUnit.nanometers } : UnitChoices)).val) *
        (Real.sqrt 2 * Real.Angle.sin setup.observation.braggGlancingAngle) =
        (Real.sqrt 2) ^ 2 *
          (setup.crystal.shownPlaneSpacing
            ({ UnitChoices.SI with length := LengthUnit.nanometers } : UnitChoices)).val *
          Real.Angle.sin setup.observation.braggGlancingAngle := by ring
    _ = 2 *
          (setup.crystal.shownPlaneSpacing
            ({ UnitChoices.SI with length := LengthUnit.nanometers } : UnitChoices)).val *
          Real.Angle.sin setup.observation.braggGlancingAngle := by rw [h_sqrt_sq]

/-
With `λ = 0.260 nm` and `φ = 18.8°`, the inferred unit-cell size is about
`0.570485 nm`.  It therefore rounds to `0.570 nm` at the precision displayed
by the choices and is strictly closest to recorded answer C.

This formalizes blueprint label `thm:physics:phyx_mini_0080:target`.
-/
theorem problem_phyx_mini_0080
    (setup : XRayCrystalSetup)
    (h_readouts : HasStatedReadouts setup)
    (h_figure : MatchesShownLatticeFigure setup)
    (h_physical : HasPhysicalDiffractionParameters setup)
    (h_spacing : SatisfiesDiagonalPlaneSpacingLaw setup)
    (h_bragg : SatisfiesBraggReflectionLaw setup) :
    round (1000 * nanometersValue setup.crystal.unitCellSize) = 570 ∧
      IsClosestAnswer setup.crystal.unitCellSize .C := by
  have h_angle :=
    bragg_glancing_angle_eq_eighteen_point_eight_degrees
      setup h_readouts h_figure
  have h_formula :=
    unit_cell_size_nanometers_formula
      setup h_readouts h_physical h_spacing h_bragg
  have h_angle_real :
      degreesAsAngle 18.8 =
        ((47 * Real.pi / 450 : ℝ) : Real.Angle) := by
    unfold degreesAsAngle
    congr 1
    ring
  have h_exact :
      nanometersValue setup.crystal.unitCellSize =
        (13 / 50 : ℝ) /
          (Real.sqrt 2 * Real.sin (47 * Real.pi / 450)) := by
    rw [h_formula, h_readouts.wavelength_nanometers, h_angle, h_angle_real,
      Real.Angle.sin_coe]
    norm_num
  /-
  Certify a narrow enclosure for `π` using the exact half-angle value at
  `π / 128` together with Mathlib's polynomial sine remainder bound.
  -/
  let a : ℝ := Real.sqrt 2
  let b : ℝ := Real.sqrt (2 + a)
  let c : ℝ := Real.sqrt (2 + b)
  let d : ℝ := Real.sqrt (2 + c)
  let f : ℝ := Real.sqrt (2 + d)
  let e : ℝ := Real.sqrt (2 - f)
  have ha_nonneg : 0 ≤ a := by simp [a]
  have ha_lower : (1.4142135623 : ℝ) < a := by
    change (1.4142135623 : ℝ) < Real.sqrt 2
    rw [Real.lt_sqrt (by norm_num)]
    norm_num
  have ha_upper : a < (1.4142135624 : ℝ) := by
    change Real.sqrt 2 < (1.4142135624 : ℝ)
    rw [Real.sqrt_lt (by norm_num) (by norm_num)]
    norm_num
  have hb_nonneg : 0 ≤ b := by simp [b]
  have hb_lower : (1.8477590649 : ℝ) < b := by
    change (1.8477590649 : ℝ) < Real.sqrt (2 + a)
    rw [Real.lt_sqrt (by norm_num)]
    nlinarith only [ha_lower]
  have hb_upper : b < (1.8477590651 : ℝ) := by
    change Real.sqrt (2 + a) < (1.8477590651 : ℝ)
    rw [Real.sqrt_lt (by positivity) (by norm_num)]
    nlinarith only [ha_upper]
  have hc_nonneg : 0 ≤ c := by simp [c]
  have hc_lower : (1.9615705607 : ℝ) < c := by
    change (1.9615705607 : ℝ) < Real.sqrt (2 + b)
    rw [Real.lt_sqrt (by norm_num)]
    nlinarith only [hb_lower]
  have hc_upper : c < (1.9615705609 : ℝ) := by
    change Real.sqrt (2 + b) < (1.9615705609 : ℝ)
    rw [Real.sqrt_lt (by positivity) (by norm_num)]
    nlinarith only [hb_upper]
  have hd_nonneg : 0 ≤ d := by simp [d]
  have hd_lower : (1.9903694532 : ℝ) < d := by
    change (1.9903694532 : ℝ) < Real.sqrt (2 + c)
    rw [Real.lt_sqrt (by norm_num)]
    nlinarith only [hc_lower]
  have hd_upper : d < (1.9903694535 : ℝ) := by
    change Real.sqrt (2 + c) < (1.9903694535 : ℝ)
    rw [Real.sqrt_lt (by positivity) (by norm_num)]
    nlinarith only [hc_upper]
  have hf_nonneg : 0 ≤ f := by simp [f]
  have hf_lower : (1.9975909122 : ℝ) < f := by
    change (1.9975909122 : ℝ) < Real.sqrt (2 + d)
    rw [Real.lt_sqrt (by norm_num)]
    nlinarith only [hd_lower]
  have hf_upper : f < (1.9975909126 : ℝ) := by
    change Real.sqrt (2 + d) < (1.9975909126 : ℝ)
    rw [Real.sqrt_lt (by positivity) (by norm_num)]
    nlinarith only [hd_upper]
  have he_lower : (0.049082455 : ℝ) < e := by
    change (0.049082455 : ℝ) < Real.sqrt (2 - f)
    rw [Real.lt_sqrt (by norm_num)]
    nlinarith only [hf_upper]
  have he_upper : e < (0.049082460 : ℝ) := by
    change Real.sqrt (2 - f) < (0.049082460 : ℝ)
    rw [Real.sqrt_lt (by nlinarith only [hf_upper]) (by norm_num)]
    nlinarith only [hf_lower]
  have hsin_pi_div_128 : Real.sin (Real.pi / 128) = e / 2 := by
    dsimp [e, f, d, c, b, a]
    convert Real.sin_pi_over_two_pow_succ 5 using 1 <;>
      norm_num [Real.sqrtTwoAddSeries]
  have hsin_small_lower :
      (0.049082455 : ℝ) / 2 < Real.sin (Real.pi / 128) := by
    rw [hsin_pi_div_128]
    linarith only [he_lower]
  have hsin_small_upper :
      Real.sin (Real.pi / 128) < (0.049082460 : ℝ) / 2 := by
    rw [hsin_pi_div_128]
    linarith only [he_upper]
  have hpi_over_128_abs : |Real.pi / 128| ≤ (1 : ℝ) := by
    rw [abs_of_pos (by positivity)]
    nlinarith only [Real.pi_le_four]
  have hsmall_sine_bound := Real.sin_bound hpi_over_128_abs
  rw [abs_of_pos (by positivity : 0 < Real.pi / 128)] at hsmall_sine_bound
  have hsmall_lower := (abs_le.1 hsmall_sine_bound).1
  have hsmall_upper := (abs_le.1 hsmall_sine_bound).2
  have hpi_lower : (3.14159 : ℝ) < Real.pi := by
    by_contra hnot
    have hxy : Real.pi / 128 ≤ (3.14159 : ℝ) / 128 := by
      exact div_le_div_of_nonneg_right (le_of_not_gt hnot) (by norm_num)
    have hx0 : 0 ≤ Real.pi / 128 := by positivity
    have hy0 : 0 ≤ (3.14159 : ℝ) / 128 := by norm_num
    have hx1 : Real.pi / 128 ≤ 1 := (le_abs_self _).trans hpi_over_128_abs
    have hy1 : (3.14159 : ℝ) / 128 ≤ 1 := by norm_num
    have hfactor :
        0 ≤ 1 - (((3.14159 : ℝ) / 128) ^ 2 +
          ((3.14159 : ℝ) / 128) * (Real.pi / 128) +
          (Real.pi / 128) ^ 2) / 6 := by
      have hxx : (Real.pi / 128) ^ 2 ≤ 1 :=
        by simpa using (sq_le_sq₀ hx0 zero_le_one).2 hx1
      have hyy : ((3.14159 : ℝ) / 128) ^ 2 ≤ 1 := by norm_num
      have hxy_one : ((3.14159 : ℝ) / 128) * (Real.pi / 128) ≤ 1 := by
        exact mul_le_one₀ hy1 hx0 hx1
      nlinarith only [hxx, hyy, hxy_one]
    have hpoly :
        Real.pi / 128 - (Real.pi / 128) ^ 3 / 6 ≤
          (3.14159 : ℝ) / 128 - ((3.14159 : ℝ) / 128) ^ 3 / 6 := by
      have hm := mul_nonneg (sub_nonneg.mpr hxy) hfactor
      rw [← sub_nonneg]
      calc
        0 ≤ ((3.14159 : ℝ) / 128 - Real.pi / 128) *
            (1 - (((3.14159 : ℝ) / 128) ^ 2 +
              ((3.14159 : ℝ) / 128) * (Real.pi / 128) +
              (Real.pi / 128) ^ 2) / 6) := hm
        _ = ((3.14159 : ℝ) / 128 - ((3.14159 : ℝ) / 128) ^ 3 / 6) -
            (Real.pi / 128 - (Real.pi / 128) ^ 3 / 6) := by ring
    have herr :
        (Real.pi / 128) ^ 4 * (5 / 96 : ℝ) ≤
          ((3.14159 : ℝ) / 128) ^ 4 * (5 / 96 : ℝ) := by
      have hp := pow_le_pow_left₀ hx0 hxy 4
      exact mul_le_mul_of_nonneg_right hp (by norm_num)
    have hnumeric :
        (3.14159 : ℝ) / 128 - ((3.14159 : ℝ) / 128) ^ 3 / 6 +
            ((3.14159 : ℝ) / 128) ^ 4 * (5 / 96 : ℝ) <
          (0.049082455 : ℝ) / 2 := by
      norm_num
    linarith only [hsmall_upper, hpoly, herr, hsin_small_lower, hnumeric]
  have hpi_upper : Real.pi < (3.1416 : ℝ) := by
    by_contra hnot
    have hyx : (3.1416 : ℝ) / 128 ≤ Real.pi / 128 := by
      exact div_le_div_of_nonneg_right (le_of_not_gt hnot) (by norm_num)
    have hx0 : 0 ≤ Real.pi / 128 := by positivity
    have hy0 : 0 ≤ (3.1416 : ℝ) / 128 := by norm_num
    have hx1 : Real.pi / 128 ≤ 1 := (le_abs_self _).trans hpi_over_128_abs
    have hy1 : (3.1416 : ℝ) / 128 ≤ 1 := by norm_num
    have hfactor :
        0 ≤ 1 - ((Real.pi / 128) ^ 2 +
          (Real.pi / 128) * ((3.1416 : ℝ) / 128) +
          ((3.1416 : ℝ) / 128) ^ 2) / 6 := by
      have hxx : (Real.pi / 128) ^ 2 ≤ 1 :=
        by simpa using (sq_le_sq₀ hx0 zero_le_one).2 hx1
      have hyy : ((3.1416 : ℝ) / 128) ^ 2 ≤ 1 := by norm_num
      have hxy_one : (Real.pi / 128) * ((3.1416 : ℝ) / 128) ≤ 1 := by
        exact mul_le_one₀ hx1 hy0 hy1
      nlinarith only [hxx, hyy, hxy_one]
    have hpoly :
        (3.1416 : ℝ) / 128 - ((3.1416 : ℝ) / 128) ^ 3 / 6 ≤
          Real.pi / 128 - (Real.pi / 128) ^ 3 / 6 := by
      have hm := mul_nonneg (sub_nonneg.mpr hyx) hfactor
      rw [← sub_nonneg]
      calc
        0 ≤ (Real.pi / 128 - (3.1416 : ℝ) / 128) *
            (1 - ((Real.pi / 128) ^ 2 +
              (Real.pi / 128) * ((3.1416 : ℝ) / 128) +
              ((3.1416 : ℝ) / 128) ^ 2) / 6) := hm
        _ = (Real.pi / 128 - (Real.pi / 128) ^ 3 / 6) -
            ((3.1416 : ℝ) / 128 - ((3.1416 : ℝ) / 128) ^ 3 / 6) := by ring
    have herr :
        (Real.pi / 128) ^ 4 * (5 / 96 : ℝ) ≤
          ((1 : ℝ) / 32) ^ 4 * (5 / 96 : ℝ) := by
      have hx32 : Real.pi / 128 ≤ (1 : ℝ) / 32 := by
        nlinarith only [Real.pi_le_four]
      have hp := pow_le_pow_left₀ hx0 hx32 4
      exact mul_le_mul_of_nonneg_right hp (by norm_num)
    have hnumeric :
        (0.049082460 : ℝ) / 2 <
          (3.1416 : ℝ) / 128 - ((3.1416 : ℝ) / 128) ^ 3 / 6 -
            ((1 : ℝ) / 32) ^ 4 * (5 / 96 : ℝ) := by
      norm_num
    linarith only [hsmall_lower, hpoly, herr, hsin_small_upper, hnumeric]
  /-
  Bound sine at one ninth of the target angle, then use the triple-angle
  identity twice. This avoids any untrusted decimal evaluation.
  -/
  let q : ℝ := 47 * Real.pi / 4050
  have hq_lower : (364579 : ℝ) / 10000000 ≤ q := by
    dsimp [q]
    nlinarith only [hpi_lower]
  have hq_upper : q ≤ (364581 : ℝ) / 10000000 := by
    dsimp [q]
    nlinarith only [hpi_upper]
  have hq_nonneg : 0 ≤ q := by
    exact (by norm_num : (0 : ℝ) ≤ 364579 / 10000000).trans hq_lower
  have hq_abs : |q| ≤ (1 : ℝ) := by
    rw [abs_of_nonneg hq_nonneg]
    linarith only [hq_upper]
  have hq_sine_bound := Real.sin_bound hq_abs
  rw [abs_of_nonneg hq_nonneg] at hq_sine_bound
  rcases abs_le.mp hq_sine_bound with ⟨hq_sine_error_lower, hq_sine_error_upper⟩
  have hq_cube_lower :
      ((364579 : ℝ) / 10000000) ^ 3 ≤ q ^ 3 :=
    pow_le_pow_left₀ (by norm_num) hq_lower 3
  have hq_cube_upper :
      q ^ 3 ≤ ((364581 : ℝ) / 10000000) ^ 3 :=
    pow_le_pow_left₀ hq_nonneg hq_upper 3
  have hq_fourth_upper :
      q ^ 4 ≤ ((364581 : ℝ) / 10000000) ^ 4 :=
    pow_le_pow_left₀ hq_nonneg hq_upper 4
  have hsin_q_lower :
      (364497 : ℝ) / 10000000 ≤ Real.sin q := by
    norm_num at hq_sine_error_lower hq_lower hq_cube_upper hq_fourth_upper ⊢
    linarith
  have hsin_q_upper :
      Real.sin q ≤ (364502 : ℝ) / 10000000 := by
    norm_num at hq_sine_error_upper hq_upper hq_cube_lower hq_fourth_upper ⊢
    linarith
  have hsin_q_nonneg : 0 ≤ Real.sin q :=
    (by norm_num : (0 : ℝ) ≤ 364497 / 10000000).trans hsin_q_lower
  have hsin_q_cube_lower :
      ((364497 : ℝ) / 10000000) ^ 3 ≤ Real.sin q ^ 3 :=
    pow_le_pow_left₀ (by norm_num) hsin_q_lower 3
  have hsin_q_cube_upper :
      Real.sin q ^ 3 ≤ ((364502 : ℝ) / 10000000) ^ 3 :=
    pow_le_pow_left₀ hsin_q_nonneg hsin_q_upper 3
  have hsin_three_q_lower :
      (1091553 : ℝ) / 10000000 ≤ Real.sin (3 * q) := by
    rw [Real.sin_three_mul]
    norm_num at hsin_q_lower hsin_q_cube_upper ⊢
    linarith
  have hsin_three_q_upper :
      Real.sin (3 * q) ≤ (1091569 : ℝ) / 10000000 := by
    rw [Real.sin_three_mul]
    norm_num at hsin_q_upper hsin_q_cube_lower ⊢
    linarith
  have hsin_three_q_nonneg : 0 ≤ Real.sin (3 * q) :=
    (by norm_num : (0 : ℝ) ≤ 1091553 / 10000000).trans hsin_three_q_lower
  have hsin_three_q_cube_lower :
      ((1091553 : ℝ) / 10000000) ^ 3 ≤ Real.sin (3 * q) ^ 3 :=
    pow_le_pow_left₀ (by norm_num) hsin_three_q_lower 3
  have hsin_three_q_cube_upper :
      Real.sin (3 * q) ^ 3 ≤ ((1091569 : ℝ) / 10000000) ^ 3 :=
    pow_le_pow_left₀ hsin_three_q_nonneg hsin_three_q_upper 3
  have hsin_nine_q_lower :
      (322263 : ℝ) / 1000000 ≤ Real.sin (9 * q) := by
    rw [show 9 * q = 3 * (3 * q) by ring, Real.sin_three_mul]
    norm_num at hsin_three_q_lower hsin_three_q_cube_upper ⊢
    linarith
  have hsin_nine_q_upper :
      Real.sin (9 * q) ≤ (322269 : ℝ) / 1000000 := by
    rw [show 9 * q = 3 * (3 * q) by ring, Real.sin_three_mul]
    norm_num at hsin_three_q_upper hsin_three_q_cube_lower ⊢
    linarith
  have h_target_angle : 47 * Real.pi / 450 = 9 * q := by
    dsimp [q]
    ring
  have hsin_target_lower :
      (322263 : ℝ) / 1000000 ≤ Real.sin (47 * Real.pi / 450) := by
    rw [h_target_angle]
    exact hsin_nine_q_lower
  have hsin_target_upper :
      Real.sin (47 * Real.pi / 450) ≤ (322269 : ℝ) / 1000000 := by
    rw [h_target_angle]
    exact hsin_nine_q_upper
  have hsin_target_pos : 0 < Real.sin (47 * Real.pi / 450) :=
    (by norm_num : (0 : ℝ) < 322263 / 1000000).trans_le hsin_target_lower
  have hsqrt_lower : (7071 : ℝ) / 5000 ≤ Real.sqrt 2 := by
    apply le_of_lt
    rw [Real.lt_sqrt (by norm_num)]
    norm_num
  have hsqrt_upper : Real.sqrt 2 ≤ (14143 : ℝ) / 10000 := by
    apply le_of_lt
    rw [Real.sqrt_lt' (by norm_num)]
    norm_num
  have hden_lower :
      (7071 : ℝ) / 5000 * (322263 / 1000000) ≤
        Real.sqrt 2 * Real.sin (47 * Real.pi / 450) := by
    exact mul_le_mul hsqrt_lower hsin_target_lower (by norm_num)
      (Real.sqrt_nonneg 2)
  have hden_upper :
      Real.sqrt 2 * Real.sin (47 * Real.pi / 450) ≤
        (14143 : ℝ) / 10000 * (322269 / 1000000) := by
    exact mul_le_mul hsqrt_upper hsin_target_upper hsin_target_pos.le (by norm_num)
  have hden_pos :
      0 < Real.sqrt 2 * Real.sin (47 * Real.pi / 450) :=
    mul_pos (Real.sqrt_pos.2 (by norm_num)) hsin_target_pos
  have hquotient_lower :
      (1139 : ℝ) / 2000 ≤
        (13 / 50 : ℝ) /
          (Real.sqrt 2 * Real.sin (47 * Real.pi / 450)) := by
    rw [le_div_iff₀ hden_pos]
    calc
      (1139 : ℝ) / 2000 *
          (Real.sqrt 2 * Real.sin (47 * Real.pi / 450)) ≤
          (1139 : ℝ) / 2000 *
            ((14143 : ℝ) / 10000 * (322269 / 1000000)) :=
        mul_le_mul_of_nonneg_left hden_upper (by norm_num)
      _ ≤ 13 / 50 := by norm_num
  have hquotient_upper :
      (13 / 50 : ℝ) /
          (Real.sqrt 2 * Real.sin (47 * Real.pi / 450)) <
        (1141 : ℝ) / 2000 := by
    rw [div_lt_iff₀ hden_pos]
    calc
      13 / 50 < (1141 : ℝ) / 2000 *
          ((7071 : ℝ) / 5000 * (322263 / 1000000)) := by norm_num
      _ ≤ (1141 : ℝ) / 2000 *
          (Real.sqrt 2 * Real.sin (47 * Real.pi / 450)) :=
        mul_le_mul_of_nonneg_left hden_lower (by norm_num)
  constructor
  · rw [h_exact, round_eq_iff]
    constructor
    · norm_num at hquotient_lower ⊢
      linarith
    · norm_num at hquotient_upper ⊢
      linarith
  · unfold IsClosestAnswer
    rw [h_exact]
    intro other h_other
    cases other with
    | A =>
        simp only [answerUnitCellSizeNanometers]
        have hA :
            0 < (13 / 50 : ℝ) /
                (Real.sqrt 2 * Real.sin (47 * Real.pi / 450)) - 0.405 := by
          nlinarith only [hquotient_lower]
        rw [abs_of_pos hA, abs_lt]
        constructor <;> nlinarith only [hquotient_lower, hquotient_upper]
    | B =>
        simp only [answerUnitCellSizeNanometers]
        have hB :
            0 < (13 / 50 : ℝ) /
                (Real.sqrt 2 * Real.sin (47 * Real.pi / 450)) - 0.520 := by
          nlinarith only [hquotient_lower]
        rw [abs_of_pos hB, abs_lt]
        constructor <;> nlinarith only [hquotient_lower, hquotient_upper]
    | C =>
        exact (h_other rfl).elim
    | D =>
        simp only [answerUnitCellSizeNanometers]
        have hD :
            (13 / 50 : ℝ) /
                (Real.sqrt 2 * Real.sin (47 * Real.pi / 450)) - 0.640 < 0 := by
          nlinarith only [hquotient_upper]
        rw [abs_of_neg hD, abs_lt]
        constructor <;> nlinarith only [hquotient_lower, hquotient_upper]

end PhyXMiniProblems.ProblemPhyXMini0080
