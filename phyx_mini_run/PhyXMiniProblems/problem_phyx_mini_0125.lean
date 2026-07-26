import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Physlib.Units.WithDim.Basic

/-!
# Adjacent bright fringes in a double-slit experiment

This file models the double-slit apparatus and the labels in the supplied
figure.  The slit separation `d`, slit-to-screen distance `ℓ`, wavelength
`λ`, and screen offsets `x₁` and `x₂` are physical lengths represented
independently of a chosen unit.  The figure angles `θ₁` and `θ₂` are
dimensionless real readouts in radians.

The source metadata records choice C (`6.20 mm`).  The stated dimensions,
however, give approximately `6.00 mm`, choice B, under either the standard
paraxial computation or the exact trigonometric model formalized below.
-/

noncomputable section

namespace PhyXMiniProblems.ProblemPhyXMini0125

open Dimension

/-- A physical length represented independently of the unit used to read it. -/
abbrev LengthQuantity : Type := Dimensionful (WithDim L𝓭 ℝ)

/-- Read a physical length as a real scalar in a selected length unit. -/
def lengthValueIn (unit : LengthUnit) (length : LengthQuantity) : ℝ :=
  (length ({ UnitChoices.SI with length := unit } : UnitChoices)).val

/-- The metre readout of a physical length. -/
def metersValue (length : LengthQuantity) : ℝ :=
  lengthValueIn LengthUnit.meters length

/-- The millimetre readout used for slit and fringe spacings. -/
def millimetersValue (length : LengthQuantity) : ℝ :=
  lengthValueIn LengthUnit.millimeters length

/-- The nanometre readout used for the light wavelength. -/
def nanometersValue (length : LengthQuantity) : ℝ :=
  lengthValueIn LengthUnit.nanometers length

/-- The two slit labels printed in the primary figure. -/
inductive SlitLabel where
  | S1
  | S2
  deriving DecidableEq, Repr

/-- The two upper bright maxima labeled by `(θ₁, x₁)` and `(θ₂, x₂)`. -/
inductive BrightFringeLabel where
  | first
  | second
  deriving DecidableEq, Repr

/-- The constructive-interference order represented by each figure label. -/
def BrightFringeLabel.order : BrightFringeLabel → ℕ
  | .first => 1
  | .second => 2

/-- Qualitative geometry of the two openings in the slit screen. -/
inductive SlitArrangement where
  | verticalPair
  | other
  deriving DecidableEq, Repr

/-- Qualitative orientation of the viewing screen relative to the optical axis. -/
inductive ScreenOrientation where
  | perpendicularToOpticalAxis
  | other
  deriving DecidableEq, Repr

/-- The wavefront regime of the light incident on the two slits. -/
inductive IncidentWavefrontRegime where
  | planarFromDistantSource
  | fromFiniteSource
  deriving DecidableEq, Repr

/-!
The physical quantities and figure-derived data for the experiment.

`Phase` remains abstract because the source gives no phase unit or scalar
calibration.  Only equality of the incident phases at `S₁` and `S₂` is used.
The fields `fringeAngleRadians` and `fringeOffsetFromCentral` interpret the
figure pairs `(θ₁, x₁)` and `(θ₂, x₂)`.
-/
structure DoubleSlitExperiment (Phase : Type) where
  /-- Figure length `d`: separation of slits `S₁` and `S₂`. -/
  slitSeparation : LengthQuantity
  /-- Figure length `ℓ`: horizontal slit-plane-to-screen distance. -/
  screenDistance : LengthQuantity
  /-- Vacuum wavelength `λ` of the monochromatic incident light. -/
  lightWavelength : LengthQuantity
  /-- Relative placement of the two openings in the slit screen. -/
  slitArrangement : SlitArrangement
  /-- Orientation of the viewing screen. -/
  screenOrientation : ScreenOrientation
  /-- Whether the incident wavefront is planar because the source is distant. -/
  incidentWavefrontRegime : IncidentWavefrontRegime
  /-- Incident optical phase at each slit. -/
  incidentPhaseAtSlit : SlitLabel → Phase
  /-- Figure angles `θ₁` and `θ₂`, in radians. -/
  fringeAngleRadians : BrightFringeLabel → ℝ
  /-- Figure offsets `x₁` and `x₂` from the central bright fringe. -/
  fringeOffsetFromCentral : BrightFringeLabel → LengthQuantity

/-- The categorical slit and screen layout visible in the primary figure. -/
def HasDepictedLayout {Phase : Type}
    (experiment : DoubleSlitExperiment Phase) : Prop :=
  experiment.slitArrangement = .verticalPair ∧
    experiment.screenOrientation = .perpendicularToOpticalAxis

/-!
The distant monochromatic source is modeled by a planar incident wavefront
and equal incident phase at the two slits.  This does not constrain any fringe
position on the viewing screen.
-/
def HasDistantInPhaseIllumination {Phase : Type}
    (experiment : DoubleSlitExperiment Phase) : Prop :=
  experiment.incidentWavefrontRegime = .planarFromDistantSource ∧
    experiment.incidentPhaseAtSlit .S1 =
      experiment.incidentPhaseAtSlit .S2

/-- Positivity and angular-range conditions for the depicted experiment. -/
def HasPhysicalParameters {Phase : Type}
    (experiment : DoubleSlitExperiment Phase) : Prop :=
  0 < metersValue experiment.slitSeparation ∧
    0 < metersValue experiment.screenDistance ∧
    0 < metersValue experiment.lightWavelength ∧
    (∀ fringe : BrightFringeLabel,
      0 < experiment.fringeAngleRadians fringe ∧
        experiment.fringeAngleRadians fringe < Real.pi / 2) ∧
    ∀ fringe : BrightFringeLabel,
      0 < metersValue (experiment.fringeOffsetFromCentral fringe)

/-!
Numerical readouts stated in the problem: `d = 0.100 mm`, `ℓ = 1.20 m`,
and `λ = 500 nm`.  No angle or fringe-spacing answer occurs here.
-/
def HasStatedReadouts {Phase : Type}
    (experiment : DoubleSlitExperiment Phase) : Prop :=
  millimetersValue experiment.slitSeparation = 0.100 ∧
    metersValue experiment.screenDistance = 1.20 ∧
    nanometersValue experiment.lightWavelength = 500

/-!
Constructive double-slit interference law for each labeled bright fringe:
`d sin θₘ = m λ`.  The equation is written using metre readouts, so all
length-valued factors use the same unit.
-/
def SatisfiesConstructiveBrightFringeLaw {Phase : Type}
    (experiment : DoubleSlitExperiment Phase) : Prop :=
  ∀ fringe : BrightFringeLabel,
    metersValue experiment.slitSeparation *
        Real.sin (experiment.fringeAngleRadians fringe) =
      (fringe.order : ℝ) * metersValue experiment.lightWavelength

/-!
Exact straight-line screen geometry for each labeled maximum:
`xₘ = ℓ tan θₘ`.  This generic law contains no requested numerical spacing.
-/
def SatisfiesStraightLineScreenGeometry {Phase : Type}
    (experiment : DoubleSlitExperiment Phase) : Prop :=
  ∀ fringe : BrightFringeLabel,
    metersValue (experiment.fringeOffsetFromCentral fringe) =
      metersValue experiment.screenDistance *
        Real.tan (experiment.fringeAngleRadians fringe)

/-- The measured separation `x₂ - x₁` of the adjacent labeled bright fringes. -/
def adjacentBrightFringeSpacingMillimeters {Phase : Type}
    (experiment : DoubleSlitExperiment Phase) : ℝ :=
  millimetersValue (experiment.fringeOffsetFromCentral .second) -
    millimetersValue (experiment.fringeOffsetFromCentral .first)

/-- Labels of the four displayed answer choices. -/
inductive AnswerChoice where
  | A
  | B
  | C
  | D
  deriving DecidableEq, Repr

/-- The fringe spacing printed beside each answer choice, in millimetres. -/
def answerSpacingMillimeters : AnswerChoice → ℝ
  | .A => 6.40
  | .B => 6.00
  | .C => 6.20
  | .D => 6.60

/-- Dataset metadata only: the source records answer choice C. -/
def recordedAnswerChoice : AnswerChoice := .C

/-- A choice is correct when its displayed value is nearest to the physical spacing. -/
def IsNearestDisplayedChoice {Phase : Type}
    (experiment : DoubleSlitExperiment Phase)
    (choice : AnswerChoice) : Prop :=
  ∀ other : AnswerChoice,
    |adjacentBrightFringeSpacingMillimeters experiment -
        answerSpacingMillimeters choice| ≤
      |adjacentBrightFringeSpacingMillimeters experiment -
        answerSpacingMillimeters other|

/-!
For the stated slit separation, screen distance, and wavelength, the spacing
between the adjacent maxima `x₁` and `x₂` is within `0.01 mm` of `6.00 mm`.
Consequently the nearest displayed value is answer choice B.

This formalizes blueprint label `thm:physics:phyx_mini_0125:target`.
-/
theorem problem_phyx_mini_0125
    {Phase : Type}
    (experiment : DoubleSlitExperiment Phase)
    (h_layout : HasDepictedLayout experiment)
    (h_illumination : HasDistantInPhaseIllumination experiment)
    (h_physical : HasPhysicalParameters experiment)
    (h_readouts : HasStatedReadouts experiment)
    (h_interference : SatisfiesConstructiveBrightFringeLaw experiment)
    (h_geometry : SatisfiesStraightLineScreenGeometry experiment) :
    |adjacentBrightFringeSpacingMillimeters experiment - 6.00| <
        (1 : ℝ) / 100 ∧
      IsNearestDisplayedChoice experiment .B := by
  have millimeters_eq_meters (length : LengthQuantity) :
      millimetersValue length = 1000 * metersValue length := by
    have h := length.2
      ({ UnitChoices.SI with length := LengthUnit.meters } : UnitChoices)
      ({ UnitChoices.SI with length := LengthUnit.millimeters } : UnitChoices)
    have hv := congrArg WithDim.val h
    norm_num [millimetersValue, metersValue, lengthValueIn,
      UnitChoices.dimScale, LengthUnit.millimeters, LengthUnit.meters,
      LengthUnit.scale, LengthUnit.div_eq_val, Dimension.L𝓭] at hv ⊢
    exact hv
  have nanometers_eq_meters (length : LengthQuantity) :
      nanometersValue length = 1000000000 * metersValue length := by
    have h := length.2
      ({ UnitChoices.SI with length := LengthUnit.meters } : UnitChoices)
      ({ UnitChoices.SI with length := LengthUnit.nanometers } : UnitChoices)
    have hv := congrArg WithDim.val h
    norm_num [nanometersValue, metersValue, lengthValueIn,
      UnitChoices.dimScale, LengthUnit.nanometers, LengthUnit.meters,
      LengthUnit.scale, LengthUnit.div_eq_val, Dimension.L𝓭] at hv ⊢
    exact hv

  rcases h_physical with
    ⟨h_slit_pos, h_screen_pos, h_wavelength_pos, h_angles, h_offsets⟩
  rcases h_readouts with ⟨h_slit_mm, h_screen_m, h_wavelength_nm⟩
  have h_slit_m :
      metersValue experiment.slitSeparation = (1 : ℝ) / 10000 := by
    nlinarith only [h_slit_mm,
      millimeters_eq_meters experiment.slitSeparation]
  have h_wavelength_m :
      metersValue experiment.lightWavelength = (1 : ℝ) / 2000000 := by
    nlinarith only [h_wavelength_nm,
      nanometers_eq_meters experiment.lightWavelength]
  have h_screen_m' :
      metersValue experiment.screenDistance = (6 : ℝ) / 5 := by
    norm_num at h_screen_m ⊢
    exact h_screen_m

  have h_angle_first := h_angles BrightFringeLabel.first
  have h_angle_second := h_angles BrightFringeLabel.second
  have h_interference_first := h_interference BrightFringeLabel.first
  have h_interference_second := h_interference BrightFringeLabel.second
  have h_sin_first :
      Real.sin (experiment.fringeAngleRadians .first) = (1 : ℝ) / 200 := by
    rw [h_slit_m, h_wavelength_m] at h_interference_first
    norm_num [BrightFringeLabel.order] at h_interference_first ⊢
    linarith only [h_interference_first]
  have h_sin_second :
      Real.sin (experiment.fringeAngleRadians .second) = (1 : ℝ) / 100 := by
    rw [h_slit_m, h_wavelength_m] at h_interference_second
    norm_num [BrightFringeLabel.order] at h_interference_second ⊢
    linarith only [h_interference_second]

  have h_cos_first_pos :
      0 < Real.cos (experiment.fringeAngleRadians .first) :=
    Real.cos_pos_of_mem_Ioo
      ⟨by linarith only [Real.pi_pos, h_angle_first.1],
        h_angle_first.2⟩
  have h_cos_second_pos :
      0 < Real.cos (experiment.fringeAngleRadians .second) :=
    Real.cos_pos_of_mem_Ioo
      ⟨by linarith only [Real.pi_pos, h_angle_second.1],
        h_angle_second.2⟩
  have h_trig_first :=
    Real.sin_sq_add_cos_sq (experiment.fringeAngleRadians .first)
  have h_trig_second :=
    Real.sin_sq_add_cos_sq (experiment.fringeAngleRadians .second)
  rw [h_sin_first] at h_trig_first
  rw [h_sin_second] at h_trig_second
  have h_cos_first_lower :
      (9999 : ℝ) / 10000 <
        Real.cos (experiment.fringeAngleRadians .first) := by
    norm_num at h_trig_first
    nlinarith only [h_cos_first_pos, h_trig_first]
  have h_cos_second_lower :
      (9999 : ℝ) / 10000 <
        Real.cos (experiment.fringeAngleRadians .second) := by
    norm_num at h_trig_second
    nlinarith only [h_cos_second_pos, h_trig_second]

  have h_tan_first :
      Real.tan (experiment.fringeAngleRadians .first) =
        ((1 : ℝ) / 200) /
          Real.cos (experiment.fringeAngleRadians .first) := by
    rw [Real.tan_eq_sin_div_cos, h_sin_first]
  have h_tan_second :
      Real.tan (experiment.fringeAngleRadians .second) =
        ((1 : ℝ) / 100) /
          Real.cos (experiment.fringeAngleRadians .second) := by
    rw [Real.tan_eq_sin_div_cos, h_sin_second]
  have h_tan_first_lower :
      (1 : ℝ) / 200 ≤
        Real.tan (experiment.fringeAngleRadians .first) := by
    rw [h_tan_first]
    apply (le_div_iff₀ h_cos_first_pos).2
    nlinarith only [Real.cos_le_one
      (experiment.fringeAngleRadians .first)]
  have h_tan_first_upper :
      Real.tan (experiment.fringeAngleRadians .first) <
        (50 : ℝ) / 9999 := by
    rw [h_tan_first]
    apply (div_lt_iff₀ h_cos_first_pos).2
    nlinarith only [h_cos_first_lower]
  have h_tan_second_lower :
      (1 : ℝ) / 100 ≤
        Real.tan (experiment.fringeAngleRadians .second) := by
    rw [h_tan_second]
    apply (le_div_iff₀ h_cos_second_pos).2
    nlinarith only [Real.cos_le_one
      (experiment.fringeAngleRadians .second)]
  have h_tan_second_upper :
      Real.tan (experiment.fringeAngleRadians .second) <
        (100 : ℝ) / 9999 := by
    rw [h_tan_second]
    apply (div_lt_iff₀ h_cos_second_pos).2
    nlinarith only [h_cos_second_lower]

  have h_geometry_first := h_geometry BrightFringeLabel.first
  have h_geometry_second := h_geometry BrightFringeLabel.second
  rw [h_screen_m'] at h_geometry_first h_geometry_second
  have h_spacing :
      adjacentBrightFringeSpacingMillimeters experiment =
        1200 *
          (Real.tan (experiment.fringeAngleRadians .second) -
            Real.tan (experiment.fringeAngleRadians .first)) := by
    rw [adjacentBrightFringeSpacingMillimeters,
      millimeters_eq_meters, millimeters_eq_meters,
      h_geometry_first, h_geometry_second]
    ring
  have h_spacing_lower :
      (599 : ℝ) / 100 <
        adjacentBrightFringeSpacingMillimeters experiment := by
    rw [h_spacing]
    nlinarith only [h_tan_second_lower, h_tan_first_upper]
  have h_spacing_upper :
      adjacentBrightFringeSpacingMillimeters experiment <
        (601 : ℝ) / 100 := by
    rw [h_spacing]
    nlinarith only [h_tan_second_upper, h_tan_first_lower]
  have h_spacing_error :
      |adjacentBrightFringeSpacingMillimeters experiment - 6.00| <
        (1 : ℝ) / 100 := by
    rw [abs_lt]
    constructor <;> norm_num <;>
      linarith only [h_spacing_lower, h_spacing_upper]

  refine ⟨h_spacing_error, ?_⟩
  have h_spacing_error_le :
      |adjacentBrightFringeSpacingMillimeters experiment - 6| ≤
        (1 : ℝ) / 100 := by
    norm_num at h_spacing_error ⊢
    exact le_of_lt h_spacing_error
  intro other
  cases other with
  | A =>
      norm_num [answerSpacingMillimeters]
      have h_nonpos :
          adjacentBrightFringeSpacingMillimeters experiment - 32 / 5 ≤ 0 := by
        linarith only [h_spacing_upper]
      rw [abs_of_nonpos h_nonpos]
      linarith only [h_spacing_error_le, h_spacing_upper]
  | B =>
      exact le_rfl
  | C =>
      norm_num [answerSpacingMillimeters]
      have h_nonpos :
          adjacentBrightFringeSpacingMillimeters experiment - 31 / 5 ≤ 0 := by
        linarith only [h_spacing_upper]
      rw [abs_of_nonpos h_nonpos]
      linarith only [h_spacing_error_le, h_spacing_upper]
  | D =>
      norm_num [answerSpacingMillimeters]
      have h_nonpos :
          adjacentBrightFringeSpacingMillimeters experiment - 33 / 5 ≤ 0 := by
        linarith only [h_spacing_upper]
      rw [abs_of_nonpos h_nonpos]
      linarith only [h_spacing_error_le, h_spacing_upper]

end PhyXMiniProblems.ProblemPhyXMini0125
