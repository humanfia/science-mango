import Mathlib.Analysis.SpecialFunctions.Trigonometric.Arctan
import Physlib.Units.WithDim.Basic

/-!
# Width of a single slit from its first diffraction minima

This file formalizes problem `phyx_mini_0047`. A monochromatic laser with
wavelength `633 nm` illuminates one narrow slit, and a screen lies `6.0 m`
along the optical `x` axis. The primary figure marks a `32 mm` separation in
the transverse `y` direction between the first dark minima on the two sides of
the central bright fringe.

Wavelengths, aperture widths, axial distances, and screen coordinates are
unit-aware physical lengths. Angles are dimensionless real readouts in
radians, measured from the positive optical axis. The exact physics below
gives a slit width of approximately `0.237376 mm`; consequently the dataset's
recorded `633 nm` answer is retained only as metadata.
-/

noncomputable section

namespace PhyXMiniProblems.ProblemPhyXMini0047

/-! ## Dimensionful optical quantities and unit readouts -/

/-- A signed, unit-independent physical quantity carrying length dimension. -/
abbrev OpticalLength : Type :=
  Dimensionful (WithDim Dimension.L𝓭 ℝ)

/-- Read a physical length as a real scalar in the selected length unit. -/
def lengthReadout (unit : LengthUnit) (length : OpticalLength) : ℝ :=
  (length ({ UnitChoices.SI with length := unit } : UnitChoices)).val

/-- Metre readout for axial geometry and positivity conditions. -/
def lengthInMeters (length : OpticalLength) : ℝ :=
  lengthReadout LengthUnit.meters length

/-- Millimetre readout for the screen separation in the source figure. -/
def lengthInMillimeters (length : OpticalLength) : ℝ :=
  lengthReadout LengthUnit.millimeters length

/-- Nanometre readout for the wavelength, answers, and requested width. -/
def lengthInNanometers (length : OpticalLength) : ℝ :=
  lengthReadout LengthUnit.nanometers length

/-! ## Apparatus and primary-figure geometry -/

/-- The aperture geometry selected by the single opening in the barrier. -/
inductive ApertureGeometry where
  | singleNarrowSlit
  deriving DecidableEq, Repr

/-- The far-field diffraction model used for the first-minimum law. -/
inductive DiffractionRegime where
  | fraunhoferSingleSlit
  deriving DecidableEq, Repr

/--
The monochromatic laser, aperture, and observation screen in the experiment.
The unknown physical quantity is `slitWidth`; no field assigns it a numerical
value or defines it from an answer choice.
-/
structure SingleSlitApparatus where
  apertureGeometry : ApertureGeometry
  diffractionRegime : DiffractionRegime
  /-- Wavelength `λ` of the incident monochromatic laser light. -/
  laserWavelength : OpticalLength
  /-- Unknown aperture width `a`, labeled “Slit width = ?” in the figure. -/
  slitWidth : OpticalLength
  /-- Axial slit-to-screen distance, labeled `x = 6.0 m` in the figure. -/
  screenDistanceAlongX : OpticalLength

/--
Signed screen coordinates and propagation angles for the two first minima.
The central-axis coordinate makes the origin drawn at the intersection of the
figure's `x` and `y` axes explicit.
-/
structure FirstMinimumGeometry where
  centralAxisY : OpticalLength
  upperFirstMinimumY : OpticalLength
  lowerFirstMinimumY : OpticalLength
  /-- Upper first-minimum ray angle from the positive `x` axis. -/
  upperAngleRadians : ℝ
  /-- Lower first-minimum ray angle from the positive `x` axis. -/
  lowerAngleRadians : ℝ

/-! ## Source and figure readouts -/

/--
The text and primary-image data: one narrow slit, `λ = 633 nm`,
`x = 6.0 m`, a centered `y = 0` optical axis, and `32 mm` between the
centers of the upper and lower first minima.

This predicate contains no value for the unknown slit width.
-/
def MatchesProblemAndFigureReadouts
    (apparatus : SingleSlitApparatus)
    (minima : FirstMinimumGeometry) : Prop :=
  apparatus.apertureGeometry = .singleNarrowSlit ∧
    lengthInNanometers apparatus.laserWavelength = 633 ∧
    lengthInMeters apparatus.screenDistanceAlongX = 6 ∧
    (∀ unit : LengthUnit, lengthReadout unit minima.centralAxisY = 0) ∧
    lengthInMillimeters minima.upperFirstMinimumY -
        lengthInMillimeters minima.lowerFirstMinimumY = 32

/--
Physical branch conditions for the nondegenerate apparatus. The two rays lie
on the signed acute branches shown in the figure. These conditions do not
determine the numerical slit width.
-/
def HasPhysicalParameters
    (apparatus : SingleSlitApparatus)
    (minima : FirstMinimumGeometry) : Prop :=
  0 < lengthInMeters apparatus.laserWavelength ∧
    0 < lengthInMeters apparatus.slitWidth ∧
    0 < lengthInMeters apparatus.screenDistanceAlongX ∧
    lengthInMeters minima.centralAxisY <
      lengthInMeters minima.upperFirstMinimumY ∧
    lengthInMeters minima.lowerFirstMinimumY <
      lengthInMeters minima.centralAxisY ∧
    0 < minima.upperAngleRadians ∧
    minima.upperAngleRadians < Real.pi / 2 ∧
    -(Real.pi / 2) < minima.lowerAngleRadians ∧
    minima.lowerAngleRadians < 0

/-- The one-slit apparatus is interpreted in the Fraunhofer regime. -/
def UsesFraunhoferSingleSlitModel
    (apparatus : SingleSlitApparatus) : Prop :=
  apparatus.diffractionRegime = .fraunhoferSingleSlit

/-! ## Governing diffraction and screen-geometry laws -/

/--
Exact first-order Fraunhofer single-slit minima and straight slit-to-screen
ray geometry. In any coherent length unit the laws are

`a sin θ_upper = λ`, `a sin θ_lower = -λ`, and `y - y₀ = L tan θ`.

The opposite-angle field records the reflection symmetry of the two first
minima about the central optical axis. No field contains the requested width
or any displayed answer.
-/
structure SatisfiesFirstMinimumDiffractionLaws
    (apparatus : SingleSlitApparatus)
    (minima : FirstMinimumGeometry) : Prop where
  upperFirstMinimumLaw : ∀ unit : LengthUnit,
    lengthReadout unit apparatus.slitWidth *
        Real.sin minima.upperAngleRadians =
      lengthReadout unit apparatus.laserWavelength
  lowerFirstMinimumLaw : ∀ unit : LengthUnit,
    lengthReadout unit apparatus.slitWidth *
        Real.sin minima.lowerAngleRadians =
      -lengthReadout unit apparatus.laserWavelength
  upperScreenProjection : ∀ unit : LengthUnit,
    lengthReadout unit minima.upperFirstMinimumY -
        lengthReadout unit minima.centralAxisY =
      lengthReadout unit apparatus.screenDistanceAlongX *
        Real.tan minima.upperAngleRadians
  lowerScreenProjection : ∀ unit : LengthUnit,
    lengthReadout unit minima.lowerFirstMinimumY -
        lengthReadout unit minima.centralAxisY =
      lengthReadout unit apparatus.screenDistanceAlongX *
        Real.tan minima.lowerAngleRadians
  oppositeFirstMinimumAngles :
    minima.lowerAngleRadians = -minima.upperAngleRadians

/-! ## Dataset answer metadata and formalization target -/

/-- Labels of the four slit-width answers printed with the dataset item. -/
inductive AnswerChoice where
  | A
  | B
  | C
  | D
  deriving DecidableEq, Repr

/-- Nanometre value printed beside each answer label. -/
def displayedSlitWidthInNanometers : AnswerChoice → ℝ
  | .A => 643
  | .B => 633
  | .C => 639
  | .D => 533

/-- The answer label recorded by the source dataset, retained as metadata only. -/
def recordedDatasetAnswer : AnswerChoice := .B

/-!
The `32 mm` separation and reflection symmetry place each first minimum
`16 mm` from the optical axis. Exact ray geometry therefore gives

`θ₁ = arctan ((16 mm) / (6 m))`,

and the first-minimum law gives the requested width

`a = 633 nm / sin θ₁ ≈ 237375.844 nm = 0.237375844 mm`.

Thus none of the four nanometre-scale displayed answers agrees with the
physical model. The recorded answer B is not a theorem premise or conclusion.

This formalizes `thm:physics:phyx_mini_0047:target`.
-/
theorem problem_phyx_mini_0047
    (apparatus : SingleSlitApparatus)
    (minima : FirstMinimumGeometry)
    (h_readouts : MatchesProblemAndFigureReadouts apparatus minima)
    (h_physical : HasPhysicalParameters apparatus minima)
    (h_model : UsesFraunhoferSingleSlitModel apparatus)
    (h_diffraction : SatisfiesFirstMinimumDiffractionLaws apparatus minima) :
    lengthInNanometers apparatus.slitWidth =
      633 / Real.sin (Real.arctan (((16 : ℝ) / 1000) / 6)) := by
  rcases h_readouts with
    ⟨_, h_wavelength_nm, h_distance_m, h_axis, h_separation_mm⟩
  rcases h_physical with
    ⟨_, _, _, _, _, h_angle_pos, h_angle_lt, _, _⟩

  have length_millimeters_eq (length : OpticalLength) :
      lengthInMillimeters length = 1000 * lengthInMeters length := by
    have h := congrArg WithDim.val
      (length.2
        ({ UnitChoices.SI with length := LengthUnit.meters } : UnitChoices)
        ({ UnitChoices.SI with length := LengthUnit.millimeters } : UnitChoices))
    change lengthInMillimeters length =
      NNReal.toReal
          (({ UnitChoices.SI with length := LengthUnit.meters } : UnitChoices).dimScale
            ({ UnitChoices.SI with length := LengthUnit.millimeters } : UnitChoices)
            Dimension.L𝓭) *
        lengthInMeters length at h
    norm_num [lengthInMillimeters, lengthInMeters, lengthReadout,
      UnitChoices.dimScale, LengthUnit.millimeters, LengthUnit.meters,
      LengthUnit.scale, LengthUnit.div_eq_val, NNReal.toReal, Dimension.L𝓭] at h ⊢
    exact h

  have h_distance_mm :
      lengthInMillimeters apparatus.screenDistanceAlongX = 6000 := by
    rw [length_millimeters_eq, h_distance_m]
    norm_num
  have h_axis_mm : lengthInMillimeters minima.centralAxisY = 0 :=
    h_axis LengthUnit.millimeters

  have h_upper_projection :=
    h_diffraction.upperScreenProjection LengthUnit.millimeters
  have h_lower_projection :=
    h_diffraction.lowerScreenProjection LengthUnit.millimeters
  change lengthInMillimeters minima.upperFirstMinimumY -
      lengthInMillimeters minima.centralAxisY =
    lengthInMillimeters apparatus.screenDistanceAlongX *
      Real.tan minima.upperAngleRadians at h_upper_projection
  change lengthInMillimeters minima.lowerFirstMinimumY -
      lengthInMillimeters minima.centralAxisY =
    lengthInMillimeters apparatus.screenDistanceAlongX *
      Real.tan minima.lowerAngleRadians at h_lower_projection
  rw [h_axis_mm, h_distance_mm] at h_upper_projection h_lower_projection
  rw [h_diffraction.oppositeFirstMinimumAngles, Real.tan_neg] at h_lower_projection

  have h_tangent :
      Real.tan minima.upperAngleRadians = ((16 : ℝ) / 1000) / 6 := by
    norm_num at h_upper_projection h_lower_projection ⊢
    linarith

  have h_angle_lower : -(Real.pi / 2) < minima.upperAngleRadians := by
    linarith [Real.pi_pos]
  have h_angle :
      minima.upperAngleRadians = Real.arctan (((16 : ℝ) / 1000) / 6) := by
    calc
      minima.upperAngleRadians =
          Real.arctan (Real.tan minima.upperAngleRadians) :=
        (Real.arctan_tan h_angle_lower h_angle_lt).symm
      _ = Real.arctan (((16 : ℝ) / 1000) / 6) :=
        congrArg Real.arctan h_tangent

  have h_sine_ne : Real.sin minima.upperAngleRadians ≠ 0 := by
    exact ne_of_gt
      (Real.sin_pos_of_pos_of_lt_pi h_angle_pos (by linarith [Real.pi_pos]))
  have h_upper_diffraction :=
    h_diffraction.upperFirstMinimumLaw LengthUnit.nanometers
  change lengthInNanometers apparatus.slitWidth *
      Real.sin minima.upperAngleRadians =
    lengthInNanometers apparatus.laserWavelength at h_upper_diffraction
  rw [h_wavelength_nm] at h_upper_diffraction
  rw [← h_angle]
  exact (eq_div_iff h_sine_ne).2 h_upper_diffraction

end PhyXMiniProblems.ProblemPhyXMini0047
