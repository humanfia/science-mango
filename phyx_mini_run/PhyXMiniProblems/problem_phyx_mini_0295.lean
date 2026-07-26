import Mathlib
import Physlib.Units.WithDim.Basic

/-!
# Traveling-wave frequency of a nylon guitar string

This file models problem `phyx_mini_0295`. A nylon string is held at fixed
supports a distance `D` apart. The primary figure shows three antinodes, with
solid and dashed curves representing the two extreme profiles of the same
standing wave. The requested frequency is that of either traveling wave whose
superposition produces this standing wave.

Physical magnitudes use Physlib's unit-independent `Dimensionful` quantities.
Real numbers below occur only as coherent SI readouts, dimensionless counts,
and displayed answer values.
-/

noncomputable section

namespace PhyXMiniProblems.ProblemPhyXMini0295

open Dimension

/-! ## Dimensionful quantities and coherent SI readouts -/

/-- A physical length. -/
abbrev LengthQuantity : Type := Dimensionful (WithDim L𝓭 NNReal)

/-- A physical frequency, carrying the inverse-time dimension. -/
abbrev FrequencyQuantity : Type := Dimensionful (WithDim T𝓭⁻¹ NNReal)

/-- A physical mass per unit length. -/
abbrev LinearMassDensityQuantity : Type :=
  Dimensionful (WithDim (M𝓭 * L𝓭⁻¹) NNReal)

/-- A physical propagation speed. -/
abbrev SpeedQuantity : Type :=
  Dimensionful (WithDim (L𝓭 * T𝓭⁻¹) NNReal)

/-- A physical force magnitude, used here for string tension. -/
abbrev ForceQuantity : Type :=
  Dimensionful (WithDim (M𝓭 * L𝓭 * T𝓭⁻¹ * T𝓭⁻¹) NNReal)

/-- Read a nonnegative, dimension-tagged physical quantity in chosen units. -/
def quantityReadout {d : Dimension}
    (units : UnitChoices) (quantity : Dimensionful (WithDim d NNReal)) : ℝ :=
  ((quantity units).val : ℝ)

/-- Metre readout of a physical length. -/
def lengthInMeters (length : LengthQuantity) : ℝ :=
  quantityReadout UnitChoices.SI length

/-- Hertz readout of a physical frequency. -/
def frequencyInHertz (frequency : FrequencyQuantity) : ℝ :=
  quantityReadout UnitChoices.SI frequency

/-- Kilograms-per-metre readout of a physical linear mass density. -/
def linearMassDensityInKilogramsPerMeter
    (density : LinearMassDensityQuantity) : ℝ :=
  quantityReadout UnitChoices.SI density

/-- Metres-per-second readout of a physical speed. -/
def speedInMetersPerSecond (speed : SpeedQuantity) : ℝ :=
  quantityReadout UnitChoices.SI speed

/-- Newton readout of a force magnitude in coherent SI base units. -/
def forceInNewtons (force : ForceQuantity) : ℝ :=
  quantityReadout UnitChoices.SI force

/-! ## String apparatus and primary-figure data -/

/-- Material classification of the vibrating string. -/
inductive StringMaterial where
  | nylon
  | other
  deriving DecidableEq, Repr

/-- The two supports delimiting the vibrating part of the string. -/
inductive StringEndpoint where
  | leftSupport
  | rightSupport
  deriving DecidableEq, Repr

/-- Mechanical boundary condition at an endpoint of the string. -/
inductive EndpointBoundary where
  | fixed
  | free
  deriving DecidableEq, Repr

/-- The only text label in the primary figure. -/
inductive FigureLabel where
  | D
  deriving DecidableEq, Repr

/-- The geometric span to which a figure label can point. -/
inductive FigureSpan where
  | betweenFixedSupports
  deriving DecidableEq, Repr

/--
Physical quantities and figure-derived roles for the vibrating string.

The wavelength, propagation speed, and component traveling-wave frequency are
unknown state variables. In particular, this structure assigns none of them
the requested numerical answer.
-/
structure GuitarStringStandingWaveSetup where
  stringMaterial : StringMaterial
  endpointBoundary : StringEndpoint → EndpointBoundary
  figureLabelTarget : FigureLabel → FigureSpan
  /-- Number of half-wavelength loops (antinodes) visible in the figure. -/
  figureAntinodeCount : ℕ
  /-- Distance `D` between the two fixed supports. -/
  supportSeparationD : LengthQuantity
  /-- Linear mass density of the uniform nylon string. -/
  linearMassDensity : LinearMassDensityQuantity
  /-- Magnitude of the uniform string tension. -/
  tension : ForceQuantity
  /-- Wavelength of either traveling component and of the standing pattern. -/
  wavelength : LengthQuantity
  /-- Propagation speed of transverse waves on the taut string. -/
  transverseWaveSpeed : SpeedQuantity
  /-- Frequency shared by the two oppositely traveling component waves. -/
  componentTravelingWaveFrequency : FrequencyQuantity

/-!
The categorical and numerical information supplied by the problem and primary
figure. The figure has nodes at its black endpoint dots and three antinodes;
the arrow labelled `D` spans those endpoints. The density conversion is
`7.20 g/m = 9/1250 kg/m`, and `90.0 cm = 9/10 m`.

No wavelength, wave speed, or frequency value is included here.
-/
structure MatchesProblemAndPrimaryFigure
    (setup : GuitarStringStandingWaveSetup) : Prop where
  string_is_nylon : setup.stringMaterial = .nylon
  left_support_is_fixed :
    setup.endpointBoundary .leftSupport = .fixed
  right_support_is_fixed :
    setup.endpointBoundary .rightSupport = .fixed
  label_D_spans_supports :
    setup.figureLabelTarget .D = .betweenFixedSupports
  three_antinodes_are_drawn : setup.figureAntinodeCount = 3
  linear_density_kg_per_m :
    linearMassDensityInKilogramsPerMeter setup.linearMassDensity = 9 / 1250
  tension_newtons : forceInNewtons setup.tension = 150
  support_separation_meters :
    lengthInMeters setup.supportSeparationD = 9 / 10

/-- Positivity assumptions selecting the nondegenerate physical wave state. -/
structure HasPositiveWaveParameters
    (setup : GuitarStringStandingWaveSetup) : Prop where
  antinode_count_positive : 0 < setup.figureAntinodeCount
  support_separation_positive : 0 < lengthInMeters setup.supportSeparationD
  linear_density_positive :
    0 < linearMassDensityInKilogramsPerMeter setup.linearMassDensity
  tension_positive : 0 < forceInNewtons setup.tension
  wavelength_positive : 0 < lengthInMeters setup.wavelength
  wave_speed_positive : 0 < speedInMetersPerSecond setup.transverseWaveSpeed
  frequency_positive :
    0 < frequencyInHertz setup.componentTravelingWaveFrequency

/-! ## Governing standing-wave and string laws -/

/--
The general fixed-end geometry `n * lambda = 2 * D`, where `n` is the number
of half-wavelength loops. This law does not prescribe the three-loop mode.
-/
structure SatisfiesFixedEndStandingWaveGeometry
    (setup : GuitarStringStandingWaveSetup) : Prop where
  mode_geometry :
    (setup.figureAntinodeCount : ℝ) * lengthInMeters setup.wavelength =
      2 * lengthInMeters setup.supportSeparationD

/-- The nondispersive traveling-wave relation `v = f * lambda`. -/
structure SatisfiesTravelingWaveRelation
    (setup : GuitarStringStandingWaveSetup) : Prop where
  wave_relation :
    speedInMetersPerSecond setup.transverseWaveSpeed =
      frequencyInHertz setup.componentTravelingWaveFrequency *
        lengthInMeters setup.wavelength

/--
The transverse-wave law for a uniform taut string, in the homogeneous squared
form `T = mu * v^2` in coherent SI readouts.
-/
structure SatisfiesTautStringWaveSpeedLaw
    (setup : GuitarStringStandingWaveSetup) : Prop where
  tension_law :
    forceInNewtons setup.tension =
      linearMassDensityInKilogramsPerMeter setup.linearMassDensity *
        speedInMetersPerSecond setup.transverseWaveSpeed ^ 2

/-! ## Exact frequency and displayed answer -/

/--
The three-antinode geometry and taut-string laws determine the unrounded
component-wave frequency as `1250 * sqrt 3 / 9` hertz.
-/
lemma componentTravelingWaveFrequencyInHertz_eq_exact
    (setup : GuitarStringStandingWaveSetup)
    (_problem : MatchesProblemAndPrimaryFigure setup)
    (_positive : HasPositiveWaveParameters setup)
    (_standingWave : SatisfiesFixedEndStandingWaveGeometry setup)
    (_travelingWave : SatisfiesTravelingWaveRelation setup)
    (_tautString : SatisfiesTautStringWaveSpeedLaw setup) :
    frequencyInHertz setup.componentTravelingWaveFrequency =
      1250 * Real.sqrt 3 / 9 := by
  have hwavelength : lengthInMeters setup.wavelength = 3 / 5 := by
    have h := _standingWave.mode_geometry
    norm_num [_problem.three_antinodes_are_drawn,
      _problem.support_separation_meters] at h ⊢
    linarith
  have hspeed_sq :
      speedInMetersPerSecond setup.transverseWaveSpeed ^ 2 = 62500 / 3 := by
    have h := _tautString.tension_law
    norm_num [_problem.tension_newtons,
      _problem.linear_density_kg_per_m] at h ⊢
    nlinarith
  have htravel := _travelingWave.wave_relation
  rw [hwavelength] at htravel
  have hsqrt_sq : Real.sqrt (3 : ℝ) ^ 2 = 3 :=
    Real.sq_sqrt (by norm_num)
  have hsqrt_pos : 0 < Real.sqrt (3 : ℝ) :=
    Real.sqrt_pos.2 (by norm_num)
  nlinarith [_positive.frequency_positive]

/-- Labels of the four displayed answer choices. -/
inductive AnswerChoice where
  | A
  | B
  | C
  | D
  deriving DecidableEq, Repr

/-- Frequency in hertz printed beside each answer label. -/
def AnswerChoice.frequencyInHertz : AnswerChoice → ℝ
  | .A => 226
  | .B => 230
  | .C => 235
  | .D => 241

/-- The answer label recorded in the supplied dataset metadata. -/
def recordedAnswerChoice : AnswerChoice := .D

/--
A displayed whole-hertz answer matches the physical frequency when it lies
within half a hertz, corresponding to rounding to the nearest hertz.
-/
def MatchesAnswerChoice
    (frequency : FrequencyQuantity) (choice : AnswerChoice) : Prop :=
  |frequencyInHertz frequency - choice.frequencyInHertz| ≤ 1 / 2

/--
The traveling-wave frequency is approximately `240.56 Hz`, hence it matches
choice D, `241 Hz`, when rounded to the nearest hertz.
-/
theorem travelingWaveFrequency_matches_recordedAnswer
    (setup : GuitarStringStandingWaveSetup)
    (_problem : MatchesProblemAndPrimaryFigure setup)
    (_positive : HasPositiveWaveParameters setup)
    (_standingWave : SatisfiesFixedEndStandingWaveGeometry setup)
    (_travelingWave : SatisfiesTravelingWaveRelation setup)
    (_tautString : SatisfiesTautStringWaveSpeedLaw setup) :
    MatchesAnswerChoice setup.componentTravelingWaveFrequency
      recordedAnswerChoice := by
  unfold MatchesAnswerChoice
  rw [componentTravelingWaveFrequencyInHertz_eq_exact setup _problem _positive
    _standingWave _travelingWave _tautString]
  simp only [recordedAnswerChoice, AnswerChoice.frequencyInHertz]
  have hsqrt_sq : Real.sqrt (3 : ℝ) ^ 2 = 3 :=
    Real.sq_sqrt (by norm_num)
  have hsqrt_nonneg : 0 ≤ Real.sqrt (3 : ℝ) :=
    Real.sqrt_nonneg 3
  rw [abs_le]
  constructor <;> nlinarith

end PhyXMiniProblems.ProblemPhyXMini0295
