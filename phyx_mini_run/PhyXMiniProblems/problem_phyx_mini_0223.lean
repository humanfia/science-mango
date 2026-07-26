import Mathlib
import Physlib.Units.WithDim.Speed

noncomputable section

namespace PhyXMiniProblems.ProblemPhyXMini0223

open Dimension

/-!
# Successive resonances of a water-closed air column

A tuning fork is held above the open top of a vertical tube.  The water
surface closes the lower end of the air column and is allowed to fall slowly.
The primary image labels the first resonant air-column length as `0.125 m` and
the next one, at the dashed lower water level, as `0.395 m`.

Lengths, cyclic frequency, and propagation speed are genuine dimensionful
Physlib quantities.  Real numbers are used only for coherent SI readouts and
dimensionless mode numbers.  A single opening-end correction is included in
both resonance equations: without it, treating the displayed `0.125 m` as an
exact quarter wavelength would be inconsistent with the measured spacing.
-/

/-! ## Dimensionful physical quantities and SI readouts -/

/-- A physical length, represented coherently in every choice of units. -/
abbrev LengthQuantity : Type := Dimensionful (WithDim L𝓭 NNReal)

/-- A physical cyclic frequency, carrying the inverse-time dimension. -/
abbrev FrequencyQuantity : Type := Dimensionful (WithDim T𝓭⁻¹ NNReal)

/-- A physical propagation speed. -/
abbrev SpeedQuantity : Type := DimSpeed

/-- Metre readout of a physical length. -/
def lengthInMeters (length : LengthQuantity) : ℝ :=
  ((length UnitChoices.SI).val : ℝ)

/-- Hertz readout (cycles per SI second) of a physical cyclic frequency. -/
def frequencyInHertz (frequency : FrequencyQuantity) : ℝ :=
  ((frequency UnitChoices.SI).val : ℝ)

/-- Metres-per-second readout of a physical propagation speed. -/
def speedInMetersPerSecond (speed : SpeedQuantity) : ℝ :=
  ((speed UnitChoices.SI).val : ℝ)

/-! ## Figure labels and physical setup -/

/-- The two resonances encountered as the water level falls. -/
inductive ResonanceObservation where
  | first
  | second
  deriving DecidableEq, Repr

/-- The two boundaries of the resonating air column. -/
inductive AirColumnBoundary where
  | upper
  | lower
  deriving DecidableEq, Repr

/-- Physical kind of an air-column boundary. -/
inductive BoundaryKind where
  | openToAtmosphere
  | closedByWater
  deriving DecidableEq, Repr

/-- Displacement behavior of the acoustic standing wave at a boundary. -/
inductive DisplacementBoundaryBehavior where
  | node
  | antinode
  deriving DecidableEq, Repr

/-- Orientation of the cylindrical tube in the source image. -/
inductive TubeOrientation where
  | vertical
  | horizontal
  deriving DecidableEq, Repr

/-- Position of the tuning fork relative to the tube. -/
inductive ForkPosition where
  | aboveOpening
  | besideTube
  deriving DecidableEq, Repr

/-- The solid and dashed water-level marks visible in the figure. -/
inductive WaterLevelMarker where
  | solid
  | dashed
  deriving DecidableEq, Repr

/-- The slow motion of the water level described in the scenario. -/
inductive WaterLevelMotion where
  | fallingSlowly
  | stationary
  deriving DecidableEq, Repr

/-!
The physical quantities and labeled geometry of the tuning-fork experiment.

`openingEndCorrection` is the common correction added to each measured
geometrical air-column length.  `resonanceModeIndex = n` labels the closed-open
mode whose effective length is `(2n+1) λ/4`.  No field fixes the requested
frequency or selects an answer choice.
-/
structure TuningForkTubeSetup where
  tuningForkFrequency : FrequencyQuantity
  soundWavelength : LengthQuantity
  soundSpeedInAir : SpeedQuantity
  openingEndCorrection : LengthQuantity
  airColumnLength : ResonanceObservation → LengthQuantity
  resonanceModeIndex : ResonanceObservation → ℕ
  boundaryKind : AirColumnBoundary → BoundaryKind
  displacementBehavior :
    AirColumnBoundary → DisplacementBoundaryBehavior
  tubeOrientation : TubeOrientation
  tuningForkPosition : ForkPosition
  waterLevelMarker : ResonanceObservation → WaterLevelMarker
  waterLevelMotion : WaterLevelMotion

/-!
Problem-statement and primary-image readouts.  The solid water level gives the
shorter `0.125 m` air column, and the dashed lower level gives the later
`0.395 m` air column.  The wording "and again" while the level falls is modeled
as consecutive closed-open resonance modes.

These data contain no frequency value and no answer label.
-/
structure MatchesProblemAndFigureData (setup : TuningForkTubeSetup) : Prop where
  first_air_column_length_meters :
    lengthInMeters (setup.airColumnLength .first) = (1 : ℝ) / 8
  second_air_column_length_meters :
    lengthInMeters (setup.airColumnLength .second) = (79 : ℝ) / 200
  successive_mode_numbers :
    setup.resonanceModeIndex .second =
      setup.resonanceModeIndex .first + 1
  upper_end_open_to_atmosphere :
    setup.boundaryKind .upper = .openToAtmosphere
  lower_end_closed_by_water :
    setup.boundaryKind .lower = .closedByWater
  tube_is_vertical : setup.tubeOrientation = .vertical
  fork_is_above_opening : setup.tuningForkPosition = .aboveOpening
  first_level_is_solid_mark : setup.waterLevelMarker .first = .solid
  second_level_is_dashed_mark : setup.waterLevelMarker .second = .dashed
  level_falls_slowly : setup.waterLevelMotion = .fallingSlowly

/-!
The standard room-condition sound-speed calibration used by the multiple
choice problem.  This is an external calibrated physical parameter, not the
requested tuning-fork frequency.
-/
structure HasStandardAirSoundSpeed (setup : TuningForkTubeSetup) : Prop where
  sound_speed_meters_per_second :
    speedInMetersPerSecond setup.soundSpeedInAir = 343

/-- Positivity conditions selecting the physical wave branch. -/
structure HasPhysicalWaveParameters (setup : TuningForkTubeSetup) : Prop where
  frequency_positive : 0 < frequencyInHertz setup.tuningForkFrequency
  wavelength_positive : 0 < lengthInMeters setup.soundWavelength
  sound_speed_positive : 0 < speedInMetersPerSecond setup.soundSpeedInAir

/-!
Governing laws for a tube open to the atmosphere at its top and effectively
closed by the water surface below.

At an open end, air displacement has an antinode; at the water surface it has
a node.  Each resonant effective length is an odd quarter wavelength.  The
last field is the nondispersive acoustic relation `v = f λ`, expressed in
coherent SI readouts.  These are general physical laws and do not state the
requested numerical frequency or an answer choice.
-/
structure SatisfiesClosedOpenAirColumnLaws
    (setup : TuningForkTubeSetup) : Prop where
  open_end_is_displacement_antinode :
    setup.displacementBehavior .upper = .antinode
  water_surface_is_displacement_node :
    setup.displacementBehavior .lower = .node
  odd_quarter_wave_resonance :
    ∀ observation : ResonanceObservation,
      lengthInMeters (setup.airColumnLength observation) +
          lengthInMeters setup.openingEndCorrection =
        ((2 * (setup.resonanceModeIndex observation : ℝ) + 1) *
            lengthInMeters setup.soundWavelength) / 4
  wave_speed_frequency_wavelength :
    speedInMetersPerSecond setup.soundSpeedInAir =
      frequencyInHertz setup.tuningForkFrequency *
        lengthInMeters setup.soundWavelength

/-! ## Consequences of the physical model -/

/--
Successive closed-open resonances are separated by half a wavelength.  The
common opening-end correction cancels when their effective lengths are
subtracted.
-/
lemma successiveResonanceSpacing
    (setup : TuningForkTubeSetup)
    (_data : MatchesProblemAndFigureData setup)
    (_laws : SatisfiesClosedOpenAirColumnLaws setup) :
    lengthInMeters (setup.airColumnLength .second) -
        lengthInMeters (setup.airColumnLength .first) =
      lengthInMeters setup.soundWavelength / 2 := by
  have hfirst := _laws.odd_quarter_wave_resonance .first
  have hsecond := _laws.odd_quarter_wave_resonance .second
  rw [_data.successive_mode_numbers] at hsecond
  norm_num [Nat.cast_add, Nat.cast_one] at hsecond
  nlinarith [hfirst, hsecond]

/-- The two measured resonance positions determine `λ = 0.540 m`. -/
lemma soundWavelength_meters_eq
    (setup : TuningForkTubeSetup)
    (_data : MatchesProblemAndFigureData setup)
    (_laws : SatisfiesClosedOpenAirColumnLaws setup) :
    lengthInMeters setup.soundWavelength = (27 : ℝ) / 50 := by
  have hspacing := successiveResonanceSpacing setup _data _laws
  rw [_data.first_air_column_length_meters,
    _data.second_air_column_length_meters] at hspacing
  norm_num at hspacing ⊢
  linarith

/-!
With sound speed `343 m/s`, the inferred cyclic frequency is exactly
`17150/27 Hz`, approximately `635.185 Hz`.
-/
lemma tuningForkFrequency_hertz_eq
    (setup : TuningForkTubeSetup)
    (_data : MatchesProblemAndFigureData setup)
    (_calibration : HasStandardAirSoundSpeed setup)
    (_physical : HasPhysicalWaveParameters setup)
    (_laws : SatisfiesClosedOpenAirColumnLaws setup) :
    frequencyInHertz setup.tuningForkFrequency = (17150 : ℝ) / 27 := by
  have hwave := _laws.wave_speed_frequency_wavelength
  rw [_calibration.sound_speed_meters_per_second,
    soundWavelength_meters_eq setup _data _laws] at hwave
  norm_num at hwave ⊢
  linarith

/-! ## Displayed answer choices and final target -/

/-- Labels of the four answers printed in the dataset item. -/
inductive AnswerChoice where
  | A
  | B
  | C
  | D
  deriving DecidableEq, Repr

/-- Frequency in hertz displayed beside each answer label. -/
def AnswerChoice.hertz : AnswerChoice → ℝ
  | .A => 615
  | .B => 675
  | .C => 655
  | .D => 635

/-- The answer label recorded in the supplied dataset metadata. -/
def recordedAnswerChoice : AnswerChoice := .D

/-!
Agreement with a whole-hertz displayed answer.  The half-hertz interval
expresses rounding to the nearest hertz rather than falsely identifying the
derived `17150/27 Hz` with the integer `635 Hz`.
-/
def MatchesAnswerChoice
    (frequency : FrequencyQuantity) (choice : AnswerChoice) : Prop :=
  |frequencyInHertz frequency - choice.hertz| ≤ (1 : ℝ) / 2

/--
The spacing between the `0.125 m` and `0.395 m` resonances gives wavelength
`0.540 m`.  Combining this with `v = fλ` and `v = 343 m/s` gives a frequency
that rounds to `635 Hz`, answer D.

This formalizes `thm:physics:phyx_mini_0223:target`.
-/
theorem problem_phyx_mini_0223
    (setup : TuningForkTubeSetup)
    (_data : MatchesProblemAndFigureData setup)
    (_calibration : HasStandardAirSoundSpeed setup)
    (_physical : HasPhysicalWaveParameters setup)
    (_laws : SatisfiesClosedOpenAirColumnLaws setup) :
    MatchesAnswerChoice setup.tuningForkFrequency recordedAnswerChoice := by
  unfold MatchesAnswerChoice recordedAnswerChoice
  rw [tuningForkFrequency_hertz_eq setup _data _calibration _physical _laws]
  norm_num [AnswerChoice.hertz, abs_of_nonneg]

end PhyXMiniProblems.ProblemPhyXMini0223
