import Mathlib.Data.Real.Basic
import Physlib.Units.WithDim.Speed

/- USER: The assigned source file did not exist when this autoformalization task began. -/

/-!
# Wavelength in front of a moving police siren

A police-car siren emits a `300 Hz` sinusoidal wave while the car moves to the
right at `30 m/s` through still air.  The sound speed is `340 m/s`.  Successive
wavefronts in front of the source are therefore closer together than they
would be for a stationary source.

Frequencies, wavelengths, sound speed, and signed axial velocities carry their
physical dimensions through Physlib.  Real numbers occur only as readouts in
named SI units and as displayed answer values.  Positive axial velocity points
to the right in the primary figure.
-/

noncomputable section

namespace PhyXMiniProblems.ProblemPhyXMini0193

open Dimension

/-! ## Dimensionful acoustic quantities and SI readouts -/

/-- A nonnegative physical acoustic frequency, with inverse-time dimension. -/
abbrev AcousticFrequency : Type := Dimensionful (WithDim T𝓭⁻¹ NNReal)

/-- A nonnegative physical acoustic wavelength. -/
abbrev AcousticLength : Type := Dimensionful (WithDim L𝓭 NNReal)

/--
A signed velocity along the figure's horizontal axis.  This is distinct from
Physlib's unsigned `DimSpeed` because source and air motion have directions.
-/
abbrev AxialVelocity : Type :=
  Dimensionful (WithDim (L𝓭 * T𝓭⁻¹) ℝ)

/-- Read a physical acoustic frequency in hertz. -/
def frequencyInHertz (frequency : AcousticFrequency) : ℝ :=
  ((frequency UnitChoices.SI).val : ℝ)

/-- Read a physical wavelength in metres. -/
def lengthInMeters (length : AcousticLength) : ℝ :=
  ((length UnitChoices.SI).val : ℝ)

/-- Read Physlib's nonnegative physical speed in metres per second. -/
def speedInMetersPerSecond (speed : DimSpeed) : ℝ :=
  ((speed UnitChoices.SI).val : ℝ)

/-- Read a signed axial velocity in metres per second. -/
def axialVelocityInMetersPerSecond (velocity : AxialVelocity) : ℝ :=
  (velocity UnitChoices.SI).val

/-! ## Physical objects and primary-figure labels -/

/-- The police car depicted as carrying the source. -/
inductive VehicleLabel where
  | policeCar
  deriving DecidableEq, Repr

/-- The source label `S` printed above the siren in the primary figure. -/
inductive SoundSourceLabel where
  | S
  deriving DecidableEq, Repr

/-- The two sides of the moving source whose wavelengths are marked `?`. -/
inductive WaveRegion where
  | behind
  | inFront
  deriving DecidableEq, Repr

/-- The two orientations along the horizontal axis in the figure. -/
inductive AxialDirection where
  | left
  | right
  deriving DecidableEq, Repr

/-- The waveform type explicitly stated for the siren. -/
inductive WaveformKind where
  | sinusoidal
  deriving DecidableEq, Repr

/-!
The moving-source acoustic setup.

Both `wavelength .behind` and `wavelength .inFront` are unknown physical
lengths corresponding to the two question-mark labels in the figure.  In
particular, the requested front wavelength is not assigned a numerical value
by this structure.
-/
structure MovingPoliceSirenSetup where
  sourceCarrier : SoundSourceLabel → VehicleLabel
  emittedWaveform : SoundSourceLabel → WaveformKind
  emittedFrequency : SoundSourceLabel → AcousticFrequency
  soundSpeedInAir : DimSpeed
  sourceVelocity : SoundSourceLabel → AxialVelocity
  airVelocity : AxialVelocity
  sourceDirection : SoundSourceLabel → AxialDirection
  waveDirection : WaveRegion → AxialDirection
  wavelength : WaveRegion → AcousticLength

/-- The source velocity relative to the air, read in metres per second. -/
def sourceVelocityRelativeToAirInMetersPerSecond
    (setup : MovingPoliceSirenSetup) : ℝ :=
  axialVelocityInMetersPerSecond (setup.sourceVelocity .S) -
    axialVelocityInMetersPerSecond setup.airVelocity

/-!
Problem-text and primary-figure data.  The siren `S` is attached to the police
car, emits a `300 Hz` sinusoid, and moves rightward at `30 m/s`.  The air is
still, the sound speed is `340 m/s`, the front wave travels rightward, and the
behind wave travels leftward.  The drawing also depicts the front wavefronts
as more closely spaced than the wavefronts behind the car.

No numerical wavelength occurs in these data premises.
-/
structure MatchesProblemAndFigure (setup : MovingPoliceSirenSetup) : Prop where
  source_is_on_police_car : setup.sourceCarrier .S = .policeCar
  siren_is_sinusoidal : setup.emittedWaveform .S = .sinusoidal
  emitted_frequency_hertz : frequencyInHertz (setup.emittedFrequency .S) = 300
  sound_speed_meters_per_second :
    speedInMetersPerSecond setup.soundSpeedInAir = 340
  source_speed_meters_per_second :
    axialVelocityInMetersPerSecond (setup.sourceVelocity .S) = 30
  still_air : axialVelocityInMetersPerSecond setup.airVelocity = 0
  source_moves_right : setup.sourceDirection .S = .right
  front_wave_moves_right : setup.waveDirection .inFront = .right
  behind_wave_moves_left : setup.waveDirection .behind = .left
  front_wavefronts_are_compressed :
    lengthInMeters (setup.wavelength .inFront) <
      lengthInMeters (setup.wavelength .behind)

/-!
Positivity and subsonic assumptions selecting the physical branch in which
sound propagating in front of the car outruns the source.
-/
structure HasSubsonicPhysicalParameters
    (setup : MovingPoliceSirenSetup) : Prop where
  emitted_frequency_positive :
    0 < frequencyInHertz (setup.emittedFrequency .S)
  sound_speed_positive : 0 < speedInMetersPerSecond setup.soundSpeedInAir
  source_relative_speed_nonnegative :
    0 ≤ sourceVelocityRelativeToAirInMetersPerSecond setup
  source_is_subsonic :
    sourceVelocityRelativeToAirInMetersPerSecond setup <
      speedInMetersPerSecond setup.soundSpeedInAir
  wavelengths_positive : ∀ region,
    0 < lengthInMeters (setup.wavelength region)

/-!
The classical wavefront-spacing law for a source moving rightward through a
medium.  During one source period, a forward wavefront advances at the sound
speed while the source advances with its air-relative speed, whereas the
separation behind is enlarged by the same source displacement:

`lambda_front * f = c - v_source/air` and
`lambda_behind * f = c + v_source/air`.

These are governing relations among independent physical quantities; neither
field states the requested numerical front wavelength or an answer choice.
-/
structure SatisfiesMovingSourceWavefrontLaw
    (setup : MovingPoliceSirenSetup) : Prop where
  front_wavefront_spacing :
    lengthInMeters (setup.wavelength .inFront) *
        frequencyInHertz (setup.emittedFrequency .S) =
      speedInMetersPerSecond setup.soundSpeedInAir -
        sourceVelocityRelativeToAirInMetersPerSecond setup
  behind_wavefront_spacing :
    lengthInMeters (setup.wavelength .behind) *
        frequencyInHertz (setup.emittedFrequency .S) =
      speedInMetersPerSecond setup.soundSpeedInAir +
        sourceVelocityRelativeToAirInMetersPerSecond setup

/-! ## Derived wavelength relation and displayed answers -/

/--
The general forward-wavelength formula derived from the wavefront-spacing law.
It still depends on the setup's independent frequency, sound speed, and
air-relative source velocity and therefore contains no numerical answer.
-/
lemma frontWavelength_formula
    (setup : MovingPoliceSirenSetup)
    (_physical : HasSubsonicPhysicalParameters setup)
    (_wavefrontLaw : SatisfiesMovingSourceWavefrontLaw setup) :
    lengthInMeters (setup.wavelength .inFront) =
      (speedInMetersPerSecond setup.soundSpeedInAir -
          sourceVelocityRelativeToAirInMetersPerSecond setup) /
        frequencyInHertz (setup.emittedFrequency .S) := by
  apply (eq_div_iff (ne_of_gt _physical.emitted_frequency_positive)).2
  exact _wavefrontLaw.front_wavefront_spacing

/-- Labels of the four answers printed with the problem. -/
inductive AnswerChoice where
  | A
  | B
  | C
  | D
  deriving DecidableEq, Repr

/-- Metre readout printed beside each displayed answer label. -/
def AnswerChoice.meters : AnswerChoice → ℝ
  | .A => 103 / 100
  | .B => 124 / 100
  | .C => 206 / 100
  | .D => 232 / 100

/-!
A wavelength agrees with a displayed answer to the nearest hundredth of a
metre.  The half-increment tolerance is `0.005 m`.
-/
def MatchesAnswerChoice
    (wavelength : AcousticLength) (choice : AnswerChoice) : Prop :=
  |lengthInMeters wavelength - choice.meters| ≤ 1 / 200

/-- The answer label recorded by the supplied dataset. -/
def recordedAnswerChoice : AnswerChoice := .A

/-!
The wavefront law and stated readouts give
`lambda_front = (340 - 30) / 300 = 31/30 m`, which rounds to `1.03 m`,
recorded answer A.

This formalizes blueprint label `thm:physics:phyx_mini_0193:target`.
-/
theorem frontWavelength_matches_recordedAnswerA
    (setup : MovingPoliceSirenSetup)
    (_problem : MatchesProblemAndFigure setup)
    (_physical : HasSubsonicPhysicalParameters setup)
    (_wavefrontLaw : SatisfiesMovingSourceWavefrontLaw setup) :
    lengthInMeters (setup.wavelength .inFront) = (31 : ℝ) / 30 ∧
      MatchesAnswerChoice (setup.wavelength .inFront) recordedAnswerChoice := by
  have hrelative :
      sourceVelocityRelativeToAirInMetersPerSecond setup = 30 := by
    simp [sourceVelocityRelativeToAirInMetersPerSecond,
      _problem.source_speed_meters_per_second, _problem.still_air]
  have hfront := frontWavelength_formula setup _physical _wavefrontLaw
  norm_num [_problem.sound_speed_meters_per_second, hrelative,
    _problem.emitted_frequency_hertz] at hfront
  refine ⟨hfront, ?_⟩
  norm_num [MatchesAnswerChoice, recordedAnswerChoice, AnswerChoice.meters,
    hfront, abs_of_nonneg]

end PhyXMiniProblems.ProblemPhyXMini0193
