import Mathlib
import Physlib.Units.WithDim.Speed

/-!
# Frequency heard from a receding police-car siren

This file formalizes problem `phyx_mini_0196`.  The primary figure places the
listener `L` to the left of the siren source `S` and declares the direction
from `L` to `S` positive.  Both move in that positive direction relative to
the air: the listener at `15 m/s` and the source at `45 m/s`.  Thus the
listener moves toward the source while the faster source recedes.

Frequency, position, velocity, and sound speed retain their physical
dimensions through Physlib.  Real numbers below occur only as named-unit
readouts, dimensionless ratios, or whole-hertz answer-table values.

Assumption/target split:

* `MatchesPrimaryFigure` records the labeled geometry and velocity readouts;
* `UsesPriorSirenCalibration` records the shared exercise calibration;
* `HasSubsonicPhysicalParameters` selects the physical branch;
* `SatisfiesLeftwardAcousticDopplerLaw` states the governing Doppler law;
* `heardFrequency_matches_recordedChoiceB` is the requested conclusion.
-/

noncomputable section

namespace PhyXMiniProblems.ProblemPhyXMini0196

open Dimension

/-! ## Dimensionful acoustic quantities and named SI readouts -/

/-- A physical acoustic frequency, carrying inverse-time dimension. -/
abbrev AcousticFrequency : Type :=
  Dimensionful (WithDim T𝓭⁻¹ NNReal)

/-- A signed physical coordinate along the horizontal road axis. -/
abbrev AxialPosition : Type :=
  Dimensionful (WithDim L𝓭 ℝ)

/--
A signed physical velocity along the road axis.  A signed quantity is used
instead of Physlib's unsigned `DimSpeed` so that the figure's positive
direction and the participants' directions of motion remain explicit.
-/
abbrev AxialVelocity : Type :=
  Dimensionful (WithDim (L𝓭 * T𝓭⁻¹) ℝ)

/-- Read a physical acoustic frequency in inverse units of a chosen time unit. -/
def frequencyReadout
    (unit : TimeUnit) (frequency : AcousticFrequency) : ℝ :=
  ((frequency {UnitChoices.SI with time := unit}).val : ℝ)

/-- Hertz readout of an acoustic frequency. -/
def frequencyInHertz (frequency : AcousticFrequency) : ℝ :=
  frequencyReadout TimeUnit.seconds frequency

/-- Read a signed physical position in a chosen length unit. -/
def positionReadout
    (unit : LengthUnit) (position : AxialPosition) : ℝ :=
  (position {UnitChoices.SI with length := unit}).val

/-- Metre readout of a signed axial position. -/
def positionInMeters (position : AxialPosition) : ℝ :=
  positionReadout LengthUnit.meters position

/-- Read a signed axial velocity in selected length and time units. -/
def axialVelocityReadout
    (lengthUnit : LengthUnit) (timeUnit : TimeUnit)
    (velocity : AxialVelocity) : ℝ :=
  (velocity {UnitChoices.SI with
    length := lengthUnit, time := timeUnit}).val

/-- Metres-per-second readout of a signed air-relative axial velocity. -/
def axialVelocityInMetersPerSecond (velocity : AxialVelocity) : ℝ :=
  axialVelocityReadout LengthUnit.meters TimeUnit.seconds velocity

/-- Read Physlib's unsigned physical speed in metres per second. -/
def speedInMetersPerSecond (speed : DimSpeed) : ℝ :=
  ((speed UnitChoices.SI).val : ℝ)

/-! ## Physical objects and primary-figure labels -/

/-- The two labeled participants in the primary figure. -/
inductive Participant where
  | listenerL
  | sirenSourceS
  deriving DecidableEq, Repr

/-- The two orientations along the depicted one-dimensional road. -/
inductive RoadDirection where
  | listenerToSource
  | sourceToListener
  deriving DecidableEq, Repr

/-- The waveform classification inherited from the siren exercise context. -/
inductive WaveformKind where
  | sinusoidal
  deriving DecidableEq, Repr

/--
The physical apparatus and observables needed for the one-dimensional
acoustic Doppler model.  `heardFrequency` is an unknown physical observable;
the structure does not assign it a numerical value or answer choice.
-/
structure SirenListenerDopplerSetup where
  axialPosition : Participant → AxialPosition
  /-- Velocity of each participant relative to the air. -/
  velocityRelativeToAir : Participant → AxialVelocity
  positiveRoadDirection : RoadDirection
  soundPropagationDirection : RoadDirection
  emittedWaveform : WaveformKind
  emittedFrequency : AcousticFrequency
  soundSpeedInAir : DimSpeed
  heardFrequency : AcousticFrequency

/-!
Primary-image geometry and readouts.  The listener `L` lies to the left of
source `S`; the arrow from `L` to `S` is positive; the sound reaching `L`
travels in the reverse direction; and the air-relative velocities are
`v_L = 15 m/s` and `v_S = 45 m/s`.

No readout of the requested heard frequency occurs here.
-/
def MatchesPrimaryFigure (setup : SirenListenerDopplerSetup) : Prop :=
  positionInMeters (setup.axialPosition .listenerL) <
      positionInMeters (setup.axialPosition .sirenSourceS) ∧
    setup.positiveRoadDirection = .listenerToSource ∧
    setup.soundPropagationDirection = .sourceToListener ∧
    axialVelocityInMetersPerSecond
        (setup.velocityRelativeToAir .listenerL) = 15 ∧
    axialVelocityInMetersPerSecond
        (setup.velocityRelativeToAir .sirenSourceS) = 45

/-!
The shared calibration from source panel 193 of the same police-siren
sequence: the siren emits a `300 Hz` sinusoid and sound travels through the
air at `340 m/s`.  These data are separated from the current panel's figure
readouts because they are not reprinted in the assigned image.

This premise contains no heard-frequency or answer-choice conclusion.
-/
def UsesPriorSirenCalibration (setup : SirenListenerDopplerSetup) : Prop :=
  setup.emittedWaveform = .sinusoidal ∧
    frequencyInHertz setup.emittedFrequency = 300 ∧
    speedInMetersPerSecond setup.soundSpeedInAir = 340

/--
Positivity and subsonic hypotheses selecting the ordinary acoustic branch and
ensuring the Doppler denominator is nonzero.
-/
def HasSubsonicPhysicalParameters
    (setup : SirenListenerDopplerSetup) : Prop :=
  0 < frequencyInHertz setup.emittedFrequency ∧
    0 < speedInMetersPerSecond setup.soundSpeedInAir ∧
    |axialVelocityInMetersPerSecond
        (setup.velocityRelativeToAir .listenerL)| <
      speedInMetersPerSecond setup.soundSpeedInAir ∧
    |axialVelocityInMetersPerSecond
        (setup.velocityRelativeToAir .sirenSourceS)| <
      speedInMetersPerSecond setup.soundSpeedInAir

/-!
The classical one-dimensional Doppler law for a wave travelling from `S` to
`L`, opposite the positive `L`-to-`S` road direction.  Both velocities are
measured relative to the air, so positive listener velocity raises the
encounter rate while positive source velocity lengthens the trailing
wavelength.  This is a general governing relation and contains no displayed
answer value.
-/
structure SatisfiesLeftwardAcousticDopplerLaw
    (setup : SirenListenerDopplerSetup) : Prop where
  frequencyLaw :
    setup.soundPropagationDirection = .sourceToListener →
      frequencyInHertz setup.heardFrequency =
        frequencyInHertz setup.emittedFrequency *
          (speedInMetersPerSecond setup.soundSpeedInAir +
            axialVelocityInMetersPerSecond
              (setup.velocityRelativeToAir .listenerL)) /
          (speedInMetersPerSecond setup.soundSpeedInAir +
            axialVelocityInMetersPerSecond
              (setup.velocityRelativeToAir .sirenSourceS))

/-! ## Displayed answers and formalization target -/

/-- Labels of the four answers printed with the problem. -/
inductive AnswerChoice where
  | A
  | B
  | C
  | D
  deriving DecidableEq, Repr

/-- Whole-hertz frequency printed beside each answer label. -/
def AnswerChoice.hertz : AnswerChoice → ℝ
  | .A => 267
  | .B => 277
  | .C => 274
  | .D => 268

/-- The answer label recorded in the supplied dataset metadata. -/
def recordedDatasetAnswer : AnswerChoice := .B

/--
Agreement with a displayed whole-hertz answer.  A half-hertz tolerance models
rounding to the nearest integer without identifying the physical frequency
itself with an exact integer.
-/
def MatchesAnswerChoice
    (frequency : AcousticFrequency) (choice : AnswerChoice) : Prop :=
  |frequencyInHertz frequency - choice.hertz| ≤ 1 / 2

/-!
Substitution of the figure and calibration readouts into the governing law.
The exact ratio is a derived conclusion, not a setup field or premise.
-/
lemma heardFrequency_hertz_eq_calibratedRatio
    (setup : SirenListenerDopplerSetup)
    (h_figure : MatchesPrimaryFigure setup)
    (h_calibration : UsesPriorSirenCalibration setup)
    (h_physical : HasSubsonicPhysicalParameters setup)
    (h_doppler : SatisfiesLeftwardAcousticDopplerLaw setup) :
    frequencyInHertz setup.heardFrequency =
      300 * (340 + 15) / (340 + 45) := by
  rcases h_figure with ⟨_, _, hprop, hvL, hvS⟩
  rcases h_calibration with ⟨_, hf, hc⟩
  simpa only [hf, hc, hvL, hvS] using h_doppler.frequencyLaw hprop

/-!
The listener's physical heard frequency rounds to recorded answer B,
`277 Hz`.

This formalizes `thm:physics:phyx_mini_0196:target`.
-/
theorem heardFrequency_matches_recordedChoiceB
    (setup : SirenListenerDopplerSetup)
    (h_figure : MatchesPrimaryFigure setup)
    (h_calibration : UsesPriorSirenCalibration setup)
    (h_physical : HasSubsonicPhysicalParameters setup)
    (h_doppler : SatisfiesLeftwardAcousticDopplerLaw setup) :
    MatchesAnswerChoice setup.heardFrequency recordedDatasetAnswer := by
  unfold MatchesAnswerChoice recordedDatasetAnswer AnswerChoice.hertz
  rw [heardFrequency_hertz_eq_calibratedRatio setup h_figure h_calibration
    h_physical h_doppler]
  norm_num [abs_of_nonpos]

end PhyXMiniProblems.ProblemPhyXMini0196
