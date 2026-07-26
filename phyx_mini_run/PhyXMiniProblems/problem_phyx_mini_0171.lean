import Mathlib
import Physlib.Units.WithDim.Speed

/-!
# Doppler shift from train whistle A

This file models problem `phyx_mini_0171`.  Two train whistles `A` and `B`
emit the same nominal frequency.  The listener lies between them and moves to
the right, away from stationary whistle `A`.  The requested quantity is the
frequency of `A` heard by that listener.

Frequencies, positions, propagation speed, and signed axial velocities carry
their physical dimensions through Physlib.  Real numbers occur only as
readouts in named units and as displayed answer values.  Positive signed
velocity denotes motion to the right in the one-dimensional model.
-/

noncomputable section

namespace PhyXMiniProblems.ProblemPhyXMini0171

open Dimension

/-! ## Dimensionful quantities and SI readouts -/

/-- A physical acoustic frequency, carrying the inverse-time dimension. -/
abbrev AcousticFrequency : Type := Dimensionful (WithDim T𝓭⁻¹ NNReal)

/-- A signed physical coordinate along the horizontal track axis. -/
abbrev AxialPosition : Type := Dimensionful (WithDim L𝓭 ℝ)

/--
A signed physical velocity along the track axis.  Physlib's `DimSpeed` is
unsigned, so a signed quantity is needed to distinguish leftward and rightward
motion and to express velocities relative to the air.
-/
abbrev AxialVelocity : Type :=
  Dimensionful (WithDim (L𝓭 * T𝓭⁻¹) ℝ)

/-- Read a physical frequency in inverse units of the chosen time unit. -/
def frequencyReadout
    (unit : TimeUnit) (frequency : AcousticFrequency) : ℝ :=
  ((frequency {UnitChoices.SI with time := unit}).val : ℝ)

/-- Hertz readout of an acoustic frequency. -/
def frequencyInHertz (frequency : AcousticFrequency) : ℝ :=
  frequencyReadout TimeUnit.seconds frequency

/-- Read a signed axial position in the chosen length unit. -/
def positionReadout (unit : LengthUnit) (position : AxialPosition) : ℝ :=
  (position {UnitChoices.SI with length := unit}).val

/-- Metre readout of an axial position. -/
def positionInMeters (position : AxialPosition) : ℝ :=
  positionReadout LengthUnit.meters position

/--
Read a signed axial velocity in the selected length and time units.  Positive
values point to the right in the primary figure.
-/
def axialVelocityReadout
    (lengthUnit : LengthUnit) (timeUnit : TimeUnit)
    (velocity : AxialVelocity) : ℝ :=
  (velocity {UnitChoices.SI with
    length := lengthUnit, time := timeUnit}).val

/-- Metres-per-second readout of a signed axial velocity. -/
def axialVelocityInMetersPerSecond (velocity : AxialVelocity) : ℝ :=
  axialVelocityReadout LengthUnit.meters TimeUnit.seconds velocity

/-- Read Physlib's unsigned dimensionful speed in metres per second. -/
def speedInMetersPerSecond (speed : DimSpeed) : ℝ :=
  ((speed UnitChoices.SI).val : ℝ)

/-! ## Physical objects and primary-figure labels -/

/-- The two train whistles named in the problem and primary figure. -/
inductive WhistleLabel where
  | A
  | B
  deriving DecidableEq, Repr

/-- The two orientations along the horizontal track axis. -/
inductive AxialDirection where
  | left
  | right
  deriving DecidableEq, Repr

/--
The dimensionful quantities and labels in the two-train whistle experiment.

The two drawn parallel tracks are idealized by their common horizontal axis.
The field `heardFrequencyFromA` is an unknown measured physical frequency; no
field assigns it a numerical answer.
-/
structure TwoTrainWhistleSetup where
  whistlePosition : WhistleLabel → AxialPosition
  whistleVelocity : WhistleLabel → AxialVelocity
  emittedFrequency : WhistleLabel → AcousticFrequency
  listenerPosition : AxialPosition
  listenerVelocity : AxialVelocity
  listenerFacing : AxialDirection
  airVelocity : AxialVelocity
  soundSpeedInAir : DimSpeed
  soundFromADirection : AxialDirection
  heardFrequencyFromA : AcousticFrequency

/-!
The numerical and geometric readouts stated by the problem and shown in the
primary figure.  The listener is between `A` and `B`; both whistles emit
`392 Hz`; `A` is stationary; the listener and `B` move rightward at `15 m/s`
and `35 m/s`; and no wind means that the air is stationary in this frame.

This predicate records setup data only.  It gives no readout for the requested
frequency `heardFrequencyFromA`.
-/
def MatchesProblemAndFigure (setup : TwoTrainWhistleSetup) : Prop :=
  positionInMeters (setup.whistlePosition .A) <
      positionInMeters setup.listenerPosition ∧
    positionInMeters setup.listenerPosition <
      positionInMeters (setup.whistlePosition .B) ∧
    frequencyInHertz (setup.emittedFrequency .A) = 392 ∧
    frequencyInHertz (setup.emittedFrequency .B) = 392 ∧
    axialVelocityInMetersPerSecond (setup.whistleVelocity .A) = 0 ∧
    axialVelocityInMetersPerSecond setup.listenerVelocity = 15 ∧
    axialVelocityInMetersPerSecond (setup.whistleVelocity .B) = 35 ∧
    axialVelocityInMetersPerSecond setup.airVelocity = 0 ∧
    setup.soundFromADirection = .right ∧
    setup.listenerFacing = .right

/-!
The conventional room-temperature air calibration `c = 343 m/s` used to
evaluate the whole-hertz answer choices.  The problem source does not print a
sound speed, so this standard auxiliary datum is kept separate from the figure
and from the Doppler law.
-/
def UsesStandardAirSoundSpeed (setup : TwoTrainWhistleSetup) : Prop :=
  speedInMetersPerSecond setup.soundSpeedInAir = 343

/--
Positivity and subsonic conditions for the source, observer, and sound wave.
Velocities are compared relative to the air so that the Doppler denominator
is nonzero and the rightward wave overtakes the listener.
-/
def HasSubsonicPhysicalParameters (setup : TwoTrainWhistleSetup) : Prop :=
  0 < frequencyInHertz (setup.emittedFrequency .A) ∧
    0 < frequencyInHertz (setup.emittedFrequency .B) ∧
    0 < speedInMetersPerSecond setup.soundSpeedInAir ∧
    |axialVelocityInMetersPerSecond setup.listenerVelocity -
        axialVelocityInMetersPerSecond setup.airVelocity| <
      speedInMetersPerSecond setup.soundSpeedInAir ∧
    |axialVelocityInMetersPerSecond (setup.whistleVelocity .A) -
        axialVelocityInMetersPerSecond setup.airVelocity| <
      speedInMetersPerSecond setup.soundSpeedInAir

/-!
The one-dimensional classical Doppler law for sound travelling to the right.
Both source and listener velocities are measured relative to the air.  This is
a governing physical relation: it does not assert any displayed answer value.
-/
structure SatisfiesRightwardAcousticDopplerLaw
    (setup : TwoTrainWhistleSetup) : Prop where
  frequencyLaw :
    frequencyInHertz setup.heardFrequencyFromA =
      frequencyInHertz (setup.emittedFrequency .A) *
        (speedInMetersPerSecond setup.soundSpeedInAir -
          (axialVelocityInMetersPerSecond setup.listenerVelocity -
            axialVelocityInMetersPerSecond setup.airVelocity)) /
        (speedInMetersPerSecond setup.soundSpeedInAir -
          (axialVelocityInMetersPerSecond (setup.whistleVelocity .A) -
            axialVelocityInMetersPerSecond setup.airVelocity))

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
  | .A => 375
  | .B => 380
  | .C => 896
  | .D => 385

/--
Agreement with a displayed whole-hertz answer.  A half-hertz tolerance models
rounding to the nearest integer rather than replacing the physical frequency
by an exact integer.
-/
def MatchesAnswerChoice
    (frequency : AcousticFrequency) (choice : AnswerChoice) : Prop :=
  |frequencyInHertz frequency - choice.hertz| ≤ 1 / 2

/-- The answer label recorded in the supplied dataset metadata. -/
def recordedAnswerChoice : AnswerChoice := .A

/--
The frequency heard from stationary whistle `A` agrees, to the precision of
the displayed whole-hertz answers, with recorded answer A (`375 Hz`).

This formalizes `thm:physics:phyx_mini_0171:target`.
-/
theorem frequencyFromA_matches_recordedAnswerA
    (setup : TwoTrainWhistleSetup)
    (h_problem : MatchesProblemAndFigure setup)
    (h_air : UsesStandardAirSoundSpeed setup)
    (h_physical : HasSubsonicPhysicalParameters setup)
    (h_doppler : SatisfiesRightwardAcousticDopplerLaw setup) :
    MatchesAnswerChoice setup.heardFrequencyFromA recordedAnswerChoice := by
  simp only [MatchesAnswerChoice, recordedAnswerChoice, AnswerChoice.hertz]
  rw [h_doppler.frequencyLaw]
  rcases h_problem with
    ⟨hposA, hposB, h_emitA, h_emitB, h_vA, h_vL, h_vB, h_vair, h_wave, h_facing⟩
  rw [h_emitA, h_air, h_vL, h_vair, h_vA]
  norm_num [abs_le]

end PhyXMiniProblems.ProblemPhyXMini0171
