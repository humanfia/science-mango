import Mathlib
import Physlib.Units.WithDim.Speed

/-!
# Receding police-siren Doppler shift

This file models problem `phyx_mini_0194`.  The primary figure places the
stationary listener `L` to the left of police-car siren `S`; the positive
`L`-to-`S` axis points right, and `S` moves right at `30 m/s`, away from the
listener.  Sound reaching `L` therefore propagates in the opposite axial
direction.

Frequency, position, sound speed, and signed axial velocity retain their
physical dimensions through Physlib.  Real numbers occur only as readouts in
named SI units and as the whole-hertz values printed in the answer table.

The supplied text and bitmap omit the emitted siren frequency.  To make the
recorded numerical answer well-posed, the nominal `300 Hz` emission used by
the answer table is represented below by a separate calibration predicate;
it is not treated as a figure readout or as the requested conclusion.
-/

noncomputable section

namespace PhyXMiniProblems.ProblemPhyXMini0194

open Dimension

/-! ## Dimensionful quantities and named-unit readouts -/

/-- A nonnegative physical acoustic frequency, with inverse-time dimension. -/
abbrev AcousticFrequency : Type :=
  Dimensionful (WithDim T𝓭⁻¹ NNReal)

/-- A signed physical coordinate along the horizontal `L`-to-`S` axis. -/
abbrev AxialPosition : Type :=
  Dimensionful (WithDim L𝓭 ℝ)

/--
A signed physical velocity along the horizontal axis.  Positive velocity
points from listener `L` toward source `S` in the primary figure.
-/
abbrev AxialVelocity : Type :=
  Dimensionful (WithDim (L𝓭 * T𝓭⁻¹) ℝ)

/-- Read a physical acoustic frequency in inverse units of the selected time unit. -/
def frequencyReadout
    (unit : TimeUnit) (frequency : AcousticFrequency) : ℝ :=
  ((frequency {UnitChoices.SI with time := unit}).val : ℝ)

/-- Hertz readout of a physical acoustic frequency. -/
def frequencyInHertz (frequency : AcousticFrequency) : ℝ :=
  frequencyReadout TimeUnit.seconds frequency

/-- Read a signed axial position in the selected length unit. -/
def positionReadout
    (unit : LengthUnit) (position : AxialPosition) : ℝ :=
  (position {UnitChoices.SI with length := unit}).val

/-- Metre readout of an axial position. -/
def positionInMeters (position : AxialPosition) : ℝ :=
  positionReadout LengthUnit.meters position

/-- Read a signed axial velocity in selected length and time units. -/
def axialVelocityReadout
    (lengthUnit : LengthUnit) (timeUnit : TimeUnit)
    (velocity : AxialVelocity) : ℝ :=
  (velocity {UnitChoices.SI with
    length := lengthUnit, time := timeUnit}).val

/-- Metres-per-second readout of a signed axial velocity. -/
def axialVelocityInMetersPerSecond (velocity : AxialVelocity) : ℝ :=
  axialVelocityReadout LengthUnit.meters TimeUnit.seconds velocity

/-- Read Physlib's nonnegative dimensionful speed in metres per second. -/
def speedInMetersPerSecond (speed : DimSpeed) : ℝ :=
  ((speed UnitChoices.SI).val : ℝ)

/-! ## Physical roles and primary-figure labels -/

/-- The two labelled locations in the primary figure. -/
inductive FigurePoint where
  | L
  | S
  deriving DecidableEq, Repr

/-- The physical kind of sound source drawn at `S`. -/
inductive SoundSourceKind where
  | policeCarSiren
  deriving DecidableEq, Repr

/-- The two orientations along the one-dimensional figure axis. -/
inductive AxialDirection where
  | listenerToSource
  | sourceToListener
  deriving DecidableEq, Repr

/--
Independent physical quantities and qualitative labels for the Doppler
experiment.  In particular, `heardFrequencyAtL` is an unknown physical
frequency and is not assigned a numerical value by this structure.
-/
structure RecedingSirenSetup where
  sourceKind : SoundSourceKind
  position : FigurePoint → AxialPosition
  velocity : FigurePoint → AxialVelocity
  airVelocity : AxialVelocity
  sourceMotionDirection : AxialDirection
  soundPropagationDirection : AxialDirection
  emittedFrequencyAtS : AcousticFrequency
  heardFrequencyAtL : AcousticFrequency
  soundSpeedInAir : DimSpeed

/-!
Problem-statement and primary-figure data.  The listener `L` is left of `S`
and at rest; source `S` is a police-car siren moving at `30 m/s` in the
`L`-to-`S` direction, hence away from `L`.  The sound that reaches `L` travels
from `S` toward `L`.

No emitted-frequency calibration, sound-speed value, or requested heard
frequency occurs in this predicate.
-/
structure MatchesProblemAndPrimaryFigure
    (setup : RecedingSirenSetup) : Prop where
  sourceIsPoliceCarSiren : setup.sourceKind = .policeCarSiren
  listenerIsLeftOfSource :
    positionInMeters (setup.position .L) <
      positionInMeters (setup.position .S)
  listenerAtRest :
    axialVelocityInMetersPerSecond (setup.velocity .L) = 0
  sourceSpeedMetersPerSecond :
    axialVelocityInMetersPerSecond (setup.velocity .S) = 30
  sourceMovesAwayFromListener :
    setup.sourceMotionDirection = .listenerToSource
  soundTravelsFromSourceToListener :
    setup.soundPropagationDirection = .sourceToListener

/-!
Standard still-air calibration used for the numerical multiple-choice
evaluation.  It is kept separate because neither still air nor `343 m/s` is
printed in the supplied problem or bitmap.
-/
structure UsesStandardStillAir
    (setup : RecedingSirenSetup) : Prop where
  airAtRest : axialVelocityInMetersPerSecond setup.airVelocity = 0
  soundSpeedMetersPerSecond :
    speedInMetersPerSecond setup.soundSpeedInAir = 343

/-!
Nominal source-frequency calibration required by the supplied answer table.
The source and bitmap omit this datum, so it is deliberately separated from
`MatchesProblemAndPrimaryFigure`.
-/
structure UsesNominalSirenEmission
    (setup : RecedingSirenSetup) : Prop where
  emittedFrequencyHertz :
    frequencyInHertz setup.emittedFrequencyAtS = 300

/-- Positivity and subsonic conditions for the classical acoustic model. -/
structure HasPhysicalDopplerParameters
    (setup : RecedingSirenSetup) : Prop where
  emittedFrequencyPositive :
    0 < frequencyInHertz setup.emittedFrequencyAtS
  heardFrequencyPositive :
    0 < frequencyInHertz setup.heardFrequencyAtL
  soundSpeedPositive :
    0 < speedInMetersPerSecond setup.soundSpeedInAir
  sourceIsSubsonicRelativeToAir :
    |axialVelocityInMetersPerSecond (setup.velocity .S) -
        axialVelocityInMetersPerSecond setup.airVelocity| <
      speedInMetersPerSecond setup.soundSpeedInAir

/-!
The one-dimensional classical Doppler law for sound travelling leftward from
`S` to `L`.  Signed listener and source velocities are measured relative to
the air.  This governing law relates independent physical quantities and
does not mention `276 Hz` or any answer label.
-/
structure SatisfiesLeftwardAcousticDopplerLaw
    (setup : RecedingSirenSetup) : Prop where
  frequencyLaw :
    frequencyInHertz setup.heardFrequencyAtL =
      frequencyInHertz setup.emittedFrequencyAtS *
        (speedInMetersPerSecond setup.soundSpeedInAir +
          (axialVelocityInMetersPerSecond (setup.velocity .L) -
            axialVelocityInMetersPerSecond setup.airVelocity)) /
        (speedInMetersPerSecond setup.soundSpeedInAir +
          (axialVelocityInMetersPerSecond (setup.velocity .S) -
            axialVelocityInMetersPerSecond setup.airVelocity))

/-! ## Derived value and displayed answer choices -/

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
  | .B => 276
  | .C => 283
  | .D => 296

/-- The recorded answer label in the supplied dataset metadata. -/
def recordedAnswerChoice : AnswerChoice := .B

/--
Agreement with a displayed whole-hertz answer to half a hertz, representing
rounding to the nearest integer rather than an exact-integer physical value.
-/
def MatchesAnswerChoice
    (frequency : AcousticFrequency) (choice : AnswerChoice) : Prop :=
  |frequencyInHertz frequency - choice.hertz| ≤ 1 / 2

/--
Under the stated figure data and the two explicit auxiliary calibrations, the
classical Doppler model predicts the exact SI readout `102900 / 373 Hz`.
-/
lemma heardFrequencyInHertz_eq_exactModelValue
    (setup : RecedingSirenSetup)
    (_figure : MatchesProblemAndPrimaryFigure setup)
    (_air : UsesStandardStillAir setup)
    (_emission : UsesNominalSirenEmission setup)
    (_doppler : SatisfiesLeftwardAcousticDopplerLaw setup) :
    frequencyInHertz setup.heardFrequencyAtL = 102900 / 373 := by
  rw [_doppler.frequencyLaw, _emission.emittedFrequencyHertz,
    _air.soundSpeedMetersPerSecond, _figure.listenerAtRest, _air.airAtRest,
    _figure.sourceSpeedMetersPerSecond]
  norm_num

/-!
The Doppler-shifted frequency rounds to `276 Hz`, so the listener hears the
frequency displayed by recorded answer choice B.

This formalizes `thm:physics:phyx_mini_0194:target`.
-/
theorem recedingSiren_matches_recordedAnswerB
    (setup : RecedingSirenSetup)
    (_figure : MatchesProblemAndPrimaryFigure setup)
    (_air : UsesStandardStillAir setup)
    (_emission : UsesNominalSirenEmission setup)
    (_physical : HasPhysicalDopplerParameters setup)
    (_doppler : SatisfiesLeftwardAcousticDopplerLaw setup) :
    MatchesAnswerChoice setup.heardFrequencyAtL recordedAnswerChoice := by
  rw [MatchesAnswerChoice, recordedAnswerChoice, AnswerChoice.hertz,
    heardFrequencyInHertz_eq_exactModelValue setup _figure _air _emission
      _doppler]
  norm_num [abs_of_nonpos]

end PhyXMiniProblems.ProblemPhyXMini0194
