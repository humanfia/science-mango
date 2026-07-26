import Mathlib
import Physlib.Units.WithDim.Speed

/-!
# Frequency heard by a listener moving away from a stationary siren

This file models problem `phyx_mini_0195`.  The primary figure places the
listener `L` to the left of the police-car siren `S` and takes the positive
axis from `L` toward `S`.  The listener therefore has signed velocity
`-30 m/s`, while the siren is at rest.  Sound reaching the listener travels
to the left.

The isolated source supplies neither the emitted frequency nor the speed of
sound, so no numerical heard frequency follows from it.  The formal target is
therefore the strongest source-supported symbolic Doppler relation, with the
emitted frequency and sound speed left as independent physical quantities.
Frequencies, positions, propagation speed, and signed axial velocities carry
their physical dimensions through Physlib; real numbers occur only as SI
readouts and as displayed answer metadata.
-/

noncomputable section

namespace PhyXMiniProblems.ProblemPhyXMini0195

open Dimension

/-! ## Dimensionful quantities and coherent SI readouts -/

/-- A physical acoustic frequency, carrying the inverse-time dimension. -/
abbrev AcousticFrequency : Type := Dimensionful (WithDim T𝓭⁻¹ NNReal)

/-- A signed physical coordinate along the horizontal road axis. -/
abbrev AxialPosition : Type := Dimensionful (WithDim L𝓭 ℝ)

/--
A signed physical velocity along the road axis.  A signed quantity is needed
because Physlib's `DimSpeed` records a nonnegative speed magnitude, whereas
the figure distinguishes motion toward the right from motion toward the left.
-/
abbrev AxialVelocity : Type :=
  Dimensionful (WithDim (L𝓭 * T𝓭⁻¹) ℝ)

/-- Read a physical acoustic frequency in hertz. -/
def frequencyInHertz (frequency : AcousticFrequency) : ℝ :=
  ((frequency UnitChoices.SI).val : ℝ)

/-- Read a signed axial position in metres. -/
def positionInMeters (position : AxialPosition) : ℝ :=
  (position UnitChoices.SI).val

/-- Read a signed axial velocity in metres per second. -/
def axialVelocityInMetersPerSecond (velocity : AxialVelocity) : ℝ :=
  (velocity UnitChoices.SI).val

/-- Read Physlib's nonnegative dimensionful speed in metres per second. -/
def speedInMetersPerSecond (speed : DimSpeed) : ℝ :=
  ((speed UnitChoices.SI).val : ℝ)

/-! ## Physical objects and primary-figure labels -/

/-- The two labeled objects in the primary figure. -/
inductive FigureObject where
  | L
  | S
  deriving DecidableEq, Repr

/-- The two directions along the horizontal road axis. -/
inductive AxialDirection where
  | left
  | right
  deriving DecidableEq, Repr

/-- The two possible orientations of the one-dimensional coordinate axis. -/
inductive AxisOrientation where
  | listenerToSource
  | sourceToListener
  deriving DecidableEq, Repr

/--
The physical quantities and figure labels in the siren--listener experiment.

`heardFrequency` is the unknown physical frequency requested by the problem;
this structure deliberately assigns it no numerical value.
-/
structure SirenListenerSetup where
  position : FigureObject → AxialPosition
  velocity : FigureObject → AxialVelocity
  emittedFrequency : AcousticFrequency
  heardFrequency : AcousticFrequency
  soundSpeedInAir : DimSpeed
  positiveAxis : AxisOrientation
  soundPropagationDirection : AxialDirection

/--
The geometric and kinematic readouts shown in the primary raster.  The
listener `L` lies to the left of the source `S`; the marked positive direction
is from `L` to `S`; the listener moves left at `30 m/s`; the police car is at
rest; and the sound that reaches the listener propagates leftward.

The velocities are signed readouts in the rest frame of the air, as required
by the classical acoustic Doppler law below.  This predicate contains no
emitted-frequency calibration, sound-speed calibration, or value for the
requested heard frequency.
-/
def MatchesPrimaryFigure (setup : SirenListenerSetup) : Prop :=
  positionInMeters (setup.position .L) < positionInMeters (setup.position .S) ∧
    axialVelocityInMetersPerSecond (setup.velocity .L) = -30 ∧
    axialVelocityInMetersPerSecond (setup.velocity .S) = 0 ∧
    setup.positiveAxis = .listenerToSource ∧
    setup.soundPropagationDirection = .left

/--
Positivity and subsonic conditions for the acoustic model.  Object velocities
are measured in the rest frame of the air; the strict bounds ensure that the
sound wave can overtake the listener and that the classical Doppler factors
are physically meaningful.
-/
def HasSubsonicPhysicalParameters (setup : SirenListenerSetup) : Prop :=
  0 < frequencyInHertz setup.emittedFrequency ∧
    0 < speedInMetersPerSecond setup.soundSpeedInAir ∧
    |axialVelocityInMetersPerSecond (setup.velocity .L)| <
      speedInMetersPerSecond setup.soundSpeedInAir ∧
    |axialVelocityInMetersPerSecond (setup.velocity .S)| <
      speedInMetersPerSecond setup.soundSpeedInAir

/-! ## Governing physical law -/

/-!
The one-dimensional classical Doppler law for sound travelling left from `S`
to `L`.  The coordinate direction is positive from listener to source, and
the signed object velocities are measured in the rest frame of the air.  Thus
the observer and source factors are respectively `c + v_L` and `c + v_S`.
This is a generic governing relation involving the unknown heard frequency;
it asserts neither a calibration nor a displayed answer value.
-/
structure SatisfiesLeftwardAcousticDopplerLaw
    (setup : SirenListenerSetup) : Prop where
  frequencyLaw :
    frequencyInHertz setup.heardFrequency =
      frequencyInHertz setup.emittedFrequency *
        (speedInMetersPerSecond setup.soundSpeedInAir +
          axialVelocityInMetersPerSecond (setup.velocity .L)) /
        (speedInMetersPerSecond setup.soundSpeedInAir +
          axialVelocityInMetersPerSecond (setup.velocity .S))

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
  | .A => 272
  | .B => 274
  | .C => 263
  | .D => 276

/-- The answer label recorded in the supplied dataset metadata. -/
def recordedAnswerChoice : AnswerChoice := .B

/-!
For a stationary siren and a listener moving away at `30 m/s`, the heard
frequency is the emitted frequency multiplied by `(c - 30) / c`, where `c` is
the (unspecified) speed of sound in metres per second.

This symbolic relation is the strongest conclusion supported by the isolated
source.  In particular, the recorded answer B is retained above only as
dataset metadata: without an emitted-frequency or sound-speed calibration,
the source does not determine any of the displayed numerical answers.

This formalizes `thm:physics:phyx_mini_0195:target`.
-/
theorem heardFrequency_eq_emitted_mul_soundSpeed_sub_thirty_div_soundSpeed
    (setup : SirenListenerSetup)
    (h_figure : MatchesPrimaryFigure setup)
    (h_physical : HasSubsonicPhysicalParameters setup)
    (h_doppler : SatisfiesLeftwardAcousticDopplerLaw setup) :
    frequencyInHertz setup.heardFrequency =
      frequencyInHertz setup.emittedFrequency *
        (speedInMetersPerSecond setup.soundSpeedInAir - 30) /
        speedInMetersPerSecond setup.soundSpeedInAir := by
  sorry

end PhyXMiniProblems.ProblemPhyXMini0195
