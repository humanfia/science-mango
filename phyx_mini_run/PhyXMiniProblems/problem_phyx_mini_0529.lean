import Mathlib
import Physlib.Relativity.LorentzGroup.Boosts.Basic
import Physlib.Units.WithDim.Speed

/- USER: The assigned source file did not exist when this autoformalization task began. -/

/-!
# Relativistic game of catch

Owen and Dina are at rest in the moving inertial frame `S'`, while Ed is at
rest in the ground frame `S`.  The primary figure fixes the positive axial
direction to the right: `S'` moves right at `0.600 c`, Owen is to the right of
Dina, and Owen throws the ball left at `0.800 c` as measured in `S'`.  Their
rest-frame separation is `1.80 * 10^12 m`.  The requested elapsed time is the
time between the throw and catch events in Ed's frame `S`.

Lengths, durations, signed coordinates, clock coordinates, and signed
velocities are unit-independent Physlib quantities.  Real numbers occur only
as readouts in named units, dimensionless velocity ratios, and displayed
multiple-choice values.

Assumption/target boundary:

* `MatchesScenarioAndPrimaryFigure` records the named frames, observers,
  axes, directions, printed numerical readouts, and the two event locations
  in `S'`.
* `SatisfiesUniformBallMotionInMovingFrame` is the governing constant-velocity
  relation for the ball in Owen and Dina's rest frame.
* `SatisfiesLorentzTimeTransformation` is the generic longitudinal Lorentz
  transformation between the two event-time differences.
* `EdMeasuresGroundFrameElapsedTime` identifies the requested physical
  duration with Ed's coordinate-time difference.
* There are no previous-part results.  Agreement with `4.88 * 10^3 s` and
  answer D occurs only in the theorem conclusion.
-/

noncomputable section

namespace PhyXMiniProblems.ProblemPhyXMini0529

open Dimension

/-! ## Dimensionful quantities and named-unit readouts -/

/-- A nonnegative physical length, independent of the selected unit. -/
abbrev LengthQuantity : Type := Dimensionful (WithDim L𝓭 NNReal)

/-- A nonnegative physical elapsed time. -/
abbrev DurationQuantity : Type := Dimensionful (WithDim T𝓭 NNReal)

/-- A signed coordinate along the common one-dimensional spatial axis. -/
abbrev AxialCoordinate : Type := Dimensionful (WithDim L𝓭 ℝ)

/-- A signed clock-coordinate value in an inertial frame. -/
abbrev ClockCoordinate : Type := Dimensionful (WithDim T𝓭 ℝ)

/-- A signed physical velocity along the common spatial axis. -/
abbrev AxialVelocity : Type :=
  Dimensionful (WithDim (L𝓭 * T𝓭⁻¹) ℝ)

/-- Read a nonnegative physical length in a selected length unit. -/
def lengthReadout (unit : LengthUnit) (length : LengthQuantity) : ℝ :=
  ((length {UnitChoices.SI with length := unit}).val : ℝ)

/-- Read a nonnegative physical duration in a selected time unit. -/
def durationReadout (unit : TimeUnit) (duration : DurationQuantity) : ℝ :=
  ((duration {UnitChoices.SI with time := unit}).val : ℝ)

/-- Read a signed axial coordinate in a selected length unit. -/
def axialCoordinateReadout
    (unit : LengthUnit) (coordinate : AxialCoordinate) : ℝ :=
  (coordinate {UnitChoices.SI with length := unit}).val

/-- Read a signed clock coordinate in a selected time unit. -/
def clockCoordinateReadout
    (unit : TimeUnit) (coordinate : ClockCoordinate) : ℝ :=
  (coordinate {UnitChoices.SI with time := unit}).val

/-- Read a signed axial velocity in coherent selected length and time units. -/
def axialVelocityReadout
    (lengthUnit : LengthUnit) (timeUnit : TimeUnit)
    (velocity : AxialVelocity) : ℝ :=
  (velocity {UnitChoices.SI with
    length := lengthUnit, time := timeUnit}).val

/-- Metre readout used by the separation and spatial event coordinates. -/
def lengthInMeters (length : LengthQuantity) : ℝ :=
  lengthReadout LengthUnit.meters length

/-- Metre readout of a signed axial coordinate. -/
def axialCoordinateInMeters (coordinate : AxialCoordinate) : ℝ :=
  axialCoordinateReadout LengthUnit.meters coordinate

/-- Second readout of a physical elapsed time. -/
def durationInSeconds (duration : DurationQuantity) : ℝ :=
  durationReadout TimeUnit.seconds duration

/-- Second readout of a signed inertial-frame clock coordinate. -/
def clockCoordinateInSeconds (coordinate : ClockCoordinate) : ℝ :=
  clockCoordinateReadout TimeUnit.seconds coordinate

/-- Metres-per-second readout of a signed axial velocity. -/
def axialVelocityInMetersPerSecond (velocity : AxialVelocity) : ℝ :=
  axialVelocityReadout LengthUnit.meters TimeUnit.seconds velocity

/-- Physlib's exact vacuum speed of light in selected length and time units. -/
def vacuumSpeedOfLightReadout
    (lengthUnit : LengthUnit) (timeUnit : TimeUnit) : ℝ :=
  (DimSpeed.speedOfLight {UnitChoices.SI with
    length := lengthUnit, time := timeUnit}).val

/-- The signed dimensionless ratio `v / c`, evaluated in coherent SI units. -/
def velocityInLightSpeedUnits (velocity : AxialVelocity) : ℝ :=
  axialVelocityInMetersPerSecond velocity /
    vacuumSpeedOfLightReadout LengthUnit.meters TimeUnit.seconds

/-! ## Frames, observers, events, and primary-figure labels -/

/-- The two inertial frames named in the problem and figure. -/
inductive InertialFrameLabel where
  | groundS
  | movingSPrime
  deriving DecidableEq, Repr

/-- The horizontal coordinate axes printed for the two frames. -/
inductive CoordinateAxisLabel where
  | x
  | xPrime
  deriving DecidableEq, Repr

/-- The three observers named in the scenario and shown in the figure. -/
inductive ObserverLabel where
  | dina
  | owen
  | ed
  deriving DecidableEq, Repr

/-- The two endpoint events of the ball's flight. -/
inductive CatchEvent where
  | throwByOwen
  | catchByDina
  deriving DecidableEq, Repr

/-- Orientations along the common horizontal axis. -/
inductive AxialDirection where
  | left
  | right
  deriving DecidableEq, Repr

/-- Individually identifiable items present in the supplied primary image. -/
inductive FigureFeature where
  | frameSLabel
  | frameSPrimeLabel
  | axisXLabel
  | axisXPrimeLabel
  | dinaObserver
  | owenObserver
  | edObserver
  | ball
  | movingFrameVelocityArrow
  | ballVelocityArrow
  | separationDimensionLine
  deriving DecidableEq, Fintype, Repr

/-!
Qualitative geometry and scalar annotations read directly from
`phyx_data/test_image/529.png`.
-/
structure RelativisticCatchFigure where
  shows : FigureFeature → Bool
  observerFrameLabel : ObserverLabel → InertialFrameLabel
  axisLabel : InertialFrameLabel → CoordinateAxisLabel
  movingFrameDirection : AxialDirection
  ballDirection : AxialDirection
  owenIsRightOfDina : Bool
  printedFrameSpeedFractionOfLight : ℝ
  printedBallSpeedFractionOfLight : ℝ
  printedSeparationMeters : ℝ

/-!
All independent physical quantities and frame-indexed event coordinates in
the scenario.  `edMeasuredFlightTime` is an unknown duration; no field assigns
it a displayed answer value.
-/
structure RelativisticCatchSetup where
  figure : RelativisticCatchFigure
  observerRestFrame : ObserverLabel → InertialFrameLabel
  movingFrameVelocityInGround : AxialVelocity
  ballVelocityInMovingFrame : AxialVelocity
  owenDinaRestSeparation : LengthQuantity
  restPositionInMovingFrame : ObserverLabel → AxialCoordinate
  eventPosition : InertialFrameLabel → CatchEvent → AxialCoordinate
  eventTime : InertialFrameLabel → CatchEvent → ClockCoordinate
  edMeasuredFlightTime : DurationQuantity

/-! ## Scenario data, figure readouts, and governing physics -/

/-!
The named labels, directions, and numerical annotations in the source and
primary image.  Positive axial velocity points right, so the ball's signed
`S'` velocity is the negative of its printed speed magnitude.

The two event positions express that the throw occurs at Owen and the catch
at Dina.  Their difference is fixed by the independently represented proper
separation; no elapsed-time answer is recorded here.
-/
structure MatchesScenarioAndPrimaryFigure
    (setup : RelativisticCatchSetup) : Prop where
  everyNamedFeatureShown : ∀ feature, setup.figure.shows feature = true
  dinaIsAtRestInMovingFrame :
    setup.observerRestFrame .dina = .movingSPrime
  owenIsAtRestInMovingFrame :
    setup.observerRestFrame .owen = .movingSPrime
  edIsAtRestInGroundFrame : setup.observerRestFrame .ed = .groundS
  figureDinaFrameLabel :
    setup.figure.observerFrameLabel .dina = .movingSPrime
  figureOwenFrameLabel :
    setup.figure.observerFrameLabel .owen = .movingSPrime
  figureEdFrameLabel : setup.figure.observerFrameLabel .ed = .groundS
  groundAxisIsX : setup.figure.axisLabel .groundS = .x
  movingAxisIsXPrime : setup.figure.axisLabel .movingSPrime = .xPrime
  movingFramePointsRight : setup.figure.movingFrameDirection = .right
  ballPointsLeft : setup.figure.ballDirection = .left
  owenDrawnRightOfDina : setup.figure.owenIsRightOfDina = true
  frameSpeedAnnotation :
    setup.figure.printedFrameSpeedFractionOfLight = (3 / 5 : ℝ)
  ballSpeedAnnotation :
    setup.figure.printedBallSpeedFractionOfLight = (4 / 5 : ℝ)
  separationAnnotation :
    setup.figure.printedSeparationMeters = (9 / 5 : ℝ) * 10 ^ 12
  movingFrameVelocityMatchesAnnotation :
    velocityInLightSpeedUnits setup.movingFrameVelocityInGround =
      setup.figure.printedFrameSpeedFractionOfLight
  ballVelocityMatchesAnnotation :
    velocityInLightSpeedUnits setup.ballVelocityInMovingFrame =
      -setup.figure.printedBallSpeedFractionOfLight
  separationMatchesAnnotation :
    lengthInMeters setup.owenDinaRestSeparation =
      setup.figure.printedSeparationMeters
  owenRestPositionRightOfDina :
    axialCoordinateInMeters (setup.restPositionInMovingFrame .dina) <
      axialCoordinateInMeters (setup.restPositionInMovingFrame .owen)
  restPositionSeparation :
    axialCoordinateInMeters (setup.restPositionInMovingFrame .owen) -
        axialCoordinateInMeters (setup.restPositionInMovingFrame .dina) =
      lengthInMeters setup.owenDinaRestSeparation
  throwOccursAtOwen :
    setup.eventPosition .movingSPrime .throwByOwen =
      setup.restPositionInMovingFrame .owen
  catchOccursAtDina :
    setup.eventPosition .movingSPrime .catchByDina =
      setup.restPositionInMovingFrame .dina

/-!
Positivity, causal speed bounds, and event ordering for the physical setup.
These conditions contain no displayed flight-time value.
-/
structure HasPhysicalRelativisticParameters
    (setup : RelativisticCatchSetup) : Prop where
  speedOfLightPositive :
    0 < vacuumSpeedOfLightReadout LengthUnit.meters TimeUnit.seconds
  separationPositive : 0 < lengthInMeters setup.owenDinaRestSeparation
  movingFrameSubluminal :
    |velocityInLightSpeedUnits setup.movingFrameVelocityInGround| < 1
  ballSubluminal :
    |velocityInLightSpeedUnits setup.ballVelocityInMovingFrame| < 1
  ballMovesLeft : velocityInLightSpeedUnits setup.ballVelocityInMovingFrame < 0
  movingFrameTimeOrdered :
    clockCoordinateInSeconds
        (setup.eventTime .movingSPrime .throwByOwen) <
      clockCoordinateInSeconds
        (setup.eventTime .movingSPrime .catchByDina)
  groundFrameTimeOrdered :
    clockCoordinateInSeconds (setup.eventTime .groundS .throwByOwen) <
      clockCoordinateInSeconds (setup.eventTime .groundS .catchByDina)
  requestedDurationPositive : 0 < durationInSeconds setup.edMeasuredFlightTime

/-!
Uniform one-dimensional motion of the ball in Owen and Dina's rest frame:
`Delta x' = u' Delta t'`.  This is a generic kinematic law involving the
unknown event-time difference, not the requested numerical answer.
-/
structure SatisfiesUniformBallMotionInMovingFrame
    (setup : RelativisticCatchSetup) : Prop where
  displacementEqualsVelocityTimesTime :
    axialCoordinateInMeters
          (setup.eventPosition .movingSPrime .catchByDina) -
        axialCoordinateInMeters
          (setup.eventPosition .movingSPrime .throwByOwen) =
      axialVelocityInMetersPerSecond setup.ballVelocityInMovingFrame *
        (clockCoordinateInSeconds
              (setup.eventTime .movingSPrime .catchByDina) -
          clockCoordinateInSeconds
              (setup.eventTime .movingSPrime .throwByOwen))

/-!
The longitudinal Lorentz transformation for the separation of the catch and
throw events,

`Delta t = gamma(beta) * (Delta t' + beta * Delta x' / c)`.

Here `beta` is the signed velocity of `S'` in `S`; the leftward event
displacement `Delta x'` supplies the minus sign relevant to this figure.  The
law is stated before inserting or rounding any answer value.
-/
structure SatisfiesLorentzTimeTransformation
    (setup : RelativisticCatchSetup) : Prop where
  eventTimeDifferenceLaw :
    clockCoordinateInSeconds (setup.eventTime .groundS .catchByDina) -
        clockCoordinateInSeconds (setup.eventTime .groundS .throwByOwen) =
      LorentzGroup.γ
          (velocityInLightSpeedUnits setup.movingFrameVelocityInGround) *
        ((clockCoordinateInSeconds
              (setup.eventTime .movingSPrime .catchByDina) -
            clockCoordinateInSeconds
              (setup.eventTime .movingSPrime .throwByOwen)) +
          velocityInLightSpeedUnits setup.movingFrameVelocityInGround *
            (axialCoordinateInMeters
                  (setup.eventPosition .movingSPrime .catchByDina) -
              axialCoordinateInMeters
                  (setup.eventPosition .movingSPrime .throwByOwen)) /
            vacuumSpeedOfLightReadout
              LengthUnit.meters TimeUnit.seconds)

/-!
Operational meaning of the question: because Ed is at rest in `S`, his
measured flight duration is the ground-frame coordinate-time difference.
This relation does not assign that duration a numerical answer.
-/
structure EdMeasuresGroundFrameElapsedTime
    (setup : RelativisticCatchSetup) : Prop where
  elapsedTimeIsGroundCoordinateDifference :
    durationInSeconds setup.edMeasuredFlightTime =
      clockCoordinateInSeconds (setup.eventTime .groundS .catchByDina) -
        clockCoordinateInSeconds (setup.eventTime .groundS .throwByOwen)

/-! ## Displayed answers and formalization target -/

/-- The four answer labels printed with the problem. -/
inductive AnswerChoice where
  | A
  | B
  | C
  | D
  deriving DecidableEq, Repr

/-- Time in seconds printed beside each multiple-choice label. -/
def displayedTimeSeconds : AnswerChoice → ℝ
  | .A => 3220
  | .B => 2540
  | .C => 3710
  | .D => 4880

/-- The answer label recorded in the supplied dataset metadata. -/
def recordedDatasetAnswer : AnswerChoice := .D

/-!
Agreement with a time printed as three significant figures in units of
`10^3 s`.  Half of the final `10 s` place gives a `5 s` rounding tolerance.
-/
def MatchesDisplayedTimeChoice
    (duration : DurationQuantity) (choice : AnswerChoice) : Prop :=
  |durationInSeconds duration - displayedTimeSeconds choice| ≤ 5

/-!
The ball's Ed-frame flight duration rounds to `4.88 * 10^3 s`, answer D.

This formalizes `thm:physics:phyx_mini_0529:target`.
-/
theorem ballFlightTimeInEdFrame_matches_answerD
    (setup : RelativisticCatchSetup)
    (hScenario : MatchesScenarioAndPrimaryFigure setup)
    (hPhysical : HasPhysicalRelativisticParameters setup)
    (hBallMotion : SatisfiesUniformBallMotionInMovingFrame setup)
    (hLorentz : SatisfiesLorentzTimeTransformation setup)
    (hEdMeasurement : EdMeasuresGroundFrameElapsedTime setup) :
    MatchesDisplayedTimeChoice
      setup.edMeasuredFlightTime recordedDatasetAnswer := by
  have hC :
      vacuumSpeedOfLightReadout LengthUnit.meters TimeUnit.seconds =
        299792458 := by
    change (DimSpeed.speedOfLight UnitChoices.SI).val = 299792458
    rw [DimSpeed.speedOfLight_in_SI]
  have hBeta :
      velocityInLightSpeedUnits setup.movingFrameVelocityInGround =
        (3 / 5 : ℝ) := by
    rw [hScenario.movingFrameVelocityMatchesAnnotation,
      hScenario.frameSpeedAnnotation]
  have hBallBeta :
      velocityInLightSpeedUnits setup.ballVelocityInMovingFrame =
        -(4 / 5 : ℝ) := by
    rw [hScenario.ballVelocityMatchesAnnotation,
      hScenario.ballSpeedAnnotation]
  have hSeparation :
      lengthInMeters setup.owenDinaRestSeparation =
        (9 / 5 : ℝ) * 10 ^ 12 := by
    rw [hScenario.separationMatchesAnnotation,
      hScenario.separationAnnotation]
  have hDisplacement :
      axialCoordinateInMeters
            (setup.eventPosition .movingSPrime .catchByDina) -
          axialCoordinateInMeters
            (setup.eventPosition .movingSPrime .throwByOwen) =
        -((9 / 5 : ℝ) * 10 ^ 12) := by
    rw [hScenario.catchOccursAtDina, hScenario.throwOccursAtOwen]
    linarith [hScenario.restPositionSeparation, hSeparation]
  have hBallVelocity :
      axialVelocityInMetersPerSecond setup.ballVelocityInMovingFrame =
        -(4 / 5 : ℝ) * 299792458 := by
    rw [velocityInLightSpeedUnits, hC] at hBallBeta
    norm_num at hBallBeta ⊢
    linarith
  have hGamma : LorentzGroup.γ (3 / 5 : ℝ) = 5 / 4 := by
    rw [LorentzGroup.γ]
    norm_num
  have hBallEquation :=
    hBallMotion.displacementEqualsVelocityTimesTime
  rw [hDisplacement, hBallVelocity] at hBallEquation
  norm_num at hBallEquation
  have hLorentzEquation := hLorentz.eventTimeDifferenceLaw
  rw [hBeta, hDisplacement, hC, hGamma] at hLorentzEquation
  norm_num at hLorentzEquation
  have hEdEquation :=
    hEdMeasurement.elapsedTimeIsGroundCoordinateDifference
  unfold MatchesDisplayedTimeChoice recordedDatasetAnswer displayedTimeSeconds
  rw [abs_le]
  constructor <;>
    linarith [hBallEquation, hLorentzEquation, hEdEquation]

end PhyXMiniProblems.ProblemPhyXMini0529
