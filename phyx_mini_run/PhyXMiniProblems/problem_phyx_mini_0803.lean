import Mathlib
import Physlib.Units.WithDim.Speed

noncomputable section

namespace PhyXMiniProblems.ProblemPhyXMini0803

open Dimension

/-!
# Bathroom-scale reading in a descending, slowing elevator

A `50.0 kg` woman rides an elevator that initially moves downward at
`10.0 m/s` and comes to rest after descending `25.0 m` with constant
acceleration. The supplied figure uses an upward-positive `Y` axis, labels
the upward normal force by `n`, the downward weight by `w = 490 N`, and the
upward acceleration by `a_y`.

Physical mass, length, speed, acceleration, and force are represented by
unit-independent Physlib dimensional quantities. Real numbers occur only at
explicitly named coherent-unit readout boundaries and in displayed metadata.
-/

/-! ## Dimensionful quantities and coherent readouts -/

/-- The physical dimension of acceleration, `L T⁻²`. -/
def accelerationDimension : Dimension := L𝓭 * T𝓭⁻¹ * T𝓭⁻¹

/-- The physical dimension of force, `M L T⁻²`. -/
def forceDimension : Dimension := M𝓭 * L𝓭 * T𝓭⁻¹ * T𝓭⁻¹

/-- A nonnegative physical mass, independent of its readout unit. -/
abbrev MassQuantity : Type := Dimensionful (WithDim M𝓭 NNReal)

/-- A nonnegative physical distance. -/
abbrev LengthQuantity : Type := Dimensionful (WithDim L𝓭 NNReal)

/-- A signed vertical displacement; positive means upward. -/
abbrev SignedLengthQuantity : Type := Dimensionful (WithDim L𝓭 ℝ)

/-- A nonnegative physical speed magnitude. -/
abbrev SpeedMagnitudeQuantity : Type := DimSpeed

/-- A signed vertical velocity; positive means upward. -/
abbrev SignedSpeedQuantity : Type :=
  Dimensionful (WithDim (L𝓭 * T𝓭⁻¹) ℝ)

/-- A nonnegative physical acceleration magnitude. -/
abbrev AccelerationMagnitudeQuantity : Type :=
  Dimensionful (WithDim accelerationDimension NNReal)

/-- A signed vertical acceleration; positive means upward. -/
abbrev SignedAccelerationQuantity : Type :=
  Dimensionful (WithDim accelerationDimension ℝ)

/-- A nonnegative physical force magnitude. -/
abbrev ForceMagnitudeQuantity : Type :=
  Dimensionful (WithDim forceDimension NNReal)

/-- Read mass in a selected mass unit. -/
def massReadout (unit : MassUnit) (mass : MassQuantity) : ℝ :=
  ((mass {UnitChoices.SI with mass := unit}).val : ℝ)

/-- Read a nonnegative distance in a selected length unit. -/
def lengthReadout (unit : LengthUnit) (length : LengthQuantity) : ℝ :=
  ((length {UnitChoices.SI with length := unit}).val : ℝ)

/-- Read signed vertical displacement in a selected length unit. -/
def signedLengthReadout
    (unit : LengthUnit) (displacement : SignedLengthQuantity) : ℝ :=
  (displacement {UnitChoices.SI with length := unit}).val

/-- Read a nonnegative speed in coherent selected length and time units. -/
def speedMagnitudeReadout
    (lengthUnit : LengthUnit) (timeUnit : TimeUnit)
    (speed : SpeedMagnitudeQuantity) : ℝ :=
  ((speed {UnitChoices.SI with
    length := lengthUnit, time := timeUnit}).val : ℝ)

/-- Read signed vertical velocity in coherent selected length and time units. -/
def signedSpeedReadout
    (lengthUnit : LengthUnit) (timeUnit : TimeUnit)
    (velocity : SignedSpeedQuantity) : ℝ :=
  (velocity {UnitChoices.SI with
    length := lengthUnit, time := timeUnit}).val

/-- Read a nonnegative acceleration in coherent selected units. -/
def accelerationMagnitudeReadout
    (lengthUnit : LengthUnit) (timeUnit : TimeUnit)
    (acceleration : AccelerationMagnitudeQuantity) : ℝ :=
  ((acceleration {UnitChoices.SI with
    length := lengthUnit, time := timeUnit}).val : ℝ)

/-- Read signed vertical acceleration in coherent selected units. -/
def signedAccelerationReadout
    (lengthUnit : LengthUnit) (timeUnit : TimeUnit)
    (acceleration : SignedAccelerationQuantity) : ℝ :=
  (acceleration {UnitChoices.SI with
    length := lengthUnit, time := timeUnit}).val

/-- Read force magnitude in the coherent unit induced by selected base units. -/
def forceMagnitudeReadout
    (massUnit : MassUnit) (lengthUnit : LengthUnit) (timeUnit : TimeUnit)
    (force : ForceMagnitudeQuantity) : ℝ :=
  ((force {UnitChoices.SI with
    mass := massUnit, length := lengthUnit, time := timeUnit}).val : ℝ)

/-- Kilogram readout used for the woman's stated mass. -/
def massInKilograms (mass : MassQuantity) : ℝ :=
  massReadout MassUnit.kilograms mass

/-- Meter readout used for the stated stopping distance. -/
def lengthInMeters (length : LengthQuantity) : ℝ :=
  lengthReadout LengthUnit.meters length

/-- Upward-positive meter readout of the stopping displacement. -/
def signedLengthInMeters (displacement : SignedLengthQuantity) : ℝ :=
  signedLengthReadout LengthUnit.meters displacement

/-- Meter-per-second readout of a speed magnitude. -/
def speedMagnitudeInMetersPerSecond (speed : SpeedMagnitudeQuantity) : ℝ :=
  speedMagnitudeReadout LengthUnit.meters TimeUnit.seconds speed

/-- Upward-positive meter-per-second readout of vertical velocity. -/
def signedSpeedInMetersPerSecond (velocity : SignedSpeedQuantity) : ℝ :=
  signedSpeedReadout LengthUnit.meters TimeUnit.seconds velocity

/-- Meter-per-second-squared readout of an acceleration magnitude. -/
def accelerationMagnitudeInMetersPerSecondSquared
    (acceleration : AccelerationMagnitudeQuantity) : ℝ :=
  accelerationMagnitudeReadout LengthUnit.meters TimeUnit.seconds acceleration

/-- Upward-positive meter-per-second-squared readout of acceleration. -/
def signedAccelerationInMetersPerSecondSquared
    (acceleration : SignedAccelerationQuantity) : ℝ :=
  signedAccelerationReadout LengthUnit.meters TimeUnit.seconds acceleration

/-- Newton readout of a physical force magnitude. -/
def forceMagnitudeInNewtons (force : ForceMagnitudeQuantity) : ℝ :=
  forceMagnitudeReadout
    MassUnit.kilograms LengthUnit.meters TimeUnit.seconds force

/-! ## Supplied-figure vocabulary and the elevator setup -/

/-- Vertical directions occurring in the motion arrow and free-body diagram. -/
inductive VerticalDirection where
  | upward
  | downward
  deriving DecidableEq, Repr

/-- The trend described by “moving down with decreasing speed.” -/
inductive SpeedTrend where
  | increasing
  | constant
  | decreasing
  deriving DecidableEq, Repr

/-- Literal labels visible in the supplied raster. -/
inductive FigureTextLabel where
  | axisY
  | axisX
  | normalN
  | weightW
  | accelerationAy
  | movingDownWithDecreasingSpeed
  deriving DecidableEq, Fintype, Repr

/-- The three directed arrows in the woman's free-body/acceleration diagram. -/
inductive FigureVectorLabel where
  | normalN
  | weightW
  | accelerationAy
  deriving DecidableEq, Fintype, Repr

/-!
Qualitative and numerical information read directly from the supplied figure.
The normal-force arrow has no numerical label, so this structure does not
contain the requested scale reading.
-/
structure ElevatorFigure where
  womanShownInsideElevator : Bool
  bathroomScaleShown : Bool
  labelShown : FigureTextLabel → Bool
  positiveYAxisDirection : VerticalDirection
  motionArrowDirection : VerticalDirection
  speedTrend : SpeedTrend
  vectorDirection : FigureVectorLabel → VerticalDirection
  weightLabelInNewtons : ℝ

/-- Motion regime asked about in the problem. -/
inductive ElevatorMotionRegime where
  | descendingAndSlowing
  | other
  deriving DecidableEq, Repr

/-!
Independent physical quantities in the scenario. In particular,
`elevatorAcceleration`, `normalForceN`, and `scaleReading` are unknowns; none
is defined from a displayed answer choice.
-/
structure BathroomScaleElevatorSetup where
  figure : ElevatorFigure
  womanMass : MassQuantity
  initialSpeedMagnitude : SpeedMagnitudeQuantity
  initialElevatorVelocity : SignedSpeedQuantity
  finalElevatorVelocity : SignedSpeedQuantity
  stoppingDistance : LengthQuantity
  stoppingDisplacement : SignedLengthQuantity
  elevatorAcceleration : SignedAccelerationQuantity
  womanAccelerationAy : SignedAccelerationQuantity
  gravitationalAcceleration : AccelerationMagnitudeQuantity
  normalForceN : ForceMagnitudeQuantity
  weightW : ForceMagnitudeQuantity
  scaleReading : ForceMagnitudeQuantity
  motionRegime : ElevatorMotionRegime
  accelerationIsConstant : Bool
  womanRemainsInContactWithScale : Bool

/-!
Primary-image evidence: the motion arrow is downward, speed is decreasing,
the `Y` axis and `n`/`a_y` arrows are upward, and `w = 490 N` points downward.
-/
structure MatchesSuppliedElevatorFigure
    (setup : BathroomScaleElevatorSetup) : Prop where
  womanIsShown : setup.figure.womanShownInsideElevator = true
  scaleIsShown : setup.figure.bathroomScaleShown = true
  allLiteralLabelsAreShown : ∀ label, setup.figure.labelShown label = true
  positiveYAxisIsUpward :
    setup.figure.positiveYAxisDirection = .upward
  motionArrowIsDownward : setup.figure.motionArrowDirection = .downward
  displayedSpeedTrendIsDecreasing : setup.figure.speedTrend = .decreasing
  normalArrowIsUpward :
    setup.figure.vectorDirection .normalN = .upward
  weightArrowIsDownward :
    setup.figure.vectorDirection .weightW = .downward
  accelerationArrowIsUpward :
    setup.figure.vectorDirection .accelerationAy = .upward
  displayedWeightIs490Newtons : setup.figure.weightLabelInNewtons = 490
  physicalWeightMatchesFigureLabel :
    forceMagnitudeInNewtons setup.weightW = setup.figure.weightLabelInNewtons

/-!
Numerical and qualitative data from the problem prose. Signed quantities use
the upward-positive convention shown in the figure. No acceleration, normal
force, or scale-reading value is assumed here.
-/
structure MatchesElevatorProblemData
    (setup : BathroomScaleElevatorSetup) : Prop where
  womanMassKilograms : massInKilograms setup.womanMass = 50
  initialSpeedMetersPerSecond :
    speedMagnitudeInMetersPerSecond setup.initialSpeedMagnitude = 10
  initialVelocityIsDownward :
    signedSpeedInMetersPerSecond setup.initialElevatorVelocity = -10
  finalVelocityAtStop :
    signedSpeedInMetersPerSecond setup.finalElevatorVelocity = 0
  stoppingDistanceMeters : lengthInMeters setup.stoppingDistance = 25
  stoppingDisplacementIsDownward :
    signedLengthInMeters setup.stoppingDisplacement = -25
  standardGravityReadout :
    accelerationMagnitudeInMetersPerSecondSquared
      setup.gravitationalAcceleration = 49 / 5
  regimeIsDescendingAndSlowing :
    setup.motionRegime = .descendingAndSlowing
  constantAcceleration : setup.accelerationIsConstant = true
  riderStaysOnScale : setup.womanRemainsInContactWithScale = true

/-- Positivity and nondegeneracy conditions on the independent magnitudes. -/
structure HasPhysicalElevatorParameters
    (setup : BathroomScaleElevatorSetup) : Prop where
  womanMassPositive : 0 < massInKilograms setup.womanMass
  initialSpeedPositive :
    0 < speedMagnitudeInMetersPerSecond setup.initialSpeedMagnitude
  stoppingDistancePositive : 0 < lengthInMeters setup.stoppingDistance
  gravityPositive :
    0 < accelerationMagnitudeInMetersPerSecondSquared
      setup.gravitationalAcceleration

/-!
Governing laws for the idealized motion and scale:

* constant-acceleration kinematics along the upward-positive vertical axis;
* the woman shares the elevator's acceleration while remaining on the scale;
* `w = m g` for the woman's weight magnitude;
* `n - w = m a_y`, Newton's second law for the woman;
* an ideal bathroom scale reports the normal-force magnitude.

All equations hold in arbitrary coherent base units. These laws constrain the
unknown scale reading but do not assign it the requested numerical value.
-/
structure SatisfiesIdealElevatorDynamicsLaws
    (setup : BathroomScaleElevatorSetup) : Prop where
  constantAccelerationKinematics :
    ∀ (lengthUnit : LengthUnit) (timeUnit : TimeUnit),
      signedSpeedReadout lengthUnit timeUnit
          setup.finalElevatorVelocity ^ 2 =
        signedSpeedReadout lengthUnit timeUnit
            setup.initialElevatorVelocity ^ 2 +
          2 * signedAccelerationReadout lengthUnit timeUnit
              setup.elevatorAcceleration *
            signedLengthReadout lengthUnit setup.stoppingDisplacement
  riderSharesElevatorAcceleration :
    ∀ (lengthUnit : LengthUnit) (timeUnit : TimeUnit),
      signedAccelerationReadout lengthUnit timeUnit
          setup.womanAccelerationAy =
        signedAccelerationReadout lengthUnit timeUnit
          setup.elevatorAcceleration
  gravitationalWeightLaw :
    ∀ (massUnit : MassUnit) (lengthUnit : LengthUnit)
        (timeUnit : TimeUnit),
      forceMagnitudeReadout massUnit lengthUnit timeUnit setup.weightW =
        massReadout massUnit setup.womanMass *
          accelerationMagnitudeReadout lengthUnit timeUnit
            setup.gravitationalAcceleration
  verticalNewtonSecondLaw :
    ∀ (massUnit : MassUnit) (lengthUnit : LengthUnit)
        (timeUnit : TimeUnit),
      forceMagnitudeReadout massUnit lengthUnit timeUnit setup.normalForceN -
          forceMagnitudeReadout massUnit lengthUnit timeUnit setup.weightW =
        massReadout massUnit setup.womanMass *
          signedAccelerationReadout lengthUnit timeUnit
            setup.womanAccelerationAy
  idealScaleMeasuresNormalForce :
    ∀ (massUnit : MassUnit) (lengthUnit : LengthUnit)
        (timeUnit : TimeUnit),
      forceMagnitudeReadout massUnit lengthUnit timeUnit setup.scaleReading =
        forceMagnitudeReadout massUnit lengthUnit timeUnit setup.normalForceN

/-! ## Displayed answers and formal targets -/

/-- Labels of the four displayed scale-reading choices. -/
inductive AnswerChoice where
  | A
  | B
  | C
  | D
  deriving DecidableEq, Fintype, Repr

/-- Every displayed choice, read in newtons. -/
def displayedScaleReadingInNewtons : AnswerChoice → ℝ
  | .A => 590
  | .B => 390
  | .C => 290
  | .D => 690

/-- Dataset answer metadata, deliberately not used as a theorem premise. -/
def recordedDatasetAnswer : AnswerChoice := .B

/--
The stopping data determine an upward elevator acceleration of `2 m/s²`.
-/
lemma elevatorAccelerationFromStoppingData
    (setup : BathroomScaleElevatorSetup)
    (data : MatchesElevatorProblemData setup)
    (laws : SatisfiesIdealElevatorDynamicsLaws setup) :
    signedAccelerationInMetersPerSecondSquared setup.elevatorAcceleration = 2 := by
  have h_initial :
      signedSpeedReadout LengthUnit.meters TimeUnit.seconds
          setup.initialElevatorVelocity = -10 := by
    simpa only [signedSpeedInMetersPerSecond] using
      data.initialVelocityIsDownward
  have h_final :
      signedSpeedReadout LengthUnit.meters TimeUnit.seconds
          setup.finalElevatorVelocity = 0 := by
    simpa only [signedSpeedInMetersPerSecond] using
      data.finalVelocityAtStop
  have h_displacement :
      signedLengthReadout LengthUnit.meters setup.stoppingDisplacement = -25 := by
    simpa only [signedLengthInMeters] using
      data.stoppingDisplacementIsDownward
  have h_kinematics :=
    laws.constantAccelerationKinematics
      LengthUnit.meters TimeUnit.seconds
  rw [h_final, h_initial, h_displacement] at h_kinematics
  change
    signedAccelerationReadout LengthUnit.meters TimeUnit.seconds
        setup.elevatorAcceleration = 2
  nlinarith

/--
While the elevator is descending with decreasing speed, the ideal scale reads
`590 N` (displayed choice A).

The source's recorded answer metadata says choice B (`390 N`), but that value
would correspond to downward rather than upward acceleration and conflicts
with both the stopping kinematics and the supplied `a_y` arrow.

This formalizes `thm:physics:phyx_mini_0803:target`.
-/
theorem scaleReadingWhileDescendingAndSlowing
    (setup : BathroomScaleElevatorSetup)
    (figure : MatchesSuppliedElevatorFigure setup)
    (data : MatchesElevatorProblemData setup)
    (physical : HasPhysicalElevatorParameters setup)
    (laws : SatisfiesIdealElevatorDynamicsLaws setup) :
    forceMagnitudeInNewtons setup.scaleReading = 590 := by
  have h_mass :
      massReadout MassUnit.kilograms setup.womanMass = 50 := by
    simpa only [massInKilograms] using data.womanMassKilograms
  have h_elevator_acceleration :
      signedAccelerationReadout LengthUnit.meters TimeUnit.seconds
          setup.elevatorAcceleration = 2 := by
    simpa only [signedAccelerationInMetersPerSecondSquared] using
      elevatorAccelerationFromStoppingData setup data laws
  have h_woman_acceleration :
      signedAccelerationReadout LengthUnit.meters TimeUnit.seconds
          setup.womanAccelerationAy = 2 := by
    rw [laws.riderSharesElevatorAcceleration
      LengthUnit.meters TimeUnit.seconds]
    exact h_elevator_acceleration
  have h_weight :
      forceMagnitudeReadout
          MassUnit.kilograms LengthUnit.meters TimeUnit.seconds setup.weightW =
        490 := by
    have h :=
      figure.physicalWeightMatchesFigureLabel
    rw [figure.displayedWeightIs490Newtons] at h
    simpa only [forceMagnitudeInNewtons] using h
  have h_newton :=
    laws.verticalNewtonSecondLaw
      MassUnit.kilograms LengthUnit.meters TimeUnit.seconds
  have h_scale :=
    laws.idealScaleMeasuresNormalForce
      MassUnit.kilograms LengthUnit.meters TimeUnit.seconds
  rw [h_weight, h_mass, h_woman_acceleration] at h_newton
  change
    forceMagnitudeReadout
        MassUnit.kilograms LengthUnit.meters TimeUnit.seconds
        setup.scaleReading = 590
  nlinarith

end PhyXMiniProblems.ProblemPhyXMini0803
