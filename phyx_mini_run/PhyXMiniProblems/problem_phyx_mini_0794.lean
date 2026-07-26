import Mathlib
import Physlib.Units.WithDim.Speed

noncomputable section

namespace PhyXMiniProblems.ProblemPhyXMini0794

open Dimension

/-!
# Police pursuit at a school crossing

A motorist passes a school-crossing sign while traveling in the positive
`x`-direction at a constant `15 m/s`. At that instant a police officer,
initially stopped at the sign, begins pursuing with constant positive
`x`-acceleration `3 m/s²`. The school-zone speed limit is `10 m/s`.

Positions, speeds, and acceleration below are unit-independent Physlib
quantities. Real numbers occur only at named-unit readout boundaries, as the
seconds parameter of the one-dimensional trajectories, and as multiple-choice
response values. The kinematic equations are governing-law hypotheses; no
premise states the requested passing time.
-/

/-! ## Dimensionful quantities and coherent-unit readouts -/

/-- A signed one-dimensional position with physical length dimension. -/
abbrev SignedPositionQuantity : Type :=
  Dimensionful (WithDim L𝓭 ℝ)

/-- A nonnegative physical speed carrying length-per-time dimension. -/
abbrev SpeedQuantity : Type := DimSpeed

/-- The physical dimension `L T⁻²` of a linear acceleration magnitude. -/
def accelerationDimension : Dimension :=
  L𝓭 * T𝓭⁻¹ * T𝓭⁻¹

/-- A nonnegative physical linear-acceleration magnitude. -/
abbrev AccelerationMagnitudeQuantity : Type :=
  Dimensionful (WithDim accelerationDimension NNReal)

/-- Read a signed position in a selected length unit. -/
def signedPositionReadout
    (lengthUnit : LengthUnit) (position : SignedPositionQuantity) : ℝ :=
  (position {UnitChoices.SI with length := lengthUnit}).val

/-- Read a speed in coherent selected length and time units. -/
def speedReadout
    (lengthUnit : LengthUnit) (timeUnit : TimeUnit)
    (speed : SpeedQuantity) : ℝ :=
  ((speed {UnitChoices.SI with
    length := lengthUnit, time := timeUnit}).val : ℝ)

/-- Read an acceleration in coherent selected length and time units. -/
def accelerationReadout
    (lengthUnit : LengthUnit) (timeUnit : TimeUnit)
    (acceleration : AccelerationMagnitudeQuantity) : ℝ :=
  ((acceleration {UnitChoices.SI with
    length := lengthUnit, time := timeUnit}).val : ℝ)

/-- SI-metre readout of a signed `x`-position. -/
def positionInMeters (position : SignedPositionQuantity) : ℝ :=
  signedPositionReadout LengthUnit.meters position

/-- Metre-per-second readout of a physical speed. -/
def speedInMetersPerSecond (speed : SpeedQuantity) : ℝ :=
  speedReadout LengthUnit.meters TimeUnit.seconds speed

/-- Kilometre-per-hour readout of a physical speed. -/
def speedInKilometersPerHour (speed : SpeedQuantity) : ℝ :=
  speedReadout LengthUnit.kilometers TimeUnit.hours speed

/-- Metre-per-second-squared readout of an acceleration magnitude. -/
def accelerationInMetersPerSecondSquared
    (acceleration : AccelerationMagnitudeQuantity) : ℝ :=
  accelerationReadout LengthUnit.meters TimeUnit.seconds acceleration

/-!
The problem also reports approximate mile-per-hour conversions. One metre per
second is exactly `3125 / 1397` international miles per hour, so this is a
scalar readout derived from the dimensionful speed rather than a new physical
speed primitive.
-/
def speedInMilesPerHour (speed : SpeedQuantity) : ℝ :=
  speedInMetersPerSecond speed * (3125 : ℝ) / 1397

/-! ## Physical roles and primary-figure vocabulary -/

/-- The two moving bodies distinguished in the pursuit. -/
inductive RoadUser where
  | policeOfficer
  | motorist
  deriving DecidableEq, Fintype, Repr

/-- Directions along the horizontal road axis. -/
inductive AxisDirection where
  | positiveX
  | negativeX
  deriving DecidableEq, Repr

/-- Idealized one-dimensional translational motion regimes. -/
inductive MotionRegime where
  | constantVelocity
  | constantAcceleration
  | other
  deriving DecidableEq, Repr

/-- Objects and graphical features visible in image `794.png`. -/
inductive FigureObject where
  | schoolCrossingSign
  | policeMotorcycle
  | motoristCar
  | roadXAxis
  deriving DecidableEq, Fintype, Repr

/-- Literal position labels visible on the figure's `x`-axis. -/
inductive FigurePositionLabel where
  | originO
  | policeXP
  | motoristXM
  deriving DecidableEq, Fintype, Repr

/-- Literal component labels attached to the two rightward arrows. -/
inductive FigureMotionLabel where
  | policeAccelerationAPx
  | motoristInitialVelocityVM0x
  deriving DecidableEq, Fintype, Repr

/-!
Typed transcription of the supplied raster. The picture gives qualitative
geometry and prints the two kinematic component values, but it contains no
passing-time label and no answer-choice annotation.
-/
structure SuppliedPursuitFigure where
  showsObject : FigureObject → Bool
  showsPositionLabel : FigurePositionLabel → Bool
  showsMotionLabel : FigureMotionLabel → Bool
  schoolSignIsAtOriginO : Bool
  policePositionLabel : FigurePositionLabel
  motoristPositionLabel : FigurePositionLabel
  policeAppearsLeftOfMotorist : Bool
  policeAccelerationArrowDirection : AxisDirection
  motoristVelocityArrowDirection : AxisDirection
  printedPoliceAccelerationMetersPerSecondSquared : ℝ
  printedMotoristVelocityMetersPerSecond : ℝ
  saysPoliceInitiallyAtRest : Bool
  saysPoliceHasConstantXAcceleration : Bool
  saysMotoristHasConstantXVelocity : Bool
  containsNumericalPassingTime : Bool
  containsAnswerChoiceLabel : Bool

/-!
Independent physical data for the school-crossing pursuit. The real argument
of `xPositionAtSeconds` is explicitly an elapsed-time readout in seconds; each
returned position remains a dimensionful physical quantity.
-/
structure SchoolCrossingPursuit where
  figure : SuppliedPursuitFigure
  schoolCrossingOrigin : SignedPositionQuantity
  initialXPosition : RoadUser → SignedPositionQuantity
  xPositionAtSeconds : RoadUser → ℝ → SignedPositionQuantity
  schoolZoneSpeedLimit : SpeedQuantity
  motoristConstantSpeed : SpeedQuantity
  officerInitialSpeed : SpeedQuantity
  officerConstantAcceleration : AccelerationMagnitudeQuantity
  positiveRoadDirection : AxisDirection
  motionRegime : RoadUser → MotionRegime

/-! ## Scenario, prose data, and figure readouts -/

/-!
Qualitative content of “just as the motorist passes the sign, the stopped
officer starts in pursuit.” These assumptions identify the common initial
place and the two motion regimes without assigning any later meeting time.
-/
structure MatchesPursuitScenario (setup : SchoolCrossingPursuit) : Prop where
  roadPointsAlongPositiveX : setup.positiveRoadDirection = .positiveX
  motoristMovesAtConstantVelocity :
    setup.motionRegime .motorist = .constantVelocity
  officerMovesAtConstantAcceleration :
    setup.motionRegime .policeOfficer = .constantAcceleration
  officerStartsAtSign :
    setup.initialXPosition .policeOfficer = setup.schoolCrossingOrigin
  motoristPassesSignAtStart :
    setup.initialXPosition .motorist = setup.schoolCrossingOrigin

/-!
Exact numerical values from the prose and the stated rounded customary-unit
conversions. In particular, no elapsed passing time appears here.
-/
structure MatchesProblemReadouts (setup : SchoolCrossingPursuit) : Prop where
  crossingOriginMeters : positionInMeters setup.schoolCrossingOrigin = 0
  speedLimitMetersPerSecond :
    speedInMetersPerSecond setup.schoolZoneSpeedLimit = 10
  speedLimitKilometersPerHour :
    speedInKilometersPerHour setup.schoolZoneSpeedLimit = 36
  speedLimitAboutTwentyTwoMilesPerHour :
    |speedInMilesPerHour setup.schoolZoneSpeedLimit - 22| < (1 : ℝ) / 2
  motoristSpeedMetersPerSecond :
    speedInMetersPerSecond setup.motoristConstantSpeed = 15
  motoristSpeedKilometersPerHour :
    speedInKilometersPerHour setup.motoristConstantSpeed = 54
  motoristSpeedAboutThirtyFourMilesPerHour :
    |speedInMilesPerHour setup.motoristConstantSpeed - 34| < (1 : ℝ) / 2
  officerInitiallyAtRest :
    speedInMetersPerSecond setup.officerInitialSpeed = 0
  officerAccelerationMetersPerSecondSquared :
    accelerationInMetersPerSecondSquared
      setup.officerConstantAcceleration = 3

/-- Qualitative arrangement and literal values read from image `794.png`. -/
structure MatchesSuppliedFigure (setup : SchoolCrossingPursuit) : Prop where
  everyObjectShown : ∀ object, setup.figure.showsObject object = true
  everyPositionLabelShown :
    ∀ label, setup.figure.showsPositionLabel label = true
  everyMotionLabelShown : ∀ label, setup.figure.showsMotionLabel label = true
  signAtOrigin : setup.figure.schoolSignIsAtOriginO = true
  policeLabelIsXP : setup.figure.policePositionLabel = .policeXP
  motoristLabelIsXM : setup.figure.motoristPositionLabel = .motoristXM
  policeDrawnLeftOfMotorist : setup.figure.policeAppearsLeftOfMotorist = true
  accelerationArrowPointsRight :
    setup.figure.policeAccelerationArrowDirection = .positiveX
  velocityArrowPointsRight :
    setup.figure.motoristVelocityArrowDirection = .positiveX
  printedPoliceAcceleration :
    setup.figure.printedPoliceAccelerationMetersPerSecondSquared = 3
  printedMotoristVelocity :
    setup.figure.printedMotoristVelocityMetersPerSecond = 15
  printedAccelerationRepresentsPhysicalAcceleration :
    setup.figure.printedPoliceAccelerationMetersPerSecondSquared =
      accelerationInMetersPerSecondSquared
        setup.officerConstantAcceleration
  printedVelocityRepresentsPhysicalSpeed :
    setup.figure.printedMotoristVelocityMetersPerSecond =
      speedInMetersPerSecond setup.motoristConstantSpeed
  policeRestCaption : setup.figure.saysPoliceInitiallyAtRest = true
  policeConstantAccelerationCaption :
    setup.figure.saysPoliceHasConstantXAcceleration = true
  motoristConstantVelocityCaption :
    setup.figure.saysMotoristHasConstantXVelocity = true
  noPassingTimePrinted : setup.figure.containsNumericalPassingTime = false
  noAnswerChoicePrinted : setup.figure.containsAnswerChoiceLabel = false

/-! ## Governing one-dimensional kinematics -/

/-!
The standard constant-velocity and constant-acceleration position laws,
written in coherent SI scalar readouts. They apply for every nonnegative
elapsed time and are independent of the desired catch-up time.
-/
structure SatisfiesPursuitKinematics
    (setup : SchoolCrossingPursuit) : Prop where
  motoristPositionLaw :
    ∀ elapsedSeconds : ℝ, 0 ≤ elapsedSeconds →
      positionInMeters
          (setup.xPositionAtSeconds .motorist elapsedSeconds) =
        positionInMeters (setup.initialXPosition .motorist) +
          speedInMetersPerSecond setup.motoristConstantSpeed * elapsedSeconds
  officerPositionLaw :
    ∀ elapsedSeconds : ℝ, 0 ≤ elapsedSeconds →
      positionInMeters
          (setup.xPositionAtSeconds .policeOfficer elapsedSeconds) =
        positionInMeters (setup.initialXPosition .policeOfficer) +
          speedInMetersPerSecond setup.officerInitialSpeed * elapsedSeconds +
          accelerationInMetersPerSecondSquared
              setup.officerConstantAcceleration * elapsedSeconds ^ 2 / 2

/-! ## Passing event and answer choices -/

/-!
An elapsed time is the officer's first positive passing time when the two
positions agree then, the officer is behind at every earlier positive time,
and the officer is ahead at every later time. This definition does not name or
build in the numerical answer.
-/
def IsFirstPositivePassingTime
    (setup : SchoolCrossingPursuit) (elapsedSeconds : ℝ) : Prop :=
  0 < elapsedSeconds ∧
    positionInMeters
        (setup.xPositionAtSeconds .policeOfficer elapsedSeconds) =
      positionInMeters
        (setup.xPositionAtSeconds .motorist elapsedSeconds) ∧
    (∀ earlierSeconds : ℝ,
      0 < earlierSeconds → earlierSeconds < elapsedSeconds →
        positionInMeters
            (setup.xPositionAtSeconds .policeOfficer earlierSeconds) <
          positionInMeters
            (setup.xPositionAtSeconds .motorist earlierSeconds)) ∧
    (∀ laterSeconds : ℝ, elapsedSeconds < laterSeconds →
      positionInMeters
          (setup.xPositionAtSeconds .motorist laterSeconds) <
        positionInMeters
          (setup.xPositionAtSeconds .policeOfficer laterSeconds))

/-- The four displayed multiple-choice responses. -/
inductive AnswerChoice where
  | A
  | B
  | C
  | D
  deriving DecidableEq, Fintype, Repr

/-- Elapsed-time value, in seconds, printed beside an answer choice. -/
def displayedElapsedSeconds : AnswerChoice → ℝ
  | .A => 16
  | .B => 10
  | .C => 7
  | .D => 14

/-- The answer label recorded by the dataset. -/
def recordedDatasetAnswer : AnswerChoice := .B

/-!
Under the scenario, numerical readouts, primary-figure transcription, and the
two governing position laws, the officer's first positive passing time is ten
seconds. Thus it coincides with displayed answer choice `B`.
-/
theorem officer_first_passes_motorist_after_ten_seconds
    (setup : SchoolCrossingPursuit)
    (_scenario : MatchesPursuitScenario setup)
    (_readouts : MatchesProblemReadouts setup)
    (_figure : MatchesSuppliedFigure setup)
    (_kinematics : SatisfiesPursuitKinematics setup) :
    IsFirstPositivePassingTime setup 10 ∧
      displayedElapsedSeconds recordedDatasetAnswer = 10 := by
  constructor
  · refine ⟨by norm_num, ?_, ?_, ?_⟩
    · rw [_kinematics.officerPositionLaw 10 (by norm_num),
        _kinematics.motoristPositionLaw 10 (by norm_num),
        _scenario.officerStartsAtSign, _scenario.motoristPassesSignAtStart,
        _readouts.crossingOriginMeters, _readouts.officerInitiallyAtRest,
        _readouts.officerAccelerationMetersPerSecondSquared,
        _readouts.motoristSpeedMetersPerSecond]
      norm_num
    · intro earlierSeconds hEarlierPositive hEarlierBeforePassing
      rw [_kinematics.officerPositionLaw earlierSeconds
          (le_of_lt hEarlierPositive),
        _kinematics.motoristPositionLaw earlierSeconds
          (le_of_lt hEarlierPositive),
        _scenario.officerStartsAtSign, _scenario.motoristPassesSignAtStart,
        _readouts.crossingOriginMeters, _readouts.officerInitiallyAtRest,
        _readouts.officerAccelerationMetersPerSecondSquared,
        _readouts.motoristSpeedMetersPerSecond]
      nlinarith
    · intro laterSeconds hLaterAfterPassing
      have hLaterNonnegative : 0 ≤ laterSeconds := by
        linarith
      rw [_kinematics.motoristPositionLaw laterSeconds hLaterNonnegative,
        _kinematics.officerPositionLaw laterSeconds hLaterNonnegative,
        _scenario.motoristPassesSignAtStart, _scenario.officerStartsAtSign,
        _readouts.crossingOriginMeters, _readouts.motoristSpeedMetersPerSecond,
        _readouts.officerInitiallyAtRest,
        _readouts.officerAccelerationMetersPerSecondSquared]
      nlinarith
  · rfl

end PhyXMiniProblems.ProblemPhyXMini0794
