import Mathlib
import Physlib.Units.WithDim.Speed

noncomputable section

namespace PhyXMiniProblems.ProblemPhyXMini0730

open Dimension

/-!
# Limiting braking deceleration for two trains on the same track

The positive longitudinal direction is the rightward direction shown in the
supplied figure. The tracked points are the front of the high-speed train and
the rear of the locomotive, so the pictured distance `D` is their initial
longitudinal separation.

Lengths, elapsed times, speeds, signed longitudinal positions, and acceleration
magnitudes are represented by unit-independent Physlib quantities. Real
numbers below are used only for selected unit readouts, one-dimensional signed
components, figure data, and displayed answer values.
-/

/-! ## Dimensionful physical quantities and readouts -/

/-- The physical dimension of longitudinal acceleration, `L T⁻²`. -/
def accelerationDimension : Dimension := L𝓭 * T𝓭⁻¹ * T𝓭⁻¹

/-- A nonnegative physical length magnitude. -/
abbrev LengthMagnitude : Type := Dimensionful (WithDim L𝓭 NNReal)

/-- A signed longitudinal position along the common track direction. -/
abbrev LongitudinalPosition : Type := Dimensionful (WithDim L𝓭 ℝ)

/-- A nonnegative elapsed-time duration. -/
abbrev TimeDuration : Type := Dimensionful (WithDim T𝓭 NNReal)

/-- A nonnegative physical speed magnitude. -/
abbrev SpeedMagnitude : Type := DimSpeed

/-- A signed longitudinal velocity component. -/
abbrev SignedSpeedQuantity : Type :=
  Dimensionful (WithDim (L𝓭 * T𝓭⁻¹) ℝ)

/-- A nonnegative magnitude of longitudinal acceleration. -/
abbrev AccelerationMagnitude : Type :=
  Dimensionful (WithDim accelerationDimension NNReal)

/-- Read a physical length magnitude in a selected length unit. -/
def lengthReadout
    (unit : LengthUnit) (length : LengthMagnitude) : ℝ :=
  ((length {UnitChoices.SI with length := unit}).val : ℝ)

/-- Read a signed longitudinal position in a selected length unit. -/
def positionReadout
    (unit : LengthUnit) (position : LongitudinalPosition) : ℝ :=
  (position {UnitChoices.SI with length := unit}).val

/-- Read an elapsed time in a selected time unit. -/
def timeReadout (unit : TimeUnit) (time : TimeDuration) : ℝ :=
  ((time {UnitChoices.SI with time := unit}).val : ℝ)

/-- Read a speed magnitude in coherent selected length and time units. -/
def speedReadout
    (lengthUnit : LengthUnit) (timeUnit : TimeUnit)
    (speed : SpeedMagnitude) : ℝ :=
  ((speed {UnitChoices.SI with
    length := lengthUnit, time := timeUnit}).val : ℝ)

/-- Read a signed longitudinal velocity in selected units. -/
def signedSpeedReadout
    (lengthUnit : LengthUnit) (timeUnit : TimeUnit)
    (speed : SignedSpeedQuantity) : ℝ :=
  (speed {UnitChoices.SI with
    length := lengthUnit, time := timeUnit}).val

/-- Read an acceleration magnitude in coherent selected units. -/
def accelerationReadout
    (lengthUnit : LengthUnit) (timeUnit : TimeUnit)
    (acceleration : AccelerationMagnitude) : ℝ :=
  ((acceleration {UnitChoices.SI with
    length := lengthUnit, time := timeUnit}).val : ℝ)

/-- Metre readout for physical lengths. -/
def lengthInMeters (length : LengthMagnitude) : ℝ :=
  lengthReadout LengthUnit.meters length

/-- Metre coordinate along the right-positive track direction. -/
def positionInMeters (position : LongitudinalPosition) : ℝ :=
  positionReadout LengthUnit.meters position

/-- Second readout for the limiting time. -/
def timeInSeconds (time : TimeDuration) : ℝ :=
  timeReadout TimeUnit.seconds time

/-- Kilometre-per-hour readout for the two stated initial speeds. -/
def speedInKilometersPerHour (speed : SpeedMagnitude) : ℝ :=
  speedReadout LengthUnit.kilometers TimeUnit.hours speed

/-- Metre-per-second readout for a speed magnitude. -/
def speedInMetersPerSecond (speed : SpeedMagnitude) : ℝ :=
  speedReadout LengthUnit.meters TimeUnit.seconds speed

/-- Signed metre-per-second longitudinal velocity component. -/
def velocityInMetersPerSecond (speed : SignedSpeedQuantity) : ℝ :=
  signedSpeedReadout LengthUnit.meters TimeUnit.seconds speed

/-- Metre-per-second-squared readout for the braking magnitude. -/
def accelerationInMetersPerSecondSquared
    (acceleration : AccelerationMagnitude) : ℝ :=
  accelerationReadout LengthUnit.meters TimeUnit.seconds acceleration

/-! ## Objects and labels from the supplied railway figure -/

/-- The two rail vehicles labelled in image `730.png`. -/
inductive RailVehicle where
  | highSpeedTrain
  | locomotive
  deriving DecidableEq, Fintype, Repr

/-- Longitudinal direction of each blue velocity arrow in the image. -/
inductive TravelDirection where
  | leftward
  | rightward
  deriving DecidableEq, Fintype, Repr

/-- The three track portions visible in the primary image. -/
inductive TrackRegion where
  | curvedMainLine
  | straightMainLine
  | sidingBranch
  deriving DecidableEq, Fintype, Repr

/-- Literal text labels visible in the primary image. -/
inductive FigureTextLabel where
  | highSpeedTrain
  | locomotive
  | distanceD
  deriving DecidableEq, Fintype, Repr

/-- Endpoints of the double-headed distance marker labelled `D`. -/
inductive DistanceMarkerEndpoint where
  | highSpeedTrainFront
  | locomotiveRear
  deriving DecidableEq, Fintype, Repr

/-!
Qualitative and numerical information transcribed from the supplied figure.
The scalar marker readout is figure evidence; a separate premise relates it to
the independent physical initial separation.
-/
structure SuppliedRailwayFigure where
  vehicleShown : RailVehicle → Bool
  vehicleTrackRegion : RailVehicle → TrackRegion
  forwardArrowShown : RailVehicle → Bool
  arrowDirection : RailVehicle → TravelDirection
  textLabelShown : FigureTextLabel → Bool
  sidingBranchShown : Bool
  sidingMergesIntoMainLine : Bool
  distanceMarkerNearEndpoint : DistanceMarkerEndpoint
  distanceMarkerFarEndpoint : DistanceMarkerEndpoint
  distanceMarkerReadoutMeters : ℝ

/-!
Independent physical quantities and trajectories in the scenario. Coordinate
time is measured in seconds from the instant braking begins. In particular,
the braking deceleration is an independent physical quantity, not a definition
of the recorded answer.
-/
structure TrainBrakingSetup where
  initialSpeed : RailVehicle → SpeedMagnitude
  motionDirection : RailVehicle → TravelDirection
  initialSeparationD : LengthMagnitude
  positionAtSeconds : RailVehicle → ℝ → LongitudinalPosition
  velocityAtSeconds : RailVehicle → ℝ → SignedSpeedQuantity
  brakingDecelerationMagnitude : AccelerationMagnitude
  limitingContactTime : TimeDuration
  figure : SuppliedRailwayFigure

/-! ## Scenario, figure evidence, readouts, and governing laws -/

/-!
Primary-image evidence: the high-speed train is on the curved main-line
approach, the locomotive is on the straight main line beyond the siding merge,
both arrows point right, and `D` spans the high-speed train's front and the
locomotive's rear.
-/
structure MatchesSuppliedRailwayFigure
    (setup : TrainBrakingSetup) : Prop where
  everyVehicleShown :
    ∀ vehicle, setup.figure.vehicleShown vehicle = true
  highSpeedTrainOnCurvedMainLine :
    setup.figure.vehicleTrackRegion .highSpeedTrain = .curvedMainLine
  locomotiveOnStraightMainLine :
    setup.figure.vehicleTrackRegion .locomotive = .straightMainLine
  everyForwardArrowShown :
    ∀ vehicle, setup.figure.forwardArrowShown vehicle = true
  bothFigureArrowsPointRight :
    ∀ vehicle, setup.figure.arrowDirection vehicle = .rightward
  everyTextLabelShown :
    ∀ label, setup.figure.textLabelShown label = true
  sidingIsShown : setup.figure.sidingBranchShown = true
  sidingMergesWithMainLine :
    setup.figure.sidingMergesIntoMainLine = true
  markerStartsAtHighSpeedTrainFront :
    setup.figure.distanceMarkerNearEndpoint = .highSpeedTrainFront
  markerEndsAtLocomotiveRear :
    setup.figure.distanceMarkerFarEndpoint = .locomotiveRear
  markerReads676Meters :
    setup.figure.distanceMarkerReadoutMeters = 676
  markerRepresentsInitialSeparation :
    setup.figure.distanceMarkerReadoutMeters =
      lengthInMeters setup.initialSeparationD

/-!
Numerical data and direction conventions stated in the problem. The
deceleration magnitude and limiting time have no numerical readout here.
-/
structure MatchesProblemReadouts (setup : TrainBrakingSetup) : Prop where
  highSpeedTrainInitialSpeed :
    speedInKilometersPerHour
      (setup.initialSpeed .highSpeedTrain) = 161
  locomotiveInitialSpeed :
    speedInKilometersPerHour
      (setup.initialSpeed .locomotive) = 29
  initialSeparationMeters :
    lengthInMeters setup.initialSeparationD = 676
  highSpeedTrainMovesRight :
    setup.motionDirection .highSpeedTrain = .rightward
  locomotiveMovesRight :
    setup.motionDirection .locomotive = .rightward

/-- Positivity and ordering conditions for the physical braking regime. -/
structure HasPhysicalTrainBrakingParameters
    (setup : TrainBrakingSetup) : Prop where
  separationPositive :
    0 < lengthInMeters setup.initialSeparationD
  decelerationMagnitudePositive :
    0 < accelerationInMetersPerSecondSquared
      setup.brakingDecelerationMagnitude
  highSpeedTrainInitiallyFaster :
    speedInMetersPerSecond (setup.initialSpeed .locomotive) <
      speedInMetersPerSecond (setup.initialSpeed .highSpeedTrain)

/-!
The high-speed train has constant rightward acceleration component `-a`, while
the locomotive continues at its constant rightward speed. These are general
one-dimensional kinematic laws. They contain neither an answer-choice value
nor a closed formula for the requested acceleration.
-/
structure SatisfiesTrainKinematics (setup : TrainBrakingSetup) : Prop where
  initialGap :
    positionInMeters (setup.positionAtSeconds .locomotive 0) -
        positionInMeters (setup.positionAtSeconds .highSpeedTrain 0) =
      lengthInMeters setup.initialSeparationD
  highSpeedTrainInitialVelocity :
    velocityInMetersPerSecond
        (setup.velocityAtSeconds .highSpeedTrain 0) =
      speedInMetersPerSecond (setup.initialSpeed .highSpeedTrain)
  locomotiveInitialVelocity :
    velocityInMetersPerSecond
        (setup.velocityAtSeconds .locomotive 0) =
      speedInMetersPerSecond (setup.initialSpeed .locomotive)
  highSpeedTrainVelocityEvolution :
    ∀ t : ℝ, 0 ≤ t →
      velocityInMetersPerSecond
          (setup.velocityAtSeconds .highSpeedTrain t) =
        velocityInMetersPerSecond
            (setup.velocityAtSeconds .highSpeedTrain 0) -
          accelerationInMetersPerSecondSquared
              setup.brakingDecelerationMagnitude * t
  highSpeedTrainPositionEvolution :
    ∀ t : ℝ, 0 ≤ t →
      positionInMeters (setup.positionAtSeconds .highSpeedTrain t) =
        positionInMeters (setup.positionAtSeconds .highSpeedTrain 0) +
          velocityInMetersPerSecond
              (setup.velocityAtSeconds .highSpeedTrain 0) * t -
            accelerationInMetersPerSecondSquared
                setup.brakingDecelerationMagnitude * t ^ 2 / 2
  locomotiveUniformVelocity :
    ∀ t : ℝ, 0 ≤ t →
      velocityInMetersPerSecond
          (setup.velocityAtSeconds .locomotive t) =
        velocityInMetersPerSecond
          (setup.velocityAtSeconds .locomotive 0)
  locomotiveUniformPosition :
    ∀ t : ℝ, 0 ≤ t →
      positionInMeters (setup.positionAtSeconds .locomotive t) =
        positionInMeters (setup.positionAtSeconds .locomotive 0) +
          velocityInMetersPerSecond
              (setup.velocityAtSeconds .locomotive 0) * t

/-!
The independent limiting time interprets “a collision is just avoided”: the
front of the following train remains strictly behind the locomotive's rear at
all earlier nonnegative times, and at the limiting zero-gap instant their
positions and velocities agree. This is a boundary-event condition, not the
requested numerical deceleration.
-/
structure SatisfiesLimitingNoCollisionCondition
    (setup : TrainBrakingSetup) : Prop where
  limitingTimePositive :
    0 < timeInSeconds setup.limitingContactTime
  separatedBeforeLimitingTime :
    ∀ t : ℝ,
      0 ≤ t →
      t < timeInSeconds setup.limitingContactTime →
        positionInMeters (setup.positionAtSeconds .highSpeedTrain t) <
          positionInMeters (setup.positionAtSeconds .locomotive t)
  positionsAgreeAtLimitingTime :
    positionInMeters
        (setup.positionAtSeconds .highSpeedTrain
          (timeInSeconds setup.limitingContactTime)) =
      positionInMeters
        (setup.positionAtSeconds .locomotive
          (timeInSeconds setup.limitingContactTime))
  velocitiesAgreeAtLimitingTime :
    velocityInMetersPerSecond
        (setup.velocityAtSeconds .highSpeedTrain
          (timeInSeconds setup.limitingContactTime)) =
      velocityInMetersPerSecond
        (setup.velocityAtSeconds .locomotive
          (timeInSeconds setup.limitingContactTime))

/-! ## Displayed answers and current target -/

/-- Labels of the four displayed deceleration choices. -/
inductive AnswerChoice where
  | A
  | B
  | C
  | D
  deriving DecidableEq, Fintype, Repr

/-- Acceleration value in `m/s²` printed beside each answer label. -/
def displayedDecelerationInMetersPerSecondSquared : AnswerChoice → ℝ
  | .A => 824 / 1000
  | .B => 886 / 1000
  | .C => 994 / 1000
  | .D => 998 / 1000

/-- The answer label recorded by the source dataset, retained as metadata. -/
def recordedDatasetAnswer : AnswerChoice := .C

/-- Agreement after rounding an acceleration to three decimal places. -/
def RoundsToNearestThousandth (actual displayed : ℝ) : Prop :=
  displayed - 1 / 2000 ≤ actual ∧ actual < displayed + 1 / 2000

/-- The physical braking magnitude agrees with a displayed choice. -/
def MatchesDisplayedDecelerationChoice
    (setup : TrainBrakingSetup) (choice : AnswerChoice) : Prop :=
  RoundsToNearestThousandth
    (accelerationInMetersPerSecondSquared
      setup.brakingDecelerationMagnitude)
    (displayedDecelerationInMetersPerSecondSquared choice)

/-!
The relative-motion kinematics determine the exact limiting deceleration as
`(161 - 29)^2 / (2 * 676 * 3.6^2) = 3025/3042 m/s²`.
-/
lemma brakingDecelerationInMetersPerSecondSquared_exact
    (setup : TrainBrakingSetup)
    (hFigure : MatchesSuppliedRailwayFigure setup)
    (hReadouts : MatchesProblemReadouts setup)
    (hPhysical : HasPhysicalTrainBrakingParameters setup)
    (hKinematics : SatisfiesTrainKinematics setup)
    (hLimiting : SatisfiesLimitingNoCollisionCondition setup) :
    accelerationInMetersPerSecondSquared
        setup.brakingDecelerationMagnitude =
      (3025 / 3042 : ℝ) := by
  have speedReadout_conversion (speed : SpeedMagnitude) :
      speedInMetersPerSecond speed =
        speedInKilometersPerHour speed * (5 / 18 : ℝ) := by
    let kmhUnits : UnitChoices := {UnitChoices.SI with
      length := LengthUnit.kilometers, time := TimeUnit.hours}
    change ((speed UnitChoices.SI).val : ℝ) =
      ((speed kmhUnits).val : ℝ) * (5 / 18 : ℝ)
    have hUnits := speed.2 kmhUnits UnitChoices.SI
    have hScale :
        kmhUnits.dimScale UnitChoices.SI (L𝓭 * T𝓭⁻¹) =
          (5 / 18 : NNReal) := by
      have hOne := DimSpeed.oneKilometerPerHour_in_SI
      rw [DimSpeed.oneKilometerPerHour,
        CarriesDimension.toDimensionful_apply_apply] at hOne
      have hValue := congrArg WithDim.val hOne
      simpa [kmhUnits] using hValue
    rw [hUnits]
    change
      (↑(kmhUnits.dimScale UnitChoices.SI (L𝓭 * T𝓭⁻¹)) : ℝ) *
          ((speed kmhUnits).val : ℝ) =
        ((speed kmhUnits).val : ℝ) * (5 / 18 : ℝ)
    rw [hScale]
    norm_num only [NNReal.coe_div, NNReal.coe_ofNat]
    ring
  have hHighSpeed :
      speedInMetersPerSecond (setup.initialSpeed .highSpeedTrain) =
        (805 / 18 : ℝ) := by
    rw [speedReadout_conversion,
      hReadouts.highSpeedTrainInitialSpeed]
    norm_num
  have hLocomotiveSpeed :
      speedInMetersPerSecond (setup.initialSpeed .locomotive) =
        (145 / 18 : ℝ) := by
    rw [speedReadout_conversion,
      hReadouts.locomotiveInitialSpeed]
    norm_num
  let t : ℝ := timeInSeconds setup.limitingContactTime
  let a : ℝ := accelerationInMetersPerSecondSquared
    setup.brakingDecelerationMagnitude
  let xHigh : ℝ :=
    positionInMeters (setup.positionAtSeconds .highSpeedTrain 0)
  let xLocomotive : ℝ :=
    positionInMeters (setup.positionAtSeconds .locomotive 0)
  have htPositive : 0 < t := by
    simpa [t] using hLimiting.limitingTimePositive
  have htNonnegative : 0 ≤ t := le_of_lt htPositive
  have hHighInitialVelocity :
      velocityInMetersPerSecond
          (setup.velocityAtSeconds .highSpeedTrain 0) =
        (805 / 18 : ℝ) := by
    rw [hKinematics.highSpeedTrainInitialVelocity, hHighSpeed]
  have hLocomotiveInitialVelocity :
      velocityInMetersPerSecond
          (setup.velocityAtSeconds .locomotive 0) =
        (145 / 18 : ℝ) := by
    rw [hKinematics.locomotiveInitialVelocity, hLocomotiveSpeed]
  have hVelocityEquality := hLimiting.velocitiesAgreeAtLimitingTime
  rw [hKinematics.highSpeedTrainVelocityEvolution t htNonnegative,
    hKinematics.locomotiveUniformVelocity t htNonnegative,
    hHighInitialVelocity, hLocomotiveInitialVelocity] at hVelocityEquality
  change (805 / 18 : ℝ) - a * t = 145 / 18 at hVelocityEquality
  have hAccelerationTime : a * t = (110 / 3 : ℝ) := by
    linarith
  have hPositionEquality := hLimiting.positionsAgreeAtLimitingTime
  rw [hKinematics.highSpeedTrainPositionEvolution t htNonnegative,
    hKinematics.locomotiveUniformPosition t htNonnegative,
    hHighInitialVelocity, hLocomotiveInitialVelocity] at hPositionEquality
  change
    xHigh + (805 / 18 : ℝ) * t - a * t ^ 2 / 2 =
      xLocomotive + (145 / 18 : ℝ) * t at hPositionEquality
  have hInitialGap := hKinematics.initialGap
  rw [hReadouts.initialSeparationMeters] at hInitialGap
  change xLocomotive - xHigh = (676 : ℝ) at hInitialGap
  have hAccelerationTimeSquared :
      a * t ^ 2 = (110 / 3 : ℝ) * t := by
    calc
      a * t ^ 2 = (a * t) * t := by ring
      _ = (110 / 3 : ℝ) * t := by rw [hAccelerationTime]
  have hTime : t = (2028 / 55 : ℝ) := by
    nlinarith [hPositionEquality, hInitialGap,
      hAccelerationTimeSquared]
  rw [hTime] at hAccelerationTime
  nlinarith [hAccelerationTime]

/-!
The exact value is approximately `0.99441 m/s²`, which rounds to
`0.994 m/s²`, answer choice `C`.

This formalizes `thm:physics:phyx_mini_0730:target`.
-/
theorem problem_phyx_mini_0730
    (setup : TrainBrakingSetup)
    (hFigure : MatchesSuppliedRailwayFigure setup)
    (hReadouts : MatchesProblemReadouts setup)
    (hPhysical : HasPhysicalTrainBrakingParameters setup)
    (hKinematics : SatisfiesTrainKinematics setup)
    (hLimiting : SatisfiesLimitingNoCollisionCondition setup) :
    accelerationInMetersPerSecondSquared
          setup.brakingDecelerationMagnitude =
        (3025 / 3042 : ℝ) ∧
      MatchesDisplayedDecelerationChoice setup .C := by
  have hExact :=
    brakingDecelerationInMetersPerSecondSquared_exact
      setup hFigure hReadouts hPhysical hKinematics hLimiting
  refine ⟨hExact, ?_⟩
  unfold MatchesDisplayedDecelerationChoice RoundsToNearestThousandth
  rw [hExact]
  norm_num [displayedDecelerationInMetersPerSecondSquared]

end PhyXMiniProblems.ProblemPhyXMini0730
