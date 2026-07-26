import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Physlib.Units.WithDim.Speed

noncomputable section

namespace PhyXMiniProblems.ProblemPhyXMini0753

open Dimension

/-!
# Wet putty released from a rotating wheel

A lump of putty rides on the rim of a wheel of radius `20.0 cm` and period
`5.00 ms`.  It detaches at the 5 o'clock position while the wheel rotates
counterclockwise.  The tangent there points upward and toward a wall `2.50 m`
away.  The release point is `1.20 m` above the floor.

Physical lengths, durations, speeds, signed velocity components, and
accelerations below are unit-independent Physlib quantities.  Real numbers
occur only as readouts in explicitly selected units, dimensionless angles in
radians, and displayed answer values.

Assumption/target boundary:

* scenario and figure predicates record the supplied measurements, rotation
  sense, clock-face release position, labels `h` and `d`, and visible geometry;
* the terrestrial-gravity predicate records the implicit standard value of
  the local gravitational acceleration;
* the governing-law structure states generic circular-motion and projectile
  relations in arbitrary compatible units;
* neither the exact specialized impact-height expression, the displayed
  `2.64 m`, nor the selection of choice C occurs in a premise.
-/

/-! ## Dimensionful physical quantities and unit readouts -/

/-- A nonnegative, unit-independent physical length. -/
abbrev LengthQuantity : Type :=
  Dimensionful (WithDim L𝓭 NNReal)

/-- A nonnegative, unit-independent elapsed time. -/
abbrev DurationQuantity : Type :=
  Dimensionful (WithDim T𝓭 NNReal)

/-- A signed component of velocity along a chosen Cartesian axis. -/
abbrev SignedVelocityQuantity : Type :=
  Dimensionful (WithDim (L𝓭 * T𝓭⁻¹) ℝ)

/-- A nonnegative acceleration magnitude, used for terrestrial gravity. -/
abbrev AccelerationMagnitude : Type :=
  Dimensionful (WithDim (L𝓭 * T𝓭⁻¹ * T𝓭⁻¹) NNReal)

/-- Read a physical length in a selected length unit. -/
def lengthReadout (unit : LengthUnit) (length : LengthQuantity) : ℝ :=
  ((length {UnitChoices.SI with length := unit}).val : ℝ)

/-- Read a physical duration in a selected time unit. -/
def durationReadout (unit : TimeUnit) (duration : DurationQuantity) : ℝ :=
  ((duration {UnitChoices.SI with time := unit}).val : ℝ)

/-- Read a nonnegative physical speed in selected length and time units. -/
def speedReadout
    (lengthUnit : LengthUnit) (timeUnit : TimeUnit) (speed : DimSpeed) : ℝ :=
  ((speed {UnitChoices.SI with
    length := lengthUnit, time := timeUnit}).val : ℝ)

/-- Read a signed velocity component in selected length and time units. -/
def signedVelocityReadout
    (lengthUnit : LengthUnit) (timeUnit : TimeUnit)
    (velocity : SignedVelocityQuantity) : ℝ :=
  (velocity {UnitChoices.SI with
    length := lengthUnit, time := timeUnit}).val

/-- Read an acceleration magnitude in selected length and time units. -/
def accelerationReadout
    (lengthUnit : LengthUnit) (timeUnit : TimeUnit)
    (acceleration : AccelerationMagnitude) : ℝ :=
  ((acceleration {UnitChoices.SI with
    length := lengthUnit, time := timeUnit}).val : ℝ)

/-- Metre readout of a physical length. -/
def lengthInMetres (length : LengthQuantity) : ℝ :=
  lengthReadout LengthUnit.meters length

/-- Centimetre readout of a physical length. -/
def lengthInCentimetres (length : LengthQuantity) : ℝ :=
  lengthReadout LengthUnit.centimeters length

/-- Second readout of a physical duration. -/
def durationInSeconds (duration : DurationQuantity) : ℝ :=
  durationReadout TimeUnit.seconds duration

/-- Millisecond readout of a physical duration. -/
def durationInMilliseconds (duration : DurationQuantity) : ℝ :=
  durationReadout TimeUnit.milliseconds duration

/-- Metres-per-second readout of a nonnegative physical speed. -/
def speedInMetresPerSecond (speed : DimSpeed) : ℝ :=
  speedReadout LengthUnit.meters TimeUnit.seconds speed

/-- Metres-per-second readout of a signed velocity component. -/
def signedVelocityInMetresPerSecond
    (velocity : SignedVelocityQuantity) : ℝ :=
  signedVelocityReadout LengthUnit.meters TimeUnit.seconds velocity

/-- Metres-per-second-squared readout of an acceleration magnitude. -/
def accelerationInMetresPerSecondSquared
    (acceleration : AccelerationMagnitude) : ℝ :=
  accelerationReadout LengthUnit.meters TimeUnit.seconds acceleration

/-! ## Scenario roles and primary-figure labels -/

/-- Sense in which the wheel rotates in the plane of the figure. -/
inductive RotationSense where
  | counterclockwise
  | clockwise
  deriving DecidableEq, Repr

/-- Clock-face location at which the putty leaves the rim. -/
inductive ClockPosition where
  | fiveOClock
  | other
  deriving DecidableEq, Repr

/-- Physical objects visible in the supplied raster. -/
inductive FigureObject where
  | wheel
  | putty
  | horizontalFloor
  | verticalWall
  deriving DecidableEq, Fintype, Repr

/-- Symbolic dimension labels printed in the supplied raster. -/
inductive FigureLabel where
  | releaseHeightH
  | wallDistanceD
  deriving DecidableEq, Fintype, Repr

/-!
Data transcribed from image 753.  The image supplies visible objects,
orientations, and the meanings of `h` and `d`; it contains no numerical impact
height.
-/
structure SuppliedWheelFigure where
  showsObject : FigureObject → Bool
  showsLabel : FigureLabel → Bool
  heightLabelH : LengthQuantity
  wallDistanceLabelD : LengthQuantity
  puttyShownOnWheelRim : Bool
  floorShownHorizontal : Bool
  wallShownVerticalAndToRight : Bool
  rotationArrowSense : RotationSense
  releaseVelocityArrowPointsUpAndRight : Bool
  containsNumericalImpactHeight : Bool

/-!
All independent physical quantities in the experiment.  In particular,
`flightDurationToWall` and `impactHeight` are observables, not definitions made
from an answer choice; the governing laws below constrain them.
-/
structure WheelPuttySetup where
  wheelRadius : LengthQuantity
  wheelPeriod : DurationQuantity
  rotationSense : RotationSense
  releaseClockPosition : ClockPosition
  releaseHeight : LengthQuantity
  wallDistance : LengthQuantity
  tangentialSpeed : DimSpeed
  /-- Launch direction measured counterclockwise from the positive horizontal. -/
  releaseVelocityAngleRadians : ℝ
  horizontalVelocity : SignedVelocityQuantity
  verticalVelocity : SignedVelocityQuantity
  gravitationalAcceleration : AccelerationMagnitude
  flightDurationToWall : DurationQuantity
  impactHeight : LengthQuantity
  figure : SuppliedWheelFigure

/-! ## Figure, numerical-data, physical-branch, and governing-law assumptions -/

/-!
Numerical and qualitative data stated in the problem prose.  No flight time,
velocity, or impact-height value occurs here.
-/
structure MatchesProblemStatement (setup : WheelPuttySetup) : Prop where
  radiusIsTwentyCentimetres :
    lengthInCentimetres setup.wheelRadius = 20
  periodIsFiveMilliseconds :
    durationInMilliseconds setup.wheelPeriod = 5
  wheelTurnsCounterclockwise :
    setup.rotationSense = .counterclockwise
  releaseOccursAtFiveOClock :
    setup.releaseClockPosition = .fiveOClock
  releaseHeightIsOnePointTwoMetres :
    lengthInMetres setup.releaseHeight = 6 / 5
  wallDistanceIsTwoPointFiveMetres :
    lengthInMetres setup.wallDistance = 5 / 2

/-!
Evidence read from the primary raster.  The `h` and `d` labels denote setup
quantities without assigning the unknown impact height.
-/
structure MatchesSuppliedWheelFigure (setup : WheelPuttySetup) : Prop where
  everyObjectIsShown :
    ∀ object, setup.figure.showsObject object = true
  bothDimensionLabelsAreShown :
    ∀ label, setup.figure.showsLabel label = true
  heightLabelDenotesReleaseHeight :
    setup.figure.heightLabelH = setup.releaseHeight
  distanceLabelDenotesWallDistance :
    setup.figure.wallDistanceLabelD = setup.wallDistance
  puttyIsShownOnRim :
    setup.figure.puttyShownOnWheelRim = true
  floorIsHorizontal :
    setup.figure.floorShownHorizontal = true
  wallIsVerticalAndToRight :
    setup.figure.wallShownVerticalAndToRight = true
  rasterRotationArrowIsCounterclockwise :
    setup.figure.rotationArrowSense = .counterclockwise
  tangentArrowPointsTowardAndUpTheWall :
    setup.figure.releaseVelocityArrowPointsUpAndRight = true
  rasterDoesNotContainNumericalAnswer :
    setup.figure.containsNumericalImpactHeight = false

/-!
The standard near-Earth gravitational acceleration used implicitly by this
elementary projectile problem.  It is environmental input, not the requested
height.
-/
structure UsesStandardTerrestrialGravity (setup : WheelPuttySetup) : Prop where
  gravityInSI :
    accelerationInMetresPerSecondSquared setup.gravitationalAcceleration =
      981 / 100

/-!
Positivity and branch conditions selecting the depicted motion.  These fields
rule out degenerate solutions without fixing the impact height.
-/
structure HasPhysicalWheelPuttyParameters (setup : WheelPuttySetup) : Prop where
  radiusPositive : 0 < lengthInMetres setup.wheelRadius
  periodPositive : 0 < durationInSeconds setup.wheelPeriod
  wallDistancePositive : 0 < lengthInMetres setup.wallDistance
  tangentialSpeedPositive : 0 < speedInMetresPerSecond setup.tangentialSpeed
  horizontalVelocityTowardWall :
    0 < signedVelocityInMetresPerSecond setup.horizontalVelocity
  verticalVelocityInitiallyUpward :
    0 < signedVelocityInMetresPerSecond setup.verticalVelocity
  gravityPositive :
    0 < accelerationInMetresPerSecondSquared setup.gravitationalAcceleration
  flightDurationPositive :
    0 < durationInSeconds setup.flightDurationToWall

/-!
The governing uniform-circular-motion, tangential-release, and constant-gravity
projectile laws.  Each dimensional equation is stated for arbitrary compatible
length and time units.  These laws contain no supplied numerical measurement,
displayed answer, or specialized impact-height result.
-/
structure SatisfiesCircularReleaseAndProjectileLaws
    (setup : WheelPuttySetup) : Prop where
  uniformCircularTangentialSpeed : ∀ lengthUnit timeUnit,
    speedReadout lengthUnit timeUnit setup.tangentialSpeed =
      2 * Real.pi * lengthReadout lengthUnit setup.wheelRadius /
        durationReadout timeUnit setup.wheelPeriod
  counterclockwiseTangentAtFiveOClock :
    setup.rotationSense = .counterclockwise →
      setup.releaseClockPosition = .fiveOClock →
        setup.releaseVelocityAngleRadians = Real.pi / 6
  horizontalVelocityComponent : ∀ lengthUnit timeUnit,
    signedVelocityReadout lengthUnit timeUnit setup.horizontalVelocity =
      speedReadout lengthUnit timeUnit setup.tangentialSpeed *
        Real.cos setup.releaseVelocityAngleRadians
  verticalVelocityComponent : ∀ lengthUnit timeUnit,
    signedVelocityReadout lengthUnit timeUnit setup.verticalVelocity =
      speedReadout lengthUnit timeUnit setup.tangentialSpeed *
        Real.sin setup.releaseVelocityAngleRadians
  horizontalFlightToWall : ∀ lengthUnit timeUnit,
    lengthReadout lengthUnit setup.wallDistance =
      signedVelocityReadout lengthUnit timeUnit setup.horizontalVelocity *
        durationReadout timeUnit setup.flightDurationToWall
  verticalConstantGravityFlight : ∀ lengthUnit timeUnit,
    lengthReadout lengthUnit setup.impactHeight =
      lengthReadout lengthUnit setup.releaseHeight +
        signedVelocityReadout lengthUnit timeUnit setup.verticalVelocity *
          durationReadout timeUnit setup.flightDurationToWall -
        accelerationReadout lengthUnit timeUnit
            setup.gravitationalAcceleration *
          (durationReadout timeUnit setup.flightDurationToWall) ^ 2 / 2

/-! ## Derived flight time and multiple-choice impact height -/

/-- Labels of the four metre-valued answer choices. -/
inductive AnswerChoice where
  | A
  | B
  | C
  | D
  deriving DecidableEq, Fintype, Repr

/-- Height in metres printed beside each answer label. -/
def displayedImpactHeightMetres : AnswerChoice → ℝ
  | .A => 64 / 25
  | .B => 13 / 5
  | .C => 66 / 25
  | .D => 133 / 50

/-- Answer label recorded in the source dataset. -/
def recordedDatasetAnswer : AnswerChoice := .C

/-!
A physical height agrees with a value displayed to the nearest hundredth of a
metre when its metre readout differs by less than half a hundredth.
-/
def RoundsToDisplayedHundredth
    (height : LengthQuantity) (choice : AnswerChoice) : Prop :=
  |lengthInMetres height - displayedImpactHeightMetres choice| < 1 / 200

/-- A choice is the unique displayed hundredth matching the impact height. -/
def IsUniqueRoundedAnswer
    (height : LengthQuantity) (choice : AnswerChoice) : Prop :=
  RoundsToDisplayedHundredth height choice ∧
    ∀ other : AnswerChoice,
      RoundsToDisplayedHundredth height other → other = choice

/-!
The wall is reached after horizontal distance divided by the horizontal
tangent-speed component.  This is a derived conclusion, not a premise.
-/
lemma flightDurationToWallInSeconds
    (setup : WheelPuttySetup)
    (_problem : MatchesProblemStatement setup)
    (_physical : HasPhysicalWheelPuttyParameters setup)
    (_laws : SatisfiesCircularReleaseAndProjectileLaws setup) :
    durationInSeconds setup.flightDurationToWall =
      (5 / 2 : ℝ) /
        ((2 * Real.pi * (1 / 5 : ℝ) / (1 / 200 : ℝ)) *
          Real.cos (Real.pi / 6)) := by
  let ucm : UnitChoices :=
    {UnitChoices.SI with length := LengthUnit.centimeters}
  have hfacCm :
      UnitChoices.dimScale UnitChoices.SI ucm L𝓭 = (100 : NNReal) := by
    simp only [UnitChoices.dimScale_apply, ucm, UnitChoices.SI_length,
      UnitChoices.SI_time, UnitChoices.SI_mass, UnitChoices.SI_charge,
      UnitChoices.SI_temperature, Dimension.L𝓭, Rat.cast_one, Rat.cast_zero,
      NNReal.rpow_one, NNReal.rpow_zero, mul_one]
    apply NNReal.eq
    simp only [LengthUnit.div_eq_val, LengthUnit.meters,
      LengthUnit.centimeters, LengthUnit.scale]
    norm_num
    rfl
  have hradiusScale := setup.wheelRadius.2 UnitChoices.SI ucm
  rw [WithDim.dim_apply, hfacCm] at hradiusScale
  have hradiusVal :=
    congrArg (fun x : WithDim L𝓭 NNReal => (x.val : ℝ)) hradiusScale
  change lengthInCentimetres setup.wheelRadius =
    100 * lengthInMetres setup.wheelRadius at hradiusVal
  have hradius : lengthInMetres setup.wheelRadius = 1 / 5 := by
    norm_num at hradiusVal ⊢
    linarith [_problem.radiusIsTwentyCentimetres]
  let ums : UnitChoices :=
    {UnitChoices.SI with time := TimeUnit.milliseconds}
  have hfacMs :
      UnitChoices.dimScale UnitChoices.SI ums T𝓭 = (1000 : NNReal) := by
    simp only [UnitChoices.dimScale_apply, ums, UnitChoices.SI_length,
      UnitChoices.SI_time, UnitChoices.SI_mass, UnitChoices.SI_charge,
      UnitChoices.SI_temperature, Dimension.T𝓭, Rat.cast_one, Rat.cast_zero,
      NNReal.rpow_one, NNReal.rpow_zero, one_mul, mul_one]
    apply NNReal.eq
    simp only [TimeUnit.div_eq_val, TimeUnit.seconds, TimeUnit.milliseconds,
      TimeUnit.scale]
    norm_num
    rfl
  have hperiodScale := setup.wheelPeriod.2 UnitChoices.SI ums
  rw [WithDim.dim_apply, hfacMs] at hperiodScale
  have hperiodVal :=
    congrArg (fun x : WithDim T𝓭 NNReal => (x.val : ℝ)) hperiodScale
  change durationInMilliseconds setup.wheelPeriod =
    1000 * durationInSeconds setup.wheelPeriod at hperiodVal
  have hperiod : durationInSeconds setup.wheelPeriod = 1 / 200 := by
    norm_num at hperiodVal ⊢
    linarith [_problem.periodIsFiveMilliseconds]
  have hangle := _laws.counterclockwiseTangentAtFiveOClock
    _problem.wheelTurnsCounterclockwise _problem.releaseOccursAtFiveOClock
  have hspeed := _laws.uniformCircularTangentialSpeed
    LengthUnit.meters TimeUnit.seconds
  change speedInMetresPerSecond setup.tangentialSpeed =
    2 * Real.pi * lengthInMetres setup.wheelRadius /
      durationInSeconds setup.wheelPeriod at hspeed
  rw [hradius, hperiod] at hspeed
  have hhorizontal := _laws.horizontalVelocityComponent
    LengthUnit.meters TimeUnit.seconds
  change signedVelocityInMetresPerSecond setup.horizontalVelocity =
    speedInMetresPerSecond setup.tangentialSpeed *
      Real.cos setup.releaseVelocityAngleRadians at hhorizontal
  rw [hangle, hspeed] at hhorizontal
  have hwall :=
    _laws.horizontalFlightToWall LengthUnit.meters TimeUnit.seconds
  change lengthInMetres setup.wallDistance =
    signedVelocityInMetresPerSecond setup.horizontalVelocity *
      durationInSeconds setup.flightDurationToWall at hwall
  rw [_problem.wallDistanceIsTwoPointFiveMetres, hhorizontal] at hwall
  have hdenpos :
      0 < (2 * Real.pi * (1 / 5 : ℝ) / (1 / 200 : ℝ)) *
        Real.cos (Real.pi / 6) := by
    rw [← hhorizontal]
    exact _physical.horizontalVelocityTowardWall
  apply (eq_div_iff (ne_of_gt hdenpos)).2
  nlinarith [hwall]

/-!
Uniform circular motion gives tangent speed `2 * pi * r / T`; at 5 o'clock
counterclockwise its components have launch angle `pi / 6`.  Horizontal motion
then determines the flight time, and the constant-gravity vertical law gives
the exact expression below.  Its value rounds to `2.64 m`, uniquely selecting
choice C.

This theorem formalizes blueprint label
`thm:physics:phyx_mini_0753:target`.
-/
theorem puttyImpactHeightAtWall
    (setup : WheelPuttySetup)
    (_problem : MatchesProblemStatement setup)
    (_figure : MatchesSuppliedWheelFigure setup)
    (_gravity : UsesStandardTerrestrialGravity setup)
    (_physical : HasPhysicalWheelPuttyParameters setup)
    (_laws : SatisfiesCircularReleaseAndProjectileLaws setup) :
    lengthInMetres setup.impactHeight =
        (6 / 5 : ℝ) +
          ((2 * Real.pi * (1 / 5 : ℝ) / (1 / 200 : ℝ)) *
              Real.sin (Real.pi / 6)) *
            ((5 / 2 : ℝ) /
              ((2 * Real.pi * (1 / 5 : ℝ) / (1 / 200 : ℝ)) *
                Real.cos (Real.pi / 6))) -
          (981 / 100 : ℝ) *
            ((5 / 2 : ℝ) /
              ((2 * Real.pi * (1 / 5 : ℝ) / (1 / 200 : ℝ)) *
                Real.cos (Real.pi / 6))) ^ 2 / 2 ∧
      IsUniqueRoundedAnswer setup.impactHeight .C := by
  let ucm : UnitChoices :=
    {UnitChoices.SI with length := LengthUnit.centimeters}
  have hfacCm :
      UnitChoices.dimScale UnitChoices.SI ucm L𝓭 = (100 : NNReal) := by
    simp only [UnitChoices.dimScale_apply, ucm, UnitChoices.SI_length,
      UnitChoices.SI_time, UnitChoices.SI_mass, UnitChoices.SI_charge,
      UnitChoices.SI_temperature, Dimension.L𝓭, Rat.cast_one, Rat.cast_zero,
      NNReal.rpow_one, NNReal.rpow_zero, mul_one]
    apply NNReal.eq
    simp only [LengthUnit.div_eq_val, LengthUnit.meters,
      LengthUnit.centimeters, LengthUnit.scale]
    norm_num
    rfl
  have hradiusScale := setup.wheelRadius.2 UnitChoices.SI ucm
  rw [WithDim.dim_apply, hfacCm] at hradiusScale
  have hradiusVal :=
    congrArg (fun x : WithDim L𝓭 NNReal => (x.val : ℝ)) hradiusScale
  change lengthInCentimetres setup.wheelRadius =
    100 * lengthInMetres setup.wheelRadius at hradiusVal
  have hradius : lengthInMetres setup.wheelRadius = 1 / 5 := by
    norm_num at hradiusVal ⊢
    linarith [_problem.radiusIsTwentyCentimetres]
  let ums : UnitChoices :=
    {UnitChoices.SI with time := TimeUnit.milliseconds}
  have hfacMs :
      UnitChoices.dimScale UnitChoices.SI ums T𝓭 = (1000 : NNReal) := by
    simp only [UnitChoices.dimScale_apply, ums, UnitChoices.SI_length,
      UnitChoices.SI_time, UnitChoices.SI_mass, UnitChoices.SI_charge,
      UnitChoices.SI_temperature, Dimension.T𝓭, Rat.cast_one, Rat.cast_zero,
      NNReal.rpow_one, NNReal.rpow_zero, one_mul, mul_one]
    apply NNReal.eq
    simp only [TimeUnit.div_eq_val, TimeUnit.seconds, TimeUnit.milliseconds,
      TimeUnit.scale]
    norm_num
    rfl
  have hperiodScale := setup.wheelPeriod.2 UnitChoices.SI ums
  rw [WithDim.dim_apply, hfacMs] at hperiodScale
  have hperiodVal :=
    congrArg (fun x : WithDim T𝓭 NNReal => (x.val : ℝ)) hperiodScale
  change durationInMilliseconds setup.wheelPeriod =
    1000 * durationInSeconds setup.wheelPeriod at hperiodVal
  have hperiod : durationInSeconds setup.wheelPeriod = 1 / 200 := by
    norm_num at hperiodVal ⊢
    linarith [_problem.periodIsFiveMilliseconds]
  have hangle := _laws.counterclockwiseTangentAtFiveOClock
    _problem.wheelTurnsCounterclockwise _problem.releaseOccursAtFiveOClock
  have hspeed := _laws.uniformCircularTangentialSpeed
    LengthUnit.meters TimeUnit.seconds
  change speedInMetresPerSecond setup.tangentialSpeed =
    2 * Real.pi * lengthInMetres setup.wheelRadius /
      durationInSeconds setup.wheelPeriod at hspeed
  rw [hradius, hperiod] at hspeed
  have hvertical := _laws.verticalVelocityComponent
    LengthUnit.meters TimeUnit.seconds
  change signedVelocityInMetresPerSecond setup.verticalVelocity =
    speedInMetresPerSecond setup.tangentialSpeed *
      Real.sin setup.releaseVelocityAngleRadians at hvertical
  rw [hangle, hspeed] at hvertical
  have htime := flightDurationToWallInSeconds setup _problem _physical _laws
  have hflight := _laws.verticalConstantGravityFlight
    LengthUnit.meters TimeUnit.seconds
  change lengthInMetres setup.impactHeight =
    lengthInMetres setup.releaseHeight +
      signedVelocityInMetresPerSecond setup.verticalVelocity *
        durationInSeconds setup.flightDurationToWall -
      accelerationInMetresPerSecondSquared setup.gravitationalAcceleration *
        (durationInSeconds setup.flightDurationToWall) ^ 2 / 2 at hflight
  rw [_problem.releaseHeightIsOnePointTwoMetres, hvertical, htime,
    _gravity.gravityInSI] at hflight
  constructor
  · exact hflight
  · have hsqrtPos : 0 < Real.sqrt 3 :=
      Real.sqrt_pos.2 (by norm_num)
    have hsqrtSq : (Real.sqrt 3) ^ 2 = 3 := by
      norm_num
    have hcompact :
        lengthInMetres setup.impactHeight =
          6 / 5 + 5 / (2 * Real.sqrt 3) -
            327 / (51200 * Real.pi ^ 2) := by
      rw [hflight, Real.sin_pi_div_six, Real.cos_pi_div_six]
      have hpi : Real.pi ≠ 0 := ne_of_gt Real.pi_pos
      have hsqrt : Real.sqrt 3 ≠ 0 := ne_of_gt hsqrtPos
      field_simp
      nlinarith
    have hsqrtLower : (1731 / 1000 : ℝ) < Real.sqrt 3 := by
      nlinarith
    have hsqrtUpper : Real.sqrt 3 < (1733 / 1000 : ℝ) := by
      nlinarith
    have hverticalUpper :
        5 / (2 * Real.sqrt 3) < (289 / 200 : ℝ) := by
      apply (div_lt_iff₀ (by positivity)).2
      nlinarith
    have hverticalLower :
        (36 / 25 : ℝ) < 5 / (2 * Real.sqrt 3) := by
      apply (lt_div_iff₀ (by positivity)).2
      nlinarith
    have hgravityPos :
        0 < 327 / (51200 * Real.pi ^ 2) := by
      positivity
    have hgravityLt :
        327 / (51200 * Real.pi ^ 2) < (1 / 500 : ℝ) := by
      apply (div_lt_iff₀ (by positivity)).2
      nlinarith [Real.two_le_pi, Real.pi_pos]
    have hroundC : RoundsToDisplayedHundredth setup.impactHeight .C := by
      unfold RoundsToDisplayedHundredth
      simp only [displayedImpactHeightMetres]
      rw [hcompact, abs_lt]
      constructor <;> norm_num <;> nlinarith
    refine ⟨hroundC, ?_⟩
    intro other hother
    cases other
    case C => rfl
    all_goals
      exfalso
      unfold RoundsToDisplayedHundredth at hroundC hother
      rw [abs_lt] at hroundC hother
      norm_num [displayedImpactHeightMetres] at hroundC hother
      linarith

end PhyXMiniProblems.ProblemPhyXMini0753
