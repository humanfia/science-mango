import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.Real.Sqrt
import Physlib.SpaceAndTime.Space.LengthUnit
import Physlib.Units.WithDim.Basic

noncomputable section

namespace PhyXMiniProblems.ProblemPhyXMini0772

open Dimension

/-!
# Angle turned by a disk while a tangentially pulled ball accelerates

A disk of radius `25.0 cm` turns freely about a fixed axle through its center,
perpendicular to the disk. A thin, strong string is wrapped around the rim and
attached to a ball. The ball's tangential acceleration obeys `a(t) = A t`, the
disk starts from rest, and `a(3 s) = 1.80 m/s²`. The target is the angle turned
when the disk reaches `15.0 rad/s`.

Dimensionful physical quantities use Physlib. Real scalars are used only for
SI-coordinate readouts, dimensionless radian angles, and displayed numerical
answer choices.
-/

/-! ## Dimensionful quantities and unit readouts -/

/-- The physical dimension `L T⁻²` of linear acceleration. -/
def accelerationDimension : Dimension := L𝓭 * T𝓭⁻¹ * T𝓭⁻¹

/-- The physical dimension `L T⁻³` of the coefficient in `a(t) = A t`. -/
def accelerationSlopeDimension : Dimension :=
  L𝓭 * T𝓭⁻¹ * T𝓭⁻¹ * T𝓭⁻¹

/-- The physical dimension `M L T⁻²` of a force magnitude. -/
def forceDimension : Dimension := M𝓭 * L𝓭 * T𝓭⁻¹ * T𝓭⁻¹

/-- A nonnegative, unit-independent physical length. -/
abbrev LengthQuantity : Type := Dimensionful (WithDim L𝓭 NNReal)

/-- A nonnegative, unit-independent physical time. -/
abbrev TimeQuantity : Type := Dimensionful (WithDim T𝓭 NNReal)

/-- A nonnegative, unit-independent force magnitude. -/
abbrev ForceQuantity : Type := Dimensionful (WithDim forceDimension NNReal)

/-- A nonnegative, unit-independent linear-acceleration magnitude. -/
abbrev AccelerationQuantity : Type :=
  Dimensionful (WithDim accelerationDimension NNReal)

/-- A nonnegative, unit-independent acceleration slope. -/
abbrev AccelerationSlopeQuantity : Type :=
  Dimensionful (WithDim accelerationSlopeDimension NNReal)

/-- A nonnegative angular speed; radians are dimensionless. -/
abbrev AngularSpeedQuantity : Type :=
  Dimensionful (WithDim T𝓭⁻¹ NNReal)

/-- A nonnegative angular acceleration; radians are dimensionless. -/
abbrev AngularAccelerationQuantity : Type :=
  Dimensionful (WithDim (T𝓭⁻¹ * T𝓭⁻¹) NNReal)

/-- Read a physical length in a selected length unit. -/
def lengthReadout (unit : LengthUnit) (length : LengthQuantity) : ℝ :=
  ((length {UnitChoices.SI with length := unit}).val : ℝ)

/-- Read a physical time in a selected time unit. -/
def timeReadout (unit : TimeUnit) (time : TimeQuantity) : ℝ :=
  ((time {UnitChoices.SI with time := unit}).val : ℝ)

/-- Read a force in the coherent unit induced by selected base units. -/
def forceReadout
    (massUnit : MassUnit) (lengthUnit : LengthUnit) (timeUnit : TimeUnit)
    (force : ForceQuantity) : ℝ :=
  ((force {UnitChoices.SI with
    mass := massUnit, length := lengthUnit, time := timeUnit}).val : ℝ)

/-- Read a linear acceleration in selected length and time units. -/
def accelerationReadout
    (lengthUnit : LengthUnit) (timeUnit : TimeUnit)
    (acceleration : AccelerationQuantity) : ℝ :=
  ((acceleration {UnitChoices.SI with
    length := lengthUnit, time := timeUnit}).val : ℝ)

/-- Read an acceleration slope in selected length and time units. -/
def accelerationSlopeReadout
    (lengthUnit : LengthUnit) (timeUnit : TimeUnit)
    (slope : AccelerationSlopeQuantity) : ℝ :=
  ((slope {UnitChoices.SI with
    length := lengthUnit, time := timeUnit}).val : ℝ)

/-- Read angular speed in radians per selected time unit. -/
def angularSpeedReadout
    (timeUnit : TimeUnit) (angularSpeed : AngularSpeedQuantity) : ℝ :=
  ((angularSpeed {UnitChoices.SI with time := timeUnit}).val : ℝ)

/-- Read angular acceleration in radians per selected time unit squared. -/
def angularAccelerationReadout
    (timeUnit : TimeUnit)
    (angularAcceleration : AngularAccelerationQuantity) : ℝ :=
  ((angularAcceleration {UnitChoices.SI with time := timeUnit}).val : ℝ)

/-- Metre readout of a physical length. -/
def lengthInMeters (length : LengthQuantity) : ℝ :=
  lengthReadout LengthUnit.meters length

/-- Centimetre readout used for the stated disk radius. -/
def lengthInCentimeters (length : LengthQuantity) : ℝ :=
  lengthReadout LengthUnit.centimeters length

/-- Second readout of a physical time. -/
def timeInSeconds (time : TimeQuantity) : ℝ :=
  timeReadout TimeUnit.seconds time

/-- Newton readout of the applied pull magnitude. -/
def forceInNewtons (force : ForceQuantity) : ℝ :=
  forceReadout MassUnit.kilograms LengthUnit.meters TimeUnit.seconds force

/-- SI readout in metres per second squared. -/
def accelerationInMetersPerSecondSquared
    (acceleration : AccelerationQuantity) : ℝ :=
  accelerationReadout LengthUnit.meters TimeUnit.seconds acceleration

/-- SI readout in metres per second cubed. -/
def accelerationSlopeInMetersPerSecondCubed
    (slope : AccelerationSlopeQuantity) : ℝ :=
  accelerationSlopeReadout LengthUnit.meters TimeUnit.seconds slope

/-- SI angular-speed readout in radians per second. -/
def angularSpeedInRadiansPerSecond
    (angularSpeed : AngularSpeedQuantity) : ℝ :=
  angularSpeedReadout TimeUnit.seconds angularSpeed

/-- SI angular-acceleration readout in radians per second squared. -/
def angularAccelerationInRadiansPerSecondSquared
    (angularAcceleration : AngularAccelerationQuantity) : ℝ :=
  angularAccelerationReadout TimeUnit.seconds angularAcceleration

/-! ## Physical roles and primary-raster vocabulary -/

/-- The disk's fixed-axis constraint stated in the prose. -/
inductive AxleConstraint where
  | throughCenterPerpendicularAndFreeToTurn
  | other
  deriving DecidableEq, Repr

/-- The idealization of the string wrapped on the rim. -/
inductive StringModel where
  | veryThinStrongWrappedAroundRim
  | other
  deriving DecidableEq, Repr

/-- Direction assigned to the pull relative to the circular rim. -/
inductive PullDirection where
  | tangentiallyAwayFromRim
  | other
  deriving DecidableEq, Repr

/-- Positive sense used for scalar angular observables. -/
inductive RotationSense where
  | clockwise
  | counterclockwise
  deriving DecidableEq, Repr

/-- Physical objects and marks visible in the supplied raster. -/
inductive FigureObject where
  | disk
  | centralAxleDot
  | stringSegment
  | ball
  | pullArrow
  deriving DecidableEq, Fintype, Repr

/-- Locations of the three literal text labels visible in the raster. -/
inductive FigureLabelLocation where
  | besideDisk
  | aboveBall
  | besidePullArrow
  deriving DecidableEq, Fintype, Repr

/-- Literal text carried by a figure label. -/
inductive FigureLabelText where
  | disk
  | ball
  | pull
  deriving DecidableEq, Repr

/-- The label text expected at each location in the primary raster. -/
def expectedFigureLabel : FigureLabelLocation → FigureLabelText
  | .besideDisk => .disk
  | .aboveBall => .ball
  | .besidePullArrow => .pull

/-!
Typed qualitative content read directly from image `772.png`. In particular,
the raster shows a thin horizontal string leaving the top of the disk
tangentially; it does not show the gray rigid rod described by the auxiliary
caption. No metric value is inferred from pixel coordinates.
-/
structure SuppliedDiskBallFigure where
  showsObject : FigureObject → Bool
  showsLabelAt : FigureLabelLocation → Bool
  labelText : FigureLabelLocation → FigureLabelText
  axleDotAtDiskCenter : Bool
  stringLeavesRimAtTop : Bool
  stringIsHorizontalAtContact : Bool
  ballLiesAtRightStringEnd : Bool
  pullArrowStartsAtBall : Bool
  pullArrowPointsRight : Bool
  showsRigidConnectingRod : Bool
  containsNumericalAngleValue : Bool
  containsNumericalAngularSpeedValue : Bool

/-!
Independent physical parameters and observables. The target event time and
turned angle are independent observables constrained only by source data and
governing laws; neither is defined from an answer choice or solved formula.
-/
structure DiskBallUnwindingSetup where
  figure : SuppliedDiskBallFigure
  axleConstraint : AxleConstraint
  stringModel : StringModel
  stringAttachedToBall : Bool
  pullDirection : PullDirection
  positiveRotationSense : RotationSense
  diskRadius : LengthQuantity
  initialTime : TimeQuantity
  thirdSecondObservationTime : TimeQuantity
  targetAngularSpeedEventTime : TimeQuantity
  appliedPullMagnitudeAtSeconds : ℝ → ForceQuantity
  ballTangentialAccelerationAtSeconds : ℝ → AccelerationQuantity
  accelerationSlope : AccelerationSlopeQuantity
  diskAngularAccelerationAtSeconds : ℝ → AngularAccelerationQuantity
  diskAngularSpeedAtSeconds : ℝ → AngularSpeedQuantity
  diskTurnedAngleRadiansAtSeconds : ℝ → ℝ
  unwoundStringLengthAtSeconds : ℝ → LengthQuantity

/-! ## Scenario, figure evidence, source readouts, and governing laws -/

/-- Qualitative assignments from the prose, including the increasing pull. -/
structure MatchesProblemScenario (setup : DiskBallUnwindingSetup) : Prop where
  diskTurnsOnStatedAxle :
    setup.axleConstraint = .throughCenterPerpendicularAndFreeToTurn
  stringMatchesDescription :
    setup.stringModel = .veryThinStrongWrappedAroundRim
  ballIsAttachedToString : setup.stringAttachedToBall = true
  pullIsTangential : setup.pullDirection = .tangentiallyAwayFromRim
  clockwiseIsPositive : setup.positiveRotationSense = .clockwise
  pullMagnitudeStrictlyIncreases :
    ∀ {t₁ t₂ : ℝ}, 0 ≤ t₁ → t₁ < t₂ →
      forceInNewtons (setup.appliedPullMagnitudeAtSeconds t₁) <
        forceInNewtons (setup.appliedPullMagnitudeAtSeconds t₂)

/-!
Objects, literal labels, and incidences transcribed from the primary image.
This evidence contains neither the requested angle nor its numerical answer.
-/
structure MatchesSuppliedFigure (setup : DiskBallUnwindingSetup) : Prop where
  everyObjectShown :
    ∀ object : FigureObject, setup.figure.showsObject object = true
  everyLabelShown :
    ∀ location : FigureLabelLocation,
      setup.figure.showsLabelAt location = true
  everyLabelCorrect :
    ∀ location : FigureLabelLocation,
      setup.figure.labelText location = expectedFigureLabel location
  axleMarkedAtCenter : setup.figure.axleDotAtDiskCenter = true
  topRimContact : setup.figure.stringLeavesRimAtTop = true
  tangentStringIsHorizontal : setup.figure.stringIsHorizontalAtContact = true
  ballAttachedAtRightEnd : setup.figure.ballLiesAtRightStringEnd = true
  pullAppliedAtBall : setup.figure.pullArrowStartsAtBall = true
  pullPointsRight : setup.figure.pullArrowPointsRight = true
  noRigidRodShown : setup.figure.showsRigidConnectingRod = false
  requestedAngleNotPrinted : setup.figure.containsNumericalAngleValue = false
  numericalAngularSpeedNotPrinted :
    setup.figure.containsNumericalAngularSpeedValue = false

/-!
Numerical data and initial conditions from the problem. Angle zero at the
initial instant is the coordinate convention for "angle turned". No event
time, event angle, or answer-choice value occurs here.
-/
structure MatchesProblemReadouts (setup : DiskBallUnwindingSetup) : Prop where
  radiusInCentimeters : lengthInCentimeters setup.diskRadius = 25
  initialTimeIsZero : timeInSeconds setup.initialTime = 0
  observationAtEndOfThirdSecond :
    timeInSeconds setup.thirdSecondObservationTime = 3
  observedBallAcceleration :
    accelerationInMetersPerSecondSquared
        (setup.ballTangentialAccelerationAtSeconds
          (timeInSeconds setup.thirdSecondObservationTime)) =
      9 / 5
  diskStartsFromRest :
    angularSpeedInRadiansPerSecond
        (setup.diskAngularSpeedAtSeconds
          (timeInSeconds setup.initialTime)) =
      0
  initialTurnedAngleIsZero :
    setup.diskTurnedAngleRadiansAtSeconds
        (timeInSeconds setup.initialTime) = 0
  initiallyNoStringHasUnwound :
    lengthInMeters
        (setup.unwoundStringLengthAtSeconds
          (timeInSeconds setup.initialTime)) =
      0

/-- Positivity and the future-time branch implicit in the physical setup. -/
structure HasPhysicalParameters (setup : DiskBallUnwindingSetup) : Prop where
  radiusPositive : 0 < lengthInMeters setup.diskRadius
  accelerationSlopePositive :
    0 < accelerationSlopeInMetersPerSecondCubed setup.accelerationSlope
  eventOccursAfterStart :
    timeInSeconds setup.initialTime <
      timeInSeconds setup.targetAngularSpeedEventTime

/-!
The source law `a(t) = A t`, with `t` the numerical SI-second coordinate. It
is a general trajectory law and does not contain the target event or angle.
-/
structure SatisfiesLinearAccelerationProfile
    (setup : DiskBallUnwindingSetup) : Prop where
  ballAccelerationLinearInTime :
    ∀ (tSeconds : ℝ), 0 ≤ tSeconds →
      accelerationInMetersPerSecondSquared
          (setup.ballTangentialAccelerationAtSeconds tSeconds) =
        accelerationSlopeInMetersPerSecondCubed setup.accelerationSlope *
          tSeconds

/-!
No-slip unwinding and rotational kinematics in the clockwise-positive
coordinate: `a = r α`, `dω/dt = α`, `dθ/dt = ω`, and `s = r θ`. These are
general laws and do not fix the angle or time at which `ω = 15 rad/s`.
-/
structure SatisfiesNoSlipUnwindingKinematics
    (setup : DiskBallUnwindingSetup) : Prop where
  tangentialAccelerationAtRim :
    ∀ (tSeconds : ℝ), 0 ≤ tSeconds →
      accelerationInMetersPerSecondSquared
          (setup.ballTangentialAccelerationAtSeconds tSeconds) =
        lengthInMeters setup.diskRadius *
          angularAccelerationInRadiansPerSecondSquared
            (setup.diskAngularAccelerationAtSeconds tSeconds)
  angularSpeedDerivative :
    ∀ (tSeconds : ℝ), 0 ≤ tSeconds →
      HasDerivAt
        (fun s ↦ angularSpeedInRadiansPerSecond
          (setup.diskAngularSpeedAtSeconds s))
        (angularAccelerationInRadiansPerSecondSquared
          (setup.diskAngularAccelerationAtSeconds tSeconds))
        tSeconds
  turnedAngleDerivative :
    ∀ (tSeconds : ℝ), 0 ≤ tSeconds →
      HasDerivAt setup.diskTurnedAngleRadiansAtSeconds
        (angularSpeedInRadiansPerSecond
          (setup.diskAngularSpeedAtSeconds tSeconds))
        tSeconds
  unwoundLengthIsRadiusTimesAngle :
    ∀ (tSeconds : ℝ), 0 ≤ tSeconds →
      lengthInMeters (setup.unwoundStringLengthAtSeconds tSeconds) =
        lengthInMeters setup.diskRadius *
          setup.diskTurnedAngleRadiansAtSeconds tSeconds

/-!
Selection of the instant asked about. Reaching `15 rad/s` is input to the
event query; the event time and angle remain to be derived.
-/
structure MatchesQuestionEvent (setup : DiskBallUnwindingSetup) : Prop where
  diskReachesFifteenRadiansPerSecond :
    angularSpeedInRadiansPerSecond
        (setup.diskAngularSpeedAtSeconds
          (timeInSeconds setup.targetAngularSpeedEventTime)) =
      15

/-! ## Derived intermediate results -/

/-- The observation `a(3) = 1.80` calibrates `A = 0.60 m/s³`. -/
lemma accelerationSlope_eq_three_fifths
    (setup : DiskBallUnwindingSetup)
    (hData : MatchesProblemReadouts setup)
    (hProfile : SatisfiesLinearAccelerationProfile setup) :
    accelerationSlopeInMetersPerSecondCubed setup.accelerationSlope =
      3 / 5 := by
  have hAtThree := hProfile.ballAccelerationLinearInTime 3 (by norm_num)
  have hObservedAtThree :
      accelerationInMetersPerSecondSquared
          (setup.ballTangentialAccelerationAtSeconds 3) = 9 / 5 := by
    rw [← hData.observationAtEndOfThirdSecond]
    exact hData.observedBallAcceleration
  rw [hObservedAtThree] at hAtThree
  linarith

/-- The positive event at `15 rad/s` occurs at `5√2/2` seconds. -/
lemma targetEventTime_eq_five_sqrt_two_over_two
    (setup : DiskBallUnwindingSetup)
    (hData : MatchesProblemReadouts setup)
    (hPhysical : HasPhysicalParameters setup)
    (hProfile : SatisfiesLinearAccelerationProfile setup)
    (hKinematics : SatisfiesNoSlipUnwindingKinematics setup)
    (hEvent : MatchesQuestionEvent setup) :
    timeInSeconds setup.targetAngularSpeedEventTime =
      5 * Real.sqrt 2 / 2 := by
  have hRadius : lengthInMeters setup.diskRadius = 1 / 4 := by
    have hScale := setup.diskRadius.2
      {UnitChoices.SI with length := LengthUnit.centimeters}
      {UnitChoices.SI with length := LengthUnit.meters}
    have hCentimeters :
        (((setup.diskRadius
          {UnitChoices.SI with length := LengthUnit.centimeters}).val : NNReal) : ℝ) = 25 := by
      simpa [lengthInCentimeters, lengthReadout] using hData.radiusInCentimeters
    have hScaleReal := congrArg
      (fun q : WithDim L𝓭 NNReal ↦ (q.val : ℝ)) hScale
    simp only [WithDim.smul_val, smul_eq_mul, NNReal.coe_mul] at hScaleReal
    change (((setup.diskRadius
      {UnitChoices.SI with length := LengthUnit.meters}).val : NNReal) : ℝ) = _
    change _ = _ at hScaleReal
    rw [hScaleReal, hCentimeters]
    simp [UnitChoices.dimScale, LengthUnit.centimeters, LengthUnit.meters,
      LengthUnit.scale, LengthUnit.div_eq_val, NNReal.toReal]
    norm_num
  have hSlope := accelerationSlope_eq_three_fifths setup hData hProfile
  have hAngularAcceleration :
      ∀ (t : ℝ), 0 ≤ t →
        angularAccelerationInRadiansPerSecondSquared
            (setup.diskAngularAccelerationAtSeconds t) = 12 / 5 * t := by
    intro t ht
    have hLinear := hProfile.ballAccelerationLinearInTime t ht
    have hTangential := hKinematics.tangentialAccelerationAtRim t ht
    rw [hSlope] at hLinear
    rw [hRadius] at hTangential
    linarith
  have hAngularSpeedDerivative :
      ∀ (t : ℝ), 0 ≤ t →
        HasDerivAt
          (fun s ↦ angularSpeedInRadiansPerSecond
            (setup.diskAngularSpeedAtSeconds s))
          (12 / 5 * t) t := by
    intro t ht
    exact (hKinematics.angularSpeedDerivative t ht).congr_deriv
      (hAngularAcceleration t ht)
  have hQuadraticDerivative :
      ∀ (t : ℝ),
        HasDerivAt (fun s : ℝ ↦ 6 / 5 * s ^ 2) (12 / 5 * t) t := by
    intro t
    have hSquare := (hasDerivAt_id t).mul (hasDerivAt_id t)
    have hScaled := HasDerivAt.const_mul (6 / 5 : ℝ) hSquare
    have hScaled' : HasDerivAt (fun s : ℝ ↦ 6 / 5 * (s * s)) (12 / 5 * t) t :=
      hScaled.congr_deriv (by simp; ring)
    simpa [pow_two] using hScaled'
  have hInitialAngularSpeed :
      angularSpeedInRadiansPerSecond
          (setup.diskAngularSpeedAtSeconds 0) = 0 := by
    simpa only [hData.initialTimeIsZero] using hData.diskStartsFromRest
  have hAngularSpeedFormula :
      ∀ (t : ℝ), 0 ≤ t →
        angularSpeedInRadiansPerSecond
            (setup.diskAngularSpeedAtSeconds t) = 6 / 5 * t ^ 2 := by
    have hSpeedDifferentiable : DifferentiableOn ℝ
        (fun s ↦ angularSpeedInRadiansPerSecond
          (setup.diskAngularSpeedAtSeconds s)) (Set.Ici 0) := by
      intro t ht
      exact (hAngularSpeedDerivative t ht).differentiableAt.differentiableWithinAt
    have hQuadraticDifferentiable : DifferentiableOn ℝ
        (fun s : ℝ ↦ 6 / 5 * s ^ 2) (Set.Ici 0) := by
      intro t _
      exact (hQuadraticDerivative t).differentiableAt.differentiableWithinAt
    have hFDerivEq : Set.EqOn
        (fderivWithin ℝ
          (fun s ↦ angularSpeedInRadiansPerSecond
            (setup.diskAngularSpeedAtSeconds s)) (Set.Ici 0))
        (fderivWithin ℝ (fun s : ℝ ↦ 6 / 5 * s ^ 2) (Set.Ici 0))
        (Set.Ici 0) := by
      intro t ht
      have hUnique := uniqueDiffOn_Ici 0 t ht
      rw [(hAngularSpeedDerivative t ht).hasFDerivAt.hasFDerivWithinAt.fderivWithin hUnique,
        (hQuadraticDerivative t).hasFDerivAt.hasFDerivWithinAt.fderivWithin hUnique]
    have hEqOn := (convex_Ici 0).eqOn_of_fderivWithin_eq
      hSpeedDifferentiable hQuadraticDifferentiable (uniqueDiffOn_Ici 0) hFDerivEq
      (x := 0) (by simp) (by simpa using hInitialAngularSpeed)
    intro t ht
    exact hEqOn ht
  let targetTime := timeInSeconds setup.targetAngularSpeedEventTime
  have hTargetTimePositive : 0 < targetTime := by
    dsimp [targetTime]
    rw [← hData.initialTimeIsZero]
    exact hPhysical.eventOccursAfterStart
  have hSpeedAtTarget := hAngularSpeedFormula targetTime hTargetTimePositive.le
  have hEventSpeed :
      angularSpeedInRadiansPerSecond
          (setup.diskAngularSpeedAtSeconds targetTime) = 15 := by
    exact hEvent.diskReachesFifteenRadiansPerSecond
  rw [hEventSpeed] at hSpeedAtTarget
  have hTargetSquare : targetTime ^ 2 = 25 / 2 := by
    linarith
  have hSqrtSquare : Real.sqrt 2 ^ 2 = 2 := Real.sq_sqrt (by norm_num)
  dsimp [targetTime] at hTargetTimePositive hTargetSquare ⊢
  nlinarith [Real.sqrt_nonneg 2]

/-! ## Displayed choices and target conclusion -/

/-- Labels of the four angle choices printed with the problem. -/
inductive AngleAnswerChoice where
  | A
  | B
  | C
  | D
  deriving DecidableEq, Fintype, Repr

/-- Angle in radians printed beside each answer label. -/
def displayedAngleInRadians : AngleAnswerChoice → ℝ
  | .A => 181 / 10
  | .B => 177 / 10
  | .C => 117 / 10
  | .D => 377 / 10

/-- Answer metadata recorded in the source dataset; this is not a premise. -/
def recordedDatasetAnswer : AngleAnswerChoice := .B

/-- Absolute distance between an exact angle and a displayed choice. -/
def distanceFromDisplayedAngle
    (exactAngleRadians : ℝ) (choice : AngleAnswerChoice) : ℝ :=
  |exactAngleRadians - displayedAngleInRadians choice|

/-- A choice is strictly closer to the exact angle than every other choice. -/
def IsUniqueClosestDisplayedAngle
    (exactAngleRadians : ℝ) (choice : AngleAnswerChoice) : Prop :=
  ∀ other, other ≠ choice →
    distanceFromDisplayedAngle exactAngleRadians choice <
      distanceFromDisplayedAngle exactAngleRadians other

/-! A displayed tenth agrees with an exact angle within `0.05 rad`. -/
def RoundsToDisplayedTenth
    (exactAngleRadians : ℝ) (choice : AngleAnswerChoice) : Prop :=
  distanceFromDisplayedAngle exactAngleRadians choice ≤ 1 / 20

/-!
Integrating the calibrated acceleration profile with no slip gives the exact
angle `25√2/2 rad`, approximately `17.68 rad`. Thus it rounds to `17.7 rad`
and choice B is uniquely closest.

This formalizes `thm:physics:phyx_mini_0772:target`.
-/
theorem problem_phyx_mini_0772
    (setup : DiskBallUnwindingSetup)
    (hScenario : MatchesProblemScenario setup)
    (hFigure : MatchesSuppliedFigure setup)
    (hData : MatchesProblemReadouts setup)
    (hPhysical : HasPhysicalParameters setup)
    (hProfile : SatisfiesLinearAccelerationProfile setup)
    (hKinematics : SatisfiesNoSlipUnwindingKinematics setup)
    (hEvent : MatchesQuestionEvent setup) :
    setup.diskTurnedAngleRadiansAtSeconds
          (timeInSeconds setup.targetAngularSpeedEventTime) =
        25 * Real.sqrt 2 / 2 ∧
      RoundsToDisplayedTenth
        (setup.diskTurnedAngleRadiansAtSeconds
          (timeInSeconds setup.targetAngularSpeedEventTime))
        .B ∧
      IsUniqueClosestDisplayedAngle
        (setup.diskTurnedAngleRadiansAtSeconds
          (timeInSeconds setup.targetAngularSpeedEventTime))
        .B := by
  have hRadius : lengthInMeters setup.diskRadius = 1 / 4 := by
    have hScale := setup.diskRadius.2
      {UnitChoices.SI with length := LengthUnit.centimeters}
      {UnitChoices.SI with length := LengthUnit.meters}
    have hCentimeters :
        (((setup.diskRadius
          {UnitChoices.SI with length := LengthUnit.centimeters}).val : NNReal) : ℝ) = 25 := by
      simpa [lengthInCentimeters, lengthReadout] using hData.radiusInCentimeters
    have hScaleReal := congrArg
      (fun q : WithDim L𝓭 NNReal ↦ (q.val : ℝ)) hScale
    simp only [WithDim.smul_val, smul_eq_mul, NNReal.coe_mul] at hScaleReal
    change (((setup.diskRadius
      {UnitChoices.SI with length := LengthUnit.meters}).val : NNReal) : ℝ) = _
    change _ = _ at hScaleReal
    rw [hScaleReal, hCentimeters]
    simp [UnitChoices.dimScale, LengthUnit.centimeters, LengthUnit.meters,
      LengthUnit.scale, LengthUnit.div_eq_val, NNReal.toReal]
    norm_num
  have hSlope := accelerationSlope_eq_three_fifths setup hData hProfile
  have hAngularAcceleration :
      ∀ (t : ℝ), 0 ≤ t →
        angularAccelerationInRadiansPerSecondSquared
            (setup.diskAngularAccelerationAtSeconds t) = 12 / 5 * t := by
    intro t ht
    have hLinear := hProfile.ballAccelerationLinearInTime t ht
    have hTangential := hKinematics.tangentialAccelerationAtRim t ht
    rw [hSlope] at hLinear
    rw [hRadius] at hTangential
    linarith
  have hAngularSpeedDerivative :
      ∀ (t : ℝ), 0 ≤ t →
        HasDerivAt
          (fun s ↦ angularSpeedInRadiansPerSecond
            (setup.diskAngularSpeedAtSeconds s))
          (12 / 5 * t) t := by
    intro t ht
    exact (hKinematics.angularSpeedDerivative t ht).congr_deriv
      (hAngularAcceleration t ht)
  have hQuadraticDerivative :
      ∀ (t : ℝ),
        HasDerivAt (fun s : ℝ ↦ 6 / 5 * s ^ 2) (12 / 5 * t) t := by
    intro t
    have hSquare := (hasDerivAt_id t).mul (hasDerivAt_id t)
    have hScaled := HasDerivAt.const_mul (6 / 5 : ℝ) hSquare
    have hScaled' : HasDerivAt (fun s : ℝ ↦ 6 / 5 * (s * s)) (12 / 5 * t) t :=
      hScaled.congr_deriv (by simp; ring)
    simpa [pow_two] using hScaled'
  have hInitialAngularSpeed :
      angularSpeedInRadiansPerSecond
          (setup.diskAngularSpeedAtSeconds 0) = 0 := by
    simpa only [hData.initialTimeIsZero] using hData.diskStartsFromRest
  have hAngularSpeedFormula :
      ∀ (t : ℝ), 0 ≤ t →
        angularSpeedInRadiansPerSecond
            (setup.diskAngularSpeedAtSeconds t) = 6 / 5 * t ^ 2 := by
    have hSpeedDifferentiable : DifferentiableOn ℝ
        (fun s ↦ angularSpeedInRadiansPerSecond
          (setup.diskAngularSpeedAtSeconds s)) (Set.Ici 0) := by
      intro t ht
      exact (hAngularSpeedDerivative t ht).differentiableAt.differentiableWithinAt
    have hQuadraticDifferentiable : DifferentiableOn ℝ
        (fun s : ℝ ↦ 6 / 5 * s ^ 2) (Set.Ici 0) := by
      intro t _
      exact (hQuadraticDerivative t).differentiableAt.differentiableWithinAt
    have hFDerivEq : Set.EqOn
        (fderivWithin ℝ
          (fun s ↦ angularSpeedInRadiansPerSecond
            (setup.diskAngularSpeedAtSeconds s)) (Set.Ici 0))
        (fderivWithin ℝ (fun s : ℝ ↦ 6 / 5 * s ^ 2) (Set.Ici 0))
        (Set.Ici 0) := by
      intro t ht
      have hUnique := uniqueDiffOn_Ici 0 t ht
      rw [(hAngularSpeedDerivative t ht).hasFDerivAt.hasFDerivWithinAt.fderivWithin hUnique,
        (hQuadraticDerivative t).hasFDerivAt.hasFDerivWithinAt.fderivWithin hUnique]
    have hEqOn := (convex_Ici 0).eqOn_of_fderivWithin_eq
      hSpeedDifferentiable hQuadraticDifferentiable (uniqueDiffOn_Ici 0) hFDerivEq
      (x := 0) (by simp) (by simpa using hInitialAngularSpeed)
    intro t ht
    exact hEqOn ht
  have hAngleDerivative :
      ∀ (t : ℝ), 0 ≤ t →
        HasDerivAt setup.diskTurnedAngleRadiansAtSeconds (6 / 5 * t ^ 2) t := by
    intro t ht
    exact (hKinematics.turnedAngleDerivative t ht).congr_deriv
      (hAngularSpeedFormula t ht)
  have hCubicDerivative :
      ∀ (t : ℝ),
        HasDerivAt (fun s : ℝ ↦ 2 / 5 * s ^ 3) (6 / 5 * t ^ 2) t := by
    intro t
    have hCube := ((hasDerivAt_id t).mul (hasDerivAt_id t)).mul (hasDerivAt_id t)
    have hScaled := HasDerivAt.const_mul (2 / 5 : ℝ) hCube
    have hScaled' : HasDerivAt
        (fun s : ℝ ↦ 2 / 5 * ((s * s) * s)) (6 / 5 * t ^ 2) t :=
      hScaled.congr_deriv (by simp [pow_two]; ring)
    simpa [pow_succ] using hScaled'
  have hInitialAngle : setup.diskTurnedAngleRadiansAtSeconds 0 = 0 := by
    simpa only [hData.initialTimeIsZero] using hData.initialTurnedAngleIsZero
  have hAngleFormula :
      ∀ (t : ℝ), 0 ≤ t →
        setup.diskTurnedAngleRadiansAtSeconds t = 2 / 5 * t ^ 3 := by
    have hAngleDifferentiable : DifferentiableOn ℝ
        setup.diskTurnedAngleRadiansAtSeconds (Set.Ici 0) := by
      intro t ht
      exact (hAngleDerivative t ht).differentiableAt.differentiableWithinAt
    have hCubicDifferentiable : DifferentiableOn ℝ
        (fun s : ℝ ↦ 2 / 5 * s ^ 3) (Set.Ici 0) := by
      intro t _
      exact (hCubicDerivative t).differentiableAt.differentiableWithinAt
    have hFDerivEq : Set.EqOn
        (fderivWithin ℝ setup.diskTurnedAngleRadiansAtSeconds (Set.Ici 0))
        (fderivWithin ℝ (fun s : ℝ ↦ 2 / 5 * s ^ 3) (Set.Ici 0))
        (Set.Ici 0) := by
      intro t ht
      have hUnique := uniqueDiffOn_Ici 0 t ht
      rw [(hAngleDerivative t ht).hasFDerivAt.hasFDerivWithinAt.fderivWithin hUnique,
        (hCubicDerivative t).hasFDerivAt.hasFDerivWithinAt.fderivWithin hUnique]
    have hEqOn := (convex_Ici 0).eqOn_of_fderivWithin_eq
      hAngleDifferentiable hCubicDifferentiable (uniqueDiffOn_Ici 0) hFDerivEq
      (x := 0) (by simp) (by simpa using hInitialAngle)
    intro t ht
    exact hEqOn ht
  have hTargetTime := targetEventTime_eq_five_sqrt_two_over_two
    setup hData hPhysical hProfile hKinematics hEvent
  have hTargetTimePositive :
      0 < timeInSeconds setup.targetAngularSpeedEventTime := by
    rw [← hData.initialTimeIsZero]
    exact hPhysical.eventOccursAfterStart
  have hExactAngle := hAngleFormula
    (timeInSeconds setup.targetAngularSpeedEventTime) hTargetTimePositive.le
  rw [hTargetTime] at hExactAngle
  have hSqrtSquare : Real.sqrt 2 ^ 2 = 2 := Real.sq_sqrt (by norm_num)
  have hSqrtCube : Real.sqrt 2 ^ 3 = 2 * Real.sqrt 2 := by
    calc
      Real.sqrt 2 ^ 3 = Real.sqrt 2 ^ 2 * Real.sqrt 2 := by ring
      _ = 2 * Real.sqrt 2 := by rw [hSqrtSquare]
  have hAngleValue :
      setup.diskTurnedAngleRadiansAtSeconds
          (timeInSeconds setup.targetAngularSpeedEventTime) = 25 * Real.sqrt 2 / 2 := by
    rw [hTargetTime, hExactAngle]
    rw [show (5 * Real.sqrt 2 / 2) ^ 3 = 125 / 8 * Real.sqrt 2 ^ 3 by ring,
      hSqrtCube]
    ring
  have hSqrtLower : (1414 / 1000 : ℝ) < Real.sqrt 2 := by
    rw [Real.lt_sqrt (by norm_num : (0 : ℝ) ≤ 1414 / 1000)]
    norm_num
  have hSqrtUpper : Real.sqrt 2 < (1415 / 1000 : ℝ) := by
    rw [Real.sqrt_lt' (by norm_num : (0 : ℝ) < 1415 / 1000)]
    norm_num
  refine ⟨hAngleValue, ?_, ?_⟩
  · rw [hAngleValue]
    change |25 * Real.sqrt 2 / 2 - 177 / 10| ≤ 1 / 20
    rw [abs_le]
    constructor <;> linarith
  · rw [hAngleValue]
    intro other hOther
    fin_cases other
    · change |25 * Real.sqrt 2 / 2 - 177 / 10| <
        |25 * Real.sqrt 2 / 2 - 181 / 10|
      rw [abs_of_nonpos (by linarith), abs_of_nonpos (by linarith)]
      linarith
    · exact (hOther rfl).elim
    · change |25 * Real.sqrt 2 / 2 - 177 / 10| <
        |25 * Real.sqrt 2 / 2 - 117 / 10|
      rw [abs_of_nonpos (by linarith), abs_of_nonneg (by linarith)]
      linarith
    · change |25 * Real.sqrt 2 / 2 - 177 / 10| <
        |25 * Real.sqrt 2 / 2 - 377 / 10|
      rw [abs_of_nonpos (by linarith), abs_of_nonpos (by linarith)]
      linarith

end PhyXMiniProblems.ProblemPhyXMini0772
