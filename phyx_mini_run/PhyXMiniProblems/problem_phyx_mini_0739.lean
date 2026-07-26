import Mathlib.Analysis.SpecialFunctions.Trigonometric.Angle
import Physlib.SpaceAndTime.Space.LengthUnit
import Physlib.Units.WithDim.Basic
import Physlib.Units.WithDim.Speed

noncomputable section

namespace PhyXMiniProblems.ProblemPhyXMini0739

open Dimension

/-!
# Maximum height of a stone projected toward a cliff

A stone is launched from ground level with speed `42.0 m/s` at `60.0°` above
the horizontal. The supplied figure shows its parabolic trajectory, the
maximum height `H` above the ground, a cliff of height `h`, and the impact
point `A`. The stone reaches `A` after `5.50 s`.

Lengths, durations, speeds, and accelerations below are unit-independent
Physlib quantities. Signed coordinates and velocity components use real-valued
dimensionful quantities. Ordinary real numbers occur only as named-unit
readouts, dimensionless trigonometric values, and answer-choice data.
-/

/-! ## Dimensionful quantities and named-unit readouts -/

/-- The physical dimension of speed, `L T⁻¹`. -/
def speedDimension : Dimension := L𝓭 * T𝓭⁻¹

/-- The physical dimension of acceleration, `L T⁻²`. -/
def accelerationDimension : Dimension := L𝓭 * T𝓭⁻¹ * T𝓭⁻¹

/-- A nonnegative physical length, independent of its readout unit. -/
abbrev LengthQuantity : Type := Dimensionful (WithDim L𝓭 NNReal)

/-- A signed position coordinate along a selected axis. -/
abbrev SignedLengthQuantity : Type := Dimensionful (WithDim L𝓭 ℝ)

/-- A nonnegative physical duration. -/
abbrev TimeQuantity : Type := Dimensionful (WithDim T𝓭 NNReal)

/-- A nonnegative launch-speed magnitude. -/
abbrev SpeedQuantity : Type := DimSpeed

/-- A signed component of velocity. -/
abbrev SignedSpeedQuantity : Type :=
  Dimensionful (WithDim speedDimension ℝ)

/-- A nonnegative gravitational-acceleration magnitude. -/
abbrev AccelerationQuantity : Type :=
  Dimensionful (WithDim accelerationDimension NNReal)

/-- Read a nonnegative physical length in a selected length unit. -/
def lengthReadout (unit : LengthUnit) (length : LengthQuantity) : ℝ :=
  ((length {UnitChoices.SI with length := unit}).val : ℝ)

/-- Read a signed coordinate in a selected length unit. -/
def signedLengthReadout
    (unit : LengthUnit) (length : SignedLengthQuantity) : ℝ :=
  (length {UnitChoices.SI with length := unit}).val

/-- Read a duration in a selected time unit. -/
def timeReadout (unit : TimeUnit) (duration : TimeQuantity) : ℝ :=
  ((duration {UnitChoices.SI with time := unit}).val : ℝ)

/-- Read a speed magnitude in coherent selected length and time units. -/
def speedReadout
    (lengthUnit : LengthUnit) (timeUnit : TimeUnit)
    (speed : SpeedQuantity) : ℝ :=
  ((speed {UnitChoices.SI with
    length := lengthUnit, time := timeUnit}).val : ℝ)

/-- Read a signed velocity component in coherent length and time units. -/
def signedSpeedReadout
    (lengthUnit : LengthUnit) (timeUnit : TimeUnit)
    (speed : SignedSpeedQuantity) : ℝ :=
  (speed {UnitChoices.SI with
    length := lengthUnit, time := timeUnit}).val

/-- Read acceleration in coherent selected length and time units. -/
def accelerationReadout
    (lengthUnit : LengthUnit) (timeUnit : TimeUnit)
    (acceleration : AccelerationQuantity) : ℝ :=
  ((acceleration {UnitChoices.SI with
    length := lengthUnit, time := timeUnit}).val : ℝ)

/-- Metre readout of a nonnegative physical length. -/
def lengthInMeters (length : LengthQuantity) : ℝ :=
  lengthReadout LengthUnit.meters length

/-- Second readout of a physical duration. -/
def timeInSeconds (duration : TimeQuantity) : ℝ :=
  timeReadout TimeUnit.seconds duration

/-- Metre-per-second readout of a speed magnitude. -/
def speedInMetersPerSecond (speed : SpeedQuantity) : ℝ :=
  speedReadout LengthUnit.meters TimeUnit.seconds speed

/-- Metre-per-second-squared readout of an acceleration magnitude. -/
def accelerationInMetersPerSecondSquared
    (acceleration : AccelerationQuantity) : ℝ :=
  accelerationReadout LengthUnit.meters TimeUnit.seconds acceleration

/-- Convert a numerical degree readout into Mathlib's physical angle type. -/
def degrees (value : ℝ) : Real.Angle :=
  ((value * Real.pi / 180 : ℝ) : Real.Angle)

/-! ## Physical scenario and primary-figure vocabulary -/

/-- The kind of launched body specified by the prose. -/
inductive ProjectileKind where
  | stone
  | other
  deriving DecidableEq, Repr

/-- The mechanical idealization used after the stone is released. -/
inductive FlightModel where
  | uniformGravityNegligibleDrag
  | other
  deriving DecidableEq, Repr

/-- Physical or geometric objects visibly distinguished in the raster. -/
inductive FigureObject where
  | initialVelocityArrow
  | parabolicTrajectory
  | horizontalGround
  | cliffWall
  | maximumHeightArrow
  | cliffHeightArrow
  deriving DecidableEq, Fintype, Repr

/-- Distinguished points in the pictured trajectory. -/
inductive FigurePoint where
  | launchPoint
  | apex
  | impactPointA
  deriving DecidableEq, Fintype, Repr

/-- Literal symbolic labels printed in the supplied figure. -/
inductive FigureLabel where
  | thetaZero
  | maximumHeightH
  | cliffHeighth
  | impactA
  deriving DecidableEq, Fintype, Repr

/-!
Primary-image data, kept separate from the kinematic laws and prose readouts.
The raster identifies the meanings of `theta₀`, `H`, `h`, and `A`, but it
contains no numerical readout for the requested maximum height.
-/
structure SuppliedCliffProjectileFigure where
  showsObject : FigureObject → Bool
  showsPoint : FigurePoint → Bool
  showsLabel : FigureLabel → Bool
  angleMarkedThetaZero : Real.Angle
  heightMarkedH : LengthQuantity
  heightMarkedh : LengthQuantity
  trajectoryIsParabolic : Bool
  launchArrowPointsAboveHorizontal : Bool
  impactPointLiesOnCliffTop : Bool
  maximumHeightMeasuredFromGround : Bool
  cliffHeightMeasuredFromGround : Bool
  containsNumericalMaximumHeightReadout : Bool

/-!
Independent quantities and observables of the launch. In particular,
`maximumHeightAboveGround` is an independent dimensionful field; it is not
defined from the answer table or from `67.5`.
-/
structure CliffProjectileSetup where
  projectileKind : ProjectileKind
  flightModel : FlightModel
  launchedFromGroundLevel : Bool
  groundIsHorizontal : Bool
  cliffFaceIsVertical : Bool
  launchSpeed : SpeedQuantity
  launchAngle : Real.Angle
  gravitationalAcceleration : AccelerationQuantity
  impactTimeAtA : TimeQuantity
  apexTime : TimeQuantity
  horizontalDistanceToCliff : LengthQuantity
  cliffHeight : LengthQuantity
  maximumHeightAboveGround : LengthQuantity
  horizontalPositionAt : TimeQuantity → SignedLengthQuantity
  verticalPositionAt : TimeQuantity → SignedLengthQuantity
  verticalVelocityAt : TimeQuantity → SignedSpeedQuantity
  figure : SuppliedCliffProjectileFigure

/-! ## Scenario, figure data, readouts, and governing laws -/

/-- Qualitative physical assignments stated or implicit in the problem. -/
structure MatchesCliffProjectileScenario
    (setup : CliffProjectileSetup) : Prop where
  projectileIsStone : setup.projectileKind = .stone
  usesUniformGravityModel :
    setup.flightModel = .uniformGravityNegligibleDrag
  startsAtGround : setup.launchedFromGroundLevel = true
  horizontalGround : setup.groundIsHorizontal = true
  verticalCliff : setup.cliffFaceIsVertical = true

/-!
Objects, points, labels, and denotations transcribed from the primary image.
No numerical value for `H` is extracted from the drawing.
-/
structure MatchesSuppliedCliffProjectileFigure
    (setup : CliffProjectileSetup) : Prop where
  everyObjectShown : ∀ object, setup.figure.showsObject object = true
  everyPointShown : ∀ point, setup.figure.showsPoint point = true
  everyLabelShown : ∀ label, setup.figure.showsLabel label = true
  thetaZeroDenotesLaunchAngle :
    setup.figure.angleMarkedThetaZero = setup.launchAngle
  HDenotesMaximumHeight :
    setup.figure.heightMarkedH = setup.maximumHeightAboveGround
  hDenotesCliffHeight :
    setup.figure.heightMarkedh = setup.cliffHeight
  parabolicPathDrawn : setup.figure.trajectoryIsParabolic = true
  launchArrowAboveHorizontal :
    setup.figure.launchArrowPointsAboveHorizontal = true
  pointAAtCliffTop : setup.figure.impactPointLiesOnCliffTop = true
  HMeasuredFromGround :
    setup.figure.maximumHeightMeasuredFromGround = true
  hMeasuredFromGround : setup.figure.cliffHeightMeasuredFromGround = true
  noNumericalMaximumHeightInFigure :
    setup.figure.containsNumericalMaximumHeightReadout = false

/-!
Exact numerical information printed in the prose. Decimal values are stored
as rational real readouts. Neither the cliff height nor the maximum height is
given numerically.
-/
structure MatchesProblemReadouts (setup : CliffProjectileSetup) : Prop where
  launchSpeedMetersPerSecond :
    speedInMetersPerSecond setup.launchSpeed = 42
  launchAngleDegrees : setup.launchAngle = degrees 60
  impactTimeSeconds : timeInSeconds setup.impactTimeAtA = 11 / 2

/-!
The standard near-Earth gravitational calibration implicit in the recorded
answer. It is separate from source readouts because the problem does not print
a value of `g`.
-/
structure UsesStandardNearEarthGravity
    (setup : CliffProjectileSetup) : Prop where
  gravityMetersPerSecondSquared :
    accelerationInMetersPerSecondSquared
      setup.gravitationalAcceleration = 49 / 5

/-!
Positivity and event ordering for the physical launch. These assumptions give
no numerical value to either `h` or `H`.
-/
structure HasPhysicalCliffProjectileParameters
    (setup : CliffProjectileSetup) : Prop where
  launchSpeedPositive : 0 < speedInMetersPerSecond setup.launchSpeed
  gravityPositive :
    0 < accelerationInMetersPerSecondSquared
      setup.gravitationalAcceleration
  impactTimePositive : 0 < timeInSeconds setup.impactTimeAtA
  apexTimePositive : 0 < timeInSeconds setup.apexTime
  apexOccursBeforeImpact :
    timeInSeconds setup.apexTime < timeInSeconds setup.impactTimeAtA
  horizontalDistancePositive :
    0 < lengthInMeters setup.horizontalDistanceToCliff
  cliffHeightPositive : 0 < lengthInMeters setup.cliffHeight
  maximumHeightPositive :
    0 < lengthInMeters setup.maximumHeightAboveGround

/-!
Uniform-gravity projectile motion from a ground-level coordinate origin.
Horizontal motion is uniform; vertical position and velocity have constant
downward acceleration. The laws quantify over coherent unit choices and do
not mention a problem-specific height or answer choice.
-/
structure SatisfiesUniformGravityProjectileLaws
    (setup : CliffProjectileSetup) : Prop where
  horizontalMotion :
    ∀ (elapsed : TimeQuantity) (lengthUnit : LengthUnit)
        (timeUnit : TimeUnit),
      signedLengthReadout lengthUnit (setup.horizontalPositionAt elapsed) =
        speedReadout lengthUnit timeUnit setup.launchSpeed *
          Real.Angle.cos setup.launchAngle * timeReadout timeUnit elapsed
  verticalMotion :
    ∀ (elapsed : TimeQuantity) (lengthUnit : LengthUnit)
        (timeUnit : TimeUnit),
      signedLengthReadout lengthUnit (setup.verticalPositionAt elapsed) =
        speedReadout lengthUnit timeUnit setup.launchSpeed *
            Real.Angle.sin setup.launchAngle * timeReadout timeUnit elapsed -
          accelerationReadout lengthUnit timeUnit
              setup.gravitationalAcceleration *
            timeReadout timeUnit elapsed ^ 2 / 2
  verticalVelocity :
    ∀ (elapsed : TimeQuantity) (lengthUnit : LengthUnit)
        (timeUnit : TimeUnit),
      signedSpeedReadout lengthUnit timeUnit
          (setup.verticalVelocityAt elapsed) =
        speedReadout lengthUnit timeUnit setup.launchSpeed *
            Real.Angle.sin setup.launchAngle -
          accelerationReadout lengthUnit timeUnit
              setup.gravitationalAcceleration *
            timeReadout timeUnit elapsed

/-!
The apex and impact events denoted by the image. At the independent apex time
the vertical velocity vanishes and the vertical coordinate is the independent
quantity `H`; at the supplied impact time the stone is at the cliff top `A`.
The final field records the literal meaning of “maximum height,” without
assigning that height any numerical value.
-/
structure SatisfiesApexAndCliffImpactEvents
    (setup : CliffProjectileSetup) : Prop where
  zeroVerticalVelocityAtApex :
    ∀ (lengthUnit : LengthUnit) (timeUnit : TimeUnit),
      signedSpeedReadout lengthUnit timeUnit
          (setup.verticalVelocityAt setup.apexTime) = 0
  apexHeightIsH :
    ∀ unit : LengthUnit,
      signedLengthReadout unit
          (setup.verticalPositionAt setup.apexTime) =
        lengthReadout unit setup.maximumHeightAboveGround
  impactHorizontalCoordinate :
    ∀ unit : LengthUnit,
      signedLengthReadout unit
          (setup.horizontalPositionAt setup.impactTimeAtA) =
        lengthReadout unit setup.horizontalDistanceToCliff
  impactVerticalCoordinate :
    ∀ unit : LengthUnit,
      signedLengthReadout unit
          (setup.verticalPositionAt setup.impactTimeAtA) =
        lengthReadout unit setup.cliffHeight
  apexIsGlobalMaximumOfBallisticTrajectory :
    ∀ (elapsed : TimeQuantity) (unit : LengthUnit),
      signedLengthReadout unit (setup.verticalPositionAt elapsed) ≤
        lengthReadout unit setup.maximumHeightAboveGround

/-! ## Derived height relation and answer selection -/

/-!
Eliminating the positive apex time from the vertical-velocity and
vertical-position laws gives the standard maximum-height formula
`H = (v₀ sin θ₀)² / (2g)`.
-/
lemma maximumHeightAboveGround_formula
    (setup : CliffProjectileSetup)
    (hPhysical : HasPhysicalCliffProjectileParameters setup)
    (hLaws : SatisfiesUniformGravityProjectileLaws setup)
    (hEvents : SatisfiesApexAndCliffImpactEvents setup) :
    lengthInMeters setup.maximumHeightAboveGround =
      (speedInMetersPerSecond setup.launchSpeed *
          Real.Angle.sin setup.launchAngle) ^ 2 /
        (2 * accelerationInMetersPerSecondSquared
          setup.gravitationalAcceleration) := by
  have hVelocity := hLaws.verticalVelocity setup.apexTime
    LengthUnit.meters TimeUnit.seconds
  rw [hEvents.zeroVerticalVelocityAtApex
    LengthUnit.meters TimeUnit.seconds] at hVelocity
  change 0 =
    speedInMetersPerSecond setup.launchSpeed *
        Real.Angle.sin setup.launchAngle -
      accelerationInMetersPerSecondSquared setup.gravitationalAcceleration *
        timeInSeconds setup.apexTime at hVelocity
  have hHeight := hLaws.verticalMotion setup.apexTime
    LengthUnit.meters TimeUnit.seconds
  rw [hEvents.apexHeightIsH LengthUnit.meters] at hHeight
  change lengthInMeters setup.maximumHeightAboveGround =
    speedInMetersPerSecond setup.launchSpeed *
        Real.Angle.sin setup.launchAngle * timeInSeconds setup.apexTime -
      accelerationInMetersPerSecondSquared setup.gravitationalAcceleration *
        timeInSeconds setup.apexTime ^ 2 / 2 at hHeight
  have hg :
      2 * accelerationInMetersPerSecondSquared
        setup.gravitationalAcceleration ≠ 0 :=
    mul_ne_zero (by norm_num) (ne_of_gt hPhysical.gravityPositive)
  exact (eq_div_iff hg).2 (by
    linear_combination
      2 * accelerationInMetersPerSecondSquared
          setup.gravitationalAcceleration * hHeight +
        (speedInMetersPerSecond setup.launchSpeed *
              Real.Angle.sin setup.launchAngle -
            accelerationInMetersPerSecondSquared
                setup.gravitationalAcceleration *
              timeInSeconds setup.apexTime) * hVelocity)

/-!
The launch data and standard gravity specialize the general formula to
`67.5 m = 135/2 m`. The `5.50 s` impact datum and cliff geometry remain in the
modeled setup even though the apex height is fixed by the initial vertical
velocity and gravity alone.
-/
lemma maximumHeightAboveGroundInMeters_eq
    (setup : CliffProjectileSetup)
    (hReadouts : MatchesProblemReadouts setup)
    (hGravity : UsesStandardNearEarthGravity setup)
    (hPhysical : HasPhysicalCliffProjectileParameters setup)
    (hLaws : SatisfiesUniformGravityProjectileLaws setup)
    (hEvents : SatisfiesApexAndCliffImpactEvents setup) :
    lengthInMeters setup.maximumHeightAboveGround = 135 / 2 := by
  rw [maximumHeightAboveGround_formula setup hPhysical hLaws hEvents]
  rw [hReadouts.launchSpeedMetersPerSecond,
    hGravity.gravityMetersPerSecondSquared,
    hReadouts.launchAngleDegrees]
  simp only [degrees, Real.Angle.sin_coe]
  have hangle : (60 : ℝ) * Real.pi / 180 = Real.pi / 3 := by
    ring
  rw [hangle, mul_pow, Real.sq_sin_pi_div_three]
  norm_num

/-- Labels of the four maximum-height choices printed in the source. -/
inductive AnswerChoice where
  | A
  | B
  | C
  | D
  deriving DecidableEq, Fintype, Repr

/-- Metre value displayed beside each answer label. -/
def displayedHeightInMeters : AnswerChoice → ℝ
  | .A => 117 / 2
  | .B => 127 / 2
  | .C => 135 / 2
  | .D => 145 / 2

/-- The answer label recorded by the source dataset. -/
def recordedDatasetAnswer : AnswerChoice := .C

/-- A displayed choice exactly matches the modeled maximum-height readout. -/
def MatchesDisplayedHeightChoice
    (setup : CliffProjectileSetup) (choice : AnswerChoice) : Prop :=
  lengthInMeters setup.maximumHeightAboveGround =
    displayedHeightInMeters choice

/-!
The projected stone reaches a maximum height of `67.5 m` above the ground.
Thus choice C matches the physical height, and no other displayed choice does.

This formalizes `thm:physics:phyx_mini_0739:target`. Neither `67.5 m` nor the
selection of C occurs in any premise structure or governing-law field.
-/
theorem problem_phyx_mini_0739
    (setup : CliffProjectileSetup)
    (hScenario : MatchesCliffProjectileScenario setup)
    (hFigure : MatchesSuppliedCliffProjectileFigure setup)
    (hReadouts : MatchesProblemReadouts setup)
    (hGravity : UsesStandardNearEarthGravity setup)
    (hPhysical : HasPhysicalCliffProjectileParameters setup)
    (hLaws : SatisfiesUniformGravityProjectileLaws setup)
    (hEvents : SatisfiesApexAndCliffImpactEvents setup) :
    lengthInMeters setup.maximumHeightAboveGround = 135 / 2 ∧
      MatchesDisplayedHeightChoice setup .C ∧
        ∀ choice : AnswerChoice,
          MatchesDisplayedHeightChoice setup choice → choice = .C := by
  have hHeight := maximumHeightAboveGroundInMeters_eq setup hReadouts
    hGravity hPhysical hLaws hEvents
  refine ⟨hHeight, ?_, ?_⟩
  · simpa [MatchesDisplayedHeightChoice, displayedHeightInMeters] using hHeight
  · intro choice hChoice
    cases choice <;>
      simp_all [MatchesDisplayedHeightChoice, displayedHeightInMeters]

end PhyXMiniProblems.ProblemPhyXMini0739
