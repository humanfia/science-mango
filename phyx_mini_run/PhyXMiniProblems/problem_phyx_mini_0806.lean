import Mathlib
import Physlib.Units.WithDim.Basic

/- USER: The assigned source file did not exist when this autoformalization task began. -/

/-!
# Force exerted by a rope on a sled in uniform circular motion

A `25.0 kg` sled moves uniformly on essentially frictionless horizontal ice.  A
taut `5.00 m` rope connects the sled to a fixed post and therefore fixes the
radius of its circular path.  The sled completes five revolutions per minute;
the rope supplies the inward horizontal force.

Mass, length, revolution rate, angular speed, acceleration, and force are
unit-independent Physlib quantities.  Real numbers are used only at coherent
SI readout boundaries, for the dimensionless revolution count and angle, and
for the displayed answer values.

Assumption/target split:

* governing laws: a taut rope makes the orbital radius equal its length,
  angular speed is `2π` times the revolution rate, uniform circular motion has
  centripetal acceleration `a = ω² R`, and radial Newtonian dynamics gives
  `F = m a` with rope tension as the only horizontal force;
* previous-part results: none;
* figure/data readouts: `m = 25.0 kg`, rope length `5.00 m`, five revolutions
  per minute, and the post, sled, rope, dashed circle, radius label `R`, and
  counterclockwise arrowheads visible in the primary bitmap;
* target conclusion: the force is exactly `125 (π / 6)² N`, hence rounds to
  `34.3 N` and selects displayed answer B.
-/

noncomputable section

namespace PhyXMiniProblems.ProblemPhyXMini0806

open Dimension

/-! ## Dimensionful quantities and coherent-SI readouts -/

/-- The physical dimension of acceleration, `L T⁻²`. -/
def accelerationDimension : Dimension :=
  L𝓭 * T𝓭⁻¹ * T𝓭⁻¹

/-- The physical dimension of force, `M L T⁻²`. -/
def forceDimension : Dimension :=
  M𝓭 * accelerationDimension

/-- A nonnegative, unit-independent physical mass. -/
abbrev MassQuantity : Type :=
  Dimensionful (WithDim M𝓭 NNReal)

/-- A nonnegative physical length, used for the rope length and orbit radius. -/
abbrev LengthQuantity : Type :=
  Dimensionful (WithDim L𝓭 NNReal)

/-- A nonnegative revolution rate, with physical dimension inverse time. -/
abbrev RevolutionRateQuantity : Type :=
  Dimensionful (WithDim T𝓭⁻¹ NNReal)

/-- A nonnegative angular-speed magnitude; radians are dimensionless. -/
abbrev AngularSpeedQuantity : Type :=
  Dimensionful (WithDim T𝓭⁻¹ NNReal)

/-- A nonnegative centripetal-acceleration magnitude. -/
abbrev AccelerationQuantity : Type :=
  Dimensionful (WithDim accelerationDimension NNReal)

/-- A nonnegative force magnitude, whose coherent SI unit is the newton. -/
abbrev ForceQuantity : Type :=
  Dimensionful (WithDim forceDimension NNReal)

/-- Read any nonnegative dimensionful quantity in coherent SI units. -/
def nonnegativeSIReadout {dimension : Dimension}
    (quantity : Dimensionful (WithDim dimension NNReal)) : ℝ :=
  ((quantity UnitChoices.SI).val : ℝ)

/-- Kilogram readout of a physical mass. -/
def massInKilograms (mass : MassQuantity) : ℝ :=
  nonnegativeSIReadout mass

/-- Metre readout of a physical length. -/
def lengthInMeters (length : LengthQuantity) : ℝ :=
  nonnegativeSIReadout length

/-- Cycle-per-second readout of a physical revolution rate. -/
def revolutionRateInHertz (rate : RevolutionRateQuantity) : ℝ :=
  nonnegativeSIReadout rate

/-- Radian-per-second readout of a physical angular-speed magnitude. -/
def angularSpeedInRadiansPerSecond (speed : AngularSpeedQuantity) : ℝ :=
  nonnegativeSIReadout speed

/-- Metre-per-second-squared readout of an acceleration magnitude. -/
def accelerationInMetersPerSecondSquared
    (acceleration : AccelerationQuantity) : ℝ :=
  nonnegativeSIReadout acceleration

/-- Newton readout of a force magnitude. -/
def forceInNewtons (force : ForceQuantity) : ℝ :=
  nonnegativeSIReadout force

/-! ## Physical scenario and primary-image vocabulary -/

/-- Shape of the sled's trajectory about the post. -/
inductive TrajectoryShape where
  | circular
  | noncircular
  deriving DecidableEq, Repr

/-- Orientation of the ice sheet. -/
inductive SurfaceOrientation where
  | horizontal
  | inclined
  deriving DecidableEq, Repr

/-- Tangential resistance regime of the ice. -/
inductive FrictionRegime where
  | essentiallyFrictionless
  | frictional
  deriving DecidableEq, Repr

/-- Radial direction of the force exerted by the rope on the sled. -/
inductive RadialDirection where
  | towardPost
  | awayFromPost
  deriving DecidableEq, Repr

/-- Sense of the motion indicated by the blue arrowheads in the bitmap. -/
inductive RotationSense where
  | clockwise
  | counterclockwise
  deriving DecidableEq, Repr

/-- Possible sources of the net horizontal force on the sled. -/
inductive HorizontalForceSource where
  | ropeTension
  | surfaceFriction
  | other
  deriving DecidableEq, Repr

/-- Literal and qualitative evidence transcribed from primary image `806.png`. -/
structure SledOrbitFigure where
  showsSled : Bool
  showsCentralPost : Bool
  showsRopeFromPostToSled : Bool
  showsDashedCircularPath : Bool
  showsDirectionArrowheads : Bool
  showsRadiusArrowFromPostToOrbit : Bool
  showsRadiusLabelR : Bool
  depictedRotationSense : RotationSense

/-!
Independent physical quantities of the experiment.  In particular,
`ropeForce` is neither defined from nor initialized with the displayed answer.
-/
structure SledOrbitSetup where
  figure : SledOrbitFigure
  surfaceOrientation : SurfaceOrientation
  frictionRegime : FrictionRegime
  trajectoryShape : TrajectoryShape
  ropeAttachedToPost : Bool
  ropeIsTaut : Bool
  motionIsUniform : Bool
  ropeForceDirection : RadialDirection
  onlyHorizontalForceSource : HorizontalForceSource
  sledMass : MassQuantity
  ropeLength : LengthQuantity
  orbitRadiusR : LengthQuantity
  revolutionRate : RevolutionRateQuantity
  angularSpeed : AngularSpeedQuantity
  centripetalAcceleration : AccelerationQuantity
  ropeForce : ForceQuantity

/-! ## Data, figure evidence, and governing laws -/

/-- Qualitative conditions stated in the physical scenario. -/
structure MatchesSledScenario (setup : SledOrbitSetup) : Prop where
  iceIsHorizontal : setup.surfaceOrientation = .horizontal
  iceIsEssentiallyFrictionless :
    setup.frictionRegime = .essentiallyFrictionless
  pathIsCircular : setup.trajectoryShape = .circular
  ropeIsAttachedToFixedPost : setup.ropeAttachedToPost = true
  tautRope : setup.ropeIsTaut = true
  uniformMotion : setup.motionIsUniform = true
  ropePullsTowardPost : setup.ropeForceDirection = .towardPost

/-!
Numerical data from the prose.  Five revolutions per minute is recorded as
`5 / 60` cycles per coherent-SI second.  No force value occurs here.
-/
structure MatchesProblemReadouts (setup : SledOrbitSetup) : Prop where
  massIsTwentyFiveKilograms : massInKilograms setup.sledMass = 25
  ropeIsFiveMetersLong : lengthInMeters setup.ropeLength = 5
  fiveRevolutionsPerMinute :
    revolutionRateInHertz setup.revolutionRate = 5 / 60

/-!
Primary-image evidence.  The bitmap's lower arrow points to the right and its
upper arrow points to the left, so its displayed sense is counterclockwise;
this follows the required primary evidence rather than the auxiliary caption's
incompatible word "clockwise".
-/
structure MatchesPrimaryFigure (setup : SledOrbitSetup) : Prop where
  sledShown : setup.figure.showsSled = true
  centralPostShown : setup.figure.showsCentralPost = true
  ropeShown : setup.figure.showsRopeFromPostToSled = true
  dashedCircularPathShown : setup.figure.showsDashedCircularPath = true
  directionArrowheadsShown : setup.figure.showsDirectionArrowheads = true
  radiusArrowShown : setup.figure.showsRadiusArrowFromPostToOrbit = true
  radiusLabelRShown : setup.figure.showsRadiusLabelR = true
  arrowsIndicateCounterclockwiseMotion :
    setup.figure.depictedRotationSense = .counterclockwise

/-- A taut radial rope identifies its physical length with orbit radius `R`. -/
structure SatisfiesTautRopeGeometry (setup : SledOrbitSetup) : Prop where
  radiusEqualsRopeLength : setup.orbitRadiusR = setup.ropeLength

/-- One complete revolution is `2π` radians. -/
structure SatisfiesAngularRateConversion (setup : SledOrbitSetup) : Prop where
  radiansPerSecond :
    angularSpeedInRadiansPerSecond setup.angularSpeed =
      2 * Real.pi * revolutionRateInHertz setup.revolutionRate

/-- Uniform circular kinematics gives centripetal acceleration `a = ω² R`. -/
structure SatisfiesUniformCircularKinematics
    (setup : SledOrbitSetup) : Prop where
  centripetalAccelerationLaw :
    accelerationInMetersPerSecondSquared setup.centripetalAcceleration =
      angularSpeedInRadiansPerSecond setup.angularSpeed ^ 2 *
        lengthInMeters setup.orbitRadiusR

/-!
On frictionless horizontal ice, rope tension is the only horizontal force and
Newton's second law in the inward radial direction is `F = m a`.  This is a
general governing relation and contains no requested numerical force.
-/
structure SatisfiesHorizontalNewtonianDynamics
    (setup : SledOrbitSetup) : Prop where
  ropeIsOnlyHorizontalForce :
    setup.onlyHorizontalForceSource = .ropeTension
  radialNewtonsSecondLaw :
    forceInNewtons setup.ropeForce =
      massInKilograms setup.sledMass *
        accelerationInMetersPerSecondSquared setup.centripetalAcceleration

/-! ## Displayed choices and requested conclusion -/

/-- Labels of the four force values displayed in the question. -/
inductive AnswerChoice where
  | a
  | b
  | c
  | d
  deriving DecidableEq, Fintype, Repr

/-- Displayed answer values, read in newtons. -/
def displayedForceInNewtons : AnswerChoice → ℝ
  | .a => 356 / 10
  | .b => 343 / 10
  | .c => 324 / 10
  | .d => 399 / 10

/-- A displayed choice is closest to a computed force magnitude. -/
def IsClosestDisplayedAnswer (forceNewtons : ℝ)
    (choice : AnswerChoice) : Prop :=
  ∀ other,
    |forceNewtons - displayedForceInNewtons choice| ≤
      |forceNewtons - displayedForceInNewtons other|

/-!
The rope force is `m R ω² = 125 (π/6)² N`.  Its distance from `34.3 N` is
less than `0.05 N`, so rounding to the stated precision gives answer B, which
is also the closest displayed choice.

Blueprint: `thm:physics:phyx_mini_0806:target`.
-/
theorem sledRopeForce_is_34_point_3_newtons
    (setup : SledOrbitSetup)
    (_scenario : MatchesSledScenario setup)
    (_readouts : MatchesProblemReadouts setup)
    (_figure : MatchesPrimaryFigure setup)
    (_geometry : SatisfiesTautRopeGeometry setup)
    (_rateConversion : SatisfiesAngularRateConversion setup)
    (_kinematics : SatisfiesUniformCircularKinematics setup)
    (_dynamics : SatisfiesHorizontalNewtonianDynamics setup) :
    forceInNewtons setup.ropeForce = 125 * (Real.pi / 6) ^ 2 ∧
      |forceInNewtons setup.ropeForce - displayedForceInNewtons .b| < 1 / 20 ∧
      IsClosestDisplayedAnswer (forceInNewtons setup.ropeForce) .b := by
  have hRadius :
      lengthInMeters setup.orbitRadiusR = 5 := by
    rw [_geometry.radiusEqualsRopeLength, _readouts.ropeIsFiveMetersLong]
  have hAngularSpeed :
      angularSpeedInRadiansPerSecond setup.angularSpeed = Real.pi / 6 := by
    rw [_rateConversion.radiansPerSecond,
      _readouts.fiveRevolutionsPerMinute]
    ring
  have hAcceleration :
      accelerationInMetersPerSecondSquared setup.centripetalAcceleration =
        5 * (Real.pi / 6) ^ 2 := by
    rw [_kinematics.centripetalAccelerationLaw, hAngularSpeed, hRadius]
    ring
  have hForce :
      forceInNewtons setup.ropeForce = 125 * (Real.pi / 6) ^ 2 := by
    rw [_dynamics.radialNewtonsSecondLaw,
      _readouts.massIsTwentyFiveKilograms, hAcceleration]
    ring
  have hPiSquareLower : (3.1415 : ℝ) ^ 2 < Real.pi ^ 2 := by
    have hProduct :
        0 < (Real.pi - 3.1415) * (Real.pi + 3.1415) :=
      mul_pos (sub_pos.mpr Real.pi_gt_d4) (by nlinarith [Real.pi_pos])
    nlinarith
  have hPiSquareUpper : Real.pi ^ 2 < (3.1416 : ℝ) ^ 2 := by
    have hProduct :
        0 < (3.1416 - Real.pi) * (3.1416 + Real.pi) :=
      mul_pos (sub_pos.mpr Real.pi_lt_d4) (by nlinarith [Real.pi_pos])
    nlinarith
  have hForceLower :
      (3425 : ℝ) / 100 < forceInNewtons setup.ropeForce := by
    rw [hForce]
    nlinarith
  have hForceUpper :
      forceInNewtons setup.ropeForce < (3435 : ℝ) / 100 := by
    rw [hForce]
    nlinarith
  have hRounded :
      |forceInNewtons setup.ropeForce - displayedForceInNewtons .b| <
        1 / 20 := by
    simp only [displayedForceInNewtons]
    rw [abs_lt]
    constructor <;> nlinarith
  refine ⟨hForce, hRounded, ?_⟩
  unfold IsClosestDisplayedAnswer
  intro other
  have hRoundedLe :
      |forceInNewtons setup.ropeForce - displayedForceInNewtons .b| ≤
        1 / 20 :=
    hRounded.le
  fin_cases other
  · simp only [displayedForceInNewtons] at hRoundedLe ⊢
    rw [abs_of_neg (by nlinarith :
      forceInNewtons setup.ropeForce - 356 / 10 < 0)]
    nlinarith
  · rfl
  · simp only [displayedForceInNewtons] at hRoundedLe ⊢
    rw [abs_of_pos (by nlinarith :
      0 < forceInNewtons setup.ropeForce - 324 / 10)]
    nlinarith
  · simp only [displayedForceInNewtons] at hRoundedLe ⊢
    rw [abs_of_neg (by nlinarith :
      forceInNewtons setup.ropeForce - 399 / 10 < 0)]
    nlinarith

end PhyXMiniProblems.ProblemPhyXMini0806
