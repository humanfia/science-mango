import Mathlib
import Physlib.ClassicalMechanics.Mass.MassUnit
import Physlib.SpaceAndTime.Space.LengthUnit
import Physlib.Units.WithDim.Basic

noncomputable section

namespace PhyXMiniProblems.ProblemPhyXMini0786

open Dimension

/-!
# A hollow spherical shell rolling through a vertical circular track

A thin-walled hollow spherical shell of mass `m` and radius `r` starts from
rest at height `h₀`.  It rolls without slipping and with negligible rolling-
friction work into the circular part of a track of radius `R`.  The supplied
figure marks the top of the circle by `A` and the leftmost point, level with
the circle's center, by `B`.

Physical quantities are represented by Physlib's unit-independent
`Dimensionful (WithDim ...)` types.  Real numbers below are only coherent-unit
readouts, dimensionless ratios, or literal figure/answer-choice data.

The recorded answer `11/5 mg` is retained only as dataset metadata.  The
source does not specify a numerical value of `h₀` or a minimum-height/contact
condition at `A`, so its physical data determine the force at `B` only as a
function of `h₀ / R`.
-/

/-! ## Dimensions, physical quantities, and coherent-unit readouts -/

/-- Speed has dimension length divided by time. -/
def speedDimension : Dimension := L𝓭 * T𝓭⁻¹

/-- Angular speed has inverse-time dimension because radians are dimensionless. -/
def angularSpeedDimension : Dimension := T𝓭⁻¹

/-- Acceleration has dimension length divided by time squared. -/
def accelerationDimension : Dimension := L𝓭 * T𝓭⁻¹ * T𝓭⁻¹

/-- Force has dimension mass-length divided by time squared. -/
def forceDimension : Dimension := M𝓭 * L𝓭 * T𝓭⁻¹ * T𝓭⁻¹

/-- Moment of inertia has dimension mass times length squared. -/
def momentOfInertiaDimension : Dimension := M𝓭 * L𝓭 * L𝓭

/-- A nonnegative, unit-independent physical mass. -/
abbrev MassQuantity : Type := Dimensionful (WithDim M𝓭 NNReal)

/-- A nonnegative, unit-independent physical length. -/
abbrev LengthQuantity : Type := Dimensionful (WithDim L𝓭 NNReal)

/-- A nonnegative, unit-independent speed magnitude. -/
abbrev SpeedQuantity : Type :=
  Dimensionful (WithDim speedDimension NNReal)

/-- A nonnegative, unit-independent angular-speed magnitude. -/
abbrev AngularSpeedQuantity : Type :=
  Dimensionful (WithDim angularSpeedDimension NNReal)

/-- A nonnegative, unit-independent acceleration magnitude. -/
abbrev AccelerationQuantity : Type :=
  Dimensionful (WithDim accelerationDimension NNReal)

/-- A nonnegative, unit-independent contact-force magnitude. -/
abbrev ForceMagnitudeQuantity : Type :=
  Dimensionful (WithDim forceDimension NNReal)

/-- A nonnegative, unit-independent moment of inertia about the rotation axis. -/
abbrev MomentOfInertiaQuantity : Type :=
  Dimensionful (WithDim momentOfInertiaDimension NNReal)

/-- Read a physical mass in a selected mass unit. -/
def massReadout (unit : MassUnit) (mass : MassQuantity) : ℝ :=
  ((mass {UnitChoices.SI with mass := unit}).val : ℝ)

/-- Read a physical length in a selected length unit. -/
def lengthReadout (unit : LengthUnit) (length : LengthQuantity) : ℝ :=
  ((length {UnitChoices.SI with length := unit}).val : ℝ)

/-- Read speed in coherent selected length and time units. -/
def speedReadout
    (lengthUnit : LengthUnit) (timeUnit : TimeUnit)
    (speed : SpeedQuantity) : ℝ :=
  ((speed {UnitChoices.SI with
    length := lengthUnit, time := timeUnit}).val : ℝ)

/-- Read angular speed in inverse units of a selected time unit. -/
def angularSpeedReadout
    (timeUnit : TimeUnit) (angularSpeed : AngularSpeedQuantity) : ℝ :=
  ((angularSpeed {UnitChoices.SI with time := timeUnit}).val : ℝ)

/-- Read acceleration in coherent selected length and time units. -/
def accelerationReadout
    (lengthUnit : LengthUnit) (timeUnit : TimeUnit)
    (acceleration : AccelerationQuantity) : ℝ :=
  ((acceleration {UnitChoices.SI with
    length := lengthUnit, time := timeUnit}).val : ℝ)

/-- Read a force magnitude in coherent selected mechanical units. -/
def forceMagnitudeReadout
    (massUnit : MassUnit) (lengthUnit : LengthUnit) (timeUnit : TimeUnit)
    (force : ForceMagnitudeQuantity) : ℝ :=
  ((force {UnitChoices.SI with
    mass := massUnit, length := lengthUnit, time := timeUnit}).val : ℝ)

/-- Read a moment of inertia in coherent selected mass and length units. -/
def momentOfInertiaReadout
    (massUnit : MassUnit) (lengthUnit : LengthUnit)
    (inertia : MomentOfInertiaQuantity) : ℝ :=
  ((inertia {UnitChoices.SI with
    mass := massUnit, length := lengthUnit}).val : ℝ)

/-! ## Physical stages and primary-figure vocabulary -/

/-- Points occupied by the shell along its route. -/
inductive MotionPoint where
  | release
  | loopBottom
  | A
  | B
  deriving DecidableEq, Fintype, Repr

/-- Marked points in the supplied figure, including the geometric center. -/
inductive FigurePoint where
  | release
  | loopBottom
  | circleCenter
  | A
  | B
  deriving DecidableEq, Fintype, Repr

/-- Points of the circular track at which contact force is modeled. -/
inductive LoopPoint where
  | loopBottom
  | A
  | B
  deriving DecidableEq, Fintype, Repr

/-- Objects and annotations visible in image `786.png`. -/
inductive FigureObject where
  | shell
  | descendingTrack
  | circularTrack
  | baseline
  | releaseHeightArrow
  | circleRadiusArrow
  deriving DecidableEq, Fintype, Repr

/-- Symbolic labels printed in image `786.png`. -/
inductive FigureLabel where
  | shellText
  | releaseHeightH0
  | circleRadiusR
  | pointA
  | pointB
  deriving DecidableEq, Fintype, Repr

/-- Idealized mass distribution of the rolling object. -/
inductive ShellMassModel where
  | thinWalledHollowSpherical
  | other
  deriving DecidableEq, Repr

/-- Kinematic contact condition between shell and track. -/
inductive RollingMode where
  | withoutSlipping
  | slipping
  deriving DecidableEq, Repr

/-- Work model for rolling friction over the portion of track used here. -/
inductive RollingFrictionWorkModel where
  | negligible
  | nonnegligible
  deriving DecidableEq, Repr

/-- Which side of the circular rail contains the shell's center of mass. -/
inductive CircularTrackContactSide where
  | insideLoop
  | outsideLoop
  deriving DecidableEq, Repr

/-- Qualitative comparison used by the source's small-shell approximation. -/
inductive RelativeScale where
  | negligible
  | comparable
  deriving DecidableEq, Repr

/-!
Literal incidence and qualitative data transcribed from the supplied raster.
The image gives symbolic `h₀` and `R` labels, not numerical values.
-/
structure SuppliedRollingShellFigure where
  showsObject : FigureObject → Bool
  showsPoint : FigurePoint → Bool
  showsLabel : FigureLabel → Bool
  descendingTrackJoinsLoopBottom : Bool
  releaseHeightMeasuredFromBaseline : Bool
  radiusArrowRunsFromCenterToTrack : Bool
  pointAIsTopOfCircle : Bool
  pointBIsLeftmostPointOfCircle : Bool
  pointBLevelWithCircleCenter : Bool

/-!
Independent physical quantities and response fields.  In particular,
`normalForceMagnitude .B` is not defined from an answer choice and is not
assigned its requested value in this structure.
-/
structure RollingShellLoopSetup where
  shellMass : MassQuantity
  shellRadius : LengthQuantity
  shellDiameter : LengthQuantity
  shellMomentOfInertia : MomentOfInertiaQuantity
  loopRadius : LengthQuantity
  releaseHeight : LengthQuantity
  gravitationalAccelerationMagnitude : AccelerationQuantity
  heightAboveBaseline : MotionPoint → LengthQuantity
  speedMagnitude : MotionPoint → SpeedQuantity
  angularSpeedMagnitude : MotionPoint → AngularSpeedQuantity
  normalForceMagnitude : LoopPoint → ForceMagnitudeQuantity
  shellMassModel : ShellMassModel
  rollingMode : RollingMode
  rollingFrictionWorkModel : RollingFrictionWorkModel
  circularTrackContactSide : CircularTrackContactSide
  diameterComparedWithReleaseHeight : RelativeScale
  diameterComparedWithLoopRadius : RelativeScale
  figure : SuppliedRollingShellFigure

/-! ## Scenario assignments, figure readouts, and physical laws -/

/-!
Problem-text assignments and primary-image readouts.  The relations
`height(A) = 2R` and `height(B) = R` encode the top and side geometry of the
vertical circle; neither relation prescribes the requested force at `B`.
-/
structure MatchesProblemAndFigureReadouts
    (setup : RollingShellLoopSetup) : Prop where
  shellIsThinWalledAndHollow :
    setup.shellMassModel = .thinWalledHollowSpherical
  rollsWithoutSlipping : setup.rollingMode = .withoutSlipping
  rollingFrictionWorkIsNegligible :
    setup.rollingFrictionWorkModel = .negligible
  shellTravelsInsideCircularTrack :
    setup.circularTrackContactSide = .insideLoop
  diameterNegligibleComparedWithReleaseHeight :
    setup.diameterComparedWithReleaseHeight = .negligible
  diameterNegligibleComparedWithLoopRadius :
    setup.diameterComparedWithLoopRadius = .negligible
  startsFromRest :
    ∀ (lengthUnit : LengthUnit) (timeUnit : TimeUnit),
      speedReadout lengthUnit timeUnit
        (setup.speedMagnitude .release) = 0 ∧
      angularSpeedReadout timeUnit
        (setup.angularSpeedMagnitude .release) = 0
  diameterIsTwiceRadius :
    ∀ lengthUnit : LengthUnit,
      lengthReadout lengthUnit setup.shellDiameter =
        2 * lengthReadout lengthUnit setup.shellRadius
  releasePointHasHeightH0 :
    ∀ lengthUnit : LengthUnit,
      lengthReadout lengthUnit
          (setup.heightAboveBaseline .release) =
        lengthReadout lengthUnit setup.releaseHeight
  loopBottomIsBaseline :
    ∀ lengthUnit : LengthUnit,
      lengthReadout lengthUnit
        (setup.heightAboveBaseline .loopBottom) = 0
  pointAHeight :
    ∀ lengthUnit : LengthUnit,
      lengthReadout lengthUnit (setup.heightAboveBaseline .A) =
        2 * lengthReadout lengthUnit setup.loopRadius
  pointBLevelWithCenter :
    ∀ lengthUnit : LengthUnit,
      lengthReadout lengthUnit (setup.heightAboveBaseline .B) =
        lengthReadout lengthUnit setup.loopRadius
  allFigureObjectsShown : ∀ object, setup.figure.showsObject object = true
  releasePointShown : setup.figure.showsPoint .release = true
  pointAShown : setup.figure.showsPoint .A = true
  pointBShown : setup.figure.showsPoint .B = true
  allPrintedLabelsShown : ∀ label, setup.figure.showsLabel label = true
  trackJoinsLoopAtBottom :
    setup.figure.descendingTrackJoinsLoopBottom = true
  heightArrowUsesBaseline :
    setup.figure.releaseHeightMeasuredFromBaseline = true
  radiusArrowIncidence :
    setup.figure.radiusArrowRunsFromCenterToTrack = true
  AAtTopReadout : setup.figure.pointAIsTopOfCircle = true
  BAtLeftReadout : setup.figure.pointBIsLeftmostPointOfCircle = true
  BLevelWithCenterReadout :
    setup.figure.pointBLevelWithCircleCenter = true

/-- Positivity assumptions for the nondegenerate shell, loop, and gravity. -/
structure HasPhysicalRollingShellParameters
    (setup : RollingShellLoopSetup) : Prop where
  shellMassPositive :
    ∀ massUnit, 0 < massReadout massUnit setup.shellMass
  shellRadiusPositive :
    ∀ lengthUnit, 0 < lengthReadout lengthUnit setup.shellRadius
  shellDiameterPositive :
    ∀ lengthUnit, 0 < lengthReadout lengthUnit setup.shellDiameter
  shellMomentOfInertiaPositive :
    ∀ massUnit lengthUnit,
      0 < momentOfInertiaReadout massUnit lengthUnit
        setup.shellMomentOfInertia
  loopRadiusPositive :
    ∀ lengthUnit, 0 < lengthReadout lengthUnit setup.loopRadius
  releaseHeightPositive :
    ∀ lengthUnit, 0 < lengthReadout lengthUnit setup.releaseHeight
  gravitationalAccelerationPositive :
    ∀ lengthUnit timeUnit,
      0 < accelerationReadout lengthUnit timeUnit
        setup.gravitationalAccelerationMagnitude

/-!
For a thin-walled hollow spherical shell about a diameter,
`I = (2/3) m r²`.  LeanExplore found Physlib's solid-sphere inertia tensor but
no corresponding hollow-shell theorem, so the needed constitutive law is
stated explicitly at the coherent-readout level.
-/
structure SatisfiesThinHollowShellInertiaLaw
    (setup : RollingShellLoopSetup) : Prop where
  hollowShellInertia :
    ∀ (massUnit : MassUnit) (lengthUnit : LengthUnit),
      momentOfInertiaReadout massUnit lengthUnit
          setup.shellMomentOfInertia =
        (2 / 3 : ℝ) * massReadout massUnit setup.shellMass *
          (lengthReadout lengthUnit setup.shellRadius) ^ 2

/-!
The no-slip constraint is `v = rω` at every occupied point.  It is a
kinematic law, separate from the qualitative assertion that the rolling mode
is no-slip.
-/
structure SatisfiesRollingWithoutSlipLaw
    (setup : RollingShellLoopSetup) : Prop where
  rollingConstraint :
    ∀ (lengthUnit : LengthUnit) (timeUnit : TimeUnit)
        (point : MotionPoint),
      speedReadout lengthUnit timeUnit (setup.speedMagnitude point) =
        lengthReadout lengthUnit setup.shellRadius *
          angularSpeedReadout timeUnit
            (setup.angularSpeedMagnitude point)

/-!
The scalar value of total mechanical energy in any coherent mechanical unit:
gravitational potential energy plus translational and rotational kinetic
energy.  This is a generic physical definition and contains no force answer.
-/
def mechanicalEnergyReadout
    (setup : RollingShellLoopSetup)
    (massUnit : MassUnit) (lengthUnit : LengthUnit) (timeUnit : TimeUnit)
    (point : MotionPoint) : ℝ :=
  massReadout massUnit setup.shellMass *
      accelerationReadout lengthUnit timeUnit
        setup.gravitationalAccelerationMagnitude *
      lengthReadout lengthUnit (setup.heightAboveBaseline point) +
    (1 / 2 : ℝ) * massReadout massUnit setup.shellMass *
      (speedReadout lengthUnit timeUnit (setup.speedMagnitude point)) ^ 2 +
    (1 / 2 : ℝ) *
      momentOfInertiaReadout massUnit lengthUnit
        setup.shellMomentOfInertia *
      (angularSpeedReadout timeUnit
        (setup.angularSpeedMagnitude point)) ^ 2

/-!
Negligible rolling-friction work makes mechanical energy at every relevant
point equal to its release value.
-/
structure SatisfiesConservativeRollingEnergyLaw
    (setup : RollingShellLoopSetup) : Prop where
  energyConservedFromRelease :
    ∀ (massUnit : MassUnit) (lengthUnit : LengthUnit)
        (timeUnit : TimeUnit) (point : MotionPoint),
      mechanicalEnergyReadout setup massUnit lengthUnit timeUnit point =
        mechanicalEnergyReadout setup massUnit lengthUnit timeUnit .release

/-!
Radial Newton laws on the inside of the circular track.  At top point `A`,
gravity and the normal force both point inward.  At side point `B`, gravity is
perpendicular to the inward radius, so only the normal force contributes.
The use of `R` as the center-of-mass path radius is the stated small-shell
approximation.
-/
structure SatisfiesCircularTrackRadialDynamics
    (setup : RollingShellLoopSetup) : Prop where
  radialNewtonLawAtA :
    ∀ (massUnit : MassUnit) (lengthUnit : LengthUnit)
        (timeUnit : TimeUnit),
      massReadout massUnit setup.shellMass *
          (speedReadout lengthUnit timeUnit
            (setup.speedMagnitude .A)) ^ 2 /
          lengthReadout lengthUnit setup.loopRadius =
        massReadout massUnit setup.shellMass *
            accelerationReadout lengthUnit timeUnit
              setup.gravitationalAccelerationMagnitude +
          forceMagnitudeReadout massUnit lengthUnit timeUnit
            (setup.normalForceMagnitude .A)
  radialNewtonLawAtB :
    ∀ (massUnit : MassUnit) (lengthUnit : LengthUnit)
        (timeUnit : TimeUnit),
      massReadout massUnit setup.shellMass *
          (speedReadout lengthUnit timeUnit
            (setup.speedMagnitude .B)) ^ 2 /
          lengthReadout lengthUnit setup.loopRadius =
        forceMagnitudeReadout massUnit lengthUnit timeUnit
          (setup.normalForceMagnitude .B)

/-! ## Answer-choice metadata -/

/-- Labels displayed with the exercise. -/
inductive AnswerChoice where
  | A
  | B
  | C
  | D
  deriving DecidableEq, Fintype, Repr

/-- Displayed dimensionless multiplier of the shell's weight `mg`. -/
def displayedWeightMultiplier : AnswerChoice → ℝ
  | .A => 1 / 5
  | .B => 11 / 5
  | .C => 10 / 7
  | .D => 20 / 7

/-- The source dataset records answer choice B; this is metadata, not a premise. -/
def recordedDatasetAnswer : AnswerChoice := .B

/-!
Source-faithful redraft of blueprint declaration
`thm:physics:phyx_mini_0786:target`.

The data actually printed in the problem determine the normal force at `B`
as a function of the release height `h₀`.  For a thin hollow shell the total
rolling kinetic energy is `(5/6) m v²`; conservation of energy from release to
`B`, followed by the radial Newton law at `B`, gives

`N_B = (6/5) m g (h₀ / R - 1)`.

This is the source-faithful conclusion: no minimum-height or marginal-contact
condition appears among its hypotheses.
-/
theorem normalForceAtB_from_releaseHeight
    (setup : RollingShellLoopSetup)
    (hScenario : MatchesProblemAndFigureReadouts setup)
    (hPhysical : HasPhysicalRollingShellParameters setup)
    (hInertia : SatisfiesThinHollowShellInertiaLaw setup)
    (hNoSlip : SatisfiesRollingWithoutSlipLaw setup)
    (hEnergy : SatisfiesConservativeRollingEnergyLaw setup)
    (hRadial : SatisfiesCircularTrackRadialDynamics setup) :
    ∀ (massUnit : MassUnit) (lengthUnit : LengthUnit)
        (timeUnit : TimeUnit),
      forceMagnitudeReadout massUnit lengthUnit timeUnit
          (setup.normalForceMagnitude .B) =
        (6 / 5 : ℝ) * massReadout massUnit setup.shellMass *
          accelerationReadout lengthUnit timeUnit
            setup.gravitationalAccelerationMagnitude *
          (lengthReadout lengthUnit setup.releaseHeight /
              lengthReadout lengthUnit setup.loopRadius - 1) := by
  sorry

end PhyXMiniProblems.ProblemPhyXMini0786
