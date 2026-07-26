import Mathlib
import Physlib.Units.WithDim.Basic

/- USER: The assigned source file did not exist when this autoformalization task began. -/

noncomputable section

namespace PhyXMiniProblems.ProblemPhyXMini0784

open Dimension

/-!
# Tangential crank force for raising a crate

A `50 kg` crate hangs from a massless rope wrapped around a wooden drum of
radius `0.25 m` and axial moment of inertia `2.9 kg m²`. A tangential force is
applied at the endpoint of a crank of radius `0.12 m`. The requested observable
is the force magnitude needed to accelerate the crate upward at `1.40 m/s²`.

Masses, lengths, accelerations, forces, moments of inertia, and torques are
unit-independent Physlib quantities. Real numbers occur only as coherent SI
readouts or as the numerical readouts printed in the multiple-choice answers.

Assumption/target split:

* governing laws: upward Newton's second law for the crate, no-slip rope
  kinematics, tangential moment arms, signed torque balance, and fixed-axis
  rotational dynamics of the drum;
* previous-part results: none;
* data and figure readouts: the component materials and idealizations, the
  stated mass, radii, drum inertia, upward acceleration, conventional
  near-Earth gravity, and the objects and labels visible in image `784.png`;
* current target: the required force has the independently derived readout
  `1302 N`, making displayed answer B (`1300 N`) the closest choice.
-/

/-! ## Dimensionful quantities and coherent SI readouts -/

/-- The physical dimension `L T⁻²` of linear acceleration. -/
def accelerationDimension : Dimension :=
  L𝓭 * T𝓭⁻¹ * T𝓭⁻¹

/-- Angular acceleration has dimension `T⁻²` because radians are dimensionless. -/
def angularAccelerationDimension : Dimension :=
  T𝓭⁻¹ * T𝓭⁻¹

/-- The physical dimension `M L T⁻²` of force. -/
def forceDimension : Dimension :=
  M𝓭 * L𝓭 * T𝓭⁻¹ * T𝓭⁻¹

/-- The physical dimension `M L²` of a moment of inertia. -/
def momentOfInertiaDimension : Dimension :=
  M𝓭 * L𝓭 * L𝓭

/-- The physical dimension `M L² T⁻²` of torque. -/
def torqueDimension : Dimension :=
  M𝓭 * L𝓭 * L𝓭 * T𝓭⁻¹ * T𝓭⁻¹

/-- A nonnegative physical mass, independent of the chosen unit system. -/
abbrev MassQuantity : Type :=
  Dimensionful (WithDim M𝓭 NNReal)

/-- A nonnegative physical length. -/
abbrev LengthQuantity : Type :=
  Dimensionful (WithDim L𝓭 NNReal)

/-- A nonnegative linear-acceleration magnitude. -/
abbrev AccelerationMagnitudeQuantity : Type :=
  Dimensionful (WithDim accelerationDimension NNReal)

/-- A nonnegative angular-acceleration magnitude. -/
abbrev AngularAccelerationMagnitudeQuantity : Type :=
  Dimensionful (WithDim angularAccelerationDimension NNReal)

/-- A nonnegative force magnitude. -/
abbrev ForceMagnitudeQuantity : Type :=
  Dimensionful (WithDim forceDimension NNReal)

/-- A nonnegative axial moment of inertia. -/
abbrev MomentOfInertiaQuantity : Type :=
  Dimensionful (WithDim momentOfInertiaDimension NNReal)

/-- A signed torque about the axle; positive torque raises the crate. -/
abbrev SignedTorqueQuantity : Type :=
  Dimensionful (WithDim torqueDimension ℝ)

/-- Read a physical mass in kilograms. -/
def massInKilograms (mass : MassQuantity) : ℝ :=
  ((mass UnitChoices.SI).val : ℝ)

/-- Read a physical length in metres. -/
def lengthInMeters (length : LengthQuantity) : ℝ :=
  ((length UnitChoices.SI).val : ℝ)

/-- Read a linear acceleration in metres per second squared. -/
def accelerationInMetersPerSecondSquared
    (acceleration : AccelerationMagnitudeQuantity) : ℝ :=
  ((acceleration UnitChoices.SI).val : ℝ)

/-- Read an angular acceleration in radians per second squared. -/
def angularAccelerationInRadiansPerSecondSquared
    (acceleration : AngularAccelerationMagnitudeQuantity) : ℝ :=
  ((acceleration UnitChoices.SI).val : ℝ)

/-- Read a force magnitude in newtons. -/
def forceMagnitudeInNewtons (force : ForceMagnitudeQuantity) : ℝ :=
  ((force UnitChoices.SI).val : ℝ)

/-- Read a moment of inertia in kilogram square metres. -/
def momentOfInertiaInKilogramSquareMeters
    (inertia : MomentOfInertiaQuantity) : ℝ :=
  ((inertia UnitChoices.SI).val : ℝ)

/-- Read a signed torque in newton metres. -/
def signedTorqueInNewtonMeters (torque : SignedTorqueQuantity) : ℝ :=
  (torque UnitChoices.SI).val

/-! ## Mechanical setup and primary-figure vocabulary -/

/-- Materials explicitly assigned to components by the prose. -/
inductive ComponentMaterial where
  | wood
  | metal
  | other
  deriving DecidableEq, Repr

/-- The bearing idealization at the pivoting end of the axle. -/
inductive BearingRegime where
  | frictionless
  | dissipative
  deriving DecidableEq, Repr

/-- The path followed by the endpoint of the crank handle. -/
inductive CrankEndpointPath where
  | verticalCircleAboutAxle
  | other
  deriving DecidableEq, Repr

/-- How the applied force is oriented relative to the crank's circular path. -/
inductive AppliedForceDirection where
  | tangentialToCrankCircle
  | radial
  | other
  deriving DecidableEq, Repr

/-- Physical objects visibly distinguished in image `784.png`. -/
inductive FigureObject where
  | woodenDrum
  | wrappedRope
  | suspendedCrate
  | metalAxle
  | crankHandle
  | crankHandleEndpoint
  | axleSupports
  deriving DecidableEq, Fintype, Repr

/-- Literal labels printed in the primary image. -/
inductive FigureLabel where
  | crankRadiusZeroPointTwelveMeters
  | appliedForceF
  deriving DecidableEq, Fintype, Repr

/-!
Typed evidence from the supplied raster. The vertical `0.12 m` dimension runs
from the axle level to the handle endpoint and is therefore the crank radius.
The raster itself does not print the requested force magnitude.
-/
structure CrankDrumFigure where
  showsObject : FigureObject → Bool
  showsLabel : FigureLabel → Bool
  labeledCrankRadius : LengthQuantity
  forceArrowApplicationPoint : FigureObject
  forceArrowDirection : AppliedForceDirection
  zeroPointTwelveIsDistanceFromAxleToHandleEndpoint : Bool
  ropeRunsDownwardFromDrumToCrate : Bool
  containsNumericalForceMagnitude : Bool

/-!
Independent observables and physical parameters of the lifting mechanism. In
particular, the applied force is a field constrained by the governing laws;
it is not defined from answer choice B.
-/
structure CrankDrumLiftSetup where
  drumMaterial : ComponentMaterial
  axleMaterial : ComponentMaterial
  bearingRegime : BearingRegime
  crankEndpointPath : CrankEndpointPath
  appliedForceDirection : AppliedForceDirection
  ropeWrappedAroundDrum : Bool
  crateSuspendedFromFreeRopeEnd : Bool
  crankRotationRaisesCrate : Bool
  crateMass : MassQuantity
  ropeMass : MassQuantity
  drumRadius : LengthQuantity
  crankRadius : LengthQuantity
  drumMomentOfInertiaAboutAxle : MomentOfInertiaQuantity
  axleMomentOfInertia : MomentOfInertiaQuantity
  crankMomentOfInertia : MomentOfInertiaQuantity
  gravitationalAcceleration : AccelerationMagnitudeQuantity
  crateUpwardAcceleration : AccelerationMagnitudeQuantity
  drumAngularAcceleration : AngularAccelerationMagnitudeQuantity
  ropeTension : ForceMagnitudeQuantity
  appliedTangentialForce : ForceMagnitudeQuantity
  handleTorqueAboutAxle : SignedTorqueQuantity
  ropeLoadTorqueAboutAxle : SignedTorqueQuantity
  netTorqueAboutAxle : SignedTorqueQuantity
  figure : CrankDrumFigure

/-! ## Scenario, problem data, figure evidence, and governing laws -/

/-!
Qualitative content and stated idealizations. Treating the rope, axle, and
crank contributions as zero is the explicit model corresponding to the
instruction to ignore them. No value of the applied force occurs here.
-/
structure MatchesIdealLiftingScenario (setup : CrankDrumLiftSetup) : Prop where
  woodenDrum : setup.drumMaterial = .wood
  metalAxle : setup.axleMaterial = .metal
  frictionlessBearing : setup.bearingRegime = .frictionless
  handleMovesInVerticalCircle :
    setup.crankEndpointPath = .verticalCircleAboutAxle
  forceIsTangential :
    setup.appliedForceDirection = .tangentialToCrankCircle
  ropeIsWrapped : setup.ropeWrappedAroundDrum = true
  crateIsSuspended : setup.crateSuspendedFromFreeRopeEnd = true
  turningCrankRaisesCrate : setup.crankRotationRaisesCrate = true
  ropeMassNegligible : massInKilograms setup.ropeMass = 0
  axleInertiaNegligible :
    momentOfInertiaInKilogramSquareMeters setup.axleMomentOfInertia = 0
  crankInertiaNegligible :
    momentOfInertiaInKilogramSquareMeters setup.crankMomentOfInertia = 0

/-!
Numerical readouts stated in the problem, plus the conventional near-Earth
value `g = 9.8 m/s²` used to resolve the recorded multiple-choice answer. This
predicate contains no applied-force readout.
-/
structure MatchesProblemReadouts (setup : CrankDrumLiftSetup) : Prop where
  crateMass : massInKilograms setup.crateMass = 50
  drumRadius : lengthInMeters setup.drumRadius = (1 : ℝ) / 4
  drumMomentOfInertia :
    momentOfInertiaInKilogramSquareMeters
        setup.drumMomentOfInertiaAboutAxle = (29 : ℝ) / 10
  crankRadius : lengthInMeters setup.crankRadius = (3 : ℝ) / 25
  requiredUpwardAcceleration :
    accelerationInMetersPerSecondSquared setup.crateUpwardAcceleration =
      (7 : ℝ) / 5
  standardGravity :
    accelerationInMetersPerSecondSquared setup.gravitationalAcceleration =
      (49 : ℝ) / 5

/-- Objects, labels, and the radial interpretation of `0.12 m` in the image. -/
structure MatchesSuppliedFigure (setup : CrankDrumLiftSetup) : Prop where
  everyObjectShown : ∀ object, setup.figure.showsObject object = true
  everyLabelShown : ∀ label, setup.figure.showsLabel label = true
  radiusLabelDenotesCrankRadius :
    setup.figure.labeledCrankRadius = setup.crankRadius
  radiusLabelReadout :
    lengthInMeters setup.figure.labeledCrankRadius = (3 : ℝ) / 25
  forceArrowAtHandleEndpoint :
    setup.figure.forceArrowApplicationPoint = .crankHandleEndpoint
  forceArrowIsTangential :
    setup.figure.forceArrowDirection = .tangentialToCrankCircle
  dimensionIsRadial :
    setup.figure.zeroPointTwelveIsDistanceFromAxleToHandleEndpoint = true
  ropeConnectsDrumAndCrate :
    setup.figure.ropeRunsDownwardFromDrumToCrate = true
  noAnswerPrinted : setup.figure.containsNumericalForceMagnitude = false

/-!
The scalar, fixed-axis mechanics used to determine the force:

* upward Newton's second law for the crate is `T - mg = ma`;
* the rope does not slip on the drum, so `a = α R`;
* tangential force and rope tension have torque magnitudes `F r` and `T R`;
* the rope torque opposes the handle torque; and
* the drum obeys the fixed-axis law `τ_net = I α`.

These are governing relations between independent observables. None gives a
numerical value for the applied force or mentions an answer choice.
-/
structure ObeysIdealCrankDrumMechanics (setup : CrankDrumLiftSetup) : Prop where
  crateNewtonSecondLaw :
    forceMagnitudeInNewtons setup.ropeTension -
        massInKilograms setup.crateMass *
          accelerationInMetersPerSecondSquared
            setup.gravitationalAcceleration =
      massInKilograms setup.crateMass *
        accelerationInMetersPerSecondSquared setup.crateUpwardAcceleration
  noSlipRopeKinematics :
    accelerationInMetersPerSecondSquared setup.crateUpwardAcceleration =
      angularAccelerationInRadiansPerSecondSquared
          setup.drumAngularAcceleration *
        lengthInMeters setup.drumRadius
  tangentialHandleTorque :
    signedTorqueInNewtonMeters setup.handleTorqueAboutAxle =
      forceMagnitudeInNewtons setup.appliedTangentialForce *
        lengthInMeters setup.crankRadius
  ropeTensionTorque :
    signedTorqueInNewtonMeters setup.ropeLoadTorqueAboutAxle =
      forceMagnitudeInNewtons setup.ropeTension *
        lengthInMeters setup.drumRadius
  onlyHandleAndRopeTorques :
    signedTorqueInNewtonMeters setup.netTorqueAboutAxle =
      signedTorqueInNewtonMeters setup.handleTorqueAboutAxle -
        signedTorqueInNewtonMeters setup.ropeLoadTorqueAboutAxle
  drumRotationalDynamics :
    signedTorqueInNewtonMeters setup.netTorqueAboutAxle =
      momentOfInertiaInKilogramSquareMeters
          setup.drumMomentOfInertiaAboutAxle *
        angularAccelerationInRadiansPerSecondSquared
          setup.drumAngularAcceleration

/-! ## Multiple-choice target -/

/-- The four force magnitudes supplied by the problem, in newtons. -/
inductive AnswerChoice where
  | A
  | B
  | C
  | D
  deriving DecidableEq, Fintype, Repr

/-- Numerical newton readout printed beside each answer label. -/
def answerMagnitudeInNewtons : AnswerChoice → ℝ
  | .A => 700
  | .B => 1300
  | .C => 1960
  | .D => 980

/-- A choice is closest to an independently determined force readout. -/
def IsClosestAnswer (forceInNewtons : ℝ) (choice : AnswerChoice) : Prop :=
  ∀ other,
    |forceInNewtons - answerMagnitudeInNewtons choice| ≤
      |forceInNewtons - answerMagnitudeInNewtons other|

/-!
With the stated data and ideal laws, the unrounded force is `1302 N`.
Consequently the closest supplied magnitude is answer B, `1300 N`.

Blueprint: `thm:physics:phyx_mini_0784:target`.
-/
theorem problem_phyx_mini_0784
    (setup : CrankDrumLiftSetup)
    (scenario : MatchesIdealLiftingScenario setup)
    (data : MatchesProblemReadouts setup)
    (figure : MatchesSuppliedFigure setup)
    (laws : ObeysIdealCrankDrumMechanics setup) :
    forceMagnitudeInNewtons setup.appliedTangentialForce = 1302 ∧
      IsClosestAnswer
        (forceMagnitudeInNewtons setup.appliedTangentialForce) .B := by
  have hcrate := laws.crateNewtonSecondLaw
  have hnoslip := laws.noSlipRopeKinematics
  have hhandle := laws.tangentialHandleTorque
  have hrope := laws.ropeTensionTorque
  have hnet := laws.onlyHandleAndRopeTorques
  have hrotation := laws.drumRotationalDynamics
  rw [data.crateMass, data.standardGravity,
    data.requiredUpwardAcceleration] at hcrate
  rw [data.requiredUpwardAcceleration, data.drumRadius] at hnoslip
  rw [data.crankRadius] at hhandle
  rw [data.drumRadius] at hrope
  rw [data.drumMomentOfInertia] at hrotation
  have hforce :
      forceMagnitudeInNewtons setup.appliedTangentialForce = 1302 := by
    nlinarith [hcrate, hnoslip, hhandle, hrope, hnet, hrotation]
  refine ⟨hforce, ?_⟩
  rw [hforce]
  intro other
  fin_cases other <;> norm_num [answerMagnitudeInNewtons]

end PhyXMiniProblems.ProblemPhyXMini0784
