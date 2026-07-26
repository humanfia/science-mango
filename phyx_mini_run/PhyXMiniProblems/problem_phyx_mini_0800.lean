import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Physlib.Units.WithDim.Basic

noncomputable section

namespace PhyXMiniProblems.ProblemPhyXMini0800

open Dimension

/-!
# Constant-speed quarry cart and bucket

A granite block and its steel-wheeled cart are pulled uphill on steel rails by
a dirt-filled bucket descending vertically.  One cable connects the two
assemblies over a pulley.  The incline is labelled `15°` in the supplied
figure.  Pulley and wheel friction are ignored, as is the cable's weight.

Weights, masses, tensions, speeds, and accelerations are represented as
unit-independent Physlib quantities.  Real numbers occur only as coherent SI
readouts, signed one-dimensional components, and dimensionless angle readouts.
-/

/-! ## Dimensionful physical quantities and SI readouts -/

/-- A nonnegative physical mass. -/
abbrev MassQuantity : Type :=
  Dimensionful (WithDim M𝓭 NNReal)

/-- A nonnegative physical force magnitude used specifically as a weight. -/
abbrev WeightQuantity : Type :=
  Dimensionful (WithDim (M𝓭 * L𝓭 * T𝓭⁻¹ * T𝓭⁻¹) NNReal)

/-- A nonnegative physical force magnitude carried by the cable. -/
abbrev TensionQuantity : Type :=
  Dimensionful (WithDim (M𝓭 * L𝓭 * T𝓭⁻¹ * T𝓭⁻¹) NNReal)

/-- A nonnegative speed magnitude. -/
abbrev SpeedQuantity : Type :=
  Dimensionful (WithDim (L𝓭 * T𝓭⁻¹) NNReal)

/-- A signed acceleration component along a specified one-dimensional axis. -/
abbrev SignedAccelerationQuantity : Type :=
  Dimensionful (WithDim (L𝓭 * T𝓭⁻¹ * T𝓭⁻¹) ℝ)

/-- A nonnegative gravitational-acceleration magnitude. -/
abbrev AccelerationMagnitudeQuantity : Type :=
  Dimensionful (WithDim (L𝓭 * T𝓭⁻¹ * T𝓭⁻¹) NNReal)

/-- Kilogram readout of a physical mass. -/
def massInKilograms (mass : MassQuantity) : ℝ :=
  ((mass UnitChoices.SI).val : ℝ)

/-- Newton readout of a physical weight. -/
def weightInNewtons (weight : WeightQuantity) : ℝ :=
  ((weight UnitChoices.SI).val : ℝ)

/-- Newton readout of a cable-tension magnitude. -/
def tensionInNewtons (tension : TensionQuantity) : ℝ :=
  ((tension UnitChoices.SI).val : ℝ)

/-- Metres-per-second readout of a speed magnitude. -/
def speedInMetersPerSecond (speed : SpeedQuantity) : ℝ :=
  ((speed UnitChoices.SI).val : ℝ)

/-- Signed metres-per-second-squared readout of an acceleration component. -/
def signedAccelerationInMetersPerSecondSquared
    (acceleration : SignedAccelerationQuantity) : ℝ :=
  (acceleration UnitChoices.SI).val

/-- SI readout of a nonnegative acceleration magnitude. -/
def accelerationMagnitudeInMetersPerSecondSquared
    (acceleration : AccelerationMagnitudeQuantity) : ℝ :=
  ((acceleration UnitChoices.SI).val : ℝ)

/-- Convert a dimensionless angle readout in degrees to radians. -/
def degreesToRadians (degrees : ℝ) : ℝ :=
  degrees * Real.pi / 180

/-! ## Problem objects, labels, and primary-figure geometry -/

/-- Materials explicitly named in the quarry scenario. -/
inductive Material where
  | granite
  | steel
  | dirt
  deriving DecidableEq, Repr

/-- Individually identifiable physical objects in the supplied image and text. -/
inductive FigureObject where
  | graniteBlock
  | cart
  | steelWheels
  | inclinedSteelRails
  | cable
  | pulley
  | dirtFilledBucket
  deriving DecidableEq, Repr

/-- Text and angle labels printed in the primary figure. -/
inductive FigureLabel where
  | cart
  | bucket
  | slopeAngle15Degrees
  deriving DecidableEq, Repr

/-- The two possible directions of the coupled one-cable motion. -/
inductive CoupledMotionDirection where
  | cartUphillBucketDownward
  | cartDownhillBucketUpward
  deriving DecidableEq, Repr

/-- Whether a rotating or rolling contact contributes friction to the model. -/
inductive FrictionModel where
  | frictionless
  | nonzero
  deriving DecidableEq, Repr

/-- Whether the cable's own weight contributes to the force balance. -/
inductive CableWeightModel where
  | negligible
  | nonnegligible
  deriving DecidableEq, Repr

/-- The standard fixed-length idealization for the connecting cable. -/
inductive CableExtensionModel where
  | inextensible
  | extensible
  deriving DecidableEq, Repr

/-- Qualitative geometry and labels transcribed from the supplied bitmap. -/
structure SuppliedQuarryFigure where
  showsObject : FigureObject → Bool
  showsLabel : FigureLabel → Bool
  cartLiesOnInclinedRails : Bool
  bucketHangsVertically : Bool
  cableRunsFromCartOverPulleyToBucket : Bool

/-!
The independent physical quantities of the coupled system.  `cartWeight`
means the combined weight `w₁` of granite block and cart; `bucketWeight` means
the combined weight `w₂` of dirt and bucket.  Positive acceleration axes are
up the incline for the cart and vertically downward for the bucket.

No equation fixing either weight in terms of the other is stored here.
-/
structure QuarryHaulSetup where
  cartWeight : WeightQuantity
  bucketWeight : WeightQuantity
  cartTotalMass : MassQuantity
  bucketTotalMass : MassQuantity
  cartEndTension : TensionQuantity
  bucketEndTension : TensionQuantity
  cartSpeedAlongSlope : SpeedQuantity
  bucketSpeedVertically : SpeedQuantity
  cartAccelerationUphill : SignedAccelerationQuantity
  bucketAccelerationDownward : SignedAccelerationQuantity
  gravitationalAcceleration : AccelerationMagnitudeQuantity
  slopeAngleRadians : ℝ
  cartPayloadMaterial : Material
  wheelMaterial : Material
  railMaterial : Material
  bucketPayloadMaterial : Material
  motionDirection : CoupledMotionDirection
  pulleyFriction : FrictionModel
  wheelRailFriction : FrictionModel
  cableWeightModel : CableWeightModel
  cableExtensionModel : CableExtensionModel
  figure : SuppliedQuarryFigure

/-!
Problem-text and primary-image readouts.  This records the `15°` incline, the
cart--pulley--bucket arrangement, the named materials, and the intended
uphill-cart/downward-bucket direction.  It assigns no numerical value to
`w₁` or `w₂`.
-/
structure MatchesProblemAndPrimaryFigure (setup : QuarryHaulSetup) : Prop where
  slopeAngleReadout : setup.slopeAngleRadians = degreesToRadians 15
  granitePayload : setup.cartPayloadMaterial = .granite
  steelWheels : setup.wheelMaterial = .steel
  steelRails : setup.railMaterial = .steel
  dirtPayload : setup.bucketPayloadMaterial = .dirt
  intendedMotion :
    setup.motionDirection = .cartUphillBucketDownward
  everyObjectShown : ∀ object, setup.figure.showsObject object = true
  everyLabelShown : ∀ label, setup.figure.showsLabel label = true
  cartOnIncline : setup.figure.cartLiesOnInclinedRails = true
  bucketVertical : setup.figure.bucketHangsVertically = true
  oneCableOverPulley :
    setup.figure.cableRunsFromCartOverPulleyToBucket = true

/-- The friction and cable idealizations explicitly stated or implied by the problem. -/
structure UsesStatedIdealizations (setup : QuarryHaulSetup) : Prop where
  pulleyIsFrictionless : setup.pulleyFriction = .frictionless
  wheelsAreFrictionless : setup.wheelRailFriction = .frictionless
  cableWeightIsNegligible : setup.cableWeightModel = .negligible
  cableIsInextensible : setup.cableExtensionModel = .inextensible

/-- Positivity and acute-angle conditions selecting the physical branch. -/
structure HasPhysicalQuarryParameters (setup : QuarryHaulSetup) : Prop where
  cartMassPositive : 0 < massInKilograms setup.cartTotalMass
  bucketMassPositive : 0 < massInKilograms setup.bucketTotalMass
  cartWeightPositive : 0 < weightInNewtons setup.cartWeight
  bucketWeightPositive : 0 < weightInNewtons setup.bucketWeight
  gravityPositive :
    0 < accelerationMagnitudeInMetersPerSecondSquared
      setup.gravitationalAcceleration
  inclineAcute :
    0 < setup.slopeAngleRadians ∧ setup.slopeAngleRadians < Real.pi / 2

/-!
The system moves in the direction described by the question at a common,
strictly positive constant speed.  In the one-dimensional Newton equations,
constant speed is recorded by zero signed acceleration of each body.
-/
structure MovesWithConstantSpeed (setup : QuarryHaulSetup) : Prop where
  direction : setup.motionDirection = .cartUphillBucketDownward
  cartActuallyMoves : 0 < speedInMetersPerSecond setup.cartSpeedAlongSlope
  commonCableSpeed :
    speedInMetersPerSecond setup.cartSpeedAlongSlope =
      speedInMetersPerSecond setup.bucketSpeedVertically
  cartAccelerationZero :
    signedAccelerationInMetersPerSecondSquared
      setup.cartAccelerationUphill = 0
  bucketAccelerationZero :
    signedAccelerationInMetersPerSecondSquared
      setup.bucketAccelerationDownward = 0

/-!
## Governing laws

The first two equations identify each named weight with `m g`.  The next two
are Newton's second law along the two positive motion axes.  Thus the cart's
downslope gravitational component is `w₁ sin θ`, while the bucket's weight is
positive downward.  The final equations are the equal-tension and equal-motion
consequences of a massless, inextensible cable over a frictionless pulley.

These are unsolved governing equations: neither the requested relation
`w₂ = w₁ sin 15°` nor any equivalent direct weight-to-weight equality is a
field of this structure.
-/
structure SatisfiesIdealQuarryHaulLaws (setup : QuarryHaulSetup) : Prop where
  cartWeightDefinition :
    weightInNewtons setup.cartWeight =
      massInKilograms setup.cartTotalMass *
        accelerationMagnitudeInMetersPerSecondSquared
          setup.gravitationalAcceleration
  bucketWeightDefinition :
    weightInNewtons setup.bucketWeight =
      massInKilograms setup.bucketTotalMass *
        accelerationMagnitudeInMetersPerSecondSquared
          setup.gravitationalAcceleration
  cartNewtonSecondLaw :
    tensionInNewtons setup.cartEndTension -
        weightInNewtons setup.cartWeight * Real.sin setup.slopeAngleRadians =
      massInKilograms setup.cartTotalMass *
        signedAccelerationInMetersPerSecondSquared
          setup.cartAccelerationUphill
  bucketNewtonSecondLaw :
    weightInNewtons setup.bucketWeight -
        tensionInNewtons setup.bucketEndTension =
      massInKilograms setup.bucketTotalMass *
        signedAccelerationInMetersPerSecondSquared
          setup.bucketAccelerationDownward
  idealPulleyEqualTensions :
    tensionInNewtons setup.cartEndTension =
      tensionInNewtons setup.bucketEndTension
  inextensibleCableAccelerationCoupling :
    signedAccelerationInMetersPerSecondSquared
        setup.cartAccelerationUphill =
      signedAccelerationInMetersPerSecondSquared
        setup.bucketAccelerationDownward

/-!
At constant speed, Newton's second law separately reduces to force balance on
the inclined cart and on the vertically moving bucket.  This is an
intermediate consequence, not a premise of the final theorem.
-/
lemma constantSpeed_end_force_balances
    (setup : QuarryHaulSetup)
    (_constantSpeed : MovesWithConstantSpeed setup)
    (_laws : SatisfiesIdealQuarryHaulLaws setup) :
    tensionInNewtons setup.cartEndTension =
        weightInNewtons setup.cartWeight * Real.sin setup.slopeAngleRadians ∧
      weightInNewtons setup.bucketWeight =
        tensionInNewtons setup.bucketEndTension := by
  constructor
  · have h := _laws.cartNewtonSecondLaw
    rw [_constantSpeed.cartAccelerationZero, mul_zero] at h
    linarith
  · have h := _laws.bucketNewtonSecondLaw
    rw [_constantSpeed.bucketAccelerationZero, mul_zero] at h
    linarith

/-!
For the frictionless, massless-cable system to move with constant speed, the
bucket-and-dirt weight must equal the component of the granite-cart weight
parallel to the `15°` slope:

`w₂ = w₁ sin 15°` (answer B).

This formalizes `thm:physics:phyx_mini_0800:target`.
-/
theorem problem_phyx_mini_0800
    (setup : QuarryHaulSetup)
    (_figure : MatchesProblemAndPrimaryFigure setup)
    (_idealizations : UsesStatedIdealizations setup)
    (_physical : HasPhysicalQuarryParameters setup)
    (_constantSpeed : MovesWithConstantSpeed setup)
    (_laws : SatisfiesIdealQuarryHaulLaws setup) :
    weightInNewtons setup.bucketWeight =
      weightInNewtons setup.cartWeight * Real.sin (degreesToRadians 15) := by
  have balances :=
    constantSpeed_end_force_balances setup _constantSpeed _laws
  calc
    weightInNewtons setup.bucketWeight =
        tensionInNewtons setup.bucketEndTension := balances.2
    _ = tensionInNewtons setup.cartEndTension :=
      _laws.idealPulleyEqualTensions.symm
    _ = weightInNewtons setup.cartWeight *
        Real.sin setup.slopeAngleRadians := balances.1
    _ = weightInNewtons setup.cartWeight *
        Real.sin (degreesToRadians 15) := by
      rw [_figure.slopeAngleReadout]

end PhyXMiniProblems.ProblemPhyXMini0800
