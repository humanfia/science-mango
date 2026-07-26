import Mathlib
import Physlib.Units.WithDim.Energy

noncomputable section

namespace PhyXMiniProblems.ProblemPhyXMini0814

open Dimension

/-!
# Spring constant needed to stop a falling elevator

A `2000 kg` elevator with broken cables is moving downward at `4.00 m/s`
when it first contacts a cushioning spring at Point 1.  It comes to rest at
Point 2 after descending `2.00 m` and compressing the spring by the same
distance.  Gravity acts downward and a safety clamp exerts a constant
`17000 N` friction force upward.

Mass, length, velocity, acceleration, force, spring stiffness, work, and
energy are represented by unit-independent Physlib quantities.  Real numbers
below occur only as coherent-SI readouts or as literal data transcribed from
the problem, image, and answer choices.

Assumption/target split:

* governing laws: `w = m g`, translational kinetic energy, linear-spring
  potential energy, work by constant gravity and clamp forces, and the
  work--energy theorem from Point 1 to Point 2;
* previous-part results: none;
* figure/data readouts: `m = 2000 kg`, `w = 19600 N`, `v₁ = -4 m/s`,
  `v₂ = 0`, Point 1 above Point 2 by `2 m`, zero initial compression,
  `2 m` final compression, and an upward `17000 N` clamp force;
* current target conclusions: the spring constant is exactly `10600 N/m`
  and therefore the displayed answer is choice B.
-/

/-! ## Dimensionful quantities and coherent-SI readouts -/

/-- Dimension of signed vertical velocity, `L T⁻¹`. -/
def verticalVelocityDimension : Dimension := L𝓭 * T𝓭⁻¹

/-- Dimension of acceleration magnitude, `L T⁻²`. -/
def accelerationDimension : Dimension := L𝓭 * T𝓭⁻¹ * T𝓭⁻¹

/-- Dimension of force magnitude, `M L T⁻²`. -/
def forceDimension : Dimension := M𝓭 * L𝓭 * T𝓭⁻¹ * T𝓭⁻¹

/-- Dimension of a linear spring constant, `M T⁻² = N/m`. -/
def springConstantDimension : Dimension := M𝓭 * T𝓭⁻¹ * T𝓭⁻¹

/-- A nonnegative, unit-independent physical mass. -/
abbrev MassQuantity : Type := Dimensionful (WithDim M𝓭 NNReal)

/-- A nonnegative physical distance or spring-compression magnitude. -/
abbrev LengthQuantity : Type := Dimensionful (WithDim L𝓭 NNReal)

/-- A signed vertical velocity, using the upward-positive convention. -/
abbrev VerticalVelocityQuantity : Type :=
  Dimensionful (WithDim verticalVelocityDimension ℝ)

/-- A nonnegative gravitational-acceleration magnitude. -/
abbrev AccelerationMagnitudeQuantity : Type :=
  Dimensionful (WithDim accelerationDimension NNReal)

/-- A nonnegative physical force magnitude. -/
abbrev ForceMagnitudeQuantity : Type :=
  Dimensionful (WithDim forceDimension NNReal)

/-- A nonnegative linear-spring force constant. -/
abbrev SpringConstantQuantity : Type :=
  Dimensionful (WithDim springConstantDimension NNReal)

/-- Coherent-SI kilogram readout of a physical mass. -/
def massInKilograms (mass : MassQuantity) : ℝ :=
  ((mass UnitChoices.SI).val : ℝ)

/-- Coherent-SI metre readout of a distance or compression. -/
def lengthInMeters (length : LengthQuantity) : ℝ :=
  ((length UnitChoices.SI).val : ℝ)

/-- Coherent-SI signed vertical-velocity readout in metres per second. -/
def verticalVelocityInMetersPerSecond
    (velocity : VerticalVelocityQuantity) : ℝ :=
  (velocity UnitChoices.SI).val

/-- Coherent-SI acceleration-magnitude readout in metres per second squared. -/
def accelerationInMetersPerSecondSquared
    (acceleration : AccelerationMagnitudeQuantity) : ℝ :=
  ((acceleration UnitChoices.SI).val : ℝ)

/-- Coherent-SI force-magnitude readout in newtons. -/
def forceInNewtons (force : ForceMagnitudeQuantity) : ℝ :=
  ((force UnitChoices.SI).val : ℝ)

/-- Coherent-SI spring-constant readout in newtons per metre. -/
def springConstantInNewtonsPerMeter
    (springConstant : SpringConstantQuantity) : ℝ :=
  ((springConstant UnitChoices.SI).val : ℝ)

/-- Coherent-SI energy or work readout in joules. -/
def energyInJoules (energy : DimEnergy) : ℝ :=
  (energy UnitChoices.SI).val

/-! ## Motion states and primary-figure vocabulary -/

/-- The two elevator states displayed in the source image. -/
inductive ElevatorInstant where
  | point1SpringContact
  | point2Stopped
  deriving DecidableEq, Fintype, Repr

/-- The two labeled levels whose vertical separation is `2.00 m`. -/
inductive FigurePoint where
  | point1
  | point2
  deriving DecidableEq, Fintype, Repr

/-- Qualitative directions used by the image's arrows and vertical geometry. -/
inductive VerticalDirection where
  | upward
  | downward
  deriving DecidableEq, Repr

/-- Condition of the elevator's supporting cables. -/
inductive CableCondition where
  | intact
  | broken
  deriving DecidableEq, Repr

/-- Idealization of the safety-clamp force during the two-metre descent. -/
inductive ClampForceModel where
  | constantOpposingDownwardMotion
  | variable
  deriving DecidableEq, Repr

/-- Constitutive model for the cushioning spring. -/
inductive SpringModel where
  | idealLinearMassless
  | nonideal
  deriving DecidableEq, Repr

/-- Qualitative spring states shown before and after compression. -/
inductive SpringConfiguration where
  | uncompressed
  | compressed
  deriving DecidableEq, Repr

/-- Physical objects visible in the supplied raster. -/
inductive FigureObject where
  | elevatorCabin
  | guideShaft
  | brokenCableEnds
  | safetyClamp
  | cushioningSpring
  deriving DecidableEq, Fintype, Repr

/-- Numerical or symbolic labels printed in the supplied raster. -/
inductive FigureLabel where
  | mass2000Kilograms
  | initialVelocity4MetersPerSecond
  | clampForce17000Newtons
  | weightEqualsMassTimesGravity
  | point1Text
  | point2Text
  | separation2Meters
  | finalVelocityZero
  deriving DecidableEq, Fintype, Repr

/-!
Literal qualitative and scalar information transcribed from image `814.png`.
The figure record contains no spring-constant value.
-/
structure ElevatorSpringFigure where
  panelShown : ElevatorInstant → Bool
  objectShown : FigureObject → Bool
  labelShown : FigureLabel → Bool
  pointShown : FigurePoint → Bool
  pointAssociatedInstant : FigurePoint → ElevatorInstant
  point1IsAbovePoint2 : Bool
  separationLabelMeters : ℝ
  initialVelocityArrowDirection : VerticalDirection
  clampForceArrowDirection : VerticalDirection
  weightArrowDirection : VerticalDirection
  springConfigurationAt : ElevatorInstant → SpringConfiguration

/-!
Independent physical quantities of the elevator's stopping process.
In particular, `springConstant` is not defined from the recorded answer or
from the desired numerical value.
-/
structure ElevatorSpringSetup where
  elevatorMass : MassQuantity
  gravitationalAccelerationMagnitude : AccelerationMagnitudeQuantity
  elevatorWeightMagnitude : ForceMagnitudeQuantity
  verticalVelocityAt : ElevatorInstant → VerticalVelocityQuantity
  descentDistancePoint1ToPoint2 : LengthQuantity
  springCompressionAt : ElevatorInstant → LengthQuantity
  safetyClampFrictionMagnitude : ForceMagnitudeQuantity
  springConstant : SpringConstantQuantity
  elevatorKineticEnergyAt : ElevatorInstant → DimEnergy
  springPotentialEnergyAt : ElevatorInstant → DimEnergy
  gravitationalWorkPoint1ToPoint2 : DimEnergy
  clampWorkPoint1ToPoint2 : DimEnergy
  cableCondition : CableCondition
  clampForceModel : ClampForceModel
  springModel : SpringModel
  elevatorGuidedInShaft : Bool
  springIntendedToStopElevator : Bool
  positiveVerticalDirection : VerticalDirection
  figure : ElevatorSpringFigure

/-! ## Source data, figure evidence, and governing laws -/

/-!
Numerical readouts stated in the prose or at the two endpoints.  No stiffness
readout or answer label occurs here.
-/
structure HasElevatorSpringProblemData
    (setup : ElevatorSpringSetup) : Prop where
  elevatorMassKilograms : massInKilograms setup.elevatorMass = 2000
  elevatorWeightNewtons : forceInNewtons setup.elevatorWeightMagnitude = 19600
  initialVelocityDownwardAtFour :
    verticalVelocityInMetersPerSecond
      (setup.verticalVelocityAt .point1SpringContact) = -4
  finalVelocityZero :
    verticalVelocityInMetersPerSecond
      (setup.verticalVelocityAt .point2Stopped) = 0
  descentDistanceMeters :
    lengthInMeters setup.descentDistancePoint1ToPoint2 = 2
  springInitiallyUncompressed :
    lengthInMeters (setup.springCompressionAt .point1SpringContact) = 0
  springFinalCompressionMeters :
    lengthInMeters (setup.springCompressionAt .point2Stopped) = 2
  clampFrictionNewtons :
    forceInNewtons setup.safetyClampFrictionMagnitude = 17000

/-- Qualitative scenario assumptions stated in the prose. -/
structure MatchesElevatorSpringScenario
    (setup : ElevatorSpringSetup) : Prop where
  cablesAreBroken : setup.cableCondition = .broken
  clampForceIsConstantAndOpposesMotion :
    setup.clampForceModel = .constantOpposingDownwardMotion
  springIsIdealAndLinear : setup.springModel = .idealLinearMassless
  elevatorRemainsGuided : setup.elevatorGuidedInShaft = true
  springIsStoppingDevice : setup.springIntendedToStopElevator = true
  upwardIsPositive : setup.positiveVerticalDirection = .upward

/-!
Primary-image evidence.  This records the Point 1/Point 2 geometry, the arrow
directions, and the printed labels without imposing a stiffness value.
-/
structure MatchesSuppliedElevatorSpringFigure
    (setup : ElevatorSpringSetup) : Prop where
  bothPanelsShown : ∀ instant, setup.figure.panelShown instant = true
  everyObjectShown : ∀ object, setup.figure.objectShown object = true
  everyPrintedLabelShown : ∀ label, setup.figure.labelShown label = true
  bothPointsShown : ∀ point, setup.figure.pointShown point = true
  point1MarksInitialState :
    setup.figure.pointAssociatedInstant .point1 = .point1SpringContact
  point2MarksStoppedState :
    setup.figure.pointAssociatedInstant .point2 = .point2Stopped
  point1AbovePoint2 : setup.figure.point1IsAbovePoint2 = true
  printedSeparation : setup.figure.separationLabelMeters = 2
  printedSeparationMatchesPhysicalDistance :
    setup.figure.separationLabelMeters =
      lengthInMeters setup.descentDistancePoint1ToPoint2
  initialVelocityArrowPointsDown :
    setup.figure.initialVelocityArrowDirection = .downward
  clampForceArrowPointsUp :
    setup.figure.clampForceArrowDirection = .upward
  weightArrowPointsDown : setup.figure.weightArrowDirection = .downward
  springUncompressedAtPoint1 :
    setup.figure.springConfigurationAt .point1SpringContact = .uncompressed
  springCompressedAtPoint2 :
    setup.figure.springConfigurationAt .point2Stopped = .compressed

/-- Positivity conditions for the physical magnitudes in the model. -/
structure HasPhysicalElevatorSpringParameters
    (setup : ElevatorSpringSetup) : Prop where
  massPositive : 0 < massInKilograms setup.elevatorMass
  gravityPositive :
    0 < accelerationInMetersPerSecondSquared
      setup.gravitationalAccelerationMagnitude
  weightPositive : 0 < forceInNewtons setup.elevatorWeightMagnitude
  descentDistancePositive :
    0 < lengthInMeters setup.descentDistancePoint1ToPoint2
  clampForcePositive :
    0 < forceInNewtons setup.safetyClampFrictionMagnitude
  springConstantPositive :
    0 < springConstantInNewtonsPerMeter setup.springConstant

/-- The weight magnitude obeys `w = m g`. -/
structure SatisfiesElevatorWeightLaw
    (setup : ElevatorSpringSetup) : Prop where
  weightEqualsMassTimesGravity :
    forceInNewtons setup.elevatorWeightMagnitude =
      massInKilograms setup.elevatorMass *
        accelerationInMetersPerSecondSquared
          setup.gravitationalAccelerationMagnitude

/-- Translational kinetic energy obeys `K = (1/2) m v²` at both endpoints. -/
structure SatisfiesElevatorKineticEnergyLaw
    (setup : ElevatorSpringSetup) : Prop where
  kineticEnergyFormula : ∀ instant,
    energyInJoules (setup.elevatorKineticEnergyAt instant) =
      (1 / 2 : ℝ) * massInKilograms setup.elevatorMass *
        verticalVelocityInMetersPerSecond
          (setup.verticalVelocityAt instant) ^ 2

/-- Linear-spring potential energy obeys `Uₛ = (1/2) k x²`. -/
structure SatisfiesLinearSpringPotentialEnergyLaw
    (setup : ElevatorSpringSetup) : Prop where
  springPotentialEnergyFormula : ∀ instant,
    energyInJoules (setup.springPotentialEnergyAt instant) =
      (1 / 2 : ℝ) *
        springConstantInNewtonsPerMeter setup.springConstant *
          lengthInMeters (setup.springCompressionAt instant) ^ 2

/-!
For the downward Point 1-to-Point 2 displacement, gravity does positive work
and the upward constant clamp force does negative work.
-/
structure SatisfiesConstantForceWorkLaws
    (setup : ElevatorSpringSetup) : Prop where
  gravitationalWorkFormula :
    energyInJoules setup.gravitationalWorkPoint1ToPoint2 =
      forceInNewtons setup.elevatorWeightMagnitude *
        lengthInMeters setup.descentDistancePoint1ToPoint2
  clampWorkFormula :
    energyInJoules setup.clampWorkPoint1ToPoint2 =
      -(forceInNewtons setup.safetyClampFrictionMagnitude *
        lengthInMeters setup.descentDistancePoint1ToPoint2)

/-!
Work--energy balance for the elevator-plus-spring system between Point 1 and
Point 2.  The spring energy is retained explicitly on both sides so the law
does not prescribe the unknown stiffness.
-/
structure SatisfiesElevatorSpringWorkEnergyTheorem
    (setup : ElevatorSpringSetup) : Prop where
  energyBalance :
    energyInJoules
          (setup.elevatorKineticEnergyAt .point2Stopped) +
        energyInJoules
          (setup.springPotentialEnergyAt .point2Stopped) =
      energyInJoules
          (setup.elevatorKineticEnergyAt .point1SpringContact) +
        energyInJoules
          (setup.springPotentialEnergyAt .point1SpringContact) +
        energyInJoules setup.gravitationalWorkPoint1ToPoint2 +
        energyInJoules setup.clampWorkPoint1ToPoint2

/-! ## Derived stiffness and displayed answer -/

/-- Labels attached to the four displayed spring-constant choices. -/
inductive SpringConstantAnswerChoice where
  | A
  | B
  | C
  | D
  deriving DecidableEq, Fintype, Repr

/-- Newton-per-metre value printed beside each answer label. -/
def SpringConstantAnswerChoice.valueInNewtonsPerMeter :
    SpringConstantAnswerChoice → ℝ
  | .A => 13600
  | .B => 10600
  | .C => 106000
  | .D => 136000

/-- The answer label recorded in the supplied dataset metadata. -/
def recordedDatasetAnswer : SpringConstantAnswerChoice := .B

/-- A displayed choice reports the physical spring constant exactly. -/
def AnswerChoiceReportsSpringConstant
    (setup : ElevatorSpringSetup)
    (choice : SpringConstantAnswerChoice) : Prop :=
  springConstantInNewtonsPerMeter setup.springConstant =
    choice.valueInNewtonsPerMeter

/-!
The endpoint data and work--energy laws determine

`(1/2) k (2 m)² = (1/2)(2000 kg)(4 m/s)²
                    + (19600 N)(2 m) - (17000 N)(2 m)`,

so the necessary spring constant is `10600 N/m`.
-/
lemma necessarySpringConstant_exact
    (setup : ElevatorSpringSetup)
    (hData : HasElevatorSpringProblemData setup)
    (hKinetic : SatisfiesElevatorKineticEnergyLaw setup)
    (hSpring : SatisfiesLinearSpringPotentialEnergyLaw setup)
    (hWork : SatisfiesConstantForceWorkLaws setup)
    (hEnergy : SatisfiesElevatorSpringWorkEnergyTheorem setup) :
    springConstantInNewtonsPerMeter setup.springConstant = 10600 := by
  have hKineticInitial :=
    hKinetic.kineticEnergyFormula ElevatorInstant.point1SpringContact
  have hKineticFinal :=
    hKinetic.kineticEnergyFormula ElevatorInstant.point2Stopped
  have hSpringInitial :=
    hSpring.springPotentialEnergyFormula ElevatorInstant.point1SpringContact
  have hSpringFinal :=
    hSpring.springPotentialEnergyFormula ElevatorInstant.point2Stopped
  have hBalance := hEnergy.energyBalance
  rw [hKineticFinal, hSpringFinal, hKineticInitial, hSpringInitial,
    hWork.gravitationalWorkFormula, hWork.clampWorkFormula] at hBalance
  norm_num [hData.elevatorMassKilograms,
    hData.initialVelocityDownwardAtFour, hData.finalVelocityZero,
    hData.descentDistanceMeters, hData.springInitiallyUncompressed,
    hData.springFinalCompressionMeters, hData.elevatorWeightNewtons,
    hData.clampFrictionNewtons] at hBalance
  linarith

/-!
The necessary stiffness is `1.06 × 10⁴ N/m`, which is displayed as choice B.

This formalizes blueprint label `thm:physics:phyx_mini_0814:target`.
-/
theorem problem_phyx_mini_0814
    (setup : ElevatorSpringSetup)
    (hData : HasElevatorSpringProblemData setup)
    (hScenario : MatchesElevatorSpringScenario setup)
    (hFigure : MatchesSuppliedElevatorSpringFigure setup)
    (hPhysical : HasPhysicalElevatorSpringParameters setup)
    (hWeight : SatisfiesElevatorWeightLaw setup)
    (hKinetic : SatisfiesElevatorKineticEnergyLaw setup)
    (hSpring : SatisfiesLinearSpringPotentialEnergyLaw setup)
    (hWork : SatisfiesConstantForceWorkLaws setup)
    (hEnergy : SatisfiesElevatorSpringWorkEnergyTheorem setup) :
    springConstantInNewtonsPerMeter setup.springConstant = 10600 ∧
      AnswerChoiceReportsSpringConstant setup recordedDatasetAnswer := by
  have hConstant :=
    necessarySpringConstant_exact setup hData hKinetic hSpring hWork hEnergy
  constructor
  · exact hConstant
  · simpa [AnswerChoiceReportsSpringConstant, recordedDatasetAnswer,
      SpringConstantAnswerChoice.valueInNewtonsPerMeter] using hConstant

end PhyXMiniProblems.ProblemPhyXMini0814
