import Mathlib
import Physlib.Units.WithDim.Basic

/- USER: The assigned source file did not exist when this autoformalization task began. -/

noncomputable section

namespace PhyXMiniProblems.ProblemPhyXMini0798

open Dimension

/-!
# Friction force stopping a sliding ketchup bottle

A `0.45 kg` ketchup bottle leaves the waitress's hand at the figure point
`O`, moving right at `2.0 m/s`.  It slides along a level counter to the point
`X`, one metre to the right, where it is at rest.  A constant horizontal
friction force exerted by the counter is the only force doing work along the
motion.

Physical mass, position, length, velocity, force, energy, and work are
represented by unit-independent Physlib quantities.  Real numbers occur only
as coherent-SI readouts, qualitative figure inscriptions, and displayed
answer values.  In particular, the friction magnitude is an independent
field of the setup and is not defined to be the recorded answer.

Assumption/target split:

* governing laws: distance is the endpoint-position difference, friction is
  constant and leftward throughout the slide, translational kinetic energy is
  `m v² / 2`, constant-friction work is `-f d`, and work equals the change in
  kinetic energy;
* previous-part results: none;
* figure/data readouts: points `O` and `X`, a horizontal line with `O` left of
  `X`, mass `0.45 kg`, rightward initial velocity `2.0 m/s`, final velocity
  zero, and endpoint separation `1.0 m`;
* target conclusion: the friction-force magnitude is `0.90 N`, corresponding
  to answer choice B.
-/

/-! ## Dimensionful physical quantities and coherent-SI readouts -/

/-- Physical force dimension, `M L T⁻²`. -/
def forceDimension : Dimension :=
  M𝓭 * L𝓭 * T𝓭⁻¹ * T𝓭⁻¹

/-- Physical energy/work dimension, `M L² T⁻²`. -/
def energyDimension : Dimension :=
  M𝓭 * L𝓭 * L𝓭 * T𝓭⁻¹ * T𝓭⁻¹

/-- A nonnegative physical mass. -/
abbrev MassQuantity : Type :=
  Dimensionful (WithDim M𝓭 NNReal)

/-- A signed horizontal position. -/
abbrev HorizontalPositionQuantity : Type :=
  Dimensionful (WithDim L𝓭 ℝ)

/-- A nonnegative travel distance. -/
abbrev LengthMagnitudeQuantity : Type :=
  Dimensionful (WithDim L𝓭 NNReal)

/-- A signed horizontal velocity, positive to the right. -/
abbrev HorizontalVelocityQuantity : Type :=
  Dimensionful (WithDim (L𝓭 * T𝓭⁻¹) ℝ)

/-- A nonnegative force magnitude. -/
abbrev ForceMagnitudeQuantity : Type :=
  Dimensionful (WithDim forceDimension NNReal)

/-- A signed horizontal force, positive to the right. -/
abbrev HorizontalForceQuantity : Type :=
  Dimensionful (WithDim forceDimension ℝ)

/-- A nonnegative kinetic-energy quantity. -/
abbrev EnergyMagnitudeQuantity : Type :=
  Dimensionful (WithDim energyDimension NNReal)

/-- Signed work; opposing friction does negative work. -/
abbrev SignedWorkQuantity : Type :=
  Dimensionful (WithDim energyDimension ℝ)

/-- Read a nonnegative dimensionful quantity in coherent SI units. -/
def nonnegativeSIReadout {dimension : Dimension}
    (quantity : Dimensionful (WithDim dimension NNReal)) : ℝ :=
  ((quantity UnitChoices.SI).val : ℝ)

/-- Read a signed dimensionful quantity in coherent SI units. -/
def signedSIReadout {dimension : Dimension}
    (quantity : Dimensionful (WithDim dimension ℝ)) : ℝ :=
  (quantity UnitChoices.SI).val

/-- Kilogram readout of a mass. -/
def massInKilograms (mass : MassQuantity) : ℝ :=
  nonnegativeSIReadout mass

/-- Metre readout of a signed horizontal position. -/
def positionInMeters (position : HorizontalPositionQuantity) : ℝ :=
  signedSIReadout position

/-- Metre readout of a nonnegative length. -/
def lengthInMeters (length : LengthMagnitudeQuantity) : ℝ :=
  nonnegativeSIReadout length

/-- Signed metre-per-second readout of a horizontal velocity. -/
def velocityInMetersPerSecond
    (velocity : HorizontalVelocityQuantity) : ℝ :=
  signedSIReadout velocity

/-- Newton readout of a force magnitude. -/
def forceMagnitudeInNewtons (force : ForceMagnitudeQuantity) : ℝ :=
  nonnegativeSIReadout force

/-- Signed newton readout of a horizontal force. -/
def horizontalForceInNewtons (force : HorizontalForceQuantity) : ℝ :=
  signedSIReadout force

/-- Joule readout of a nonnegative energy. -/
def energyInJoules (energy : EnergyMagnitudeQuantity) : ℝ :=
  nonnegativeSIReadout energy

/-- Signed joule readout of work. -/
def workInJoules (work : SignedWorkQuantity) : ℝ :=
  signedSIReadout work

/-! ## Scenario roles and primary-figure vocabulary -/

/-- The two bottle positions explicitly labelled in the supplied image. -/
inductive FigurePoint where
  | O
  | X
  deriving DecidableEq, Fintype, Repr

/-- Horizontal directions distinguished by the problem. -/
inductive HorizontalDirection where
  | left
  | right
  deriving DecidableEq, Repr

/-- Geometry of the supporting counter. -/
inductive CounterGeometry where
  | smoothLevelHorizontal
  | other
  deriving DecidableEq, Repr

/-- The idealized contact force during the slide. -/
inductive ContactForceModel where
  | constantHorizontalFrictionOpposingMotion
  | other
  deriving DecidableEq, Repr

/-- Literal diagram information transcribed from the primary image. -/
structure BottleSlideFigure where
  showsBottleAt : FigurePoint → Bool
  showsPointLabel : FigurePoint → Bool
  horizontalBaselineShown : Bool
  pointOrderLeftToRight : FigurePoint × FigurePoint
  initialVelocityArrowDirection : HorizontalDirection
  printedMassKilograms : ℝ
  printedInitialVelocityMetersPerSecond : ℝ
  printedFinalVelocityMetersPerSecond : ℝ
  printedDistanceOXMeters : ℝ

/-!
The physical bottle and its independent dynamical observables.  The force,
kinetic-energy, and work fields are connected only by the governing laws
below; no field is assigned the requested numerical answer.
-/
structure BottleSlideSetup where
  bottleMass : MassQuantity
  positionAt : FigurePoint → HorizontalPositionQuantity
  horizontalVelocityAt : FigurePoint → HorizontalVelocityQuantity
  travelDistanceOX : LengthMagnitudeQuantity
  frictionForceMagnitude : ForceMagnitudeQuantity
  horizontalFrictionForceAt :
    HorizontalPositionQuantity → HorizontalForceQuantity
  kineticEnergyAt : FigurePoint → EnergyMagnitudeQuantity
  frictionWorkOX : SignedWorkQuantity
  initialMotionDirection : HorizontalDirection
  counterGeometry : CounterGeometry
  contactForceModel : ContactForceModel
  handHasReleasedAtO : Bool
  figure : BottleSlideFigure

/-! ## Scenario assumptions and figure/data readouts -/

/-- Qualitative physical idealizations stated in the problem prose. -/
structure MatchesBottleSlideScenario (setup : BottleSlideSetup) : Prop where
  initiallyMovesRight : setup.initialMotionDirection = .right
  counterIsLevelAndHorizontal :
    setup.counterGeometry = .smoothLevelHorizontal
  contactForceIsConstantOpposingFriction :
    setup.contactForceModel = .constantHorizontalFrictionOpposingMotion
  bottleHasLeftTheWaitressHand : setup.handHasReleasedAtO = true

/-!
Objects, labels, geometry, and numerical inscriptions visible in image 798.
The physical-quantity equalities connect those inscriptions to the setup but
contain no assertion about the friction magnitude.
-/
structure MatchesPrimaryFigure (setup : BottleSlideSetup) : Prop where
  bothBottleStatesShown :
    ∀ point : FigurePoint, setup.figure.showsBottleAt point = true
  bothEndpointLabelsShown :
    ∀ point : FigurePoint, setup.figure.showsPointLabel point = true
  horizontalLineShown : setup.figure.horizontalBaselineShown = true
  OIsLeftOfX : setup.figure.pointOrderLeftToRight = (.O, .X)
  initialVelocityArrowPointsRight :
    setup.figure.initialVelocityArrowDirection = .right
  printedMass : setup.figure.printedMassKilograms = 0.45
  printedInitialVelocity :
    setup.figure.printedInitialVelocityMetersPerSecond = 2.0
  printedFinalVelocity :
    setup.figure.printedFinalVelocityMetersPerSecond = 0
  printedTravelDistance : setup.figure.printedDistanceOXMeters = 1.0
  massMatchesPrintedLabel :
    massInKilograms setup.bottleMass = setup.figure.printedMassKilograms
  initialVelocityMatchesPrintedLabel :
    velocityInMetersPerSecond (setup.horizontalVelocityAt .O) =
      setup.figure.printedInitialVelocityMetersPerSecond
  finalVelocityMatchesPrintedLabel :
    velocityInMetersPerSecond (setup.horizontalVelocityAt .X) =
      setup.figure.printedFinalVelocityMetersPerSecond
  travelDistanceMatchesPrintedLabel :
    lengthInMeters setup.travelDistanceOX =
      setup.figure.printedDistanceOXMeters

/-- Positivity and endpoint ordering selecting the physical branch. -/
structure HasPhysicalBottleSlideParameters
    (setup : BottleSlideSetup) : Prop where
  bottleMassPositive : 0 < massInKilograms setup.bottleMass
  travelDistancePositive : 0 < lengthInMeters setup.travelDistanceOX
  initialVelocityRightward :
    0 < velocityInMetersPerSecond (setup.horizontalVelocityAt .O)
  endpointOrder :
    positionInMeters (setup.positionAt .O) <
      positionInMeters (setup.positionAt .X)

/-! ## Governing constant-friction and work--energy laws -/

/-!
The scalar laws use rightward as positive.  The signed friction field is
therefore the negative of its nonnegative magnitude at every position between
`O` and `X`.  The remaining fields state the endpoint distance, translational
kinetic energy, work of a constant opposing force, and the work--energy
theorem.  None states a numerical value for the friction force.
-/
structure SatisfiesConstantFrictionWorkEnergyLaws
    (setup : BottleSlideSetup) : Prop where
  endpointDistance :
    lengthInMeters setup.travelDistanceOX =
      positionInMeters (setup.positionAt .X) -
        positionInMeters (setup.positionAt .O)
  constantLeftwardFriction :
    ∀ position : HorizontalPositionQuantity,
      positionInMeters (setup.positionAt .O) ≤ positionInMeters position →
      positionInMeters position ≤ positionInMeters (setup.positionAt .X) →
      horizontalForceInNewtons (setup.horizontalFrictionForceAt position) =
        -forceMagnitudeInNewtons setup.frictionForceMagnitude
  translationalKineticEnergy :
    ∀ point : FigurePoint,
      energyInJoules (setup.kineticEnergyAt point) =
        (1 / 2 : ℝ) * massInKilograms setup.bottleMass *
          velocityInMetersPerSecond (setup.horizontalVelocityAt point) ^ 2
  constantFrictionWork :
    workInJoules setup.frictionWorkOX =
      -forceMagnitudeInNewtons setup.frictionForceMagnitude *
        lengthInMeters setup.travelDistanceOX
  workEnergyTheorem :
    energyInJoules (setup.kineticEnergyAt .X) -
        energyInJoules (setup.kineticEnergyAt .O) =
      workInJoules setup.frictionWorkOX

/-!
Eliminating the endpoint kinetic energies and friction work yields the usual
constant-friction stopping formula.  It is a derived conclusion, not a field
or premise of the physical model.
-/
lemma frictionForceMagnitude_formula
    (setup : BottleSlideSetup)
    (_physical : HasPhysicalBottleSlideParameters setup)
    (_laws : SatisfiesConstantFrictionWorkEnergyLaws setup) :
    forceMagnitudeInNewtons setup.frictionForceMagnitude =
      massInKilograms setup.bottleMass *
          (velocityInMetersPerSecond (setup.horizontalVelocityAt .O) ^ 2 -
            velocityInMetersPerSecond (setup.horizontalVelocityAt .X) ^ 2) /
        (2 * lengthInMeters setup.travelDistanceOX) := by
  have hd : lengthInMeters setup.travelDistanceOX ≠ 0 :=
    ne_of_gt _physical.travelDistancePositive
  field_simp
  nlinarith [_laws.translationalKineticEnergy .O,
    _laws.translationalKineticEnergy .X,
    _laws.constantFrictionWork,
    _laws.workEnergyTheorem]

/-! ## Displayed choices and formalization target -/

/-- Labels of the four displayed multiple-choice answers. -/
inductive AnswerChoice where
  | A
  | B
  | C
  | D
  deriving DecidableEq, Fintype, Repr

/-- Force magnitude printed beside each answer choice, in newtons. -/
def AnswerChoice.forceMagnitudeNewtons : AnswerChoice → ℝ
  | .A => 0.45
  | .B => 0.90
  | .C => 1.35
  | .D => 1.80

/-- The answer label recorded in the supplied dataset metadata. -/
def recordedAnswerChoice : AnswerChoice := .B

/-- A physical friction magnitude agrees with a displayed answer choice. -/
def MatchesAnswerChoice
    (force : ForceMagnitudeQuantity) (choice : AnswerChoice) : Prop :=
  forceMagnitudeInNewtons force = choice.forceMagnitudeNewtons

/-!
The constant-friction work--energy model and the printed figure data imply a
friction-force magnitude of exactly `0.90 N`, the recorded answer B.

This formalizes `thm:physics:phyx_mini_0798:target`.
-/
theorem frictionForceMagnitude_is_0_90_newtons
    (setup : BottleSlideSetup)
    (_scenario : MatchesBottleSlideScenario setup)
    (_figure : MatchesPrimaryFigure setup)
    (_physical : HasPhysicalBottleSlideParameters setup)
    (_laws : SatisfiesConstantFrictionWorkEnergyLaws setup) :
    forceMagnitudeInNewtons setup.frictionForceMagnitude = 0.90 ∧
      MatchesAnswerChoice setup.frictionForceMagnitude recordedAnswerChoice := by
  have hm : massInKilograms setup.bottleMass = 0.45 :=
    _figure.massMatchesPrintedLabel.trans _figure.printedMass
  have hvO :
      velocityInMetersPerSecond (setup.horizontalVelocityAt .O) = 2.0 :=
    _figure.initialVelocityMatchesPrintedLabel.trans
      _figure.printedInitialVelocity
  have hvX :
      velocityInMetersPerSecond (setup.horizontalVelocityAt .X) = 0 :=
    _figure.finalVelocityMatchesPrintedLabel.trans _figure.printedFinalVelocity
  have hd : lengthInMeters setup.travelDistanceOX = 1.0 :=
    _figure.travelDistanceMatchesPrintedLabel.trans
      _figure.printedTravelDistance
  have hforce := frictionForceMagnitude_formula setup _physical _laws
  rw [hm, hvO, hvX, hd] at hforce
  norm_num at hforce
  constructor <;>
    norm_num [MatchesAnswerChoice, recordedAnswerChoice,
      AnswerChoice.forceMagnitudeNewtons] at hforce ⊢ <;>
    exact hforce

end PhyXMiniProblems.ProblemPhyXMini0798
