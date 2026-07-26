import Mathlib
import Physlib.Units.WithDim.Basic
import Physlib.Units.WithDim.Energy
import Physlib.Units.WithDim.Speed

/- USER: The assigned source file did not exist when this autoformalization task began. -/

noncomputable section

namespace PhyXMiniProblems.ProblemPhyXMini0790

open Dimension

/-!
# Bird striking a uniform hinged bar

A `500.0 g` bird flies horizontally at `2.25 m/s` into a stationary,
vertical, uniform bar.  The bar has length `0.750 m`, mass `1.50 kg`, and a
fixed hinge at its base.  The impact point is `25.0 cm` below the top, hence
`0.500 m` above the hinge.  The collision starts the bar rotating, after
which the bar falls from vertical to horizontal.

The source does not specify the bird's velocity or attachment state after the
impact, so its data alone do not determine a numerical answer.  In the
separated branch, the final angular speed remains a function of the bird's
unspecified outgoing tangential velocity.  In the attached branch, the bird
shares the bar's angular speed and contributes both inertia and gravitational
potential energy during the fall.  Angular momentum about the hinge is
conserved during the impact, whereas mechanical energy is conserved only
during the subsequent frictionless fall.  Gravity is deliberately left as a
dimensionful parameter rather than calibrated to an unstated numerical value.

Mass, length, speed, acceleration, angular-speed magnitude, moment of
inertia, angular momentum, and energy are represented by unit-independent
Physlib quantities.  Real numbers occur only as coherent-SI readouts,
schematic figure data, and displayed numerical values.

Assumption/target split:

* governing laws: uniform-bar center of mass and hinged moment of inertia,
  impact geometry, angular-momentum factorization and conservation about the
  hinge during the short impact, rotational kinetic energy, gravitational
  potential-energy loss, and mechanical-energy conservation during the fall;
* previous-part results: none;
* figure/data readouts: the bird, rightward arrow, dashed horizontal impact
  line, vertical `25.0 cm` marker, vertical bar, and base hinge; bird mass and
  incoming speed; bar mass and length; and initially stationary bar;
* governing branch information: an attached bird shares the bar's tangential
  speed and remains part of the falling system; a separated bird has a free
  signed outgoing tangential component and no longer contributes to the bar's
  fall energy;
* target conclusions: the two source-supported symbolic squared-speed laws,
  one for each post-impact disposition.  The recorded answer choice B is
  retained only as dataset metadata, not asserted to follow from the source.
-/

/-! ## Dimensionful physical quantities and SI readouts -/

/-- Acceleration has dimension length divided by time squared. -/
def accelerationDimension : Dimension :=
  L𝓭 * T𝓭⁻¹ * T𝓭⁻¹

/-- A scalar moment of inertia has dimension mass times length squared. -/
def momentOfInertiaDimension : Dimension :=
  M𝓭 * L𝓭 * L𝓭

/-- Angular momentum has dimension mass times length squared per time. -/
def angularMomentumDimension : Dimension :=
  momentOfInertiaDimension * T𝓭⁻¹

/-- A nonnegative, unit-independent physical mass. -/
abbrev MassQuantity : Type :=
  Dimensionful (WithDim M𝓭 NNReal)

/-- A nonnegative, unit-independent physical length. -/
abbrev LengthQuantity : Type :=
  Dimensionful (WithDim L𝓭 NNReal)

/-- A nonnegative, unit-independent speed magnitude. -/
abbrev SpeedQuantity : Type :=
  DimSpeed

/-!
A signed tangential velocity component.  Unlike `DimSpeed`, this carrier uses
`ℝ`, allowing a separated bird's post-impact component to record continued
forward motion, rest, or rebound without collapsing velocity to a bare scalar.
-/
abbrev TangentialVelocityComponentQuantity : Type :=
  Dimensionful (WithDim (L𝓭 * T𝓭⁻¹) ℝ)

/-- A nonnegative, unit-independent acceleration magnitude. -/
abbrev AccelerationQuantity : Type :=
  Dimensionful (WithDim accelerationDimension NNReal)

/-!
The magnitude of an axial angular velocity.  Radians are dimensionless, so
its physical dimension is inverse time.  The answer choices ask only for
this magnitude, not for a signed rotation convention.
-/
abbrev AngularSpeedQuantity : Type :=
  Dimensionful (WithDim T𝓭⁻¹ NNReal)

/-- A nonnegative moment of inertia about the base hinge. -/
abbrev MomentOfInertiaQuantity : Type :=
  Dimensionful (WithDim momentOfInertiaDimension NNReal)

/-!
A signed angular-momentum component about the hinge.  Positive orientation is
chosen to be the rotation induced by the incoming bird.
-/
abbrev AngularMomentumQuantity : Type :=
  Dimensionful (WithDim angularMomentumDimension ℝ)

/-- Mechanical energy, using Physlib's unit-independent energy quantity. -/
abbrev EnergyQuantity : Type :=
  DimEnergy

/-- Coherent-SI readout of a nonnegative dimensionful quantity. -/
def nonnegativeSIReadout {dimension : Dimension}
    (quantity : Dimensionful (WithDim dimension NNReal)) : ℝ :=
  ((quantity UnitChoices.SI).val : ℝ)

/-- Coherent-SI readout of a signed dimensionful quantity. -/
def signedSIReadout {dimension : Dimension}
    (quantity : Dimensionful (WithDim dimension ℝ)) : ℝ :=
  (quantity UnitChoices.SI).val

/-- Kilogram readout of a physical mass. -/
def massInKilograms (mass : MassQuantity) : ℝ :=
  nonnegativeSIReadout mass

/-- Metre readout of a physical length. -/
def lengthInMeters (length : LengthQuantity) : ℝ :=
  nonnegativeSIReadout length

/-- Metre-per-second readout of a speed magnitude. -/
def speedInMetersPerSecond (speed : SpeedQuantity) : ℝ :=
  nonnegativeSIReadout speed

/-- Signed metre-per-second readout of a tangential velocity component. -/
def tangentialVelocityComponentInMetersPerSecond
    (velocity : TangentialVelocityComponentQuantity) : ℝ :=
  signedSIReadout velocity

/-- Metre-per-second-squared readout of an acceleration magnitude. -/
def accelerationInMetersPerSecondSquared
    (acceleration : AccelerationQuantity) : ℝ :=
  nonnegativeSIReadout acceleration

/-- Radian-per-second readout of an angular-speed magnitude. -/
def angularSpeedInRadiansPerSecond
    (angularSpeed : AngularSpeedQuantity) : ℝ :=
  nonnegativeSIReadout angularSpeed

/-- Kilogram-metre-squared readout of a moment of inertia. -/
def momentOfInertiaInKilogramMetersSquared
    (momentOfInertia : MomentOfInertiaQuantity) : ℝ :=
  nonnegativeSIReadout momentOfInertia

/-- Kilogram-metre-squared-per-second readout of angular momentum. -/
def angularMomentumInKilogramMetersSquaredPerSecond
    (angularMomentum : AngularMomentumQuantity) : ℝ :=
  signedSIReadout angularMomentum

/-- Joule readout of a mechanical energy. -/
def energyInJoules (energy : EnergyQuantity) : ℝ :=
  signedSIReadout energy

/-! ## Physical stages and primary-image vocabulary -/

/-- Stages on the two sides of the short bird-bar collision. -/
inductive ImpactStage where
  | immediatelyBefore
  | immediatelyAfter
  deriving DecidableEq, Fintype, Repr

/-!
Whether the bird separates from the bar after impact or remains attached.
The supplied problem and figure do not select either constructor.
-/
inductive BirdPostImpactDisposition where
  | separated
  | attachedToBar
  deriving DecidableEq, Repr

/-- Bar states needed for the impact and the subsequent fall. -/
inductive BarStage where
  | beforeImpact
  | immediatelyAfterImpact
  | justReachesGround
  deriving DecidableEq, Fintype, Repr

/-- The orientations of the bar relevant to the problem. -/
inductive BarOrientation where
  | vertical
  | horizontal
  deriving DecidableEq, Repr

/-- Horizontal direction of the bird's arrow in the supplied figure. -/
inductive HorizontalDirection where
  | rightward
  | leftward
  deriving DecidableEq, Repr

/-- Physical and graphical objects visible in image `790.png`. -/
inductive BirdBarFigureObject where
  | bird
  | birdMotionArrow
  | dashedImpactGuide
  | verticalDistanceMarker
  | bar
  | baseHinge
  | horizontalGround
  deriving DecidableEq, Fintype, Repr

/-- Text labels printed in the primary image. -/
inductive BirdBarFigureLabel where
  | bird
  | twentyFivePointZeroCentimeters
  | hinge
  deriving DecidableEq, Fintype, Repr

/-!
Literal qualitative evidence from the supplied raster.  The numeric field is
the printed `25.0 cm` label, not a distance inferred from drawing pixels.
-/
structure BirdBarFigure where
  showsObject : BirdBarFigureObject → Bool
  showsLabel : BirdBarFigureLabel → Bool
  birdArrowDirection : HorizontalDirection
  birdFlightGuideIsHorizontal : Bool
  impactGuideIsDashed : Bool
  impactGuideMeetsBar : Bool
  distanceMarkerIsVertical : Bool
  distanceMarkerRunsFromBarTopToImpactGuide : Bool
  barIsDrawnVertical : Bool
  barBaseCoincidesWithHinge : Bool
  hingeLiesOnGroundLine : Bool
  topToImpactLabelCentimeters : ℝ

/-!
Independent physical quantities for the collision and the falling bar.  In
particular, the final angular speed is an observable field: it is not defined
from the answer choice or from the desired formula.
-/
structure HingedBarImpactSetup where
  figure : BirdBarFigure
  birdMass : MassQuantity
  barMass : MassQuantity
  birdIncomingSpeedMagnitude : SpeedQuantity
  birdTangentialVelocityComponentImmediatelyAfterImpact :
    TangentialVelocityComponentQuantity
  birdPostImpactDisposition : BirdPostImpactDisposition
  barLength : LengthQuantity
  topToImpactDistance : LengthQuantity
  hingeToImpactDistance : LengthQuantity
  barCenterOfMassDistanceFromHinge : LengthQuantity
  barCenterOfMassVerticalDrop : LengthQuantity
  gravitationalAccelerationMagnitude : AccelerationQuantity
  barAngularSpeed : BarStage → AngularSpeedQuantity
  barMomentOfInertiaAboutHinge : MomentOfInertiaQuantity
  hingeImpulseMomentAboutHinge : AngularMomentumQuantity
  gravitationalAngularImpulseDuringImpact : AngularMomentumQuantity
  totalAngularMomentumAboutHinge : ImpactStage → AngularMomentumQuantity
  barRotationalKineticEnergy : BarStage → EnergyQuantity
  barGravitationalPotentialEnergy : BarStage → EnergyQuantity
  birdRotationalKineticEnergy : BarStage → EnergyQuantity
  birdGravitationalPotentialEnergy : BarStage → EnergyQuantity
  barOrientation : BarStage → BarOrientation
  barIsUniform : Bool
  hingeIsFixedAtBarBase : Bool
  impactDurationIsNegligible : Bool
  hingeFrictionDuringFallIsNegligible : Bool
  positiveRotationIsInducedByIncomingBird : Bool

/-! ## Figure evidence, problem data, and physical idealizations -/

/-!
Facts read directly from the primary image: a rightward bird arrow and dashed
horizontal guide meet a vertical bar, the vertical marker from the bar's top
to that guide reads `25.0 cm`, and the bar is hinged to the ground at its base.
-/
structure MatchesPrimaryBirdBarFigure
    (setup : HingedBarImpactSetup) : Prop where
  everyFigureObjectShown :
    ∀ object, setup.figure.showsObject object = true
  everyPrintedLabelShown :
    ∀ label, setup.figure.showsLabel label = true
  birdArrowPointsRight :
    setup.figure.birdArrowDirection = .rightward
  horizontalFlightGuide :
    setup.figure.birdFlightGuideIsHorizontal = true
  dashedImpactGuide :
    setup.figure.impactGuideIsDashed = true
  impactGuideMeetsBar :
    setup.figure.impactGuideMeetsBar = true
  verticalDistanceMarker :
    setup.figure.distanceMarkerIsVertical = true
  markerRunsFromTopToImpactGuide :
    setup.figure.distanceMarkerRunsFromBarTopToImpactGuide = true
  verticalBarShown :
    setup.figure.barIsDrawnVertical = true
  baseAtHinge :
    setup.figure.barBaseCoincidesWithHinge = true
  hingeOnGround :
    setup.figure.hingeLiesOnGroundLine = true
  printedDistanceCentimeters :
    setup.figure.topToImpactLabelCentimeters = 25

/-!
Numerical and qualitative data stated in the problem.  The distances are
stored independently; their geometric relation belongs to the governing-law
structure below.  Deliberately, this structure says nothing about the bird's
post-impact velocity component or disposition, because the source says
nothing about them.
-/
structure MatchesBirdBarProblemData
    (setup : HingedBarImpactSetup) : Prop where
  birdMassKilograms :
    massInKilograms setup.birdMass = 1 / 2
  birdIncomingSpeedMetersPerSecond :
    speedInMetersPerSecond setup.birdIncomingSpeedMagnitude = 9 / 4
  barMassKilograms :
    massInKilograms setup.barMass = 3 / 2
  barLengthMeters :
    lengthInMeters setup.barLength = 3 / 4
  topToImpactDistanceMeters :
    lengthInMeters setup.topToImpactDistance = 1 / 4
  figureDistanceMatchesPhysicalDistance :
    setup.figure.topToImpactLabelCentimeters =
      100 * lengthInMeters setup.topToImpactDistance
  barInitiallyStationary :
    angularSpeedInRadiansPerSecond
      (setup.barAngularSpeed .beforeImpact) = 0

/-!
Qualitative states before impact and when the bar reaches the ground.  These
conditions identify the fall through ninety degrees without assigning the
unknown final angular speed.
-/
structure MatchesHingedBarScenario
    (setup : HingedBarImpactSetup) : Prop where
  barUniform : setup.barIsUniform = true
  fixedBaseHinge : setup.hingeIsFixedAtBarBase = true
  barVerticalBeforeImpact :
    setup.barOrientation .beforeImpact = .vertical
  barStillVerticalImmediatelyAfterImpact :
    setup.barOrientation .immediatelyAfterImpact = .vertical
  barHorizontalAtGround :
    setup.barOrientation .justReachesGround = .horizontal
  positiveRotationComesFromBird :
    setup.positiveRotationIsInducedByIncomingBird = true

/-!
Positivity and nondegeneracy conditions for the displayed physical setup.
They contain no solved angular speed at either post-impact stage.
-/
structure HasPhysicalBirdBarParameters
    (setup : HingedBarImpactSetup) : Prop where
  birdMassPositive : 0 < massInKilograms setup.birdMass
  barMassPositive : 0 < massInKilograms setup.barMass
  incomingSpeedPositive :
    0 < speedInMetersPerSecond setup.birdIncomingSpeedMagnitude
  barLengthPositive : 0 < lengthInMeters setup.barLength
  impactDistanceBelowTopPositive :
    0 < lengthInMeters setup.topToImpactDistance
  impactLiesBelowTop :
    lengthInMeters setup.topToImpactDistance <
      lengthInMeters setup.barLength
  hingeToImpactDistancePositive :
    0 < lengthInMeters setup.hingeToImpactDistance
  centerOfMassDistancePositive :
    0 < lengthInMeters setup.barCenterOfMassDistanceFromHinge
  centerOfMassDropPositive :
    0 < lengthInMeters setup.barCenterOfMassVerticalDrop
  gravityPositive :
    0 < accelerationInMetersPerSecondSquared
      setup.gravitationalAccelerationMagnitude
  momentOfInertiaPositive :
    0 < momentOfInertiaInKilogramMetersSquared
      setup.barMomentOfInertiaAboutHinge

/-! ## Governing impact and falling-bar laws -/

/-!
Geometry and mass distribution of a thin uniform bar hinged at one end.  The
impact lever arm is the bar length minus the labeled distance below its top;
the center of mass is halfway along the bar; and `I_hinge = M L^2 / 3`.
-/
structure SatisfiesUniformHingedBarLaws
    (setup : HingedBarImpactSetup) : Prop where
  impactLeverArmGeometry :
    lengthInMeters setup.hingeToImpactDistance =
      lengthInMeters setup.barLength -
        lengthInMeters setup.topToImpactDistance
  centerOfMassAtMidpoint :
    lengthInMeters setup.barCenterOfMassDistanceFromHinge =
      lengthInMeters setup.barLength / 2
  verticalToHorizontalCenterOfMassDrop :
    lengthInMeters setup.barCenterOfMassVerticalDrop =
      lengthInMeters setup.barCenterOfMassDistanceFromHinge
  uniformBarMomentOfInertiaAboutEnd :
    momentOfInertiaInKilogramMetersSquared
        setup.barMomentOfInertiaAboutHinge =
      (1 / 3 : ℝ) * massInKilograms setup.barMass *
        lengthInMeters setup.barLength ^ 2

/-!
Angular momentum about the base hinge during the short collision.  The hinge
impulse has zero moment about the hinge, and the gravitational impulse is
negligible over the collision duration.  The bird's path is perpendicular to
the vertical lever arm, so its contribution is `m v r`.  The immediately
post-impact component is signed in the positive rotation convention; hence a
negative readout represents rebound.
-/
structure SatisfiesShortImpactAngularMomentumLaws
    (setup : HingedBarImpactSetup) : Prop where
  shortImpact :
    setup.impactDurationIsNegligible = true
  hingeImpulseHasZeroMomentAboutHinge :
    angularMomentumInKilogramMetersSquaredPerSecond
      setup.hingeImpulseMomentAboutHinge = 0
  gravitationalImpulseDuringImpactIsNegligible :
    angularMomentumInKilogramMetersSquaredPerSecond
      setup.gravitationalAngularImpulseDuringImpact = 0
  angularMomentumImmediatelyBeforeImpact :
    angularMomentumInKilogramMetersSquaredPerSecond
        (setup.totalAngularMomentumAboutHinge .immediatelyBefore) =
      massInKilograms setup.birdMass *
          speedInMetersPerSecond setup.birdIncomingSpeedMagnitude *
          lengthInMeters setup.hingeToImpactDistance +
        momentOfInertiaInKilogramMetersSquared
            setup.barMomentOfInertiaAboutHinge *
          angularSpeedInRadiansPerSecond
            (setup.barAngularSpeed .beforeImpact)
  angularMomentumImmediatelyAfterImpact :
    angularMomentumInKilogramMetersSquaredPerSecond
        (setup.totalAngularMomentumAboutHinge .immediatelyAfter) =
      momentOfInertiaInKilogramMetersSquared
            setup.barMomentOfInertiaAboutHinge *
          angularSpeedInRadiansPerSecond
            (setup.barAngularSpeed .immediatelyAfterImpact) +
        massInKilograms setup.birdMass *
          tangentialVelocityComponentInMetersPerSecond
            setup.birdTangentialVelocityComponentImmediatelyAfterImpact *
          lengthInMeters setup.hingeToImpactDistance
  angularMomentumAboutHingeConserved :
    angularMomentumInKilogramMetersSquaredPerSecond
        (setup.totalAngularMomentumAboutHinge .immediatelyBefore) =
      angularMomentumInKilogramMetersSquaredPerSecond
        (setup.totalAngularMomentumAboutHinge .immediatelyAfter)
  attachedBirdSharesBarTangentialSpeed :
    setup.birdPostImpactDisposition = .attachedToBar →
      tangentialVelocityComponentInMetersPerSecond
          setup.birdTangentialVelocityComponentImmediatelyAfterImpact =
        lengthInMeters setup.hingeToImpactDistance *
          angularSpeedInRadiansPerSecond
            (setup.barAngularSpeed .immediatelyAfterImpact)

/-!
Mechanical-energy laws after the inelastic impact.  Energy is not asserted to
be conserved across the bird-bar collision.  If the bird separates, only the
bar's energy enters the subsequent fall.  If it remains attached at the impact
point, its rotational kinetic and gravitational potential energies enter as
well.  This branch-sensitive law leaves the source's missing post-impact state
visible rather than silently selecting one collision outcome.
-/
structure SatisfiesFrictionlessBarFallEnergyLaws
    (setup : HingedBarImpactSetup) : Prop where
  negligibleHingeFriction :
    setup.hingeFrictionDuringFallIsNegligible = true
  rotationalKineticEnergyImmediatelyAfterImpact :
    2 * energyInJoules
        (setup.barRotationalKineticEnergy .immediatelyAfterImpact) =
      momentOfInertiaInKilogramMetersSquared
          setup.barMomentOfInertiaAboutHinge *
        angularSpeedInRadiansPerSecond
          (setup.barAngularSpeed .immediatelyAfterImpact) ^ 2
  rotationalKineticEnergyAtGround :
    2 * energyInJoules
        (setup.barRotationalKineticEnergy .justReachesGround) =
      momentOfInertiaInKilogramMetersSquared
          setup.barMomentOfInertiaAboutHinge *
        angularSpeedInRadiansPerSecond
          (setup.barAngularSpeed .justReachesGround) ^ 2
  gravitationalPotentialEnergyLoss :
    energyInJoules
          (setup.barGravitationalPotentialEnergy .immediatelyAfterImpact) -
        energyInJoules
          (setup.barGravitationalPotentialEnergy .justReachesGround) =
      massInKilograms setup.barMass *
        accelerationInMetersPerSecondSquared
          setup.gravitationalAccelerationMagnitude *
        lengthInMeters setup.barCenterOfMassVerticalDrop
  attachedBirdRotationalKineticEnergyImmediatelyAfterImpact :
    setup.birdPostImpactDisposition = .attachedToBar →
      2 * energyInJoules
          (setup.birdRotationalKineticEnergy .immediatelyAfterImpact) =
        massInKilograms setup.birdMass *
          (lengthInMeters setup.hingeToImpactDistance *
            angularSpeedInRadiansPerSecond
              (setup.barAngularSpeed .immediatelyAfterImpact)) ^ 2
  attachedBirdRotationalKineticEnergyAtGround :
    setup.birdPostImpactDisposition = .attachedToBar →
      2 * energyInJoules
          (setup.birdRotationalKineticEnergy .justReachesGround) =
        massInKilograms setup.birdMass *
          (lengthInMeters setup.hingeToImpactDistance *
            angularSpeedInRadiansPerSecond
              (setup.barAngularSpeed .justReachesGround)) ^ 2
  attachedBirdGravitationalPotentialEnergyLoss :
    setup.birdPostImpactDisposition = .attachedToBar →
      energyInJoules
            (setup.birdGravitationalPotentialEnergy .immediatelyAfterImpact) -
          energyInJoules
            (setup.birdGravitationalPotentialEnergy .justReachesGround) =
        massInKilograms setup.birdMass *
          accelerationInMetersPerSecondSquared
            setup.gravitationalAccelerationMagnitude *
          lengthInMeters setup.hingeToImpactDistance
  separatedBirdBarEnergyConservedDuringFall :
    setup.birdPostImpactDisposition = .separated →
      energyInJoules
            (setup.barRotationalKineticEnergy .immediatelyAfterImpact) +
          energyInJoules
            (setup.barGravitationalPotentialEnergy .immediatelyAfterImpact) =
        energyInJoules
            (setup.barRotationalKineticEnergy .justReachesGround) +
          energyInJoules
            (setup.barGravitationalPotentialEnergy .justReachesGround)
  attachedBirdBarEnergyConservedDuringFall :
    setup.birdPostImpactDisposition = .attachedToBar →
      energyInJoules
            (setup.barRotationalKineticEnergy .immediatelyAfterImpact) +
          energyInJoules
            (setup.birdRotationalKineticEnergy .immediatelyAfterImpact) +
          (energyInJoules
            (setup.barGravitationalPotentialEnergy .immediatelyAfterImpact) +
          energyInJoules
            (setup.birdGravitationalPotentialEnergy .immediatelyAfterImpact)) =
        energyInJoules
            (setup.barRotationalKineticEnergy .justReachesGround) +
          energyInJoules
            (setup.birdRotationalKineticEnergy .justReachesGround) +
          (energyInJoules
            (setup.barGravitationalPotentialEnergy .justReachesGround) +
          energyInJoules
            (setup.birdGravitationalPotentialEnergy .justReachesGround))

/-! ## Derived relations and recorded-answer metadata -/

/-- The figure and bar length place the impact point one half metre above the hinge. -/
lemma hingeToImpactDistance_is_one_half_meter
    (setup : HingedBarImpactSetup)
    (hData : MatchesBirdBarProblemData setup)
    (hBar : SatisfiesUniformHingedBarLaws setup) :
    lengthInMeters setup.hingeToImpactDistance = 1 / 2 := by
  sorry

/-- The stated uniform bar has hinged moment of inertia `9/32 kg m^2`. -/
lemma barMomentOfInertia_is_nine_over_thirty_two
    (setup : HingedBarImpactSetup)
    (hData : MatchesBirdBarProblemData setup)
    (hBar : SatisfiesUniformHingedBarLaws setup) :
    momentOfInertiaInKilogramMetersSquared
      setup.barMomentOfInertiaAboutHinge = 9 / 32 := by
  sorry

/-!
Before any stop-and-separate idealization is imposed, conservation leaves the
bar's post-impact angular speed coupled to the bird's unspecified outgoing
tangential velocity.  This relation makes the source underdetermination
explicit rather than assigning the missing bird state in `MatchesBirdBarProblemData`.
-/
lemma shortImpact_balance_exposes_outgoing_bird_velocity
    (setup : HingedBarImpactSetup)
    (hData : MatchesBirdBarProblemData setup)
    (hImpact : SatisfiesShortImpactAngularMomentumLaws setup) :
    momentOfInertiaInKilogramMetersSquared
          setup.barMomentOfInertiaAboutHinge *
        angularSpeedInRadiansPerSecond
          (setup.barAngularSpeed .immediatelyAfterImpact) +
      massInKilograms setup.birdMass *
        tangentialVelocityComponentInMetersPerSecond
          setup.birdTangentialVelocityComponentImmediatelyAfterImpact *
        lengthInMeters setup.hingeToImpactDistance =
      massInKilograms setup.birdMass *
        speedInMetersPerSecond setup.birdIncomingSpeedMagnitude *
        lengthInMeters setup.hingeToImpactDistance := by
  sorry

/-- Labels of the four angular-speed choices printed with the problem. -/
inductive AnswerChoice where
  | A
  | B
  | C
  | D
  deriving DecidableEq, Fintype, Repr

/-- Radian-per-second value printed beside each answer label. -/
def AnswerChoice.radiansPerSecond : AnswerChoice → ℝ
  | .A => 102 / 25
  | .B => 329 / 50
  | .C => 217 / 100
  | .D => 1239 / 100

/-- The answer label recorded in the supplied dataset metadata. -/
def recordedDatasetAnswer : AnswerChoice := .B

/-!
The source determines a branch-sensitive symbolic relation, not a single
number.  If the bird separates, its unknown signed outgoing tangential
velocity remains in the answer.  If it remains attached, impact kinematics
fix the common post-impact angular speed and the bird contributes to both the
rotational inertia and the gravitational energy of the falling system.

For the stated masses and geometry, both fall branches acquire the term `4 g`.
The recorded answer label is retained only as metadata; no branch is selected
and no answer choice is asserted physically correct.

This formalizes `thm:physics:phyx_mini_0790:target`.
-/
theorem angularVelocity_when_bar_reaches_ground
    (setup : HingedBarImpactSetup)
    (hFigure : MatchesPrimaryBirdBarFigure setup)
    (hData : MatchesBirdBarProblemData setup)
    (hScenario : MatchesHingedBarScenario setup)
    (hPhysical : HasPhysicalBirdBarParameters setup)
    (hBar : SatisfiesUniformHingedBarLaws setup)
    (hImpact : SatisfiesShortImpactAngularMomentumLaws setup)
    (hFall : SatisfiesFrictionlessBarFallEnergyLaws setup) :
    (setup.birdPostImpactDisposition = .separated →
      angularSpeedInRadiansPerSecond
            (setup.barAngularSpeed .justReachesGround) ^ 2 =
        (2 - (8 / 9 : ℝ) *
            tangentialVelocityComponentInMetersPerSecond
              setup.birdTangentialVelocityComponentImmediatelyAfterImpact) ^ 2 +
          4 * accelerationInMetersPerSecondSquared
            setup.gravitationalAccelerationMagnitude) ∧
      (setup.birdPostImpactDisposition = .attachedToBar →
        angularSpeedInRadiansPerSecond
              (setup.barAngularSpeed .justReachesGround) ^ 2 =
          324 / 169 +
            4 * accelerationInMetersPerSecondSquared
              setup.gravitationalAccelerationMagnitude) ∧
      recordedDatasetAnswer = .B := by
  sorry

end PhyXMiniProblems.ProblemPhyXMini0790
