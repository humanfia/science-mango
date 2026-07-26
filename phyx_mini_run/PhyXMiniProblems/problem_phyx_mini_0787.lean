import Mathlib
import Physlib.ClassicalMechanics.RigidBody.KineticEnergy
import Physlib.Units.WithDim.Energy
import Physlib.Units.WithDim.Speed

/- USER: The assigned source file did not exist when this autoformalization task began. -/

/-!
# A hollow basketball rolling from a rough slope onto a smooth slope

A basketball is modeled as a thin hollow spherical shell.  It starts from rest
with its center of mass at height `H₀` above the valley datum, rolls without
slipping down the rough side, and then climbs the frictionless smooth side.
Rolling resistance is neglected and total mechanical energy is conserved.

The setup keeps mass, radius, height, speed, angular speed, moment of inertia,
acceleration, and energy dimensionful by using Physlib quantities.  Real
numbers occur only at coherent-SI readout boundaries, inside Physlib's
SI-coordinate rigid-body API, and as dimensionless answer fractions.

Assumption/target split:

* governing laws: `I = (2/3) M R²` for a thin hollow sphere,
  translational and rotational kinetic-energy laws, `U = M g h`, decomposition
  and conservation of total mechanical energy, no-slip kinematics at the end
  of the rough section, and conservation of angular speed on the frictionless
  smooth section;
* previous-part results: none;
* figure/data readouts: the ball begins at the upper left, `H₀` is measured to
  the dashed valley datum, the left slope is labelled Rough, the right slope is
  labelled Smooth, the ball starts from rest, and the rough-to-smooth
  transition is at datum height;
* target conclusion: the center of mass reaches height `(3/5) H₀` on the
  smooth side, corresponding to answer choice B.
-/

noncomputable section

namespace PhyXMiniProblems.ProblemPhyXMini0787

open Dimension

/-! ## Dimensionful physical quantities and coherent-SI readouts -/

/-- A nonnegative, unit-independent physical mass. -/
abbrev MassQuantity : Type :=
  Dimensionful (WithDim M𝓭 NNReal)

/-- A nonnegative physical length, used for radius and height. -/
abbrev LengthQuantity : Type :=
  Dimensionful (WithDim L𝓭 NNReal)

/-- A nonnegative speed magnitude. -/
abbrev SpeedQuantity : Type := DimSpeed

/-- A nonnegative angular-speed magnitude; radians are dimensionless. -/
abbrev AngularSpeedQuantity : Type :=
  Dimensionful (WithDim T𝓭⁻¹ NNReal)

/-- The dimension of a moment of inertia, `mass * length²`. -/
def momentOfInertiaDimension : Dimension :=
  M𝓭 * L𝓭 * L𝓭

/-- A nonnegative axial moment of inertia. -/
abbrev MomentOfInertiaQuantity : Type :=
  Dimensionful (WithDim momentOfInertiaDimension NNReal)

/-- The dimension of an acceleration, `length / time²`. -/
def accelerationDimension : Dimension :=
  L𝓭 * T𝓭⁻¹ * T𝓭⁻¹

/-- A nonnegative acceleration magnitude. -/
abbrev AccelerationQuantity : Type :=
  Dimensionful (WithDim accelerationDimension NNReal)

/-- A physical energy with dimension `mass * length² / time²`. -/
abbrev EnergyQuantity : Type := DimEnergy

/-- Read a nonnegative dimensionful quantity in coherent SI units. -/
def nonnegativeSIReadout {dimension : Dimension}
    (quantity : Dimensionful (WithDim dimension NNReal)) : ℝ :=
  ((quantity UnitChoices.SI).val : ℝ)

/-- Metre readout of a physical length. -/
def lengthInMeters (length : LengthQuantity) : ℝ :=
  nonnegativeSIReadout length

/-- Kilogram readout of a physical mass. -/
def massInKilograms (mass : MassQuantity) : ℝ :=
  nonnegativeSIReadout mass

/-- Metre-per-second readout of a speed. -/
def speedInMetersPerSecond (speed : SpeedQuantity) : ℝ :=
  nonnegativeSIReadout speed

/-- Radian-per-second readout of an angular speed. -/
def angularSpeedInRadiansPerSecond
    (angularSpeed : AngularSpeedQuantity) : ℝ :=
  nonnegativeSIReadout angularSpeed

/-- Kilogram-metre-squared readout of an axial moment of inertia. -/
def momentOfInertiaInKilogramMetersSquared
    (inertia : MomentOfInertiaQuantity) : ℝ :=
  nonnegativeSIReadout inertia

/-- Metre-per-second-squared readout of an acceleration magnitude. -/
def accelerationInMetersPerSecondSquared
    (acceleration : AccelerationQuantity) : ℝ :=
  nonnegativeSIReadout acceleration

/-- Joule readout of a physical energy. -/
def energyInJoules (energy : EnergyQuantity) : ℝ :=
  (energy UnitChoices.SI).val

/-! ## Motion, contact regimes, and primary-image vocabulary -/

/-- The three instants used in the energy comparison. -/
inductive MotionEvent where
  | release
  | roughToSmoothTransition
  | highestPointOnSmoothSide
  deriving DecidableEq, Fintype, Repr

/-- The two terrain phases distinguished in the problem and image. -/
inductive MotionPhase where
  | roughDescent
  | smoothAscent
  deriving DecidableEq, Fintype, Repr

/-- Finish of the terrain under the ball. -/
inductive SurfaceFinish where
  | rough
  | smooth
  deriving DecidableEq, Repr

/-- Tangential contact behavior relevant to the two terrain phases. -/
inductive ContactRegime where
  | rollingWithoutSlip
  | frictionlessNoTangentialForce
  deriving DecidableEq, Repr

/-- Rigid-body shape used for the basketball approximation. -/
inductive BallShape where
  | thinHollowSphericalShell
  | solidSphere
  deriving DecidableEq, Repr

/-- Visible parts of the supplied bitmap. -/
inductive FigurePart where
  | basketball
  | leftSlope
  | valleyBottom
  | rightSlope
  | initialHeightArrow
  | dashedValleyDatum
  deriving DecidableEq, Fintype, Repr

/-- Literal semantic labels appearing in the bitmap. -/
inductive FigureLabel where
  | roughSurface
  | smoothSurface
  | initialHeightH0
  deriving DecidableEq, Fintype, Repr

/-- Qualitative location of the depicted ball. -/
inductive DepictedBallLocation where
  | upperLeftOnRoughSlope
  | elsewhere
  deriving DecidableEq, Repr

/-!
Qualitative evidence transcribed from image `787.png`.  No metric distance is
inferred from pixel positions.  The symbolic `H₀` label is attached to the
vertical arrow from the ball's initial center-of-mass level to the dashed
valley datum.
-/
structure BasketballValleyFigure where
  showsPart : FigurePart → Bool
  showsLabel : FigureLabel → Bool
  labelRefersTo : FigureLabel → FigurePart
  depictedBallLocation : DepictedBallLocation
  heightArrowTopAlignedWithBallCenter : Bool
  heightArrowBottomAlignedWithDatum : Bool
  leftSlopeMeetsValleyBottom : Bool
  valleyBottomMeetsRightSlope : Bool

/-! ## Independent physical setup -/

/-!
All observables, including the unknown height at the highest point, are stored
independently.  In particular, `centerOfMassHeightAboveValleyDatum` is not
defined from an answer fraction or from the conservation laws.

The `RigidBody 3` and its angular-velocity vector use Physlib's existing
three-dimensional SI-coordinate rotational-energy definition.  Separate
dimensionful fields record the physical quantities before taking SI readouts.
-/
structure RollingBasketballSetup where
  figure : BasketballValleyFigure
  ballShape : BallShape
  ballMass : MassQuantity
  ballRadius : LengthQuantity
  initialHeightH0 : LengthQuantity
  centerOfMassHeightAboveValleyDatum : MotionEvent → LengthQuantity
  centerOfMassSpeed : MotionEvent → SpeedQuantity
  angularSpeed : MotionEvent → AngularSpeedQuantity
  axialMomentOfInertia : MomentOfInertiaQuantity
  gravitationalAcceleration : AccelerationQuantity
  gravitationalPotentialEnergy : MotionEvent → EnergyQuantity
  translationalKineticEnergy : MotionEvent → EnergyQuantity
  rotationalKineticEnergy : MotionEvent → EnergyQuantity
  rigidBodySI : RigidBody 3
  rotationAxis : Fin 3
  angularVelocityVector_rad_per_s : MotionEvent → Fin 3 → ℝ
  surfaceFinish : MotionPhase → SurfaceFinish
  contactRegime : MotionPhase → ContactRegime
  rollingResistanceNeglected : Bool

/-! ## Figure evidence and stated problem data -/

/-- Labels, geometry, and placement read directly from the primary bitmap. -/
structure MatchesPrimaryBasketballValleyFigure
    (setup : RollingBasketballSetup) : Prop where
  everyPartIsShown :
    ∀ part, setup.figure.showsPart part = true
  everyLabelIsShown :
    ∀ label, setup.figure.showsLabel label = true
  roughLabelRefersToLeftSlope :
    setup.figure.labelRefersTo .roughSurface = .leftSlope
  smoothLabelRefersToRightSlope :
    setup.figure.labelRefersTo .smoothSurface = .rightSlope
  heightLabelRefersToArrow :
    setup.figure.labelRefersTo .initialHeightH0 = .initialHeightArrow
  ballBeginsAtUpperLeft :
    setup.figure.depictedBallLocation = .upperLeftOnRoughSlope
  arrowStartsAtBallCenterLevel :
    setup.figure.heightArrowTopAlignedWithBallCenter = true
  arrowEndsAtDashedValleyDatum :
    setup.figure.heightArrowBottomAlignedWithDatum = true
  leftSlopeJoinsValley :
    setup.figure.leftSlopeMeetsValleyBottom = true
  valleyJoinsRightSlope :
    setup.figure.valleyBottomMeetsRightSlope = true

/-!
Problem-text data and event meanings.  The ball starts from rest at height
`H₀`; the rough-to-smooth transition is at the valley datum; and the named
highest point is a translational turning point, while the ball may still spin.
These facts do not specify that highest point's height.
-/
structure MatchesRollingBasketballProblemData
    (setup : RollingBasketballSetup) : Prop where
  basketballIsHollowShell :
    setup.ballShape = .thinHollowSphericalShell
  releaseHeightIsH0 :
    lengthInMeters
        (setup.centerOfMassHeightAboveValleyDatum .release) =
      lengthInMeters setup.initialHeightH0
  transitionIsAtValleyDatum :
    lengthInMeters
        (setup.centerOfMassHeightAboveValleyDatum
          .roughToSmoothTransition) = 0
  releasedFromTranslationalRest :
    speedInMetersPerSecond (setup.centerOfMassSpeed .release) = 0
  releasedFromRotationalRest :
    angularSpeedInRadiansPerSecond (setup.angularSpeed .release) = 0
  highestPointIsTranslationalTurningPoint :
    speedInMetersPerSecond
        (setup.centerOfMassSpeed .highestPointOnSmoothSide) = 0
  descendingSurfaceIsRough :
    setup.surfaceFinish .roughDescent = .rough
  ascendingSurfaceIsSmooth :
    setup.surfaceFinish .smoothAscent = .smooth
  roughPartPreventsSlipping :
    setup.contactRegime .roughDescent = .rollingWithoutSlip
  smoothPartHasNoTangentialFriction :
    setup.contactRegime .smoothAscent = .frictionlessNoTangentialForce
  rollingFrictionIsNeglected :
    setup.rollingResistanceNeglected = true

/-- Positivity and nonnegativity conditions selecting the physical branch. -/
structure HasPhysicalRollingBasketballParameters
    (setup : RollingBasketballSetup) : Prop where
  positiveMass : 0 < massInKilograms setup.ballMass
  positiveRadius : 0 < lengthInMeters setup.ballRadius
  positiveInitialHeight : 0 < lengthInMeters setup.initialHeightH0
  positiveGravity :
    0 < accelerationInMetersPerSecondSquared
      setup.gravitationalAcceleration
  everyHeightNonnegative :
    ∀ event,
      0 ≤ lengthInMeters
        (setup.centerOfMassHeightAboveValleyDatum event)
  everyEnergyNonnegative :
    ∀ event,
      0 ≤ energyInJoules (setup.gravitationalPotentialEnergy event) ∧
      0 ≤ energyInJoules (setup.translationalKineticEnergy event) ∧
      0 ≤ energyInJoules (setup.rotationalKineticEnergy event)

/-! ## Governing energy and rigid-body laws -/

/-!
The hollow-shell inertia, standard kinetic and potential energies, Physlib
rotational-energy connection, and conservation of total mechanical energy.
All equalities are stated in coherent SI readouts.  None contains the unknown
height as a solved multiple of `H₀`.
-/
structure SatisfiesRollingBasketballEnergyLaws
    (setup : RollingBasketballSetup) : Prop where
  rigidBodyMassMatchesBasketball :
    setup.rigidBodySI.mass = massInKilograms setup.ballMass
  angularVelocityIsAlongRotationAxis :
    ∀ (event : MotionEvent) (component : Fin 3),
      setup.angularVelocityVector_rad_per_s event component =
        if component = setup.rotationAxis then
          angularSpeedInRadiansPerSecond (setup.angularSpeed event)
        else 0
  axialInertiaTensorEntry :
    setup.rigidBodySI.inertiaTensor setup.rotationAxis setup.rotationAxis =
      momentOfInertiaInKilogramMetersSquared setup.axialMomentOfInertia
  hollowSphericalShellMomentOfInertia :
    momentOfInertiaInKilogramMetersSquared setup.axialMomentOfInertia =
      (2 / 3 : ℝ) * massInKilograms setup.ballMass *
        lengthInMeters setup.ballRadius ^ 2
  translationalKineticEnergyLaw :
    ∀ event,
      energyInJoules (setup.translationalKineticEnergy event) =
        (1 / 2 : ℝ) * massInKilograms setup.ballMass *
          speedInMetersPerSecond (setup.centerOfMassSpeed event) ^ 2
  rotationalKineticEnergyUsesPhyslib :
    ∀ event,
      energyInJoules (setup.rotationalKineticEnergy event) =
        setup.rigidBodySI.rotationalKineticEnergy
          (setup.angularVelocityVector_rad_per_s event)
  axialRotationalKineticEnergyLaw :
    ∀ event,
      energyInJoules (setup.rotationalKineticEnergy event) =
        (1 / 2 : ℝ) *
          momentOfInertiaInKilogramMetersSquared
            setup.axialMomentOfInertia *
          angularSpeedInRadiansPerSecond (setup.angularSpeed event) ^ 2
  gravitationalPotentialEnergyLaw :
    ∀ event,
      energyInJoules (setup.gravitationalPotentialEnergy event) =
        massInKilograms setup.ballMass *
          accelerationInMetersPerSecondSquared
            setup.gravitationalAcceleration *
          lengthInMeters
            (setup.centerOfMassHeightAboveValleyDatum event)
  totalMechanicalEnergyIsConserved :
    ∀ event,
      energyInJoules (setup.gravitationalPotentialEnergy event) +
            energyInJoules (setup.translationalKineticEnergy event) +
          energyInJoules (setup.rotationalKineticEnergy event) =
        energyInJoules
              (setup.gravitationalPotentialEnergy .release) +
            energyInJoules
              (setup.translationalKineticEnergy .release) +
          energyInJoules (setup.rotationalKineticEnergy .release)

/-! ## Governing contact and phase-transition laws -/

/-!
At the end of the rough section, rolling without slipping gives `v = R ω`.
On the smooth section there is no tangential contact force and hence no torque
about the center, so the angular speed is unchanged during the ascent.  The
second equality is a phase law, not a statement about the attained height.
-/
structure SatisfiesRoughAndSmoothContactLaws
    (setup : RollingBasketballSetup) : Prop where
  noSlipAtEndOfRoughSection :
    speedInMetersPerSecond
        (setup.centerOfMassSpeed .roughToSmoothTransition) =
      lengthInMeters setup.ballRadius *
        angularSpeedInRadiansPerSecond
          (setup.angularSpeed .roughToSmoothTransition)
  angularSpeedConservedOnSmoothSection :
    angularSpeedInRadiansPerSecond
        (setup.angularSpeed .highestPointOnSmoothSide) =
      angularSpeedInRadiansPerSecond
        (setup.angularSpeed .roughToSmoothTransition)

/-! ## Derived energy partitions -/

/-!
For the hollow shell, the no-slip relation and `I = (2/3) M R²` imply that
the translational kinetic energy at the bottom is three fifths of the initial
gravitational potential energy.  This is an intermediate energy statement,
not the requested final height.
-/
lemma translationalEnergyAtTransition_eq_threeFifths_initialPotentialEnergy
    (setup : RollingBasketballSetup)
    (_data : MatchesRollingBasketballProblemData setup)
    (_physical : HasPhysicalRollingBasketballParameters setup)
    (_energyLaws : SatisfiesRollingBasketballEnergyLaws setup)
    (_contactLaws : SatisfiesRoughAndSmoothContactLaws setup) :
    energyInJoules
        (setup.translationalKineticEnergy .roughToSmoothTransition) =
      (3 / 5 : ℝ) *
        energyInJoules
          (setup.gravitationalPotentialEnergy .release) := by
  have hReleaseTrans :=
    _energyLaws.translationalKineticEnergyLaw MotionEvent.release
  have hReleaseRot :=
    _energyLaws.axialRotationalKineticEnergyLaw MotionEvent.release
  have hTransitionPotential :=
    _energyLaws.gravitationalPotentialEnergyLaw
      MotionEvent.roughToSmoothTransition
  have hTransitionTrans :=
    _energyLaws.translationalKineticEnergyLaw
      MotionEvent.roughToSmoothTransition
  have hTransitionRot :=
    _energyLaws.axialRotationalKineticEnergyLaw
      MotionEvent.roughToSmoothTransition
  have hConservation :=
    _energyLaws.totalMechanicalEnergyIsConserved
      MotionEvent.roughToSmoothTransition
  rw [_data.releasedFromTranslationalRest] at hReleaseTrans
  rw [_data.releasedFromRotationalRest] at hReleaseRot
  rw [_data.transitionIsAtValleyDatum] at hTransitionPotential
  rw [_contactLaws.noSlipAtEndOfRoughSection] at hTransitionTrans
  rw [_energyLaws.hollowSphericalShellMomentOfInertia] at hTransitionRot
  norm_num at hReleaseTrans hReleaseRot hTransitionPotential
  ring_nf at hTransitionTrans hTransitionRot ⊢
  nlinarith

/-!
During the frictionless ascent the rotational energy is retained, so the
translational energy present at the transition becomes gravitational potential
energy at the highest point.
-/
lemma potentialEnergyAtHighestPoint_eq_transitionTranslationalEnergy
    (setup : RollingBasketballSetup)
    (_data : MatchesRollingBasketballProblemData setup)
    (_energyLaws : SatisfiesRollingBasketballEnergyLaws setup)
    (_contactLaws : SatisfiesRoughAndSmoothContactLaws setup) :
    energyInJoules
        (setup.gravitationalPotentialEnergy .highestPointOnSmoothSide) =
      energyInJoules
        (setup.translationalKineticEnergy .roughToSmoothTransition) := by
  have hTransitionPotential :=
    _energyLaws.gravitationalPotentialEnergyLaw
      MotionEvent.roughToSmoothTransition
  have hHighestTrans :=
    _energyLaws.translationalKineticEnergyLaw
      MotionEvent.highestPointOnSmoothSide
  have hHighestRot :=
    _energyLaws.axialRotationalKineticEnergyLaw
      MotionEvent.highestPointOnSmoothSide
  have hTransitionRot :=
    _energyLaws.axialRotationalKineticEnergyLaw
      MotionEvent.roughToSmoothTransition
  have hConservationHighest :=
    _energyLaws.totalMechanicalEnergyIsConserved
      MotionEvent.highestPointOnSmoothSide
  have hConservationTransition :=
    _energyLaws.totalMechanicalEnergyIsConserved
      MotionEvent.roughToSmoothTransition
  rw [_data.transitionIsAtValleyDatum] at hTransitionPotential
  rw [_data.highestPointIsTranslationalTurningPoint] at hHighestTrans
  rw [_contactLaws.angularSpeedConservedOnSmoothSection] at hHighestRot
  norm_num at hTransitionPotential hHighestTrans
  linarith

/-! ## Answer metadata and final conclusion -/

/-- Labels of the four displayed answers. -/
inductive AnswerChoice where
  | A
  | B
  | C
  | D
  deriving DecidableEq, Fintype, Repr

/-- Dimensionless height multiplier displayed in each answer choice. -/
def AnswerChoice.heightFraction : AnswerChoice → ℝ
  | .A => 2 / 5
  | .B => 3 / 5
  | .C => 1 / 3
  | .D => 2 / 3

/-- Dataset metadata: the recorded answer is choice B. -/
def recordedAnswerChoice : AnswerChoice := .B

/-!
The ball rises to three fifths of its initial center-of-mass height on the
smooth side.  Its rotational kinetic energy cannot be converted into
gravitational potential energy there because the frictionless surface exerts
no tangential torque.  This is displayed answer choice B.

This formalizes blueprint label `thm:physics:phyx_mini_0787:target`.
-/
theorem problem_phyx_mini_0787
    (setup : RollingBasketballSetup)
    (_figure : MatchesPrimaryBasketballValleyFigure setup)
    (_data : MatchesRollingBasketballProblemData setup)
    (_physical : HasPhysicalRollingBasketballParameters setup)
    (_energyLaws : SatisfiesRollingBasketballEnergyLaws setup)
    (_contactLaws : SatisfiesRoughAndSmoothContactLaws setup) :
    lengthInMeters
        (setup.centerOfMassHeightAboveValleyDatum
          .highestPointOnSmoothSide) =
      (3 / 5 : ℝ) * lengthInMeters setup.initialHeightH0 := by
  have hPartition :=
    translationalEnergyAtTransition_eq_threeFifths_initialPotentialEnergy
      setup _data _physical _energyLaws _contactLaws
  have hAscent :=
    potentialEnergyAtHighestPoint_eq_transitionTranslationalEnergy
      setup _data _energyLaws _contactLaws
  have hPotentialRatio := hAscent.trans hPartition
  rw [_energyLaws.gravitationalPotentialEnergyLaw
        MotionEvent.highestPointOnSmoothSide,
      _energyLaws.gravitationalPotentialEnergyLaw MotionEvent.release,
      _data.releaseHeightIsH0] at hPotentialRatio
  have hMassGravityPositive :
      0 < massInKilograms setup.ballMass *
        accelerationInMetersPerSecondSquared
          setup.gravitationalAcceleration :=
    mul_pos _physical.positiveMass _physical.positiveGravity
  nlinarith

end PhyXMiniProblems.ProblemPhyXMini0787
