import Mathlib.Analysis.Real.Sqrt
import Physlib.ClassicalMechanics.RigidBody.KineticEnergy
import Physlib.Units.WithDim.Energy
import Physlib.Units.WithDim.Speed

/- USER: The assigned source file did not exist when this autoformalization task began. -/

noncomputable section

namespace PhyXMiniProblems.ProblemPhyXMini0824

open Dimension

/-!
# A solid cylinder descending while a fixed string unwinds

A massless string is wrapped around a uniform solid cylinder of mass `M` and
radius `R`.  Its free end is held stationary.  The cylinder is released from
rest at the figure's level `1`; as it descends to level `2`, the string
unwinds without slipping or stretching.  The vertical separation is `h`, and
the requested observable is the center-of-mass speed at level `2`.

Physical magnitudes use Physlib's unit-independent `Dimensionful` quantities.
Real numbers below are coherent SI readouts, dimensionless relations among
those readouts, and the coefficients printed in the answer choices.

Assumption/target split:

* `MatchesProblemStatement` records the solid cylinder, ideal string, held
  end, release from rest, and the fact that the level separation is `h`;
* `MatchesPrimaryFigure` records only labels and qualitative geometry visible
  in image `824.png`;
* `HasPhysicalParameters` records positivity of `M`, `R`, `g`, and `h`;
* `SatisfiesUnwindingSolidCylinderLaws` records the solid-cylinder inertia
  law, rigid-body kinetic energies, no-slip kinematics, gravitational energy
  loss, and conservation of mechanical energy;
* there are no previous-part results; and
* the squared-speed relation and the requested square-root speed occur only as
  conclusions of the derived lemma and final theorem.
-/

/-! ## Dimensionful quantities and coherent SI readouts -/

/-- Linear acceleration has physical dimension `L T⁻²`. -/
def accelerationDimension : Dimension := L𝓭 * T𝓭⁻¹ * T𝓭⁻¹

/-- Angular speed has inverse-time dimension because radians are dimensionless. -/
def angularSpeedDimension : Dimension := T𝓭⁻¹

/-- Axial moment of inertia has physical dimension `M L²`. -/
def momentOfInertiaDimension : Dimension := M𝓭 * L𝓭 * L𝓭

/-- A nonnegative physical mass, independent of the choice of units. -/
abbrev MassQuantity : Type :=
  Dimensionful (WithDim M𝓭 NNReal)

/-- A nonnegative physical length, used for `R`, `h`, and descent distance. -/
abbrev LengthQuantity : Type :=
  Dimensionful (WithDim L𝓭 NNReal)

/-- A nonnegative center-of-mass speed magnitude. -/
abbrev SpeedQuantity : Type := DimSpeed

/-- A nonnegative gravitational-acceleration magnitude. -/
abbrev AccelerationQuantity : Type :=
  Dimensionful (WithDim accelerationDimension NNReal)

/-- A nonnegative angular-speed magnitude. -/
abbrev AngularSpeedQuantity : Type :=
  Dimensionful (WithDim angularSpeedDimension NNReal)

/-- A nonnegative scalar moment of inertia about the cylinder axis. -/
abbrev MomentOfInertiaQuantity : Type :=
  Dimensionful (WithDim momentOfInertiaDimension NNReal)

/-- A physical energy with dimension `M L² T⁻²`. -/
abbrev EnergyQuantity : Type := DimEnergy

/-- Read a physical mass in kilograms. -/
def massInKilograms (mass : MassQuantity) : ℝ :=
  ((mass UnitChoices.SI).val : ℝ)

/-- Read a physical length in metres. -/
def lengthInMeters (length : LengthQuantity) : ℝ :=
  ((length UnitChoices.SI).val : ℝ)

/-- Read a center-of-mass speed in metres per second. -/
def speedInMetersPerSecond (speed : SpeedQuantity) : ℝ :=
  ((speed UnitChoices.SI).val : ℝ)

/-- Read gravitational acceleration in metres per second squared. -/
def accelerationInMetersPerSecondSquared
    (acceleration : AccelerationQuantity) : ℝ :=
  ((acceleration UnitChoices.SI).val : ℝ)

/-- Read angular speed in radians per second. -/
def angularSpeedInRadiansPerSecond
    (angularSpeed : AngularSpeedQuantity) : ℝ :=
  ((angularSpeed UnitChoices.SI).val : ℝ)

/-- Read axial moment of inertia in kilogram metres squared. -/
def momentOfInertiaInKilogramMetersSquared
    (inertia : MomentOfInertiaQuantity) : ℝ :=
  ((inertia UnitChoices.SI).val : ℝ)

/-- Read a physical energy in joules. -/
def energyInJoules (energy : EnergyQuantity) : ℝ :=
  (energy UnitChoices.SI).val /
    (DimEnergy.joule UnitChoices.SI).val

/-! ## Motion stages and primary-figure vocabulary -/

/-- The release level `1` and the lower observation level `2`. -/
inductive MotionStage where
  | levelOne
  | levelTwo
  deriving DecidableEq, Fintype, Repr

/-- Physical or graphical objects directly visible in image `824.png`. -/
inductive FigureObject where
  | cylinderAtLevelOne
  | cylinderAtLevelTwo
  | verticalString
  | holdingHand
  | downwardVelocityArrow
  | curvedAngularVelocityArrow
  deriving DecidableEq, Fintype, Repr

/-- Literal symbols and level markers directly visible in image `824.png`. -/
inductive FigureLabel where
  | radiusR
  | massM
  | levelOne
  | levelTwo
  | heightH
  | initialCenterOfMassSpeedZero
  | initialAngularSpeedZero
  | finalCenterOfMassSpeed
  | finalAngularSpeed
  deriving DecidableEq, Fintype, Repr

/-- The side of the cylinder on which the vertical string is tangent. -/
inductive CylinderSide where
  | left
  | right
  deriving DecidableEq, Repr

/-- Vertical directions used by the figure's displacement and velocity arrows. -/
inductive VerticalDirection where
  | upward
  | downward
  deriving DecidableEq, Repr

/-- Rotation sense as viewed in the plane of the supplied drawing. -/
inductive RotationSense where
  | clockwise
  | counterclockwise
  deriving DecidableEq, Repr

/-- Qualitative geometry and labels transcribed from the primary bitmap. -/
structure SuppliedYoYoFigure where
  showsObject : FigureObject → Bool
  showsLabel : FigureLabel → Bool
  stringIsVertical : Bool
  tangentSide : CylinderSide
  levelOneIsAboveLevelTwo : Bool
  displacementDirection : VerticalDirection
  finalVelocityDirection : VerticalDirection
  finalRotationSense : RotationSense

/-! ## Physical setup, supplied data, and governing laws -/

/-- The mass distribution of the cylindrical body. -/
inductive CylinderMassDistribution where
  | uniformSolidCylinder
  | other
  deriving DecidableEq, Repr

/-- Idealized mass model for the string. -/
inductive StringMassModel where
  | massless
  | massive
  deriving DecidableEq, Repr

/-- Whether the string can change its length. -/
inductive StringElasticityModel where
  | inextensible
  | extensible
  deriving DecidableEq, Repr

/-- Relative motion of the wrapped string and cylinder rim. -/
inductive StringCylinderContact where
  | wrappedWithoutSlip
  | slipping
  deriving DecidableEq, Repr

/-- Boundary condition imposed at the string's free end. -/
inductive FreeEndCondition where
  | heldStationary
  | moving
  deriving DecidableEq, Repr

/-- How the cylinder begins its motion. -/
inductive ReleaseProtocol where
  | releasedFromRest
  | externallyDriven
  deriving DecidableEq, Repr

/-!
The cylinder and its release-to-observation motion.  `heightH` and the
level-2 speed are independent observables constrained by the supplied data and
governing laws; neither is defined from an answer choice.
-/
structure UnwindingCylinderSetup where
  figure : SuppliedYoYoFigure
  cylinderMass : MassQuantity
  cylinderRadius : LengthQuantity
  gravitationalAcceleration : AccelerationQuantity
  heightH : LengthQuantity
  distanceDescended : MotionStage → LengthQuantity
  centerOfMassSpeed : MotionStage → SpeedQuantity
  angularSpeed : MotionStage → AngularSpeedQuantity
  gravitationalPotentialEnergyLost : MotionStage → EnergyQuantity
  translationalKineticEnergy : MotionStage → EnergyQuantity
  rotationalKineticEnergy : MotionStage → EnergyQuantity
  axialMomentOfInertia : MomentOfInertiaQuantity
  rigidBodySI : RigidBody 3
  symmetryAxis : Fin 3
  angularVelocityVector_rad_per_s : MotionStage → Fin 3 → ℝ
  massDistribution : CylinderMassDistribution
  stringMassModel : StringMassModel
  stringElasticityModel : StringElasticityModel
  stringCylinderContact : StringCylinderContact
  freeEndCondition : FreeEndCondition
  releaseProtocol : ReleaseProtocol

/-!
Every object and label in the primary image is present.  The string is
vertical and tangent on the cylinder's right; level `2` and the velocity arrow
are below level `1`.  The curved arrow in the bitmap is counterclockwise,
which is also the sense required for the right rim point to be instantaneously
at rest while the center moves downward.
-/
structure MatchesPrimaryFigure (setup : UnwindingCylinderSetup) : Prop where
  allObjectsAreShown :
    ∀ object : FigureObject, setup.figure.showsObject object = true
  allLabelsAreShown :
    ∀ label : FigureLabel, setup.figure.showsLabel label = true
  stringVertical : setup.figure.stringIsVertical = true
  stringTangentOnRight : setup.figure.tangentSide = .right
  levelOneAboveLevelTwo : setup.figure.levelOneIsAboveLevelTwo = true
  descentArrowPointsDown :
    setup.figure.displacementDirection = .downward
  velocityArrowPointsDown :
    setup.figure.finalVelocityDirection = .downward
  angularArrowIsCounterclockwise :
    setup.figure.finalRotationSense = .counterclockwise

/-!
Problem-text data and the initial readouts printed in the figure.  The
level-2 distance is identified with the independently stored figure height
`h`; no value for the level-2 speed is assumed.
-/
structure MatchesProblemStatement (setup : UnwindingCylinderSetup) : Prop where
  cylinderIsUniformAndSolid :
    setup.massDistribution = .uniformSolidCylinder
  stringIsMassless : setup.stringMassModel = .massless
  stringDoesNotStretch :
    setup.stringElasticityModel = .inextensible
  stringUnwindsWithoutSlip :
    setup.stringCylinderContact = .wrappedWithoutSlip
  freeEndIsHeldStationary :
    setup.freeEndCondition = .heldStationary
  cylinderIsReleasedFromRest :
    setup.releaseProtocol = .releasedFromRest
  levelOneDistanceIsZero :
    lengthInMeters (setup.distanceDescended .levelOne) = 0
  levelTwoDistanceIsHeightH :
    lengthInMeters (setup.distanceDescended .levelTwo) =
      lengthInMeters setup.heightH
  levelOneCenterOfMassSpeedIsZero :
    speedInMetersPerSecond (setup.centerOfMassSpeed .levelOne) = 0
  levelOneAngularSpeedIsZero :
    angularSpeedInRadiansPerSecond (setup.angularSpeed .levelOne) = 0

/-- Positivity and nondegeneracy of the independent physical parameters. -/
structure HasPhysicalParameters (setup : UnwindingCylinderSetup) : Prop where
  cylinderMassPositive : 0 < massInKilograms setup.cylinderMass
  cylinderRadiusPositive : 0 < lengthInMeters setup.cylinderRadius
  gravitationalAccelerationPositive :
    0 < accelerationInMetersPerSecondSquared
      setup.gravitationalAcceleration
  heightPositive : 0 < lengthInMeters setup.heightH

/-!
The governing mechanics of the idealized cylinder-string system:

* a uniform solid cylinder has axial inertia `I = M R² / 2`;
* translational kinetic energy is `M v² / 2`;
* rotational kinetic energy is Physlib's contraction `ω · (Iω) / 2`;
* because the held string is stationary and does not slip, `v = R ω`;
* gravitational potential-energy loss is `M g y`; and
* with release from rest and no dissipative losses, that loss equals the sum
  of translational and rotational kinetic energies.

No field states the requested level-2 speed or its squared value.
-/
structure SatisfiesUnwindingSolidCylinderLaws
    (setup : UnwindingCylinderSetup) : Prop where
  rigidBodyMassMatchesCylinderMass :
    setup.rigidBodySI.mass = massInKilograms setup.cylinderMass
  angularVelocityIsAlongSymmetryAxis :
    ∀ (stage : MotionStage) (component : Fin 3),
      setup.angularVelocityVector_rad_per_s stage component =
        if component = setup.symmetryAxis then
          angularSpeedInRadiansPerSecond (setup.angularSpeed stage)
        else 0
  axialInertiaTensorEntry :
    setup.rigidBodySI.inertiaTensor setup.symmetryAxis setup.symmetryAxis =
      momentOfInertiaInKilogramMetersSquared setup.axialMomentOfInertia
  uniformSolidCylinderAxialInertia :
    momentOfInertiaInKilogramMetersSquared setup.axialMomentOfInertia =
      (1 / 2 : ℝ) * massInKilograms setup.cylinderMass *
        lengthInMeters setup.cylinderRadius ^ 2
  translationalKineticEnergyLaw :
    ∀ stage : MotionStage,
      energyInJoules (setup.translationalKineticEnergy stage) =
        (1 / 2 : ℝ) * massInKilograms setup.cylinderMass *
          speedInMetersPerSecond (setup.centerOfMassSpeed stage) ^ 2
  rotationalKineticEnergyUsesPhyslib :
    ∀ stage : MotionStage,
      energyInJoules (setup.rotationalKineticEnergy stage) =
        setup.rigidBodySI.rotationalKineticEnergy
          (setup.angularVelocityVector_rad_per_s stage)
  noSlipUnwindingKinematics :
    ∀ stage : MotionStage,
      speedInMetersPerSecond (setup.centerOfMassSpeed stage) =
        lengthInMeters setup.cylinderRadius *
          angularSpeedInRadiansPerSecond (setup.angularSpeed stage)
  gravitationalPotentialEnergyLossLaw :
    ∀ stage : MotionStage,
      energyInJoules (setup.gravitationalPotentialEnergyLost stage) =
        massInKilograms setup.cylinderMass *
          accelerationInMetersPerSecondSquared
            setup.gravitationalAcceleration *
          lengthInMeters (setup.distanceDescended stage)
  mechanicalEnergyConservationFromRest :
    ∀ stage : MotionStage,
      energyInJoules (setup.gravitationalPotentialEnergyLost stage) =
        energyInJoules (setup.translationalKineticEnergy stage) +
          energyInJoules (setup.rotationalKineticEnergy stage)

/-! ## Derived speed and displayed answer metadata -/

/-!
Energy conservation, `I = M R² / 2`, and `v = R ω` imply
`v_cm² = (4/3) g h` at level `2`.
-/
lemma centerOfMassSpeed_squared_after_descent
    (setup : UnwindingCylinderSetup)
    (_data : MatchesProblemStatement setup)
    (_physical : HasPhysicalParameters setup)
    (_laws : SatisfiesUnwindingSolidCylinderLaws setup) :
    speedInMetersPerSecond (setup.centerOfMassSpeed .levelTwo) ^ 2 =
      (4 / 3 : ℝ) *
        accelerationInMetersPerSecondSquared
          setup.gravitationalAcceleration *
        lengthInMeters setup.heightH := by
  have hrot :
      energyInJoules (setup.rotationalKineticEnergy .levelTwo) =
        (1 / 2 : ℝ) *
          momentOfInertiaInKilogramMetersSquared
            setup.axialMomentOfInertia *
          angularSpeedInRadiansPerSecond
            (setup.angularSpeed .levelTwo) ^ 2 := by
    calc
      energyInJoules (setup.rotationalKineticEnergy .levelTwo) =
          setup.rigidBodySI.rotationalKineticEnergy
            (setup.angularVelocityVector_rad_per_s .levelTwo) :=
        _laws.rotationalKineticEnergyUsesPhyslib .levelTwo
      _ = (1 / 2 : ℝ) *
          momentOfInertiaInKilogramMetersSquared
            setup.axialMomentOfInertia *
          angularSpeedInRadiansPerSecond
            (setup.angularSpeed .levelTwo) ^ 2 := by
        rw [RigidBody.rotationalKineticEnergy]
        simp only [dotProduct, Matrix.mulVec]
        rw [Finset.sum_eq_single setup.symmetryAxis]
        · rw [Finset.sum_eq_single setup.symmetryAxis]
          · simp only [_laws.angularVelocityIsAlongSymmetryAxis, if_pos,
              _laws.axialInertiaTensorEntry]
            ring
          · intro component _ hcomponent
            simp [_laws.angularVelocityIsAlongSymmetryAxis, hcomponent]
          · simp
        · intro component _ hcomponent
          simp [_laws.angularVelocityIsAlongSymmetryAxis, hcomponent]
        · simp
  have henergy :=
    _laws.mechanicalEnergyConservationFromRest .levelTwo
  rw [_laws.gravitationalPotentialEnergyLossLaw .levelTwo,
      _laws.translationalKineticEnergyLaw .levelTwo,
      hrot,
      _data.levelTwoDistanceIsHeightH,
      _laws.uniformSolidCylinderAxialInertia] at henergy
  have hkinematics :=
    _laws.noSlipUnwindingKinematics .levelTwo
  rw [hkinematics] at henergy ⊢
  nlinarith [_physical.cylinderMassPositive]

/-- Labels of the four answer choices printed in the problem. -/
inductive AnswerChoice where
  | A
  | B
  | C
  | D
  deriving DecidableEq, Fintype, Repr

/-- The dimensionless coefficient of `g h` printed under each square root. -/
def AnswerChoice.speedSquaredCoefficient : AnswerChoice → ℝ
  | .A => 4 / 5
  | .B => 4 / 3
  | .C => 2 / 3
  | .D => 2 / 5

/-- Dataset metadata recording the supplied answer label. -/
def recordedAnswerChoice : AnswerChoice := .B

/-!
After the cylinder descends through the figure height `h`, its center-of-mass
speed is `sqrt ((4/3) g h)`.  This is answer choice `B` and formalizes
blueprint label `thm:physics:phyx_mini_0824:target`.
-/
theorem centerOfMassSpeed_after_descent
    (setup : UnwindingCylinderSetup)
    (_figure : MatchesPrimaryFigure setup)
    (_data : MatchesProblemStatement setup)
    (_physical : HasPhysicalParameters setup)
    (_laws : SatisfiesUnwindingSolidCylinderLaws setup) :
    speedInMetersPerSecond (setup.centerOfMassSpeed .levelTwo) =
      Real.sqrt
        ((4 / 3 : ℝ) *
          accelerationInMetersPerSecondSquared
            setup.gravitationalAcceleration *
          lengthInMeters setup.heightH) := by
  have hsq :=
    centerOfMassSpeed_squared_after_descent
      setup _data _physical _laws
  have hnonneg :
      0 ≤ speedInMetersPerSecond
        (setup.centerOfMassSpeed .levelTwo) :=
    NNReal.coe_nonneg _
  rw [← hsq, Real.sqrt_sq hnonneg]

end PhyXMiniProblems.ProblemPhyXMini0824
