import Mathlib
import Physlib.ClassicalMechanics.HarmonicOscillator.Basic
import Physlib.ClassicalMechanics.RigidBody.KineticEnergy
import Physlib.Units.WithDim.Energy
import Physlib.Units.WithDim.Speed

/-!
# Rotational kinetic energy of a spring-driven rolling solid cylinder

A solid cylinder of mass `M` is joined at its axle to a horizontal spring of
stiffness `k`.  It is released from rest after the spring has been stretched
and rolls without slipping until it passes through the spring's equilibrium
position.

The physical magnitudes below use Physlib's unit-independent dimensional
quantities.  Real numbers occur only as coherent SI readouts, three-dimensional
coordinate components required by Physlib's rigid-body API, and the numerical
answer choices.  Spring and rotational energies are connected respectively to
`ClassicalMechanics.HarmonicOscillator.potentialEnergy` and
`RigidBody.rotationalKineticEnergy`; neither requested numerical value is put
in the setup or the governing-law structure.
-/

noncomputable section

namespace PhyXMiniProblems.ProblemPhyXMini0279

open Dimension

/-! ## Dimensionful physical quantities and SI readouts -/

/-- The nonnegative physical mass of the solid cylinder. -/
abbrev MassQuantity : Type :=
  Dimensionful (WithDim M𝓭 NNReal)

/-- A nonnegative length magnitude, used for radius and spring extension. -/
abbrev LengthQuantity : Type :=
  Dimensionful (WithDim L𝓭 NNReal)

/-- A nonnegative speed magnitude. -/
abbrev SpeedQuantity : Type := DimSpeed

/-- Angular-speed magnitude, with dimension inverse time. -/
abbrev AngularSpeedQuantity : Type :=
  Dimensionful (WithDim T𝓭⁻¹ NNReal)

/-- Spring stiffness, of dimension force per length, equivalently `M T⁻²`. -/
abbrev SpringConstantQuantity : Type :=
  Dimensionful (WithDim (M𝓭 * T𝓭⁻¹ * T𝓭⁻¹) NNReal)

/-- Axial moment of inertia, with dimension `M L²`. -/
abbrev MomentOfInertiaQuantity : Type :=
  Dimensionful (WithDim (M𝓭 * L𝓭 * L𝓭) NNReal)

/-- Physical energy, with dimension `M L² T⁻²`. -/
abbrev EnergyQuantity : Type := DimEnergy

/-- Kilogram readout of a physical mass. -/
def massInKilograms (mass : MassQuantity) : ℝ :=
  ((mass UnitChoices.SI).val : ℝ)

/-- Metre readout of a physical length magnitude. -/
def lengthInMeters (length : LengthQuantity) : ℝ :=
  ((length UnitChoices.SI).val : ℝ)

/-- Metre-per-second readout of a physical speed magnitude. -/
def speedInMetersPerSecond (speed : SpeedQuantity) : ℝ :=
  ((speed UnitChoices.SI).val : ℝ)

/-- Radian-per-second readout of an angular-speed magnitude. -/
def angularSpeedInRadiansPerSecond
    (angularSpeed : AngularSpeedQuantity) : ℝ :=
  ((angularSpeed UnitChoices.SI).val : ℝ)

/-- Newton-per-metre readout of a physical spring stiffness. -/
def springConstantInNewtonsPerMeter
    (springConstant : SpringConstantQuantity) : ℝ :=
  ((springConstant UnitChoices.SI).val : ℝ)

/-- Kilogram-metre-squared readout of a moment of inertia. -/
def momentOfInertiaInKilogramMetersSquared
    (inertia : MomentOfInertiaQuantity) : ℝ :=
  ((inertia UnitChoices.SI).val : ℝ)

/-- Joule readout of a physical energy. -/
def energyInJoules (energy : EnergyQuantity) : ℝ :=
  (energy UnitChoices.SI).val

/-! ## Motion events and primary-figure labels -/

/-- The two instants compared by conservation of mechanical energy. -/
inductive MotionEvent where
  | release
  | equilibriumPassage
  deriving DecidableEq, Repr

/-- Physical objects visible in the supplied bitmap. -/
inductive FigureObject where
  | solidCylinder
  | cylinderAxle
  | spring
  | verticalWall
  | horizontalSurface
  deriving DecidableEq, Repr

/-- Mathematical labels printed in the supplied bitmap. -/
inductive FigureLabel where
  | cylinderMassM
  | springConstantK
  deriving DecidableEq, Repr

/-- Endpoints of the spring visible in the figure. -/
inductive SpringEndpoint where
  | cylinderAxle
  | wallAnchor
  deriving DecidableEq, Repr

/-- Orientation categories needed to transcribe the support and spring. -/
inductive Orientation where
  | horizontal
  | vertical
  deriving DecidableEq, Repr

/-- Sense of the curved rotation arrow in the primary bitmap. -/
inductive RotationSense where
  | clockwise
  | counterclockwise
  deriving DecidableEq, Repr

/-- The mass distribution stated in the problem text. -/
inductive CylinderShape where
  | solidCircularCylinder
  | thinCylindricalShell
  deriving DecidableEq, Repr

/-- Contact regime between the cylinder and the supporting surface. -/
inductive SurfaceContact where
  | rollingWithoutSlip
  | slipping
  deriving DecidableEq, Repr

/-- How the spring-cylinder system begins its motion. -/
inductive ReleaseProtocol where
  | releasedFromRest
  | externallyDriven
  deriving DecidableEq, Repr

/-- Qualitative information read directly from the primary bitmap. -/
structure RollingCylinderFigure where
  showsObject : FigureObject → Bool
  showsLabel : FigureLabel → Bool
  labelRefersTo : FigureLabel → FigureObject
  springEndpoints : SpringEndpoint × SpringEndpoint
  springOrientation : Orientation
  supportOrientation : Orientation
  cylinderTouchesSupport : Bool
  cylinderLiesLeftOfWall : Bool
  springIsAttachedAtCylinderAxle : Bool
  rotationArrowSense : RotationSense

/-! ## Physical setup, problem data, and governing laws -/

/-!
The independent physical quantities for the rolling cylinder at release and
at the subsequent equilibrium passage.

The Physlib harmonic oscillator is an SI-coordinate model for the effective
one-dimensional rolling mode.  The Physlib rigid body and its angular-velocity
vector model the cylinder's rotation in three-dimensional SI coordinates.
Neither library object is defined from the requested energy.
-/
structure RollingCylinderSpringSetup where
  figure : RollingCylinderFigure
  cylinderMass : MassQuantity
  cylinderRadius : LengthQuantity
  springConstant_k : SpringConstantQuantity
  springExtension : MotionEvent → LengthQuantity
  centerOfMassSpeed : MotionEvent → SpeedQuantity
  angularSpeed : MotionEvent → AngularSpeedQuantity
  springPotentialEnergy : MotionEvent → EnergyQuantity
  translationalKineticEnergy : MotionEvent → EnergyQuantity
  rotationalKineticEnergy : MotionEvent → EnergyQuantity
  axialMomentOfInertia : MomentOfInertiaQuantity
  effectiveOscillatorSI : ClassicalMechanics.HarmonicOscillator
  oscillatorDisplacementVector_m :
    MotionEvent → EuclideanSpace ℝ (Fin 1)
  rigidBodySI : RigidBody 3
  rollingAxis : Fin 3
  angularVelocityVector_rad_per_s : MotionEvent → Fin 3 → ℝ
  cylinderShape : CylinderShape
  surfaceContact : SurfaceContact
  releaseProtocol : ReleaseProtocol

/-!
Primary-image evidence.  The mass label `M` is above the orange cylinder, the
stiffness label `k` is above the spring, the spring joins the black axle to the
right wall, and the cylinder rests on a horizontal surface.  On the left side
of a wheel, the upward-pointing curved arrow is clockwise; this primary-image
readout takes precedence over the auxiliary caption's opposite description.
-/
structure MatchesPrimaryFigure
    (setup : RollingCylinderSpringSetup) : Prop where
  allObjectsShown :
    ∀ object : FigureObject, setup.figure.showsObject object = true
  allLabelsShown :
    ∀ label : FigureLabel, setup.figure.showsLabel label = true
  massLabelRefersToCylinder :
    setup.figure.labelRefersTo .cylinderMassM = .solidCylinder
  stiffnessLabelRefersToSpring :
    setup.figure.labelRefersTo .springConstantK = .spring
  axleToWallSpring :
    setup.figure.springEndpoints = (.cylinderAxle, .wallAnchor)
  springIsHorizontal : setup.figure.springOrientation = .horizontal
  supportIsHorizontal : setup.figure.supportOrientation = .horizontal
  cylinderTouchesSurface : setup.figure.cylinderTouchesSupport = true
  cylinderIsLeftOfWall : setup.figure.cylinderLiesLeftOfWall = true
  centerAttachmentVisible :
    setup.figure.springIsAttachedAtCylinderAxle = true
  arrowIsClockwise : setup.figure.rotationArrowSense = .clockwise

/-!
Numerical and qualitative data supplied by the problem.  The initial stretch
`0.250 m` is represented exactly by `1/4 m`; the equilibrium passage has zero
spring extension.  Release from rest is recorded by both the center-of-mass
and angular-speed readouts.
-/
structure MatchesProblemData
    (setup : RollingCylinderSpringSetup) : Prop where
  stiffnessReadout :
    springConstantInNewtonsPerMeter setup.springConstant_k = 3
  initialStretchReadout :
    lengthInMeters (setup.springExtension .release) = 1 / 4
  releaseCenterOfMassSpeedIsZero :
    speedInMetersPerSecond (setup.centerOfMassSpeed .release) = 0
  releaseAngularSpeedIsZero :
    angularSpeedInRadiansPerSecond (setup.angularSpeed .release) = 0
  equilibriumExtensionIsZero :
    lengthInMeters (setup.springExtension .equilibriumPassage) = 0
  cylinderIsSolid : setup.cylinderShape = .solidCircularCylinder
  rollsWithoutSlipping : setup.surfaceContact = .rollingWithoutSlip
  systemIsReleasedFromRest : setup.releaseProtocol = .releasedFromRest

/-- Positivity and nondegeneracy of the physical parameters. -/
structure HasPhysicalParameters
    (setup : RollingCylinderSpringSetup) : Prop where
  cylinderMassPositive : 0 < massInKilograms setup.cylinderMass
  cylinderRadiusPositive : 0 < lengthInMeters setup.cylinderRadius
  springConstantPositive :
    0 < springConstantInNewtonsPerMeter setup.springConstant_k
  initialStretchPositive :
    0 < lengthInMeters (setup.springExtension .release)

/-!
The governing spring, rigid-body, rolling, and conservation laws.

* Physlib's oscillator gives the Hooke-law spring potential energy.
* The solid-cylinder axial inertia is `I = M R² / 2`.
* Physlib's rigid-body definition gives rotational kinetic energy from the
  inertia tensor and the angular-velocity vector.
* Translation has kinetic energy `M v² / 2`, and no slip gives `v = R ω`.
* Total spring-plus-translational-plus-rotational mechanical energy agrees at
  release and at the equilibrium passage.

These laws quantify over the two motion events and never state the requested
`0.03125 J` rotational-energy readout.
-/
structure SatisfiesRollingCylinderSpringLaws
    (setup : RollingCylinderSpringSetup) : Prop where
  effectiveOscillatorMass :
    setup.effectiveOscillatorSI.m =
      massInKilograms setup.cylinderMass +
        momentOfInertiaInKilogramMetersSquared setup.axialMomentOfInertia /
          lengthInMeters setup.cylinderRadius ^ 2
  effectiveOscillatorStiffness :
    setup.effectiveOscillatorSI.k =
      springConstantInNewtonsPerMeter setup.springConstant_k
  oscillatorCoordinateMatchesExtension :
    ∀ event : MotionEvent,
      setup.oscillatorDisplacementVector_m event 0 =
        lengthInMeters (setup.springExtension event)
  springPotentialEnergyUsesPhyslib :
    ∀ event : MotionEvent,
      energyInJoules (setup.springPotentialEnergy event) =
        setup.effectiveOscillatorSI.potentialEnergy
          (setup.oscillatorDisplacementVector_m event)
  rigidBodyMassMatchesCylinderMass :
    setup.rigidBodySI.mass = massInKilograms setup.cylinderMass
  angularVelocityIsAlongRollingAxis :
    ∀ (event : MotionEvent) (component : Fin 3),
      setup.angularVelocityVector_rad_per_s event component =
        if component = setup.rollingAxis then
          angularSpeedInRadiansPerSecond (setup.angularSpeed event)
        else 0
  axialInertiaTensorEntry :
    setup.rigidBodySI.inertiaTensor setup.rollingAxis setup.rollingAxis =
      momentOfInertiaInKilogramMetersSquared setup.axialMomentOfInertia
  solidCylinderAxialInertia :
    momentOfInertiaInKilogramMetersSquared setup.axialMomentOfInertia =
      (1 / 2 : ℝ) * massInKilograms setup.cylinderMass *
        lengthInMeters setup.cylinderRadius ^ 2
  translationalKineticEnergyLaw :
    ∀ event : MotionEvent,
      energyInJoules (setup.translationalKineticEnergy event) =
        (1 / 2 : ℝ) * massInKilograms setup.cylinderMass *
          speedInMetersPerSecond (setup.centerOfMassSpeed event) ^ 2
  rotationalKineticEnergyUsesPhyslib :
    ∀ event : MotionEvent,
      energyInJoules (setup.rotationalKineticEnergy event) =
        setup.rigidBodySI.rotationalKineticEnergy
          (setup.angularVelocityVector_rad_per_s event)
  rollingWithoutSlipKinematics :
    ∀ event : MotionEvent,
      speedInMetersPerSecond (setup.centerOfMassSpeed event) =
        lengthInMeters setup.cylinderRadius *
          angularSpeedInRadiansPerSecond (setup.angularSpeed event)
  mechanicalEnergyConservation :
    energyInJoules (setup.springPotentialEnergy .release) +
          energyInJoules (setup.translationalKineticEnergy .release) +
        energyInJoules (setup.rotationalKineticEnergy .release) =
      energyInJoules (setup.springPotentialEnergy .equilibriumPassage) +
          energyInJoules
            (setup.translationalKineticEnergy .equilibriumPassage) +
        energyInJoules (setup.rotationalKineticEnergy .equilibriumPassage)

/-! ## Derived relations and answer metadata -/

/-- The initially stretched spring stores `3/32 J`. -/
lemma initialSpringPotentialEnergy_eq_three_over_thirtyTwo
    (setup : RollingCylinderSpringSetup)
    (_data : MatchesProblemData setup)
    (_laws : SatisfiesRollingCylinderSpringLaws setup) :
    energyInJoules (setup.springPotentialEnergy .release) = 3 / 32 := by
  rw [_laws.springPotentialEnergyUsesPhyslib,
    ClassicalMechanics.HarmonicOscillator.potentialEnergy,
    _laws.effectiveOscillatorStiffness, _data.stiffnessReadout]
  simp only [smul_eq_mul]
  rw [PiLp.inner_apply]
  simp only [Fin.sum_univ_one, Real.inner_apply]
  rw [_laws.oscillatorCoordinateMatchesExtension,
    _data.initialStretchReadout]
  norm_num

/-!
For a rolling solid cylinder, rotational kinetic energy is one third of the
kinetic energy present at equilibrium, hence one third of the initially
stored spring energy in this lossless release.
-/
lemma rotationalKineticEnergy_is_oneThird_initialSpringEnergy
    (setup : RollingCylinderSpringSetup)
    (_data : MatchesProblemData setup)
    (_physical : HasPhysicalParameters setup)
    (_laws : SatisfiesRollingCylinderSpringLaws setup) :
    energyInJoules
        (setup.rotationalKineticEnergy .equilibriumPassage) =
      energyInJoules (setup.springPotentialEnergy .release) / 3 := by
  have rotationalKineticEnergyLaw (event : MotionEvent) :
      energyInJoules (setup.rotationalKineticEnergy event) =
        (1 / 2 : ℝ) *
          momentOfInertiaInKilogramMetersSquared
            setup.axialMomentOfInertia *
          angularSpeedInRadiansPerSecond (setup.angularSpeed event) ^ 2 := by
    rw [_laws.rotationalKineticEnergyUsesPhyslib,
      RigidBody.rotationalKineticEnergy]
    simp only [dotProduct, Matrix.mulVec,
      _laws.angularVelocityIsAlongRollingAxis]
    simp [_laws.axialInertiaTensorEntry]
    ring
  have equilibriumSpringPotentialEnergyIsZero :
      energyInJoules
          (setup.springPotentialEnergy .equilibriumPassage) = 0 := by
    rw [_laws.springPotentialEnergyUsesPhyslib,
      ClassicalMechanics.HarmonicOscillator.potentialEnergy]
    simp only [smul_eq_mul]
    rw [PiLp.inner_apply]
    simp only [Fin.sum_univ_one, Real.inner_apply]
    rw [_laws.oscillatorCoordinateMatchesExtension,
      _data.equilibriumExtensionIsZero]
    ring
  have releaseTranslationalKineticEnergyIsZero :
      energyInJoules
          (setup.translationalKineticEnergy .release) = 0 := by
    rw [_laws.translationalKineticEnergyLaw,
      _data.releaseCenterOfMassSpeedIsZero]
    ring
  have releaseRotationalKineticEnergyIsZero :
      energyInJoules
          (setup.rotationalKineticEnergy .release) = 0 := by
    rw [rotationalKineticEnergyLaw,
      _data.releaseAngularSpeedIsZero]
    ring
  have equilibriumTranslationalEnergyIsTwiceRotational :
      energyInJoules
          (setup.translationalKineticEnergy .equilibriumPassage) =
        2 * energyInJoules
          (setup.rotationalKineticEnergy .equilibriumPassage) := by
    rw [_laws.translationalKineticEnergyLaw,
      _laws.rollingWithoutSlipKinematics,
      rotationalKineticEnergyLaw,
      _laws.solidCylinderAxialInertia]
    ring
  have energyConservation := _laws.mechanicalEnergyConservation
  rw [releaseTranslationalKineticEnergyIsZero,
    releaseRotationalKineticEnergyIsZero,
    equilibriumSpringPotentialEnergyIsZero,
    equilibriumTranslationalEnergyIsTwiceRotational] at energyConservation
  linarith

/-- Labels of the four displayed answer choices. -/
inductive AnswerChoice where
  | A
  | B
  | C
  | D
  deriving DecidableEq, Repr

/-- Rotational-energy readout in joules printed beside each answer label. -/
def AnswerChoice.joules : AnswerChoice → ℝ
  | .A => 2225 / 100000
  | .B => 2825 / 100000
  | .C => 3625 / 100000
  | .D => 3125 / 100000

/-- Dataset metadata recording the supplied answer label. -/
def recordedAnswerChoice : AnswerChoice := .D

/-- A physical energy agrees exactly with the value printed for a choice. -/
def MatchesDisplayedEnergy
    (energy : EnergyQuantity) (choice : AnswerChoice) : Prop :=
  energyInJoules energy = choice.joules

/-!
At the equilibrium passage, conservation of energy and rolling without slip
give the solid cylinder rotational kinetic energy

`K_rot = (1/3) (1/2 k x₀²) = 1/32 J = 0.03125 J`,

which is answer choice `D`.

This formalizes blueprint label `thm:physics:phyx_mini_0279:target`.
-/
theorem rotationalKineticEnergyAtEquilibrium_eq_one_over_thirtyTwo
    (setup : RollingCylinderSpringSetup)
    (_figure : MatchesPrimaryFigure setup)
    (_data : MatchesProblemData setup)
    (_physical : HasPhysicalParameters setup)
    (_laws : SatisfiesRollingCylinderSpringLaws setup) :
    energyInJoules
        (setup.rotationalKineticEnergy .equilibriumPassage) =
      1 / 32 := by
  calc
    energyInJoules
          (setup.rotationalKineticEnergy .equilibriumPassage) =
        energyInJoules (setup.springPotentialEnergy .release) / 3 :=
      rotationalKineticEnergy_is_oneThird_initialSpringEnergy
        setup _data _physical _laws
    _ = (3 / 32 : ℝ) / 3 := by
      rw [initialSpringPotentialEnergy_eq_three_over_thirtyTwo
        setup _data _laws]
    _ = 1 / 32 := by norm_num

/-- The same physical conclusion expressed using the recorded answer label. -/
theorem rotationalKineticEnergyAtEquilibrium_matches_answerD
    (setup : RollingCylinderSpringSetup)
    (_figure : MatchesPrimaryFigure setup)
    (_data : MatchesProblemData setup)
    (_physical : HasPhysicalParameters setup)
    (_laws : SatisfiesRollingCylinderSpringLaws setup) :
    MatchesDisplayedEnergy
      (setup.rotationalKineticEnergy .equilibriumPassage) .D := by
  unfold MatchesDisplayedEnergy AnswerChoice.joules
  rw [rotationalKineticEnergyAtEquilibrium_eq_one_over_thirtyTwo
    setup _figure _data _physical _laws]
  norm_num

end PhyXMiniProblems.ProblemPhyXMini0279
