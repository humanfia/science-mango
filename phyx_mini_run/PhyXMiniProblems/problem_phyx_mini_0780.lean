import Mathlib
import Physlib.ClassicalMechanics.RigidBody.KineticEnergy
import Physlib.Units.WithDim.Energy
import Physlib.Units.WithDim.Speed

/-!
# A hollow cylinder falling while a string unwinds

A thin, light string is wrapped around the outer rim of a uniform hollow
cylinder.  The string's upper end is fixed, and the cylinder is released from
rest.  The supplied figure marks the inner radius as `20.0 cm` and the outer
radius as `35.0 cm`; the cylinder's mass is `4.75 kg`.  The problem asks for
the distance fallen when the center-of-mass speed reaches `6.66 m/s`.

Physical magnitudes are represented by Physlib's unit-independent
dimensionful quantities.  Real numbers below are coherent-SI readouts and the
displayed numerical answer choices.  The model records the hollow-cylinder
moment-of-inertia law, no-slip unwinding, gravitational energy loss, rigid-body
rotational kinetic energy, and conservation of mechanical energy explicitly.
The requested distance is not a premise of any of those laws.
-/

noncomputable section

namespace PhyXMiniProblems.ProblemPhyXMini0780

open Dimension

/-! ## Dimensionful physical quantities and SI readouts -/

/-- The nonnegative physical mass of the hollow cylinder. -/
abbrev MassQuantity : Type :=
  Dimensionful (WithDim M𝓭 NNReal)

/-- A nonnegative length magnitude, used for both radii and fall distance. -/
abbrev LengthQuantity : Type :=
  Dimensionful (WithDim L𝓭 NNReal)

/-- A nonnegative center-of-mass speed magnitude. -/
abbrev SpeedQuantity : Type := DimSpeed

/-- An angular-speed magnitude, with physical dimension inverse time. -/
abbrev AngularSpeedQuantity : Type :=
  Dimensionful (WithDim T𝓭⁻¹ NNReal)

/-- An acceleration magnitude, with physical dimension `L T⁻²`. -/
abbrev AccelerationQuantity : Type :=
  Dimensionful (WithDim (L𝓭 * T𝓭⁻¹ * T𝓭⁻¹) NNReal)

/-- A scalar moment of inertia about the cylinder's symmetry axis. -/
abbrev MomentOfInertiaQuantity : Type :=
  Dimensionful (WithDim (M𝓭 * L𝓭 * L𝓭) NNReal)

/-- A real-valued physical energy. -/
abbrev EnergyQuantity : Type := DimEnergy

/-- Kilogram readout of a physical mass. -/
def massInKilograms (mass : MassQuantity) : ℝ :=
  ((mass UnitChoices.SI).val : ℝ)

/-- Metre readout of a physical length. -/
def lengthInMeters (length : LengthQuantity) : ℝ :=
  ((length UnitChoices.SI).val : ℝ)

/-- Metre-per-second readout of a physical speed. -/
def speedInMetersPerSecond (speed : SpeedQuantity) : ℝ :=
  ((speed UnitChoices.SI).val : ℝ)

/-- Radian-per-second readout of an angular-speed magnitude. -/
def angularSpeedInRadiansPerSecond
    (angularSpeed : AngularSpeedQuantity) : ℝ :=
  ((angularSpeed UnitChoices.SI).val : ℝ)

/-- Metre-per-second-squared readout of an acceleration magnitude. -/
def accelerationInMetersPerSecondSquared
    (acceleration : AccelerationQuantity) : ℝ :=
  ((acceleration UnitChoices.SI).val : ℝ)

/-- Kilogram-metre-squared readout of a scalar moment of inertia. -/
def momentOfInertiaInKilogramMetersSquared
    (inertia : MomentOfInertiaQuantity) : ℝ :=
  ((inertia UnitChoices.SI).val : ℝ)

/-- Joule readout of a physical energy. -/
def energyInJoules (energy : EnergyQuantity) : ℝ :=
  (energy UnitChoices.SI).val

/-! ## Motion events and primary-figure labels -/

/-- The release event and the later event specified by the target speed. -/
inductive MotionEvent where
  | release
  | targetSpeedReached
  deriving DecidableEq, Repr

/-- Physical objects visible in the supplied bitmap. -/
inductive FigureObject where
  | hollowCylinder
  | centralHole
  | string
  | overheadSupport
  deriving DecidableEq, Repr

/-- The two numerical radius labels printed in the supplied bitmap. -/
inductive FigureLabel where
  | innerRadius20cm
  | outerRadius35cm
  deriving DecidableEq, Repr

/-- Which cylindrical surface a radius label identifies. -/
inductive RadiusKind where
  | inner
  | outer
  deriving DecidableEq, Repr

/-- Orientations needed to transcribe the string and support. -/
inductive Orientation where
  | horizontal
  | vertical
  deriving DecidableEq, Repr

/-- Direct qualitative and label evidence from the primary bitmap. -/
structure HollowCylinderFigure where
  showsObject : FigureObject → Bool
  showsLabel : FigureLabel → Bool
  labelRefersTo : FigureLabel → RadiusKind
  stringOrientation : Orientation
  supportOrientation : Orientation
  stringTouchesOuterRim : Bool
  stringUpperEndTouchesSupport : Bool

/-! ## Physical setup, problem data, and governing laws -/

/-- The cylinder's mass distribution stated in the problem. -/
inductive CylinderMassDistribution where
  | uniformHollowCylinder
  | nonuniformHollowCylinder
  deriving DecidableEq, Repr

/-- Idealized string-mass models. -/
inductive StringMassModel where
  | lightWithNegligibleMass
  | massive
  deriving DecidableEq, Repr

/-- Idealized transverse-thickness models for the string. -/
inductive StringThicknessModel where
  | thin
  | finiteThickness
  deriving DecidableEq, Repr

/-- How the string and cylinder move relative to one another. -/
inductive StringContactRegime where
  | wrappedAroundOuterRimWithoutSlip
  | slippingOnOuterRim
  deriving DecidableEq, Repr

/-- How the cylinder begins its motion. -/
inductive ReleaseProtocol where
  | releasedFromRest
  | externallyDriven
  deriving DecidableEq, Repr

/-!
The physical quantities and SI rigid-body data used to model the two events.
The fall distance is an independent physical quantity: it is not defined from
the requested `3.76 m` answer.
-/
structure FallingHollowCylinderSetup where
  figure : HollowCylinderFigure
  cylinderMass : MassQuantity
  innerRadius : LengthQuantity
  outerRadius : LengthQuantity
  gravitationalAcceleration : AccelerationQuantity
  distanceFallen : MotionEvent → LengthQuantity
  centerOfMassSpeed : MotionEvent → SpeedQuantity
  angularSpeed : MotionEvent → AngularSpeedQuantity
  gravitationalPotentialEnergyLost : MotionEvent → EnergyQuantity
  translationalKineticEnergy : MotionEvent → EnergyQuantity
  rotationalKineticEnergy : MotionEvent → EnergyQuantity
  axialMomentOfInertia : MomentOfInertiaQuantity
  rigidBodySI : RigidBody 3
  centralSymmetryAxis : Fin 3
  angularVelocityVector_rad_per_s : MotionEvent → Fin 3 → ℝ
  massDistribution : CylinderMassDistribution
  stringMassModel : StringMassModel
  stringThicknessModel : StringThicknessModel
  stringContactRegime : StringContactRegime
  releaseProtocol : ReleaseProtocol

/-!
Primary-image evidence: the cylinder is annular, the string is vertical and
tangent to the outer rim, its upper end meets a horizontal support, and arrows
from the center label the inner and outer radii as `20.0 cm` and `35.0 cm`.
-/
structure MatchesPrimaryFigure
    (setup : FallingHollowCylinderSetup) : Prop where
  allObjectsShown :
    ∀ object : FigureObject, setup.figure.showsObject object = true
  allLabelsShown :
    ∀ label : FigureLabel, setup.figure.showsLabel label = true
  innerLabelRefersToInnerRadius :
    setup.figure.labelRefersTo .innerRadius20cm = .inner
  outerLabelRefersToOuterRadius :
    setup.figure.labelRefersTo .outerRadius35cm = .outer
  stringIsVertical : setup.figure.stringOrientation = .vertical
  supportIsHorizontal : setup.figure.supportOrientation = .horizontal
  stringIsTangentToOuterRim : setup.figure.stringTouchesOuterRim = true
  stringIsFixedAbove : setup.figure.stringUpperEndTouchesSupport = true

/-!
Numerical and qualitative data supplied by the statement and primary figure.
The radius readouts convert `20.0 cm` and `35.0 cm` to `1/5 m` and `7/20 m`.
The standard terrestrial acceleration readout `9.81 m/s²` is made explicit so
that the rounding convention behind the multiple-choice answer is visible.
-/
structure MatchesProblemData
    (setup : FallingHollowCylinderSetup) : Prop where
  massReadout : massInKilograms setup.cylinderMass = 19 / 4
  innerRadiusReadout : lengthInMeters setup.innerRadius = 1 / 5
  outerRadiusReadout : lengthInMeters setup.outerRadius = 7 / 20
  gravitationalAccelerationReadout :
    accelerationInMetersPerSecondSquared
        setup.gravitationalAcceleration = 981 / 100
  releaseDistanceIsZero :
    lengthInMeters (setup.distanceFallen .release) = 0
  releaseCenterOfMassSpeedIsZero :
    speedInMetersPerSecond (setup.centerOfMassSpeed .release) = 0
  releaseAngularSpeedIsZero :
    angularSpeedInRadiansPerSecond (setup.angularSpeed .release) = 0
  targetCenterOfMassSpeedReadout :
    speedInMetersPerSecond
        (setup.centerOfMassSpeed .targetSpeedReached) = 333 / 50
  cylinderIsUniformAndHollow :
    setup.massDistribution = .uniformHollowCylinder
  stringIsLight :
    setup.stringMassModel = .lightWithNegligibleMass
  stringIsThin : setup.stringThicknessModel = .thin
  stringUnwindsAtOuterRim :
    setup.stringContactRegime = .wrappedAroundOuterRimWithoutSlip
  cylinderIsReleasedFromRest :
    setup.releaseProtocol = .releasedFromRest

/-- Positivity and nondegeneracy of the independent physical parameters. -/
structure HasPhysicalParameters
    (setup : FallingHollowCylinderSetup) : Prop where
  cylinderMassPositive : 0 < massInKilograms setup.cylinderMass
  innerRadiusPositive : 0 < lengthInMeters setup.innerRadius
  outerRadiusPositive : 0 < lengthInMeters setup.outerRadius
  innerRadiusLessThanOuterRadius :
    lengthInMeters setup.innerRadius < lengthInMeters setup.outerRadius
  gravitationalAccelerationPositive :
    0 < accelerationInMetersPerSecondSquared
      setup.gravitationalAcceleration

/-!
The governing rigid-body, kinematic, and energy laws.

* A uniform hollow cylinder has axial inertia
  `I = (1/2) M (R_inner² + R_outer²)`.
* The thin string unwinds without slip, so `v = R_outer ω`.
* Translational kinetic energy is `M v² / 2`, while rotational kinetic
  energy is linked to Physlib's inertia-tensor definition.
* The loss of gravitational potential energy is `M g h` and, because the
  cylinder starts from rest and the light string stores no energy, equals the
  sum of translational and rotational kinetic energies.

None of these fields states the requested fall distance or its displayed
two-decimal approximation.
-/
structure SatisfiesFallingHollowCylinderLaws
    (setup : FallingHollowCylinderSetup) : Prop where
  rigidBodyMassMatchesCylinderMass :
    setup.rigidBodySI.mass = massInKilograms setup.cylinderMass
  angularVelocityIsAlongSymmetryAxis :
    ∀ (event : MotionEvent) (component : Fin 3),
      setup.angularVelocityVector_rad_per_s event component =
        if component = setup.centralSymmetryAxis then
          angularSpeedInRadiansPerSecond (setup.angularSpeed event)
        else 0
  axialInertiaTensorEntry :
    setup.rigidBodySI.inertiaTensor
        setup.centralSymmetryAxis setup.centralSymmetryAxis =
      momentOfInertiaInKilogramMetersSquared setup.axialMomentOfInertia
  uniformHollowCylinderAxialInertia :
    momentOfInertiaInKilogramMetersSquared setup.axialMomentOfInertia =
      (1 / 2 : ℝ) * massInKilograms setup.cylinderMass *
        (lengthInMeters setup.innerRadius ^ 2 +
          lengthInMeters setup.outerRadius ^ 2)
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
  noSlipUnwindingKinematics :
    ∀ event : MotionEvent,
      speedInMetersPerSecond (setup.centerOfMassSpeed event) =
        lengthInMeters setup.outerRadius *
          angularSpeedInRadiansPerSecond (setup.angularSpeed event)
  gravitationalPotentialEnergyLossLaw :
    ∀ event : MotionEvent,
      energyInJoules (setup.gravitationalPotentialEnergyLost event) =
        massInKilograms setup.cylinderMass *
          accelerationInMetersPerSecondSquared
            setup.gravitationalAcceleration *
          lengthInMeters (setup.distanceFallen event)
  mechanicalEnergyConservationFromRest :
    ∀ event : MotionEvent,
      energyInJoules (setup.gravitationalPotentialEnergyLost event) =
        energyInJoules (setup.translationalKineticEnergy event) +
          energyInJoules (setup.rotationalKineticEnergy event)

/-! ## Derived distance and answer metadata -/

/-!
With `g = 9.81 m/s²`, the exact ideal-model distance is
`2008323 / 534100 m`, approximately `3.760200337 m`.
-/
lemma distanceAtTargetSpeed_exact
    (setup : FallingHollowCylinderSetup)
    (_data : MatchesProblemData setup)
    (_physical : HasPhysicalParameters setup)
    (_laws : SatisfiesFallingHollowCylinderLaws setup) :
    lengthInMeters (setup.distanceFallen .targetSpeedReached) =
      2008323 / 534100 := by
  have hrot :
      energyInJoules
          (setup.rotationalKineticEnergy .targetSpeedReached) =
        (1 / 2 : ℝ) *
          momentOfInertiaInKilogramMetersSquared
            setup.axialMomentOfInertia *
          angularSpeedInRadiansPerSecond
              (setup.angularSpeed .targetSpeedReached) ^ 2 := by
    rw [_laws.rotationalKineticEnergyUsesPhyslib,
      RigidBody.rotationalKineticEnergy]
    simp only [dotProduct, Matrix.mulVec,
      _laws.angularVelocityIsAlongSymmetryAxis]
    simp [_laws.axialInertiaTensorEntry, pow_two]
    ring
  have hkin :=
    _laws.noSlipUnwindingKinematics .targetSpeedReached
  have hinertia := _laws.uniformHollowCylinderAxialInertia
  have htrans :=
    _laws.translationalKineticEnergyLaw .targetSpeedReached
  have hpotential :=
    _laws.gravitationalPotentialEnergyLossLaw .targetSpeedReached
  have henergy :=
    _laws.mechanicalEnergyConservationFromRest .targetSpeedReached
  rw [_data.targetCenterOfMassSpeedReadout,
    _data.outerRadiusReadout] at hkin
  rw [_data.massReadout, _data.innerRadiusReadout,
    _data.outerRadiusReadout] at hinertia
  rw [_data.massReadout,
    _data.targetCenterOfMassSpeedReadout] at htrans
  rw [_data.massReadout,
    _data.gravitationalAccelerationReadout] at hpotential
  norm_num at hkin hinertia htrans
  rw [hrot, hinertia] at henergy
  nlinarith

/-- A displayed metre value is a valid nearest-hundredth approximation. -/
def RoundsToNearestHundredthMeter
    (distance : LengthQuantity) (displayedMeters : ℝ) : Prop :=
  abs (lengthInMeters distance - displayedMeters) < 1 / 200

/-- Labels of the four displayed answer choices. -/
inductive AnswerChoice where
  | A
  | B
  | C
  | D
  deriving DecidableEq, Repr

/-- Distance in metres printed beside each displayed answer label. -/
def AnswerChoice.meters : AnswerChoice → ℝ
  | .A => 119 / 25
  | .B => 94 / 25
  | .C => 69 / 25
  | .D => 44 / 25

/-- Dataset metadata recording the supplied answer label. -/
def recordedAnswerChoice : AnswerChoice := .B

/-- A physical distance rounds to the metre value displayed for a choice. -/
def MatchesDisplayedDistance
    (distance : LengthQuantity) (choice : AnswerChoice) : Prop :=
  RoundsToNearestHundredthMeter distance choice.meters

/-!
The cylinder must fall about `3.76 m` before its center reaches `6.66 m/s`.
This is answer choice `B` and formalizes blueprint label
`thm:physics:phyx_mini_0780:target`.
-/
theorem distanceAtTargetSpeed_roundsTo_threePointSevenSixMeters
    (setup : FallingHollowCylinderSetup)
    (_figure : MatchesPrimaryFigure setup)
    (_data : MatchesProblemData setup)
    (_physical : HasPhysicalParameters setup)
    (_laws : SatisfiesFallingHollowCylinderLaws setup) :
    RoundsToNearestHundredthMeter
      (setup.distanceFallen .targetSpeedReached) (94 / 25) := by
  rw [RoundsToNearestHundredthMeter,
    distanceAtTargetSpeed_exact setup _data _physical _laws]
  norm_num [abs_of_nonneg]

/-- The same conclusion expressed through the recorded answer label. -/
theorem distanceAtTargetSpeed_matches_answerB
    (setup : FallingHollowCylinderSetup)
    (_figure : MatchesPrimaryFigure setup)
    (_data : MatchesProblemData setup)
    (_physical : HasPhysicalParameters setup)
    (_laws : SatisfiesFallingHollowCylinderLaws setup) :
    MatchesDisplayedDistance
      (setup.distanceFallen .targetSpeedReached) .B := by
  exact distanceAtTargetSpeed_roundsTo_threePointSevenSixMeters
    setup _figure _data _physical _laws

end PhyXMiniProblems.ProblemPhyXMini0780
