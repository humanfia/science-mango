import Mathlib.Data.Real.Basic
import Physlib.Units.WithDim.Energy

/- USER: The assigned source file did not exist when this autoformalization task began. -/

noncomputable section

namespace PhyXMiniProblems.ProblemPhyXMini0770

open Dimension

/-!
# Fall distance for a stone driving a uniform-disk pulley

A `1.50 kg` stone hangs from a very light wire wrapped around the rim of a
uniform solid-disk pulley of mass `2.50 kg` and radius `20.0 cm`.  The axle is
frictionless, the wire does not slip, and the system is released from rest.
We determine the fall distance when the pulley's rotational kinetic energy is
`4.50 J`.

Physical quantities use Physlib's unit-independent `Dimensionful` type.  Real
numbers below are only named-unit readouts or the numerical values printed in
the problem and its answer choices.
-/

/-! ## Dimensionful quantities and SI readouts -/

/-- A nonnegative physical mass. -/
abbrev MassQuantity : Type :=
  Dimensionful (WithDim M𝓭 NNReal)

/-- A nonnegative physical length. -/
abbrev LengthQuantity : Type :=
  Dimensionful (WithDim L𝓭 NNReal)

/-- A nonnegative linear-speed magnitude. -/
abbrev SpeedQuantity : Type :=
  Dimensionful (WithDim (L𝓭 * T𝓭⁻¹) NNReal)

/-- A nonnegative angular-speed magnitude; radians are dimensionless. -/
abbrev AngularSpeedQuantity : Type :=
  Dimensionful (WithDim T𝓭⁻¹ NNReal)

/-- A nonnegative acceleration magnitude. -/
abbrev AccelerationQuantity : Type :=
  Dimensionful (WithDim (L𝓭 * T𝓭⁻¹ * T𝓭⁻¹) NNReal)

/-- Axial moment of inertia, with dimension mass times length squared. -/
abbrev MomentOfInertiaQuantity : Type :=
  Dimensionful (WithDim (M𝓭 * L𝓭 * L𝓭) NNReal)

/-- Physical energy, with dimension mass times length squared per time squared. -/
abbrev EnergyQuantity : Type := DimEnergy

/-- Read a mass in SI kilograms. -/
def massInKilograms (mass : MassQuantity) : ℝ :=
  ((mass UnitChoices.SI).val : ℝ)

/-- Read a length in SI metres. -/
def lengthInMeters (length : LengthQuantity) : ℝ :=
  ((length UnitChoices.SI).val : ℝ)

/-- Read a speed magnitude in SI metres per second. -/
def speedInMetersPerSecond (speed : SpeedQuantity) : ℝ :=
  ((speed UnitChoices.SI).val : ℝ)

/-- Read an angular speed in radians per SI second. -/
def angularSpeedInRadiansPerSecond
    (angularSpeed : AngularSpeedQuantity) : ℝ :=
  ((angularSpeed UnitChoices.SI).val : ℝ)

/-- Read an acceleration in SI metres per second squared. -/
def accelerationInMetersPerSecondSquared
    (acceleration : AccelerationQuantity) : ℝ :=
  ((acceleration UnitChoices.SI).val : ℝ)

/-- Read an axial moment of inertia in `kg m²`. -/
def momentOfInertiaInKilogramMetersSquared
    (inertia : MomentOfInertiaQuantity) : ℝ :=
  ((inertia UnitChoices.SI).val : ℝ)

/-- Read an energy in joules, calibrated against Physlib's joule. -/
def energyInJoules (energy : EnergyQuantity) : ℝ :=
  (energy UnitChoices.SI).val /
    (DimEnergy.joule UnitChoices.SI).val

/-! ## Problem and primary-image vocabulary -/

/-- The three physical objects visible in the supplied bitmap. -/
inductive FigureObject where
  | pulleyDisk
  | verticalWire
  | stone
  deriving DecidableEq, Fintype, Repr

/-- The two text labels printed in the supplied bitmap. -/
inductive FigureTextLabel where
  | pulleyMass250kg
  | stoneMass150kg
  deriving DecidableEq, Fintype, Repr

/-- How the pulley's mass is distributed. -/
inductive PulleyMassModel where
  | uniformSolidDisk
  | other
  deriving DecidableEq, Repr

/-- Resistance at the pulley's fixed axle. -/
inductive AxleResistanceModel where
  | frictionless
  | other
  deriving DecidableEq, Repr

/-- The mass idealization of the connecting wire. -/
inductive WireMassModel where
  | negligible
  | other
  deriving DecidableEq, Repr

/-- Contact between the wrapped wire and the pulley rim. -/
inductive WirePulleyContact where
  | wrappedNoSlip
  | other
  deriving DecidableEq, Repr

/-- Qualitative and printed information transcribed from the primary image. -/
structure SuppliedPulleyStoneFigure where
  showsObject : FigureObject → Bool
  showsTextLabel : FigureTextLabel → Bool
  printedMassKilograms : FigureObject → Option ℝ
  pulleyDrawnAsCircle : Bool
  wireDrawnVerticalAndTangentToLeftRim : Bool
  stoneDrawnBelowPulley : Bool

/-!
The independent physical quantities describing release and the later state at
which the pulley's energy is inspected.  In particular, `fallDistance` is a
response field constrained by the governing laws below; it is not defined
from any answer choice.
-/
structure PulleyStoneSetup where
  pulleyMass : MassQuantity
  pulleyRadius : LengthQuantity
  stoneMass : MassQuantity
  gravitationalAcceleration : AccelerationQuantity
  fallDistance : LengthQuantity
  initialStoneSpeed : SpeedQuantity
  finalStoneSpeed : SpeedQuantity
  initialPulleyAngularSpeed : AngularSpeedQuantity
  finalPulleyAngularSpeed : AngularSpeedQuantity
  pulleyMomentOfInertia : MomentOfInertiaQuantity
  finalPulleyRotationalEnergy : EnergyQuantity
  pulleyMassModel : PulleyMassModel
  axleResistanceModel : AxleResistanceModel
  wireMassModel : WireMassModel
  wirePulleyContact : WirePulleyContact
  figure : SuppliedPulleyStoneFigure

/-!
Numerical problem data and primary-image readouts.  The radius is stated in
the text but is not printed in the bitmap.  Release from rest is stated in the
text and is recorded for both translational and rotational motion.
-/
structure MatchesProblemAndFigureReadouts (setup : PulleyStoneSetup) : Prop where
  pulleyMassKilograms : massInKilograms setup.pulleyMass = 5 / 2
  pulleyRadiusMeters : lengthInMeters setup.pulleyRadius = 1 / 5
  stoneMassKilograms : massInKilograms setup.stoneMass = 3 / 2
  targetPulleyEnergyJoules :
    energyInJoules setup.finalPulleyRotationalEnergy = 9 / 2
  stoneReleasedFromRest :
    speedInMetersPerSecond setup.initialStoneSpeed = 0
  pulleyReleasedFromRest :
    angularSpeedInRadiansPerSecond setup.initialPulleyAngularSpeed = 0
  pulleyIsUniformSolidDisk : setup.pulleyMassModel = .uniformSolidDisk
  axleIsFrictionless : setup.axleResistanceModel = .frictionless
  wireMassIsNegligible : setup.wireMassModel = .negligible
  wireIsWrappedWithoutSlip : setup.wirePulleyContact = .wrappedNoSlip
  everyFigureObjectShown :
    ∀ object, setup.figure.showsObject object = true
  everyFigureTextLabelShown :
    ∀ label, setup.figure.showsTextLabel label = true
  pulleyPrintedMass :
    setup.figure.printedMassKilograms .pulleyDisk = some (5 / 2)
  stonePrintedMass :
    setup.figure.printedMassKilograms .stone = some (3 / 2)
  wireHasNoPrintedMass :
    setup.figure.printedMassKilograms .verticalWire = none
  circularPulleyReadout : setup.figure.pulleyDrawnAsCircle = true
  tangentWireReadout :
    setup.figure.wireDrawnVerticalAndTangentToLeftRim = true
  stoneBelowPulleyReadout : setup.figure.stoneDrawnBelowPulley = true

/-- The conventional near-Earth gravitational acceleration used in the
multiple-choice numerical evaluation. -/
structure UsesStandardEarthGravity (setup : PulleyStoneSetup) : Prop where
  gravitationalAccelerationSI :
    accelerationInMetersPerSecondSquared setup.gravitationalAcceleration = 49 / 5

/-- Positivity and nondegeneracy conditions for the physical experiment. -/
structure HasPhysicalParameters (setup : PulleyStoneSetup) : Prop where
  pulleyMassPositive : 0 < massInKilograms setup.pulleyMass
  pulleyRadiusPositive : 0 < lengthInMeters setup.pulleyRadius
  stoneMassPositive : 0 < massInKilograms setup.stoneMass
  gravityPositive :
    0 < accelerationInMetersPerSecondSquared setup.gravitationalAcceleration
  fallDistancePositive : 0 < lengthInMeters setup.fallDistance
  finalPulleyEnergyPositive :
    0 < energyInJoules setup.finalPulleyRotationalEnergy

/-!
## Governing laws

For an ideal fixed-axis uniform disk and a taut non-slipping wire:

* `I = M R² / 2`;
* the rim speed equals the stone speed, `v = R ω`;
* the pulley's rotational kinetic energy is `I ω² / 2`;
* with a massless wire and frictionless axle, the loss `m g h` of
  gravitational potential energy equals the total gain in translational and
  rotational kinetic energy.

These laws relate independent response fields.  They contain neither the
exact solved distance `33/49 m` nor the displayed answer `0.673 m`.
-/
structure SatisfiesIdealPulleyStoneLaws (setup : PulleyStoneSetup) : Prop where
  uniformSolidDiskMomentOfInertia :
    momentOfInertiaInKilogramMetersSquared setup.pulleyMomentOfInertia =
      (1 / 2 : ℝ) * massInKilograms setup.pulleyMass *
        lengthInMeters setup.pulleyRadius ^ 2
  initialNoSlipTangentialCoupling :
    speedInMetersPerSecond setup.initialStoneSpeed =
      lengthInMeters setup.pulleyRadius *
        angularSpeedInRadiansPerSecond setup.initialPulleyAngularSpeed
  finalNoSlipTangentialCoupling :
    speedInMetersPerSecond setup.finalStoneSpeed =
      lengthInMeters setup.pulleyRadius *
        angularSpeedInRadiansPerSecond setup.finalPulleyAngularSpeed
  finalPulleyRotationalEnergyLaw :
    energyInJoules setup.finalPulleyRotationalEnergy =
      (1 / 2 : ℝ) *
        momentOfInertiaInKilogramMetersSquared setup.pulleyMomentOfInertia *
          angularSpeedInRadiansPerSecond setup.finalPulleyAngularSpeed ^ 2
  mechanicalEnergyConservation :
    (1 / 2 : ℝ) * massInKilograms setup.stoneMass *
          speedInMetersPerSecond setup.initialStoneSpeed ^ 2 +
        (1 / 2 : ℝ) *
          momentOfInertiaInKilogramMetersSquared setup.pulleyMomentOfInertia *
          angularSpeedInRadiansPerSecond setup.initialPulleyAngularSpeed ^ 2 +
        massInKilograms setup.stoneMass *
          accelerationInMetersPerSecondSquared setup.gravitationalAcceleration *
          lengthInMeters setup.fallDistance =
      (1 / 2 : ℝ) * massInKilograms setup.stoneMass *
          speedInMetersPerSecond setup.finalStoneSpeed ^ 2 +
        energyInJoules setup.finalPulleyRotationalEnergy

/-! ## Exact result and multiple-choice metadata -/

/-- The four fall distances displayed in the problem. -/
inductive AnswerChoice where
  | A
  | B
  | C
  | D
  deriving DecidableEq, Fintype, Repr

/-- Numerical metre readout printed beside an answer choice. -/
def displayedFallDistanceMeters : AnswerChoice → ℝ
  | .A => 712 / 1000
  | .B => 673 / 1000
  | .C => 364 / 1000
  | .D => 198 / 1000

/-- A displayed three-decimal distance represents the modeled distance when
the discrepancy is strictly less than half of the last displayed metre digit. -/
def FitsDisplayedFallDistance
    (setup : PulleyStoneSetup) (choice : AnswerChoice) : Prop :=
  |lengthInMeters setup.fallDistance - displayedFallDistanceMeters choice| <
    1 / 2000

/-- The ideal-energy model determines the exact fall distance
`h = 33/49 m`. -/
lemma fallDistance_exact
    (setup : PulleyStoneSetup)
    (_readouts : MatchesProblemAndFigureReadouts setup)
    (_gravity : UsesStandardEarthGravity setup)
    (_physical : HasPhysicalParameters setup)
    (_laws : SatisfiesIdealPulleyStoneLaws setup) :
    lengthInMeters setup.fallDistance = 33 / 49 := by
  have h_inertia := _laws.uniformSolidDiskMomentOfInertia
  have h_coupling := _laws.finalNoSlipTangentialCoupling
  have h_rotational := _laws.finalPulleyRotationalEnergyLaw
  have h_energy := _laws.mechanicalEnergyConservation
  rw [_readouts.pulleyMassKilograms, _readouts.pulleyRadiusMeters] at h_inertia
  rw [_readouts.pulleyRadiusMeters] at h_coupling
  rw [_readouts.targetPulleyEnergyJoules] at h_rotational
  rw [_readouts.stoneMassKilograms, _readouts.stoneReleasedFromRest,
    _readouts.pulleyReleasedFromRest, _readouts.targetPulleyEnergyJoules,
    _gravity.gravitationalAccelerationSI] at h_energy
  norm_num at h_inertia h_coupling h_rotational h_energy ⊢
  rw [h_inertia] at h_rotational
  rw [h_coupling] at h_energy
  nlinarith

/-- Physics formalization target
(`thm:physics:phyx_mini_0770:target`): the exact ideal-model distance rounds
to the displayed choice B, `0.673 m`. -/
theorem fallDistance_matches_answerB
    (setup : PulleyStoneSetup)
    (_readouts : MatchesProblemAndFigureReadouts setup)
    (_gravity : UsesStandardEarthGravity setup)
    (_physical : HasPhysicalParameters setup)
    (_laws : SatisfiesIdealPulleyStoneLaws setup) :
    lengthInMeters setup.fallDistance = 33 / 49 ∧
      FitsDisplayedFallDistance setup .B := by
  have h_exact :=
    fallDistance_exact setup _readouts _gravity _physical _laws
  constructor
  · exact h_exact
  · rw [FitsDisplayedFallDistance, h_exact]
    norm_num [displayedFallDistanceMeters]

end PhyXMiniProblems.ProblemPhyXMini0770
