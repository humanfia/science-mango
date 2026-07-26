import Mathlib
import Physlib.Units.WithDim.Basic

noncomputable section

namespace PhyXMiniProblems.ProblemPhyXMini0199

open Dimension

/-!
# Additional lowering of a car under an increased load

A family with total mass `200 kg` produces an additional suspension compression
of `3.0 cm` in a `1200 kg` car.  The question replaces that added load by
`300 kg` and asks for the additional lowering from the car-only equilibrium.

The primary image shows one MacPherson strut assembly: a coil spring over a
shock-absorber/strut, together with its control arm, brake disc, brake caliper,
ball joint, and mounting bolts.  The physical masses, lengths, gravitational
acceleration, and equivalent suspension stiffness below are unit-independent
Physlib quantities.  Real numbers are used only for scalar readouts in named
coherent units and for the malformed, unitless answer tokens in the source.
-/

/-! ## Dimensionful physical quantities and readouts -/

/-- A physical mass represented coherently in every choice of units. -/
abbrev MassQuantity : Type := Dimensionful (WithDim M𝓭 ℝ)

/-- A physical vertical displacement or compression. -/
abbrev LengthQuantity : Type := Dimensionful (WithDim L𝓭 ℝ)

/-- A physical acceleration, used for the local gravitational acceleration. -/
abbrev AccelerationQuantity : Type :=
  Dimensionful (WithDim (L𝓭 * T𝓭⁻¹ * T𝓭⁻¹) ℝ)

/-- Equivalent stiffness of the car's parallel suspension springs. -/
abbrev SpringStiffnessQuantity : Type :=
  Dimensionful (WithDim (M𝓭 * T𝓭⁻¹ * T𝓭⁻¹) ℝ)

/-- Scalar mass readout in a selected coherent unit system. -/
def massReadout (units : UnitChoices) (mass : MassQuantity) : ℝ :=
  (mass units).val

/-- Scalar length readout in a selected coherent unit system. -/
def lengthReadout (units : UnitChoices) (length : LengthQuantity) : ℝ :=
  (length units).val

/-- Scalar acceleration readout in a selected coherent unit system. -/
def accelerationReadout
    (units : UnitChoices) (acceleration : AccelerationQuantity) : ℝ :=
  (acceleration units).val

/-- Scalar spring-stiffness readout in a selected coherent unit system. -/
def springStiffnessReadout
    (units : UnitChoices) (stiffness : SpringStiffnessQuantity) : ℝ :=
  (stiffness units).val

/-- The kilogram readout supplied by the SI unit choice. -/
def massInKilograms (mass : MassQuantity) : ℝ :=
  massReadout UnitChoices.SI mass

/-- SI base units with centimeters selected as the length unit. -/
noncomputable def centimeterUnitChoices : UnitChoices :=
  { UnitChoices.SI with length := LengthUnit.centimeters }

/-- The centimeter readout used for the measured and requested lowering. -/
def lengthInCentimeters (length : LengthQuantity) : ℝ :=
  lengthReadout centimeterUnitChoices length

/-! ## Primary-figure labels and qualitative roles -/

/-- Mechanical components visible in the supplied suspension bitmap. -/
inductive SuspensionComponent where
  | coilSpring
  | shockAbsorberOrStrut
  | controlArm
  | brakeDisc
  | brakeCaliper
  | ballJoint
  | mountingBolts
  deriving DecidableEq, Repr

/-- Qualitative physical roles attributed to the visible components. -/
inductive SuspensionRole where
  | supportsLoadAndAbsorbsShock
  | dampsVibration
  | guidesWheelMotion
  | rotatesWithWheel
  | appliesBrakeFriction
  | permitsPivoting
  | securesAssembly
  deriving DecidableEq, Repr

/-- Suspension architecture identified by the primary image. -/
inductive SuspensionKind where
  | macPhersonStrut
  deriving DecidableEq, Repr

/-- The reference height from which the stated extra lowering is measured. -/
inductive CompressionReference where
  | carOnlyStaticEquilibrium
  deriving DecidableEq, Repr

/--
Qualitative visibility, geometry, and component roles read from the image.
The bitmap contains no mass or compression scale.
-/
structure SuspensionFigure where
  isVisible : SuspensionComponent → Prop
  isAbove : SuspensionComponent → SuspensionComponent → Prop
  isConnectedTo : SuspensionComponent → SuspensionComponent → Prop
  role : SuspensionComponent → SuspensionRole
  depictedAssemblyCount : ℕ

/-! ## Physical setup and supplied data -/

/--
The car, the two added-load cases, and the common suspension model.

`additionalLowering` is measured relative to the equilibrium height of the
car without either added load.  It is an independent response function; its
value at `requestedAddedMass` is not fixed by this structure.
-/
structure CarSuspensionSetup where
  suspensionKind : SuspensionKind
  compressionReference : CompressionReference
  carMass : MassQuantity
  calibrationOccupantCount : ℕ
  calibrationAddedMass : MassQuantity
  requestedAddedMass : MassQuantity
  equivalentSpringStiffness : SpringStiffnessQuantity
  gravitationalAcceleration : AccelerationQuantity
  additionalLowering : MassQuantity → LengthQuantity
  figure : SuspensionFigure

/--
Numerical data stated in the prose.  In particular, only the `200 kg`
calibration compression is recorded; the compression under `300 kg` is absent.
-/
structure MatchesProblemStatement (setup : CarSuspensionSetup) : Prop where
  referenceIsCarOnlyEquilibrium :
    setup.compressionReference = .carOnlyStaticEquilibrium
  carMassKilograms : massInKilograms setup.carMass = 1200
  calibrationFamilySize : setup.calibrationOccupantCount = 4
  calibrationAddedMassKilograms :
    massInKilograms setup.calibrationAddedMass = 200
  requestedAddedMassKilograms :
    massInKilograms setup.requestedAddedMass = 300
  calibrationCompressionCentimeters :
    lengthInCentimeters
        (setup.additionalLowering setup.calibrationAddedMass) = 3

/--
Readouts from the supplied MacPherson-strut image.  These fields preserve the
visible components and their qualitative geometry, but assert no numerical
lowering and therefore do not determine the answer.
-/
structure MatchesSuppliedMacPhersonFigure
    (setup : CarSuspensionSetup) : Prop where
  suspensionIsMacPherson : setup.suspensionKind = .macPhersonStrut
  oneAssemblyDepicted : setup.figure.depictedAssemblyCount = 1
  coilSpringVisible : setup.figure.isVisible .coilSpring
  strutVisible : setup.figure.isVisible .shockAbsorberOrStrut
  controlArmVisible : setup.figure.isVisible .controlArm
  brakeDiscVisible : setup.figure.isVisible .brakeDisc
  brakeCaliperVisible : setup.figure.isVisible .brakeCaliper
  ballJointVisible : setup.figure.isVisible .ballJoint
  mountingBoltsVisible : setup.figure.isVisible .mountingBolts
  coilSpringAboveStrut :
    setup.figure.isAbove .coilSpring .shockAbsorberOrStrut
  controlArmConnectedToBallJoint :
    setup.figure.isConnectedTo .controlArm .ballJoint
  brakeCaliperConnectedToDisc :
    setup.figure.isConnectedTo .brakeCaliper .brakeDisc
  coilSpringRole :
    setup.figure.role .coilSpring = .supportsLoadAndAbsorbsShock
  strutRole : setup.figure.role .shockAbsorberOrStrut = .dampsVibration
  controlArmRole : setup.figure.role .controlArm = .guidesWheelMotion
  brakeDiscRole : setup.figure.role .brakeDisc = .rotatesWithWheel
  brakeCaliperRole : setup.figure.role .brakeCaliper = .appliesBrakeFriction
  ballJointRole : setup.figure.role .ballJoint = .permitsPivoting
  mountingBoltsRole : setup.figure.role .mountingBolts = .securesAssembly

/-- Positivity and nondegeneracy conditions for the static loading regime. -/
structure HasPhysicalSuspensionParameters
    (setup : CarSuspensionSetup) : Prop where
  carMassPositive : 0 < massInKilograms setup.carMass
  calibrationAddedMassPositive :
    0 < massInKilograms setup.calibrationAddedMass
  requestedAddedMassPositive :
    0 < massInKilograms setup.requestedAddedMass
  equivalentStiffnessPositive :
    0 < springStiffnessReadout UnitChoices.SI
      setup.equivalentSpringStiffness
  gravitationalAccelerationPositive :
    0 < accelerationReadout UnitChoices.SI setup.gravitationalAcceleration
  calibrationCompressionPositive :
    0 < lengthInCentimeters
      (setup.additionalLowering setup.calibrationAddedMass)

/-!
Static Hooke equilibrium for the *additional* load on the unchanged car:
`k_eff x(m) = m g`.  It is stated in every coherent unit system and for every
nonnegative added mass, so the single equivalent-stiffness field applies to
both load cases.  This governing law contains neither `4.5 cm` nor any value
for the requested compression.
-/
structure SatisfiesStaticSuspensionLaws
    (setup : CarSuspensionSetup) : Prop where
  addedLoadHookeEquilibrium :
    ∀ (addedMass : MassQuantity),
      0 ≤ massInKilograms addedMass →
      ∀ units : UnitChoices,
        springStiffnessReadout units setup.equivalentSpringStiffness *
            lengthReadout units (setup.additionalLowering addedMass) =
          massReadout units addedMass *
            accelerationReadout units setup.gravitationalAcceleration

/-!
Eliminating the common stiffness and gravitational acceleration gives the
cross-multiplied proportionality between the calibration and requested load
cases.  No numerical value for the requested lowering is assumed.
-/
lemma addedMass_compression_cross_relation
    (setup : CarSuspensionSetup)
    (_physical : HasPhysicalSuspensionParameters setup)
    (_laws : SatisfiesStaticSuspensionLaws setup)
    (units : UnitChoices) :
    massReadout units setup.calibrationAddedMass *
        lengthReadout units
          (setup.additionalLowering setup.requestedAddedMass) =
      massReadout units setup.requestedAddedMass *
        lengthReadout units
          (setup.additionalLowering setup.calibrationAddedMass) := by
  have hcal := _laws.addedLoadHookeEquilibrium setup.calibrationAddedMass
    (le_of_lt _physical.calibrationAddedMassPositive) units
  have hreq := _laws.addedLoadHookeEquilibrium setup.requestedAddedMass
    (le_of_lt _physical.requestedAddedMassPositive) units
  have hk_scale := congrArg WithDim.val
    (setup.equivalentSpringStiffness.property UnitChoices.SI units)
  simp only [WithDim.smul_val, NNReal.smul_def, smul_eq_mul] at hk_scale
  have hk_units :
      springStiffnessReadout units setup.equivalentSpringStiffness ≠ 0 := by
    unfold springStiffnessReadout
    rw [hk_scale]
    exact mul_ne_zero
      (NNReal.coe_ne_zero.mpr
        (UnitChoices.dimScale_ne_zero UnitChoices.SI units _))
      (ne_of_gt _physical.equivalentStiffnessPositive)
  apply mul_left_cancel₀ hk_units
  calc
    _ = massReadout units setup.calibrationAddedMass *
        (springStiffnessReadout units setup.equivalentSpringStiffness *
          lengthReadout units
            (setup.additionalLowering setup.requestedAddedMass)) := by
      ring
    _ = massReadout units setup.calibrationAddedMass *
        (massReadout units setup.requestedAddedMass *
          accelerationReadout units setup.gravitationalAcceleration) := by
      rw [hreq]
    _ = massReadout units setup.requestedAddedMass *
        (massReadout units setup.calibrationAddedMass *
          accelerationReadout units setup.gravitationalAcceleration) := by
      ring
    _ = massReadout units setup.requestedAddedMass *
        (springStiffnessReadout units setup.equivalentSpringStiffness *
          lengthReadout units
            (setup.additionalLowering setup.calibrationAddedMass)) := by
      rw [hcal]
    _ = _ := by ring

/-! ## Malformed multiple-choice metadata -/

/-- Labels attached to the four answer tokens in the source record. -/
inductive AnswerChoice where
  | A
  | B
  | C
  | D
  deriving DecidableEq, Repr

/--
The raw numeric tokens printed by the source.  Since no units accompany them
and their magnitudes do not represent the requested centimeter lowering, they
are retained only as dimensionless dataset metadata.
-/
def displayedRawNumericToken : AnswerChoice → ℝ
  | .A => 7.5 * 10 ^ 4
  | .B => 6.5 * 10 ^ 3
  | .C => 5.5 * 10 ^ 4
  | .D => 6.5 * 10 ^ 4

/-- The answer label recorded in the source dataset. -/
def recordedAnswerChoice : AnswerChoice := .D

/-!
Because the same linear suspension responds to `300 kg` instead of `200 kg`,
its additional lowering is `(300 / 200) * 3 cm = 9/2 cm = 4.5 cm`.

This formalizes blueprint label `thm:physics:phyx_mini_0199:target`.
-/
theorem problem_phyx_mini_0199
    (setup : CarSuspensionSetup)
    (_statement : MatchesProblemStatement setup)
    (_figure : MatchesSuppliedMacPhersonFigure setup)
    (_physical : HasPhysicalSuspensionParameters setup)
    (_laws : SatisfiesStaticSuspensionLaws setup) :
    lengthInCentimeters
        (setup.additionalLowering setup.requestedAddedMass) =
      9 / 2 := by
  have hmass (mass : MassQuantity) :
      massReadout centimeterUnitChoices mass = massInKilograms mass := by
    change (mass centimeterUnitChoices).val = (mass UnitChoices.SI).val
    rw [mass.property UnitChoices.SI centimeterUnitChoices]
    simp only [WithDim.dim_apply, WithDim.smul_val]
    have hscale : UnitChoices.dimScale UnitChoices.SI
        centimeterUnitChoices M𝓭 = 1 := by
      simp [centimeterUnitChoices, UnitChoices.dimScale, M𝓭]
    rw [hscale]
    simp
  have hcross := addedMass_compression_cross_relation setup _physical _laws
    centimeterUnitChoices
  change massReadout centimeterUnitChoices setup.calibrationAddedMass *
      lengthInCentimeters
        (setup.additionalLowering setup.requestedAddedMass) =
    massReadout centimeterUnitChoices setup.requestedAddedMass *
      lengthInCentimeters
        (setup.additionalLowering setup.calibrationAddedMass) at hcross
  rw [hmass setup.calibrationAddedMass,
    hmass setup.requestedAddedMass,
    _statement.calibrationAddedMassKilograms,
    _statement.requestedAddedMassKilograms,
    _statement.calibrationCompressionCentimeters] at hcross
  norm_num at hcross ⊢
  linarith

end PhyXMiniProblems.ProblemPhyXMini0199
