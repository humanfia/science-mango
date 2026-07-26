import Mathlib
import Physlib.SpaceAndTime.Space.LengthUnit
import Physlib.Units.WithDim.Energy

noncomputable section

namespace PhyXMiniProblems.ProblemPhyXMini0582

open Dimension
open scoped BigOperators

/-!
# Quantized rotational energies of a rigid diatomic molecule

The supplied figure shows two atoms of equal mass `m` separated by the fixed
distance `d`.  The rotation axis passes through their midpoint, perpendicular
to the bond, so each atom moves at radius `d / 2`.  The dashed orbit and the
arrow labelled `ω` record the rotation about that axis.

Physical mass, length, angular speed, moment of inertia, angular momentum,
Planck's constant, and energy are represented by unit-independent Physlib
quantities.  Scalar equations are stated only after choosing coherent units.
The energy levels are independent setup fields constrained by the governing
laws below; they are not defined to equal the requested answer.
-/

/-! ## Dimensionful quantities and coherent scalar readouts -/

/-- Angular speed has physical dimension inverse time. -/
def angularSpeedDimension : Dimension := T𝓭⁻¹

/-- Moment of inertia has physical dimension mass times length squared. -/
def momentOfInertiaDimension : Dimension := M𝓭 * L𝓭 * L𝓭

/-- Action and angular momentum have dimension mass times length squared per time. -/
def actionDimension : Dimension := M𝓭 * L𝓭 * L𝓭 * T𝓭⁻¹

/-- A nonnegative, unit-independent physical mass. -/
abbrev MassQuantity : Type := Dimensionful (WithDim M𝓭 NNReal)

/-- A nonnegative, unit-independent physical length. -/
abbrev LengthQuantity : Type := Dimensionful (WithDim L𝓭 NNReal)

/-- A nonnegative angular-speed magnitude. -/
abbrev AngularSpeedQuantity : Type :=
  Dimensionful (WithDim angularSpeedDimension NNReal)

/-- A nonnegative moment of inertia about the depicted axis. -/
abbrev MomentOfInertiaQuantity : Type :=
  Dimensionful (WithDim momentOfInertiaDimension NNReal)

/-- A nonnegative angular-momentum magnitude. -/
abbrev AngularMomentumMagnitude : Type :=
  Dimensionful (WithDim actionDimension NNReal)

/-- The ordinary Planck constant `h`, as a unit-independent action. -/
abbrev PlanckConstantQuantity : Type :=
  Dimensionful (WithDim actionDimension NNReal)

/-- Read a physical mass in a selected mass unit. -/
def massReadout (unit : MassUnit) (mass : MassQuantity) : ℝ :=
  ((mass {UnitChoices.SI with mass := unit}).val : ℝ)

/-- Read a physical length in a selected length unit. -/
def lengthReadout (unit : LengthUnit) (length : LengthQuantity) : ℝ :=
  ((length {UnitChoices.SI with length := unit}).val : ℝ)

/-- Read angular speed in inverse units of the selected time unit. -/
def angularSpeedReadout
    (timeUnit : TimeUnit) (angularSpeed : AngularSpeedQuantity) : ℝ :=
  ((angularSpeed {UnitChoices.SI with time := timeUnit}).val : ℝ)

/-- Read moment of inertia in coherent selected mass and length units. -/
def momentOfInertiaReadout
    (massUnit : MassUnit) (lengthUnit : LengthUnit)
    (inertia : MomentOfInertiaQuantity) : ℝ :=
  ((inertia {UnitChoices.SI with
    mass := massUnit, length := lengthUnit}).val : ℝ)

/-- Read angular momentum in coherent mechanical units. -/
def angularMomentumReadout
    (massUnit : MassUnit) (lengthUnit : LengthUnit) (timeUnit : TimeUnit)
    (angularMomentum : AngularMomentumMagnitude) : ℝ :=
  ((angularMomentum {UnitChoices.SI with
    mass := massUnit, length := lengthUnit, time := timeUnit}).val : ℝ)

/-- Read `h` in the same action units as angular momentum. -/
def planckConstantReadout
    (massUnit : MassUnit) (lengthUnit : LengthUnit) (timeUnit : TimeUnit)
    (planckConstant : PlanckConstantQuantity) : ℝ :=
  ((planckConstant {UnitChoices.SI with
    mass := massUnit, length := lengthUnit, time := timeUnit}).val : ℝ)

/-- Read energy in the coherent unit induced by the selected base units. -/
def energyReadout
    (massUnit : MassUnit) (lengthUnit : LengthUnit) (timeUnit : TimeUnit)
    (energy : DimEnergy) : ℝ :=
  (energy {UnitChoices.SI with
    mass := massUnit, length := lengthUnit, time := timeUnit}).val

/-! ## Molecule roles and primary-figure vocabulary -/

/-- The two equal atoms on opposite sides of the rotation axis. -/
inductive AtomRole where
  | leftAtom
  | rightAtom
  deriving DecidableEq, Fintype, Repr

/-- The physical approximation used for the molecule. -/
inductive MolecularRotorModel where
  | rigidTwoPointMasses
  | other
  deriving DecidableEq, Repr

/-- The relation between the depicted axis and the internuclear bond. -/
inductive AxisGeometry where
  | throughMidpointPerpendicularToBond
  | other
  deriving DecidableEq, Repr

/-- Objects and graphical marks visible in the supplied raster. -/
inductive FigureObject where
  | axisLine
  | leftAtomSphere
  | rightAtomSphere
  | dashedCircularOrbit
  | angularVelocityArrow
  | leftRadiusArrow
  | rightRadiusArrow
  deriving DecidableEq, Fintype, Repr

/-- Individual occurrences of text visible in the supplied raster. -/
inductive FigureTextLabel where
  | axis
  | omega
  | leftMassM
  | rightMassM
  | leftRadiusDOverTwo
  | rightRadiusDOverTwo
  deriving DecidableEq, Fintype, Repr

/--
Literal and qualitative information read from image 582.  The drawn orbit is
an ellipse only because a circular orbit is displayed in perspective.
-/
structure SuppliedDiatomicRotorFigure where
  showsObject : FigureObject → Bool
  showsTextLabel : FigureTextLabel → Bool
  printedText : FigureTextLabel → String
  leftAtomShownLeftOfAxis : Bool
  rightAtomShownRightOfAxis : Bool
  atomsShownOnOppositeSides : Bool
  atomCentersShownOnDashedOrbit : AtomRole → Bool
  radiusArrowTerminatesAtAxis : AtomRole → Bool
  orbitDrawnAsPerspectiveEllipse : Bool
  axisDrawnVerticallyOnPage : Bool
  directedRotationShown : Bool

/-! ## Independent physical setup -/

/--
Independent quantities and roles of the rotating molecule.  In particular,
the inertia and level energies are observables to be related by laws, not
definitions containing the requested closed form.
-/
structure DiatomicMolecularRotorSetup where
  atomMass : AtomRole → MassQuantity
  internuclearSeparation : LengthQuantity
  orbitRadius : AtomRole → LengthQuantity
  momentOfInertiaAboutAxis : MomentOfInertiaQuantity
  angularSpeedAtLevel : ℕ → AngularSpeedQuantity
  angularMomentumAtLevel : ℕ → AngularMomentumMagnitude
  rotationalEnergyAtLevel : ℕ → DimEnergy
  ordinaryPlanckConstant : PlanckConstantQuantity
  molecularModel : MolecularRotorModel
  rotationAxisGeometry : AxisGeometry
  separationIsFixed : Bool
  moleculeIsRotatingAboutAxis : Bool
  figure : SuppliedDiatomicRotorFigure

/-! ## Scenario, figure evidence, and physical admissibility -/

/-- The prose-level rigid, equal-mass diatomic-rotor scenario. -/
structure MatchesDiatomicRotorScenario
    (setup : DiatomicMolecularRotorSetup) : Prop where
  rigidTwoPointMassModel : setup.molecularModel = .rigidTwoPointMasses
  fixedInternuclearSeparation : setup.separationIsFixed = true
  rotatesAboutIndicatedAxis : setup.moleculeIsRotatingAboutAxis = true
  centeredPerpendicularAxis :
    setup.rotationAxisGeometry = .throughMidpointPerpendicularToBond
  equalAtomMasses : ∀ massUnit : MassUnit,
    massReadout massUnit (setup.atomMass .leftAtom) =
      massReadout massUnit (setup.atomMass .rightAtom)

/-- Exact labels and qualitative geometry transcribed from the primary image. -/
structure MatchesSuppliedDiatomicRotorFigure
    (setup : DiatomicMolecularRotorSetup) : Prop where
  allObjectsShown : ∀ object, setup.figure.showsObject object = true
  allTextLabelsShown : ∀ label, setup.figure.showsTextLabel label = true
  axisText : setup.figure.printedText .axis = "Axis"
  omegaText : setup.figure.printedText .omega = "ω"
  leftMassText : setup.figure.printedText .leftMassM = "m"
  rightMassText : setup.figure.printedText .rightMassM = "m"
  leftRadiusText : setup.figure.printedText .leftRadiusDOverTwo = "d/2"
  rightRadiusText : setup.figure.printedText .rightRadiusDOverTwo = "d/2"
  leftAtomPlacement : setup.figure.leftAtomShownLeftOfAxis = true
  rightAtomPlacement : setup.figure.rightAtomShownRightOfAxis = true
  oppositeSidesReadout : setup.figure.atomsShownOnOppositeSides = true
  atomsOnOrbit : ∀ atom, setup.figure.atomCentersShownOnDashedOrbit atom = true
  radiusArrowsMeetAxis : ∀ atom,
    setup.figure.radiusArrowTerminatesAtAxis atom = true
  perspectiveOrbitReadout : setup.figure.orbitDrawnAsPerspectiveEllipse = true
  verticalAxisOnPage : setup.figure.axisDrawnVerticallyOnPage = true
  rotationArrowsReadout : setup.figure.directedRotationShown = true

/-- Positivity and nonnegativity conditions for the physical magnitudes. -/
structure HasPhysicalDiatomicRotorParameters
    (setup : DiatomicMolecularRotorSetup) : Prop where
  atomMassPositive : ∀ (atom : AtomRole) (massUnit : MassUnit),
    0 < massReadout massUnit (setup.atomMass atom)
  separationPositive : ∀ lengthUnit : LengthUnit,
    0 < lengthReadout lengthUnit setup.internuclearSeparation
  orbitRadiusPositive : ∀ (atom : AtomRole) (lengthUnit : LengthUnit),
    0 < lengthReadout lengthUnit (setup.orbitRadius atom)
  momentOfInertiaPositive : ∀
      (massUnit : MassUnit) (lengthUnit : LengthUnit),
    0 < momentOfInertiaReadout massUnit lengthUnit
      setup.momentOfInertiaAboutAxis
  ordinaryPlanckConstantPositive : ∀
      (massUnit : MassUnit) (lengthUnit : LengthUnit) (timeUnit : TimeUnit),
    0 < planckConstantReadout massUnit lengthUnit timeUnit
      setup.ordinaryPlanckConstant
  rotationalEnergyNonnegative : ∀
      (n : ℕ) (massUnit : MassUnit) (lengthUnit : LengthUnit)
      (timeUnit : TimeUnit),
    0 ≤ energyReadout massUnit lengthUnit timeUnit
      (setup.rotationalEnergyAtLevel n)

/-! ## Geometry, classical rotor laws, and Bohr quantization -/

/-- Each atom is at the figure-labelled radius `d/2` from the centered axis. -/
structure SatisfiesCenteredDiatomicGeometry
    (setup : DiatomicMolecularRotorSetup) : Prop where
  radiusIsHalfSeparation : ∀
      (atom : AtomRole) (lengthUnit : LengthUnit),
    lengthReadout lengthUnit (setup.orbitRadius atom) =
      lengthReadout lengthUnit setup.internuclearSeparation / 2

/--
Classical laws for a two-point-mass rotor: `I = Σ mᵢrᵢ²`, `L = Iω`, and
`E = Iω²/2`.  None contains the requested expression in `m`, `d`, `h`, and `n`.
-/
structure SatisfiesRigidDiatomicRotorLaws
    (setup : DiatomicMolecularRotorSetup) : Prop where
  pointMassMomentOfInertia : ∀
      (massUnit : MassUnit) (lengthUnit : LengthUnit),
    momentOfInertiaReadout massUnit lengthUnit
        setup.momentOfInertiaAboutAxis =
      ∑ atom : AtomRole,
        massReadout massUnit (setup.atomMass atom) *
          lengthReadout lengthUnit (setup.orbitRadius atom) ^ 2
  angularMomentumLaw : ∀
      (n : ℕ) (massUnit : MassUnit) (lengthUnit : LengthUnit)
      (timeUnit : TimeUnit),
    angularMomentumReadout massUnit lengthUnit timeUnit
        (setup.angularMomentumAtLevel n) =
      momentOfInertiaReadout massUnit lengthUnit
          setup.momentOfInertiaAboutAxis *
        angularSpeedReadout timeUnit (setup.angularSpeedAtLevel n)
  rotationalKineticEnergyLaw : ∀
      (n : ℕ) (massUnit : MassUnit) (lengthUnit : LengthUnit)
      (timeUnit : TimeUnit),
    energyReadout massUnit lengthUnit timeUnit
        (setup.rotationalEnergyAtLevel n) =
      momentOfInertiaReadout massUnit lengthUnit
          setup.momentOfInertiaAboutAxis *
        angularSpeedReadout timeUnit (setup.angularSpeedAtLevel n) ^ 2 / 2

/-- Bohr quantization of angular-momentum magnitude: `Lₙ = n h/(2π)`. -/
structure SatisfiesBohrAngularMomentumQuantization
    (setup : DiatomicMolecularRotorSetup) : Prop where
  angularMomentumQuantization : ∀
      (n : ℕ) (massUnit : MassUnit) (lengthUnit : LengthUnit)
      (timeUnit : TimeUnit),
    angularMomentumReadout massUnit lengthUnit timeUnit
        (setup.angularMomentumAtLevel n) =
      (n : ℝ) *
        planckConstantReadout massUnit lengthUnit timeUnit
          setup.ordinaryPlanckConstant /
        (2 * Real.pi)

/-! ## Intermediate consequences and quantized-energy target -/

/-- Two equal masses at radius `d/2` have `I = md²/2`. -/
lemma diatomic_momentOfInertia_readout
    (setup : DiatomicMolecularRotorSetup)
    (hScenario : MatchesDiatomicRotorScenario setup)
    (hGeometry : SatisfiesCenteredDiatomicGeometry setup)
    (hRotor : SatisfiesRigidDiatomicRotorLaws setup) :
    ∀ (massUnit : MassUnit) (lengthUnit : LengthUnit),
      momentOfInertiaReadout massUnit lengthUnit
          setup.momentOfInertiaAboutAxis =
        massReadout massUnit (setup.atomMass .leftAtom) *
          lengthReadout lengthUnit setup.internuclearSeparation ^ 2 / 2 := by
  intro massUnit lengthUnit
  rw [hRotor.pointMassMomentOfInertia]
  rw [show Finset.univ = {.leftAtom, .rightAtom} by
    ext atom
    fin_cases atom <;> simp]
  simp only [Finset.mem_singleton, reduceCtorEq, not_false_eq_true,
    Finset.sum_insert, Finset.sum_singleton]
  rw [hGeometry.radiusIsHalfSeparation,
    hGeometry.radiusIsHalfSeparation,
    ← hScenario.equalAtomMasses massUnit]
  ring

/-- The scalar-axis rotor laws imply `E = L²/(2I)`. -/
lemma rotationalEnergy_eq_angularMomentumSquared_div_inertia
    (setup : DiatomicMolecularRotorSetup)
    (hPhysical : HasPhysicalDiatomicRotorParameters setup)
    (hRotor : SatisfiesRigidDiatomicRotorLaws setup) :
    ∀ (n : ℕ) (massUnit : MassUnit) (lengthUnit : LengthUnit)
        (timeUnit : TimeUnit),
      energyReadout massUnit lengthUnit timeUnit
          (setup.rotationalEnergyAtLevel n) =
        angularMomentumReadout massUnit lengthUnit timeUnit
            (setup.angularMomentumAtLevel n) ^ 2 /
          (2 * momentOfInertiaReadout massUnit lengthUnit
            setup.momentOfInertiaAboutAxis) := by
  intro n massUnit lengthUnit timeUnit
  have hInertia_ne :
      momentOfInertiaReadout massUnit lengthUnit
          setup.momentOfInertiaAboutAxis ≠ 0 :=
    ne_of_gt (hPhysical.momentOfInertiaPositive massUnit lengthUnit)
  rw [hRotor.rotationalKineticEnergyLaw, hRotor.angularMomentumLaw]
  field_simp

/--
The possible rotational energies are
`Eₙ = n² h² / (4 π² m d²)` in every coherent unit system.
-/
lemma quantized_rotationalEnergy_readout
    (setup : DiatomicMolecularRotorSetup)
    (hScenario : MatchesDiatomicRotorScenario setup)
    (hPhysical : HasPhysicalDiatomicRotorParameters setup)
    (hGeometry : SatisfiesCenteredDiatomicGeometry setup)
    (hRotor : SatisfiesRigidDiatomicRotorLaws setup)
    (hQuantization : SatisfiesBohrAngularMomentumQuantization setup) :
    ∀ (n : ℕ) (massUnit : MassUnit) (lengthUnit : LengthUnit)
        (timeUnit : TimeUnit),
      energyReadout massUnit lengthUnit timeUnit
          (setup.rotationalEnergyAtLevel n) =
        (n : ℝ) ^ 2 *
            planckConstantReadout massUnit lengthUnit timeUnit
              setup.ordinaryPlanckConstant ^ 2 /
          (4 * Real.pi ^ 2 *
            massReadout massUnit (setup.atomMass .leftAtom) *
            lengthReadout lengthUnit setup.internuclearSeparation ^ 2) := by
  intro n massUnit lengthUnit timeUnit
  rw [rotationalEnergy_eq_angularMomentumSquared_div_inertia
    setup hPhysical hRotor]
  rw [hQuantization.angularMomentumQuantization]
  rw [diatomic_momentOfInertia_readout
    setup hScenario hGeometry hRotor]
  have hMass := hPhysical.atomMassPositive .leftAtom massUnit
  have hDistance := hPhysical.separationPositive lengthUnit
  have hPi := Real.pi_pos
  field_simp
  ring

/-! ## Multiple-choice data and final theorem -/

/-- Labels of the four formulas displayed in the source. -/
inductive AnswerChoice where
  | A
  | B
  | C
  | D
  deriving DecidableEq, Fintype, Repr

/-- The formula printed beside each answer choice, read in coherent units. -/
def displayedEnergyReadout
    (setup : DiatomicMolecularRotorSetup) (n : ℕ)
    (massUnit : MassUnit) (lengthUnit : LengthUnit) (timeUnit : TimeUnit) :
    AnswerChoice → ℝ
  | .A =>
      (n : ℝ) ^ 2 *
          planckConstantReadout massUnit lengthUnit timeUnit
            setup.ordinaryPlanckConstant ^ 2 /
        (2 * Real.pi ^ 2 *
          massReadout massUnit (setup.atomMass .leftAtom) *
          lengthReadout lengthUnit setup.internuclearSeparation ^ 2)
  | .B =>
      (n : ℝ) ^ 2 *
          planckConstantReadout massUnit lengthUnit timeUnit
            setup.ordinaryPlanckConstant ^ 2 /
        (8 * Real.pi ^ 2 *
          massReadout massUnit (setup.atomMass .leftAtom) *
          lengthReadout lengthUnit setup.internuclearSeparation ^ 2)
  | .C =>
      (n : ℝ) ^ 2 *
          planckConstantReadout massUnit lengthUnit timeUnit
            setup.ordinaryPlanckConstant ^ 2 /
        (4 * Real.pi ^ 2 *
          massReadout massUnit (setup.atomMass .leftAtom) *
          lengthReadout lengthUnit setup.internuclearSeparation ^ 2)
  | .D =>
      (n : ℝ) *
          planckConstantReadout massUnit lengthUnit timeUnit
            setup.ordinaryPlanckConstant ^ 2 /
        (4 * Real.pi ^ 2 *
          massReadout massUnit (setup.atomMass .leftAtom) *
          lengthReadout lengthUnit setup.internuclearSeparation ^ 2)

/-- The answer label recorded by the source dataset. -/
def recordedDatasetAnswer : AnswerChoice := .C

/-- A displayed choice agrees with the modeled energy at level `n`. -/
def MatchesAnswerChoice
    (setup : DiatomicMolecularRotorSetup) (n : ℕ)
    (massUnit : MassUnit) (lengthUnit : LengthUnit) (timeUnit : TimeUnit)
    (choice : AnswerChoice) : Prop :=
  energyReadout massUnit lengthUnit timeUnit
      (setup.rotationalEnergyAtLevel n) =
    displayedEnergyReadout setup n massUnit lengthUnit timeUnit choice

/--
The figure geometry, rigid-rotor mechanics, and Bohr quantization imply
`Eₙ = n²h²/(4π²md²)`, which is precisely answer choice C.

This is the declaration for `thm:physics:phyx_mini_0582:target`.
-/
theorem problem_phyx_mini_0582
    (setup : DiatomicMolecularRotorSetup)
    (hScenario : MatchesDiatomicRotorScenario setup)
    (hFigure : MatchesSuppliedDiatomicRotorFigure setup)
    (hPhysical : HasPhysicalDiatomicRotorParameters setup)
    (hGeometry : SatisfiesCenteredDiatomicGeometry setup)
    (hRotor : SatisfiesRigidDiatomicRotorLaws setup)
    (hQuantization : SatisfiesBohrAngularMomentumQuantization setup) :
    (∀ (n : ℕ) (massUnit : MassUnit) (lengthUnit : LengthUnit)
        (timeUnit : TimeUnit),
      energyReadout massUnit lengthUnit timeUnit
          (setup.rotationalEnergyAtLevel n) =
        (n : ℝ) ^ 2 *
            planckConstantReadout massUnit lengthUnit timeUnit
              setup.ordinaryPlanckConstant ^ 2 /
          (4 * Real.pi ^ 2 *
            massReadout massUnit (setup.atomMass .leftAtom) *
            lengthReadout lengthUnit setup.internuclearSeparation ^ 2)) ∧
      (∀ (n : ℕ) (massUnit : MassUnit) (lengthUnit : LengthUnit)
          (timeUnit : TimeUnit),
        MatchesAnswerChoice setup n massUnit lengthUnit timeUnit
          recordedDatasetAnswer) := by
  have hEnergy :=
    quantized_rotationalEnergy_readout setup hScenario hPhysical hGeometry
      hRotor hQuantization
  constructor
  · exact hEnergy
  · intro n massUnit lengthUnit timeUnit
    simpa [MatchesAnswerChoice, recordedDatasetAnswer,
      displayedEnergyReadout] using
      hEnergy n massUnit lengthUnit timeUnit

end PhyXMiniProblems.ProblemPhyXMini0582
