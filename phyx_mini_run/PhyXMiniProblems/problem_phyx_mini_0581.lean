import Mathlib
import Physlib.ClassicalMechanics.Mass.MassUnit
import Physlib.QuantumMechanics.PlanckConstant
import Physlib.Units.WithDim.Energy

noncomputable section

namespace PhyXMiniProblems.ProblemPhyXMini0581

open Dimension
open scoped BigOperators

/-!
# First excited energy of eleven noninteracting electrons in a well

The primary figure shows five one-electron energy levels.  Their energies are
`4`, `6`, `7`, `11`, and `12` times the unit `h^2 / (8 m L^2)`, and their
printed orbital-degeneracy annotations are respectively ground/nondegenerate,
triple, double, triple, and nondegenerate.

Physical lengths, masses, actions, and energies are represented by Physlib
dimensionful quantities.  Natural numbers are used only for electron counts,
orbital degeneracies, and the integer multipliers printed in the diagram.

Assumption/target split:

* governing laws: the infinite-well energy scale, Pauli capacity with two spin
  states per orbital, additivity of noninteracting one-electron energies, and
  the order-theoretic meanings of ground and first-excited configurations;
* previous-part results: none;
* figure/data readouts: the five level multipliers and printed degeneracies,
  one electron in the reference diagram, and eleven electrons in the system;
* current conclusions: the ground occupation/energy multiplier `65`, the
  first-excited occupation, and the requested multiplier `66` (choice C).
-/

/-! ## Dimensionful physical quantities and readouts -/

/-- A nonnegative, unit-independent physical length. -/
abbrev LengthQuantity : Type :=
  Dimensionful (WithDim L𝓭 NNReal)

/-- A nonnegative, unit-independent physical mass. -/
abbrev MassQuantity : Type :=
  Dimensionful (WithDim M𝓭 NNReal)

/-- The physical dimension of action, used for the ordinary Planck constant. -/
def actionDimension : Dimension :=
  M𝓭 * L𝓭 * L𝓭 * T𝓭⁻¹

/-- A nonnegative, unit-independent physical action. -/
abbrev ActionQuantity : Type :=
  Dimensionful (WithDim actionDimension NNReal)

/-- Read a physical length in the selected length unit. -/
def lengthReadout (unit : LengthUnit) (length : LengthQuantity) : ℝ :=
  ((length {UnitChoices.SI with length := unit}).val : ℝ)

/-- Read a physical mass in the selected mass unit. -/
def massReadout (unit : MassUnit) (mass : MassQuantity) : ℝ :=
  ((mass {UnitChoices.SI with mass := unit}).val : ℝ)

/-- Width of the well, read in metres. -/
def lengthInMeters (length : LengthQuantity) : ℝ :=
  lengthReadout LengthUnit.meters length

/-- Electron mass, read in kilograms. -/
def massInKilograms (mass : MassQuantity) : ℝ :=
  massReadout MassUnit.kilograms mass

/-- Ordinary Planck action, read coherently in joule-seconds. -/
def actionInJouleSeconds (action : ActionQuantity) : ℝ :=
  ((action UnitChoices.SI).val : ℝ)

/-- Read an energy in an arbitrary coherent choice of units. -/
def energyReadout (units : UnitChoices) (energy : DimEnergy) : ℝ :=
  (energy units).val

/-- Read an energy in coherent SI units, hence in joules. -/
def energyInJoules (energy : DimEnergy) : ℝ :=
  energyReadout UnitChoices.SI energy

/-!
`energy` is `multiplier` times `scale` independently of the units used to read
the two energies.  This is the dimensionally meaningful form of the multiple
asked for in the problem.
-/
def IsEnergyMultipleOf
    (energy scale : DimEnergy) (multiplier : ℕ) : Prop :=
  ∀ units : UnitChoices,
    energyReadout units energy =
      (multiplier : ℝ) * energyReadout units scale

/-! ## Figure labels and electron configurations -/

/-- The five one-electron levels shown in the supplied diagram. -/
inductive WellEnergyLevel where
  | level4
  | level6
  | level7
  | level11
  | level12
  deriving DecidableEq, Fintype, Repr

/-- Literal kinds of annotations printed to the right of the level lines. -/
inductive PrintedLevelAnnotation where
  | ground
  | nondegenerate
  | double
  | triple
  deriving DecidableEq, Repr

/-- Orbital multiplicity represented by each printed annotation. -/
def PrintedLevelAnnotation.spatialMultiplicity :
    PrintedLevelAnnotation → ℕ
  | .ground => 1
  | .nondegenerate => 1
  | .double => 2
  | .triple => 3

/-!
Primary-image data.  The axis label records that the displayed vertical
numbers are multiples of `h^2 / (8mL^2)` rather than bare energies.
-/
structure InfiniteWellEnergyDiagram where
  verticalAxisLabel : String
  levelLineShown : WellEnergyLevel → Bool
  levelLineHorizontal : WellEnergyLevel → Bool
  printedEnergyMultiplier : WellEnergyLevel → ℕ
  printedAnnotation : WellEnergyLevel → PrintedLevelAnnotation

/-- Particle species represented by the occupation numbers. -/
inductive ParticleSpecies where
  | electron
  | other
  deriving DecidableEq, Repr

/-- Potential model selected in the fictitious problem. -/
inductive PotentialModel where
  | infinitePotentialWell
  | other
  deriving DecidableEq, Repr

/-- Number of electrons occupying each displayed one-particle energy level. -/
abbrev ElectronConfiguration : Type :=
  WellEnergyLevel → ℕ

/-!
Independent physical quantities and states of the model.  Neither the ground
nor first-excited configuration is defined by an answer choice or by a
numerical occupation pattern; the predicates below characterize them by
Pauli admissibility and energy order.
-/
structure ElevenElectronWellSetup where
  particleSpecies : ParticleSpecies
  potentialModel : PotentialModel
  ordinaryPlanckAction : ActionQuantity
  electronMass : MassQuantity
  wellWidth : LengthQuantity
  oneParticleEnergyScale : DimEnergy
  oneParticleLevelEnergy : WellEnergyLevel → DimEnergy
  spatialDegeneracy : WellEnergyLevel → ℕ
  spinMultiplicity : ℕ
  referenceDiagramElectronCount : ℕ
  totalElectronCount : ℕ
  manyElectronEnergy : ElectronConfiguration → DimEnergy
  groundConfiguration : ElectronConfiguration
  firstExcitedConfiguration : ElectronConfiguration
  electrostaticInteractionsNeglected : Bool
  diagramListsAllRelevantLevels : Bool
  diagram : InfiniteWellEnergyDiagram

/-- Total number of electrons in an occupation-number configuration. -/
def configurationElectronCount (configuration : ElectronConfiguration) : ℕ :=
  ∑ level : WellEnergyLevel, configuration level

/-- Pauli capacity of a level: spin multiplicity times orbital degeneracy. -/
def pauliCapacity
    (setup : ElevenElectronWellSetup) (level : WellEnergyLevel) : ℕ :=
  setup.spinMultiplicity * setup.spatialDegeneracy level

/--
An eleven-electron configuration obeys particle-number conservation and the
Pauli capacity of every displayed level.
-/
def IsAdmissibleConfiguration
    (setup : ElevenElectronWellSetup)
    (configuration : ElectronConfiguration) : Prop :=
  configurationElectronCount configuration = setup.totalElectronCount ∧
    ∀ level, configuration level ≤ pauliCapacity setup level

/-- SI energy readout of a many-electron occupation configuration. -/
def configurationEnergyInJoules
    (setup : ElevenElectronWellSetup)
    (configuration : ElectronConfiguration) : ℝ :=
  energyInJoules (setup.manyElectronEnergy configuration)

/-- An admissible configuration of least many-electron energy. -/
def IsGroundConfiguration
    (setup : ElevenElectronWellSetup)
    (configuration : ElectronConfiguration) : Prop :=
  IsAdmissibleConfiguration setup configuration ∧
    ∀ other, IsAdmissibleConfiguration setup other →
      configurationEnergyInJoules setup configuration ≤
        configurationEnergyInJoules setup other

/-!
An admissible state of least energy strictly above a specified ground state.
This definition permits degeneracy at the first-excited energy.
-/
def IsFirstExcitedConfiguration
    (setup : ElevenElectronWellSetup)
    (ground excited : ElectronConfiguration) : Prop :=
  IsGroundConfiguration setup ground ∧
    IsAdmissibleConfiguration setup excited ∧
    configurationEnergyInJoules setup ground <
      configurationEnergyInJoules setup excited ∧
    ∀ other, IsAdmissibleConfiguration setup other →
      configurationEnergyInJoules setup ground <
        configurationEnergyInJoules setup other →
      configurationEnergyInJoules setup excited ≤
        configurationEnergyInJoules setup other

/-! ## Scenario facts, figure evidence, and governing laws -/

/-- Prose data and modeling regime stated in the problem. -/
structure MatchesElevenElectronWellScenario
    (setup : ElevenElectronWellSetup) : Prop where
  particlesAreElectrons : setup.particleSpecies = .electron
  wellIsInfinite : setup.potentialModel = .infinitePotentialWell
  referenceDiagramHasOneElectron : setup.referenceDiagramElectronCount = 1
  systemHasElevenElectrons : setup.totalElectronCount = 11
  electronSpinMultiplicity : setup.spinMultiplicity = 2
  electrostaticInteractionsAreNeglected :
    setup.electrostaticInteractionsNeglected = true
  allRelevantLevelsAreDisplayed : setup.diagramListsAllRelevantLevels = true

/-!
Exact level values and annotations transcribed from the primary image, together
with the calibration of physical one-particle energies and degeneracies from
those readouts.  No many-electron energy or occupation pattern occurs here.
-/
structure MatchesSuppliedInfiniteWellDiagram
    (setup : ElevenElectronWellSetup) : Prop where
  verticalAxisLabel : setup.diagram.verticalAxisLabel = "E (h²/8mL²)"
  everyLevelLineShown :
    ∀ level, setup.diagram.levelLineShown level = true
  everyLevelLineHorizontal :
    ∀ level, setup.diagram.levelLineHorizontal level = true
  level4Multiplier : setup.diagram.printedEnergyMultiplier .level4 = 4
  level6Multiplier : setup.diagram.printedEnergyMultiplier .level6 = 6
  level7Multiplier : setup.diagram.printedEnergyMultiplier .level7 = 7
  level11Multiplier : setup.diagram.printedEnergyMultiplier .level11 = 11
  level12Multiplier : setup.diagram.printedEnergyMultiplier .level12 = 12
  level4GroundAnnotation :
    setup.diagram.printedAnnotation .level4 = .ground
  level6TripleAnnotation :
    setup.diagram.printedAnnotation .level6 = .triple
  level7DoubleAnnotation :
    setup.diagram.printedAnnotation .level7 = .double
  level11TripleAnnotation :
    setup.diagram.printedAnnotation .level11 = .triple
  level12NondegenerateAnnotation :
    setup.diagram.printedAnnotation .level12 = .nondegenerate
  levelEnergyCalibration : ∀ (units : UnitChoices) level,
    energyReadout units (setup.oneParticleLevelEnergy level) =
      (setup.diagram.printedEnergyMultiplier level : ℝ) *
        energyReadout units setup.oneParticleEnergyScale
  degeneracyCalibration : ∀ level,
    setup.spatialDegeneracy level =
      (setup.diagram.printedAnnotation level).spatialMultiplicity

/-!
The displayed energy unit is the physical quantity `h²/(8mL²)`.  The equality
is expressed using coherent SI readouts, where its right side is in joules.
This scale law does not specify any many-electron state or answer multiplier.
-/
structure SatisfiesInfiniteWellEnergyScaleLaw
    (setup : ElevenElectronWellSetup) : Prop where
  scaleIsHSquaredOverEightMLSquared :
    energyInJoules setup.oneParticleEnergyScale =
      actionInJouleSeconds setup.ordinaryPlanckAction ^ 2 /
        (8 * massInKilograms setup.electronMass *
          lengthInMeters setup.wellWidth ^ 2)

/-!
Physlib exposes the reduced Planck constant `Constants.ℏ`; the ordinary
constant in the figure is `h = 2πℏ`.  This reference fact remains symbolic
with respect to the requested integer multiplier.
-/
structure UsesOrdinaryPlanckConstant
    (setup : ElevenElectronWellSetup) : Prop where
  ordinaryPlanckConstantReadout :
    actionInJouleSeconds setup.ordinaryPlanckAction =
      2 * Real.pi * (Constants.ℏ : ℝ)

/-- Positivity assumptions selecting a physically meaningful well. -/
structure HasPhysicalInfiniteWellParameters
    (setup : ElevenElectronWellSetup) : Prop where
  positivePlanckAction :
    0 < actionInJouleSeconds setup.ordinaryPlanckAction
  positiveElectronMass : 0 < massInKilograms setup.electronMass
  positiveWellWidth : 0 < lengthInMeters setup.wellWidth
  positiveEnergyScale : 0 < energyInJoules setup.oneParticleEnergyScale

/-!
When electrostatic interactions are neglected, the many-electron energy is
the sum of occupied one-electron energies.  This law is stated for every
admissible configuration and in every unit choice; it contains no special
occupation pattern and no answer multiplier.
-/
structure SatisfiesNoninteractingElectronEnergyLaw
    (setup : ElevenElectronWellSetup) : Prop where
  energyIsSumOfOccupiedLevelEnergies :
    ∀ (units : UnitChoices) (configuration : ElectronConfiguration),
      IsAdmissibleConfiguration setup configuration →
      energyReadout units (setup.manyElectronEnergy configuration) =
        ∑ level : WellEnergyLevel,
          (configuration level : ℝ) *
            energyReadout units (setup.oneParticleLevelEnergy level)

/-!
The two distinguished configuration fields really denote the ground and
first-excited states according to the general energy-order definitions above.
No numerical energy or occupation is assumed.
-/
structure HasGroundAndFirstExcitedConfigurations
    (setup : ElevenElectronWellSetup) : Prop where
  groundStateCharacterization :
    IsGroundConfiguration setup setup.groundConfiguration
  firstExcitedStateCharacterization :
    IsFirstExcitedConfiguration setup setup.groundConfiguration
      setup.firstExcitedConfiguration

/-! ## Displayed choices and current conclusions -/

/-- Labels of the four displayed energy-multiplier choices. -/
inductive AnswerChoice where
  | A
  | B
  | C
  | D
  deriving DecidableEq, Fintype, Repr

/-- Integer multiple of `h²/(8mL²)` printed beside an answer choice. -/
def AnswerChoice.energyMultiplier : AnswerChoice → ℕ
  | .A => 65
  | .B => 68
  | .C => 66
  | .D => 64

/-- Answer label recorded in the source dataset. -/
def recordedDatasetAnswer : AnswerChoice := .C

/-- A displayed choice matches the physical first-excited system energy. -/
def MatchesDisplayedFirstExcitedEnergy
    (setup : ElevenElectronWellSetup) (choice : AnswerChoice) : Prop :=
  IsEnergyMultipleOf
    (setup.manyElectronEnergy setup.firstExcitedConfiguration)
    setup.oneParticleEnergyScale choice.energyMultiplier

/-!
Filling the lowest Pauli capacities gives the eleven-electron ground
occupation `(2, 6, 3, 0, 0)` and total multiplier
`2·4 + 6·6 + 3·7 = 65`.
-/
lemma ground_configuration_occupation_and_energy
    (setup : ElevenElectronWellSetup)
    (_scenario : MatchesElevenElectronWellScenario setup)
    (_figure : MatchesSuppliedInfiniteWellDiagram setup)
    (_physical : HasPhysicalInfiniteWellParameters setup)
    (_energyLaw : SatisfiesNoninteractingElectronEnergyLaw setup)
    (_states : HasGroundAndFirstExcitedConfigurations setup) :
    setup.groundConfiguration .level4 = 2 ∧
      setup.groundConfiguration .level6 = 6 ∧
      setup.groundConfiguration .level7 = 3 ∧
      setup.groundConfiguration .level11 = 0 ∧
      setup.groundConfiguration .level12 = 0 ∧
      IsEnergyMultipleOf
        (setup.manyElectronEnergy setup.groundConfiguration)
        setup.oneParticleEnergyScale 65 := by
  classical
  have sum_levels_nat (f : WellEnergyLevel → ℕ) :
      (∑ level : WellEnergyLevel, f level) =
        f .level4 + f .level6 + f .level7 + f .level11 + f .level12 := by
    rw [show (Finset.univ : Finset WellEnergyLevel) =
      {.level4, .level6, .level7, .level11, .level12} by decide]
    simp [add_assoc]
  have sum_levels_real (f : WellEnergyLevel → ℝ) :
      (∑ level : WellEnergyLevel, f level) =
        f .level4 + f .level6 + f .level7 + f .level11 + f .level12 := by
    rw [show (Finset.univ : Finset WellEnergyLevel) =
      {.level4, .level6, .level7, .level11, .level12} by decide]
    simp [add_assoc]
  let candidate : ElectronConfiguration := fun level =>
    match level with
    | .level4 => 2
    | .level6 => 6
    | .level7 => 3
    | .level11 => 0
    | .level12 => 0
  have hcand : IsAdmissibleConfiguration setup candidate := by
    constructor
    · rw [_scenario.systemHasElevenElectrons]
      simp [configurationElectronCount, sum_levels_nat, candidate]
    · intro level
      cases level <;>
        simp [pauliCapacity, candidate, _scenario.electronSpinMultiplicity,
          _figure.degeneracyCalibration, _figure.level4GroundAnnotation,
          _figure.level6TripleAnnotation, _figure.level7DoubleAnnotation,
          _figure.level11TripleAnnotation,
          _figure.level12NondegenerateAnnotation,
          PrintedLevelAnnotation.spatialMultiplicity]
  have hgroundAdm := _states.groundStateCharacterization.1
  have hcount := hgroundAdm.1
  simp only [configurationElectronCount, sum_levels_nat,
    _scenario.systemHasElevenElectrons] at hcount
  have hcap4 := hgroundAdm.2 .level4
  have hcap6 := hgroundAdm.2 .level6
  have hcap7 := hgroundAdm.2 .level7
  have hcap11 := hgroundAdm.2 .level11
  have hcap12 := hgroundAdm.2 .level12
  simp [pauliCapacity, _scenario.electronSpinMultiplicity,
    _figure.degeneracyCalibration, _figure.level4GroundAnnotation,
    _figure.level6TripleAnnotation, _figure.level7DoubleAnnotation,
    _figure.level11TripleAnnotation,
    _figure.level12NondegenerateAnnotation,
    PrintedLevelAnnotation.spatialMultiplicity] at hcap4 hcap6 hcap7 hcap11 hcap12
  have hmin := _states.groundStateCharacterization.2 candidate hcand
  change
    energyReadout UnitChoices.SI
        (setup.manyElectronEnergy setup.groundConfiguration) ≤
      energyReadout UnitChoices.SI (setup.manyElectronEnergy candidate) at hmin
  rw [_energyLaw.energyIsSumOfOccupiedLevelEnergies UnitChoices.SI
      setup.groundConfiguration hgroundAdm,
    _energyLaw.energyIsSumOfOccupiedLevelEnergies UnitChoices.SI candidate hcand,
    sum_levels_real, sum_levels_real] at hmin
  have hlevel4 := _figure.levelEnergyCalibration UnitChoices.SI .level4
  have hlevel6 := _figure.levelEnergyCalibration UnitChoices.SI .level6
  have hlevel7 := _figure.levelEnergyCalibration UnitChoices.SI .level7
  have hlevel11 := _figure.levelEnergyCalibration UnitChoices.SI .level11
  have hlevel12 := _figure.levelEnergyCalibration UnitChoices.SI .level12
  rw [_figure.level4Multiplier] at hlevel4
  rw [_figure.level6Multiplier] at hlevel6
  rw [_figure.level7Multiplier] at hlevel7
  rw [_figure.level11Multiplier] at hlevel11
  rw [_figure.level12Multiplier] at hlevel12
  rw [hlevel4, hlevel6, hlevel7, hlevel11, hlevel12] at hmin
  dsimp [candidate] at hmin
  ring_nf at hmin
  have hs := _physical.positiveEnergyScale
  change 0 < energyReadout UnitChoices.SI setup.oneParticleEnergyScale at hs
  have hweight :
      (4 : ℝ) * setup.groundConfiguration .level4 +
        6 * setup.groundConfiguration .level6 +
        7 * setup.groundConfiguration .level7 +
        11 * setup.groundConfiguration .level11 +
        12 * setup.groundConfiguration .level12 ≤ 65 := by
    nlinarith
  have hweightNat :
      4 * setup.groundConfiguration .level4 +
        6 * setup.groundConfiguration .level6 +
        7 * setup.groundConfiguration .level7 +
        11 * setup.groundConfiguration .level11 +
        12 * setup.groundConfiguration .level12 ≤ 65 := by
    exact_mod_cast hweight
  have h4 : setup.groundConfiguration .level4 = 2 := by omega
  have h6 : setup.groundConfiguration .level6 = 6 := by omega
  have h7 : setup.groundConfiguration .level7 = 3 := by omega
  have h11 : setup.groundConfiguration .level11 = 0 := by omega
  have h12 : setup.groundConfiguration .level12 = 0 := by omega
  refine ⟨h4, h6, h7, h11, h12, ?_⟩
  intro units
  rw [_energyLaw.energyIsSumOfOccupiedLevelEnergies units
      setup.groundConfiguration hgroundAdm,
    sum_levels_real]
  have ulevel4 := _figure.levelEnergyCalibration units .level4
  have ulevel6 := _figure.levelEnergyCalibration units .level6
  have ulevel7 := _figure.levelEnergyCalibration units .level7
  have ulevel11 := _figure.levelEnergyCalibration units .level11
  have ulevel12 := _figure.levelEnergyCalibration units .level12
  rw [_figure.level4Multiplier] at ulevel4
  rw [_figure.level6Multiplier] at ulevel6
  rw [_figure.level7Multiplier] at ulevel7
  rw [_figure.level11Multiplier] at ulevel11
  rw [_figure.level12Multiplier] at ulevel12
  rw [ulevel4, ulevel6, ulevel7, ulevel11, ulevel12,
    h4, h6, h7, h11, h12]
  ring

/-!
The least energy strictly above the ground state moves one electron from the
filled multiplier-`6` level into the one remaining spin-orbital at multiplier
`7`, giving occupation `(2, 5, 4, 0, 0)`.
-/
lemma first_excited_configuration_occupation
    (setup : ElevenElectronWellSetup)
    (_scenario : MatchesElevenElectronWellScenario setup)
    (_figure : MatchesSuppliedInfiniteWellDiagram setup)
    (_physical : HasPhysicalInfiniteWellParameters setup)
    (_energyLaw : SatisfiesNoninteractingElectronEnergyLaw setup)
    (_states : HasGroundAndFirstExcitedConfigurations setup) :
    setup.firstExcitedConfiguration .level4 = 2 ∧
      setup.firstExcitedConfiguration .level6 = 5 ∧
      setup.firstExcitedConfiguration .level7 = 4 ∧
      setup.firstExcitedConfiguration .level11 = 0 ∧
      setup.firstExcitedConfiguration .level12 = 0 := by
  classical
  have sum_levels_nat (f : WellEnergyLevel → ℕ) :
      (∑ level : WellEnergyLevel, f level) =
        f .level4 + f .level6 + f .level7 + f .level11 + f .level12 := by
    rw [show (Finset.univ : Finset WellEnergyLevel) =
      {.level4, .level6, .level7, .level11, .level12} by decide]
    simp [add_assoc]
  have sum_levels_real (f : WellEnergyLevel → ℝ) :
      (∑ level : WellEnergyLevel, f level) =
        f .level4 + f .level6 + f .level7 + f .level11 + f .level12 := by
    rw [show (Finset.univ : Finset WellEnergyLevel) =
      {.level4, .level6, .level7, .level11, .level12} by decide]
    simp [add_assoc]
  rcases ground_configuration_occupation_and_energy setup _scenario _figure
      _physical _energyLaw _states with
    ⟨_g4, _g6, _g7, _g11, _g12, hgroundMultiple⟩
  let candidate : ElectronConfiguration := fun level =>
    match level with
    | .level4 => 2
    | .level6 => 5
    | .level7 => 4
    | .level11 => 0
    | .level12 => 0
  have hcand : IsAdmissibleConfiguration setup candidate := by
    constructor
    · rw [_scenario.systemHasElevenElectrons]
      simp [configurationElectronCount, sum_levels_nat, candidate]
    · intro level
      cases level <;>
        simp [pauliCapacity, candidate, _scenario.electronSpinMultiplicity,
          _figure.degeneracyCalibration, _figure.level4GroundAnnotation,
          _figure.level6TripleAnnotation, _figure.level7DoubleAnnotation,
          _figure.level11TripleAnnotation,
          _figure.level12NondegenerateAnnotation,
          PrintedLevelAnnotation.spatialMultiplicity]
  have hfirst := _states.firstExcitedStateCharacterization
  have hexcAdm := hfirst.2.1
  have hgroundEnergy := hgroundMultiple UnitChoices.SI
  have hcandMultiple :
      IsEnergyMultipleOf (setup.manyElectronEnergy candidate)
        setup.oneParticleEnergyScale 66 := by
    intro units
    rw [_energyLaw.energyIsSumOfOccupiedLevelEnergies units candidate hcand,
      sum_levels_real]
    have ulevel4 := _figure.levelEnergyCalibration units .level4
    have ulevel6 := _figure.levelEnergyCalibration units .level6
    have ulevel7 := _figure.levelEnergyCalibration units .level7
    have ulevel11 := _figure.levelEnergyCalibration units .level11
    have ulevel12 := _figure.levelEnergyCalibration units .level12
    rw [_figure.level4Multiplier] at ulevel4
    rw [_figure.level6Multiplier] at ulevel6
    rw [_figure.level7Multiplier] at ulevel7
    rw [_figure.level11Multiplier] at ulevel11
    rw [_figure.level12Multiplier] at ulevel12
    rw [ulevel4, ulevel6, ulevel7, ulevel11, ulevel12]
    dsimp [candidate]
    ring
  have hcandEnergy := hcandMultiple UnitChoices.SI
  norm_num at hgroundEnergy hcandEnergy
  have hs := _physical.positiveEnergyScale
  change 0 < energyReadout UnitChoices.SI setup.oneParticleEnergyScale at hs
  have hgroundCand :
      configurationEnergyInJoules setup setup.groundConfiguration <
        configurationEnergyInJoules setup candidate := by
    change
      energyReadout UnitChoices.SI
          (setup.manyElectronEnergy setup.groundConfiguration) <
        energyReadout UnitChoices.SI (setup.manyElectronEnergy candidate)
    rw [hgroundEnergy, hcandEnergy]
    exact mul_lt_mul_of_pos_right (by norm_num) hs
  have hmin := hfirst.2.2.2 candidate hcand hgroundCand
  change
    energyReadout UnitChoices.SI
        (setup.manyElectronEnergy setup.firstExcitedConfiguration) ≤
      energyReadout UnitChoices.SI (setup.manyElectronEnergy candidate) at hmin
  rw [_energyLaw.energyIsSumOfOccupiedLevelEnergies UnitChoices.SI
      setup.firstExcitedConfiguration hexcAdm,
    hcandEnergy, sum_levels_real] at hmin
  have hlevel4 := _figure.levelEnergyCalibration UnitChoices.SI .level4
  have hlevel6 := _figure.levelEnergyCalibration UnitChoices.SI .level6
  have hlevel7 := _figure.levelEnergyCalibration UnitChoices.SI .level7
  have hlevel11 := _figure.levelEnergyCalibration UnitChoices.SI .level11
  have hlevel12 := _figure.levelEnergyCalibration UnitChoices.SI .level12
  rw [_figure.level4Multiplier] at hlevel4
  rw [_figure.level6Multiplier] at hlevel6
  rw [_figure.level7Multiplier] at hlevel7
  rw [_figure.level11Multiplier] at hlevel11
  rw [_figure.level12Multiplier] at hlevel12
  rw [hlevel4, hlevel6, hlevel7, hlevel11, hlevel12] at hmin
  ring_nf at hmin
  have habove := hfirst.2.2.1
  change
    energyReadout UnitChoices.SI
        (setup.manyElectronEnergy setup.groundConfiguration) <
      energyReadout UnitChoices.SI
        (setup.manyElectronEnergy setup.firstExcitedConfiguration) at habove
  rw [hgroundEnergy,
    _energyLaw.energyIsSumOfOccupiedLevelEnergies UnitChoices.SI
      setup.firstExcitedConfiguration hexcAdm,
    sum_levels_real, hlevel4, hlevel6, hlevel7, hlevel11, hlevel12] at habove
  ring_nf at habove
  have hweight_le :
      (4 : ℝ) * setup.firstExcitedConfiguration .level4 +
        6 * setup.firstExcitedConfiguration .level6 +
        7 * setup.firstExcitedConfiguration .level7 +
        11 * setup.firstExcitedConfiguration .level11 +
        12 * setup.firstExcitedConfiguration .level12 ≤ 66 := by
    nlinarith
  have hweight_gt :
      (65 : ℝ) <
        4 * setup.firstExcitedConfiguration .level4 +
          6 * setup.firstExcitedConfiguration .level6 +
          7 * setup.firstExcitedConfiguration .level7 +
          11 * setup.firstExcitedConfiguration .level11 +
          12 * setup.firstExcitedConfiguration .level12 := by
    nlinarith
  have hweightNat_le :
      4 * setup.firstExcitedConfiguration .level4 +
        6 * setup.firstExcitedConfiguration .level6 +
        7 * setup.firstExcitedConfiguration .level7 +
        11 * setup.firstExcitedConfiguration .level11 +
        12 * setup.firstExcitedConfiguration .level12 ≤ 66 := by
    exact_mod_cast hweight_le
  have hweightNat_gt :
      65 <
        4 * setup.firstExcitedConfiguration .level4 +
          6 * setup.firstExcitedConfiguration .level6 +
          7 * setup.firstExcitedConfiguration .level7 +
          11 * setup.firstExcitedConfiguration .level11 +
          12 * setup.firstExcitedConfiguration .level12 := by
    exact_mod_cast hweight_gt
  have hcount := hexcAdm.1
  simp only [configurationElectronCount, sum_levels_nat,
    _scenario.systemHasElevenElectrons] at hcount
  have hcap4 := hexcAdm.2 .level4
  have hcap6 := hexcAdm.2 .level6
  have hcap7 := hexcAdm.2 .level7
  have hcap11 := hexcAdm.2 .level11
  have hcap12 := hexcAdm.2 .level12
  simp [pauliCapacity, _scenario.electronSpinMultiplicity,
    _figure.degeneracyCalibration, _figure.level4GroundAnnotation,
    _figure.level6TripleAnnotation, _figure.level7DoubleAnnotation,
    _figure.level11TripleAnnotation,
    _figure.level12NondegenerateAnnotation,
    PrintedLevelAnnotation.spatialMultiplicity] at hcap4 hcap6 hcap7 hcap11 hcap12
  omega

/-!
The first-excited many-electron energy is
`2·4 + 5·6 + 4·7 = 66` times `h²/(8mL²)`, so displayed choice C is correct.

Blueprint: `thm:physics:phyx_mini_0581:target`.
-/
theorem firstExcitedEnergyOfElevenElectrons_is_choiceC
    (setup : ElevenElectronWellSetup)
    (_scenario : MatchesElevenElectronWellScenario setup)
    (_figure : MatchesSuppliedInfiniteWellDiagram setup)
    (_scaleLaw : SatisfiesInfiniteWellEnergyScaleLaw setup)
    (_planck : UsesOrdinaryPlanckConstant setup)
    (_physical : HasPhysicalInfiniteWellParameters setup)
    (_energyLaw : SatisfiesNoninteractingElectronEnergyLaw setup)
    (_states : HasGroundAndFirstExcitedConfigurations setup) :
    IsEnergyMultipleOf
        (setup.manyElectronEnergy setup.firstExcitedConfiguration)
        setup.oneParticleEnergyScale 66 ∧
      AnswerChoice.energyMultiplier .C = 66 ∧
      MatchesDisplayedFirstExcitedEnergy setup .C := by
  classical
  have sum_levels_real (f : WellEnergyLevel → ℝ) :
      (∑ level : WellEnergyLevel, f level) =
        f .level4 + f .level6 + f .level7 + f .level11 + f .level12 := by
    rw [show (Finset.univ : Finset WellEnergyLevel) =
      {.level4, .level6, .level7, .level11, .level12} by decide]
    simp [add_assoc]
  rcases first_excited_configuration_occupation setup _scenario _figure
      _physical _energyLaw _states with
    ⟨h4, h6, h7, h11, h12⟩
  have hexcAdm :=
    _states.firstExcitedStateCharacterization.2.1
  have hmultiple :
      IsEnergyMultipleOf
        (setup.manyElectronEnergy setup.firstExcitedConfiguration)
        setup.oneParticleEnergyScale 66 := by
    intro units
    rw [_energyLaw.energyIsSumOfOccupiedLevelEnergies units
        setup.firstExcitedConfiguration hexcAdm,
      sum_levels_real]
    have ulevel4 := _figure.levelEnergyCalibration units .level4
    have ulevel6 := _figure.levelEnergyCalibration units .level6
    have ulevel7 := _figure.levelEnergyCalibration units .level7
    have ulevel11 := _figure.levelEnergyCalibration units .level11
    have ulevel12 := _figure.levelEnergyCalibration units .level12
    rw [_figure.level4Multiplier] at ulevel4
    rw [_figure.level6Multiplier] at ulevel6
    rw [_figure.level7Multiplier] at ulevel7
    rw [_figure.level11Multiplier] at ulevel11
    rw [_figure.level12Multiplier] at ulevel12
    rw [ulevel4, ulevel6, ulevel7, ulevel11, ulevel12,
      h4, h6, h7, h11, h12]
    ring
  refine ⟨hmultiple, rfl, ?_⟩
  simpa [MatchesDisplayedFirstExcitedEnergy,
    AnswerChoice.energyMultiplier] using hmultiple

end PhyXMiniProblems.ProblemPhyXMini0581
