import Mathlib
import Physlib.Units.WithDim.Energy

noncomputable section

namespace PhyXMiniProblems.ProblemPhyXMini0580

open Dimension
open scoped BigOperators

/-!
# Ground-state energy of 22 electrons in a three-dimensional infinite well

The primary raster is a one-particle energy-level diagram.  It lists energy
multipliers `3, 6, 9, 11, 12, 14` in units of
`h² / (8 m L²)`.  The levels at `6, 9, 11, 14` are triply degenerate, while
the ground level at `3` and the level at `12` are nondegenerate.

The model below keeps action, mass, length, and energy as unit-independent
Physlib quantities.  Real numbers are used only for coherent-SI readouts and
for the dimensionless multipliers printed in the figure.  The Pauli capacity,
noninteracting energy sum, and minimum-energy characterization are governing
laws; neither the occupation numbers nor the requested multiplier `186` occur
in a hypothesis.

Assumption/target split:

* governing laws: the `h²/(8mL²)` energy scale, diagram-to-spectrum relation,
  two-spin Pauli capacity, negligible electron interaction, additive energy,
  and minimum-energy characterization of the ground state;
* previous-part results: none;
* figure/data readouts: the six multipliers, degeneracy words, line order,
  horizontal blue geometry, a one-electron source diagram, and 22 electrons
  in the system being asked about;
* target conclusions: the filled-shell occupation counts and the total
  ground-state energy multiplier `186`, which selects answer C.
-/

/-! ## Dimensionful physical quantities and SI readouts -/

/-- A nonnegative, unit-independent physical length. -/
abbrev LengthQuantity : Type := Dimensionful (WithDim L𝓭 NNReal)

/-- A nonnegative, unit-independent physical mass. -/
abbrev MassQuantity : Type := Dimensionful (WithDim M𝓭 NNReal)

/-- The physical dimension `M L² T⁻¹` of action. -/
def actionDimension : Dimension := M𝓭 * L𝓭 * L𝓭 * T𝓭⁻¹

/-- A nonnegative physical action, used here for the ordinary Planck constant. -/
abbrev ActionQuantity : Type :=
  Dimensionful (WithDim actionDimension NNReal)

/-- Coherent-SI readout of a physical length, in metres. -/
def lengthInMeters (length : LengthQuantity) : ℝ :=
  ((length UnitChoices.SI).val : ℝ)

/-- Coherent-SI readout of a physical mass, in kilograms. -/
def massInKilograms (mass : MassQuantity) : ℝ :=
  ((mass UnitChoices.SI).val : ℝ)

/-- Coherent-SI readout of an action, in joule-seconds. -/
def actionInJouleSeconds (action : ActionQuantity) : ℝ :=
  ((action UnitChoices.SI).val : ℝ)

/-- Coherent-SI readout of a Physlib energy, in joules. -/
def energyInJoules (energy : DimEnergy) : ℝ :=
  (energy UnitChoices.SI).val

/-! ## One-particle levels, spin states, and figure vocabulary -/

/-- The six energy levels visible in the supplied diagram. -/
inductive InfiniteWellLevel where
  | e3
  | e6
  | e9
  | e11
  | e12
  | e14
  deriving DecidableEq, Fintype, Repr

/-- The two electron spin states that can occupy one spatial state. -/
inductive ElectronSpin where
  | up
  | down
  deriving DecidableEq, Fintype, Repr

/-- Literal degeneracy words printed next to the energy lines. -/
inductive DegeneracyLabel where
  | ground
  | nondegenerate
  | triple
  deriving DecidableEq, Repr

/-- Number of spatial one-electron states represented by a degeneracy word. -/
def DegeneracyLabel.spatialStateCount : DegeneracyLabel → ℕ
  | .ground => 1
  | .nondegenerate => 1
  | .triple => 3

/-- Orientation of a level line in the raster. -/
inductive LevelLineOrientation where
  | horizontal
  | other
  deriving DecidableEq, Repr

/-- Color category of a level line in the raster. -/
inductive LevelLineColor where
  | blue
  | other
  deriving DecidableEq, Repr

/-- Quantity named on the vertical axis. -/
inductive VerticalAxisQuantity where
  | energy
  | other
  deriving DecidableEq, Repr

/-- Symbolic unit expression printed beside the vertical-axis energy label. -/
inductive PrintedEnergyUnit where
  | hSquaredOverEightMassLengthSquared
  | other
  deriving DecidableEq, Repr

/-- Literal and geometric information carried by the primary energy diagram. -/
structure InfiniteWellEnergyFigure where
  verticalAxisQuantity : VerticalAxisQuantity
  printedEnergyUnit : PrintedEnergyUnit
  printedEnergyMultiplier : InfiniteWellLevel → ℕ
  printedDegeneracy : InfiniteWellLevel → DegeneracyLabel
  lineOrientation : InfiniteWellLevel → LevelLineOrientation
  lineColor : InfiniteWellLevel → LevelLineColor
  verticalOrderTopToBottom : List InfiniteWellLevel

/-! ## Physical setup and occupation-energy bookkeeping -/

/-- The confinement model stated in the problem. -/
inductive ConfinementModel where
  | threeDimensionalInfinitePotentialWell
  | other
  deriving DecidableEq, Repr

/-- The particle species loaded into the well. -/
inductive ConfinedParticleSpecies where
  | electron
  | other
  deriving DecidableEq, Repr

/-!
The dimensionful well parameters, spectrum, occupation, and total energy.
The fields are independent data; all physical relations between them are
imposed below as scenario, readout, or governing-law premises.
-/
structure ManyElectronInfiniteWellSetup where
  confinementModel : ConfinementModel
  spatialDimension : ℕ
  confinedParticleSpecies : ConfinedParticleSpecies
  diagramElectronCount : ℕ
  systemElectronCount : ℕ
  planckConstant : ActionQuantity
  electronMass : MassQuantity
  sideLength : LengthQuantity
  oneParticleEnergyScale : DimEnergy
  oneParticleEnergy : InfiniteWellLevel → DimEnergy
  groundStateOccupation : InfiniteWellLevel → ℕ
  electronInteractionEnergyContribution : DimEnergy
  manyElectronGroundStateEnergy : DimEnergy
  figure : InfiniteWellEnergyFigure

/-- SI value of the scale `h²/(8mL²)` named on the figure axis. -/
def infiniteWellEnergyScaleInJoules
    (setup : ManyElectronInfiniteWellSetup) : ℝ :=
  actionInJouleSeconds setup.planckConstant ^ 2 /
    (8 * massInKilograms setup.electronMass *
      lengthInMeters setup.sideLength ^ 2)

/-- Maximum number of electrons at a pictured level under the Pauli rule. -/
def levelElectronCapacity
    (figure : InfiniteWellEnergyFigure) (level : InfiniteWellLevel) : ℕ :=
  Fintype.card ElectronSpin *
    (figure.printedDegeneracy level).spatialStateCount

/-- An occupation has 22-particle bookkeeping and respects every Pauli cap. -/
def IsPauliAllowedOccupation
    (setup : ManyElectronInfiniteWellSetup)
    (occupation : InfiniteWellLevel → ℕ) : Prop :=
  (∑ level, occupation level) = setup.systemElectronCount ∧
    ∀ level, occupation level ≤ levelElectronCapacity setup.figure level

/-- Sum of occupied one-particle energy readouts for an occupation. -/
def occupationEnergyInJoules
    (setup : ManyElectronInfiniteWellSetup)
    (occupation : InfiniteWellLevel → ℕ) : ℝ :=
  ∑ level,
    (occupation level : ℝ) * energyInJoules (setup.oneParticleEnergy level)

/-! ## Scenario, primary-image evidence, and governing laws -/

/-- Prose data specifying the well, particles, initial diagram, and new load. -/
structure MatchesInfiniteWellScenario
    (setup : ManyElectronInfiniteWellSetup) : Prop where
  modelIsThreeDimensionalInfiniteWell :
    setup.confinementModel = .threeDimensionalInfinitePotentialWell
  dimensionIsThree : setup.spatialDimension = 3
  particlesAreElectrons : setup.confinedParticleSpecies = .electron
  originalDiagramContainsOneElectron : setup.diagramElectronCount = 1
  requestedSystemContainsTwentyTwoElectrons : setup.systemElectronCount = 22

/-!
Exact data transcribed from the primary raster.  This contains no occupation
numbers, many-electron ground-state energy, or requested answer multiplier.
-/
structure MatchesInfiniteWellFigure
    (setup : ManyElectronInfiniteWellSetup) : Prop where
  axisShowsEnergy : setup.figure.verticalAxisQuantity = .energy
  axisShowsInfiniteWellUnit :
    setup.figure.printedEnergyUnit =
      .hSquaredOverEightMassLengthSquared
  e3Multiplier : setup.figure.printedEnergyMultiplier .e3 = 3
  e6Multiplier : setup.figure.printedEnergyMultiplier .e6 = 6
  e9Multiplier : setup.figure.printedEnergyMultiplier .e9 = 9
  e11Multiplier : setup.figure.printedEnergyMultiplier .e11 = 11
  e12Multiplier : setup.figure.printedEnergyMultiplier .e12 = 12
  e14Multiplier : setup.figure.printedEnergyMultiplier .e14 = 14
  e3GroundLabel : setup.figure.printedDegeneracy .e3 = .ground
  e6TripleLabel : setup.figure.printedDegeneracy .e6 = .triple
  e9TripleLabel : setup.figure.printedDegeneracy .e9 = .triple
  e11TripleLabel : setup.figure.printedDegeneracy .e11 = .triple
  e12NondegenerateLabel :
    setup.figure.printedDegeneracy .e12 = .nondegenerate
  e14TripleLabel : setup.figure.printedDegeneracy .e14 = .triple
  displayedVerticalOrder :
    setup.figure.verticalOrderTopToBottom =
      [.e14, .e12, .e11, .e9, .e6, .e3]
  everyLevelLineIsHorizontal : ∀ level,
    setup.figure.lineOrientation level = .horizontal
  everyLevelLineIsBlue : ∀ level,
    setup.figure.lineColor level = .blue

/-- Positivity conditions for the physical well and its energy scale. -/
structure HasPhysicalInfiniteWellParameters
    (setup : ManyElectronInfiniteWellSetup) : Prop where
  planckConstantPositive :
    0 < actionInJouleSeconds setup.planckConstant
  electronMassPositive : 0 < massInKilograms setup.electronMass
  sideLengthPositive : 0 < lengthInMeters setup.sideLength
  energyScalePositive : 0 < energyInJoules setup.oneParticleEnergyScale

/-!
Governing laws for the independent-electron filling calculation:

* the named energy scale is `h²/(8mL²)`;
* each one-particle energy is its printed multiplier times that scale;
* the shown occupation is Pauli-allowed and minimizes the noninteracting sum;
* electron-electron electrostatic interactions contribute zero in the stated
  approximation; and
* the many-electron ground-state energy is the occupied one-particle sum plus
  that interaction contribution.

No field states a level occupation or the numerical total `186`.
-/
structure SatisfiesIndependentElectronFillingLaws
    (setup : ManyElectronInfiniteWellSetup) : Prop where
  energyScaleFormula :
    energyInJoules setup.oneParticleEnergyScale =
      infiniteWellEnergyScaleInJoules setup
  oneParticleSpectrumFollowsFigure : ∀ level,
    energyInJoules (setup.oneParticleEnergy level) =
      (setup.figure.printedEnergyMultiplier level : ℝ) *
        energyInJoules setup.oneParticleEnergyScale
  groundOccupationIsPauliAllowed :
    IsPauliAllowedOccupation setup setup.groundStateOccupation
  groundOccupationMinimizesEnergy : ∀ candidate,
    IsPauliAllowedOccupation setup candidate →
      occupationEnergyInJoules setup setup.groundStateOccupation ≤
        occupationEnergyInJoules setup candidate
  electronInteractionsAreNegligible :
    energyInJoules setup.electronInteractionEnergyContribution = 0
  totalGroundEnergyIsAdditive :
    energyInJoules setup.manyElectronGroundStateEnergy =
      occupationEnergyInJoules setup setup.groundStateOccupation +
        energyInJoules setup.electronInteractionEnergyContribution

/-! ## Derived filling pattern and formalization target -/

/-!
The Pauli caps and strict energy ordering force the first five levels to be
filled as `2, 6, 6, 6, 2`, leaving the level at multiplier `14` empty.
This is a derived conclusion, not a premise of the main theorem.
-/
lemma ground_state_occupation_for_twenty_two_electrons
    (setup : ManyElectronInfiniteWellSetup)
    (_scenario : MatchesInfiniteWellScenario setup)
    (_figure : MatchesInfiniteWellFigure setup)
    (_physical : HasPhysicalInfiniteWellParameters setup)
    (_laws : SatisfiesIndependentElectronFillingLaws setup) :
    setup.groundStateOccupation .e3 = 2 ∧
      setup.groundStateOccupation .e6 = 6 ∧
      setup.groundStateOccupation .e9 = 6 ∧
      setup.groundStateOccupation .e11 = 6 ∧
      setup.groundStateOccupation .e12 = 2 ∧
      setup.groundStateOccupation .e14 = 0 := by
  have hLevels :
      (Finset.univ : Finset InfiniteWellLevel) =
        {.e3, .e6, .e9, .e11, .e12, .e14} := by
    decide
  have hSpinCard : Fintype.card ElectronSpin = 2 := by
    decide
  let filledShells : InfiniteWellLevel → ℕ
    | .e3 => 2
    | .e6 => 6
    | .e9 => 6
    | .e11 => 6
    | .e12 => 2
    | .e14 => 0
  have hFilledShellsAllowed :
      IsPauliAllowedOccupation setup filledShells := by
    constructor
    · rw [_scenario.requestedSystemContainsTwentyTwoElectrons]
      decide
    · intro level
      fin_cases level <;>
        simp [filledShells, levelElectronCapacity,
          hSpinCard, DegeneracyLabel.spatialStateCount,
          _figure.e3GroundLabel, _figure.e6TripleLabel,
          _figure.e9TripleLabel, _figure.e11TripleLabel,
          _figure.e12NondegenerateLabel, _figure.e14TripleLabel]
  have hMinimum :=
    _laws.groundOccupationMinimizesEnergy filledShells hFilledShellsAllowed
  simp only [occupationEnergyInJoules] at hMinimum
  rw [hLevels] at hMinimum
  simp_rw [_laws.oneParticleSpectrumFollowsFigure] at hMinimum
  simp [filledShells, _figure.e3Multiplier, _figure.e6Multiplier,
    _figure.e9Multiplier, _figure.e11Multiplier, _figure.e12Multiplier,
    _figure.e14Multiplier] at hMinimum
  have hCount := _laws.groundOccupationIsPauliAllowed.1
  rw [_scenario.requestedSystemContainsTwentyTwoElectrons] at hCount
  rw [hLevels] at hCount
  simp at hCount
  have hCap3 := _laws.groundOccupationIsPauliAllowed.2 .e3
  have hCap6 := _laws.groundOccupationIsPauliAllowed.2 .e6
  have hCap9 := _laws.groundOccupationIsPauliAllowed.2 .e9
  have hCap11 := _laws.groundOccupationIsPauliAllowed.2 .e11
  have hCap12 := _laws.groundOccupationIsPauliAllowed.2 .e12
  have hCap14 := _laws.groundOccupationIsPauliAllowed.2 .e14
  simp [levelElectronCapacity, hSpinCard, DegeneracyLabel.spatialStateCount,
    _figure.e3GroundLabel] at hCap3
  simp [levelElectronCapacity, hSpinCard, DegeneracyLabel.spatialStateCount,
    _figure.e6TripleLabel] at hCap6
  simp [levelElectronCapacity, hSpinCard, DegeneracyLabel.spatialStateCount,
    _figure.e9TripleLabel] at hCap9
  simp [levelElectronCapacity, hSpinCard, DegeneracyLabel.spatialStateCount,
    _figure.e11TripleLabel] at hCap11
  simp [levelElectronCapacity, hSpinCard, DegeneracyLabel.spatialStateCount,
    _figure.e12NondegenerateLabel] at hCap12
  simp [levelElectronCapacity, hSpinCard, DegeneracyLabel.spatialStateCount,
    _figure.e14TripleLabel] at hCap14
  have hWeightedEnergy :
      3 * (setup.groundStateOccupation .e3 : ℝ) +
          6 * (setup.groundStateOccupation .e6 : ℝ) +
          9 * (setup.groundStateOccupation .e9 : ℝ) +
          11 * (setup.groundStateOccupation .e11 : ℝ) +
          12 * (setup.groundStateOccupation .e12 : ℝ) +
          14 * (setup.groundStateOccupation .e14 : ℝ) ≤
        186 := by
    nlinarith [_physical.energyScalePositive]
  have hWeightedEnergyNat :
      3 * setup.groundStateOccupation .e3 +
          6 * setup.groundStateOccupation .e6 +
          9 * setup.groundStateOccupation .e9 +
          11 * setup.groundStateOccupation .e11 +
          12 * setup.groundStateOccupation .e12 +
          14 * setup.groundStateOccupation .e14 ≤
        186 := by
    exact_mod_cast hWeightedEnergy
  omega

/-- Labels of the four displayed answers. -/
inductive AnswerChoice where
  | A
  | B
  | C
  | D
  deriving DecidableEq, Fintype, Repr

/-- Dimensionless energy multiplier printed beside each answer choice. -/
def displayedGroundEnergyMultiplier : AnswerChoice → ℕ
  | .A => 174
  | .B => 192
  | .C => 186
  | .D => 162

/-- Dataset metadata records answer choice C. -/
def recordedAnswerChoice : AnswerChoice := .C

/-!
Filling the levels gives

`2*3 + 6*6 + 6*9 + 6*11 + 2*12 = 186`.

Thus the total ground-state energy is `186 h²/(8mL²)`, selecting answer C.
The first conjunct states the requested multiplier directly; the second ties
it to the recorded answer label without putting that answer into any premise.

Blueprint label: `thm:physics:phyx_mini_0580:target`.
-/
theorem problem_phyx_mini_0580
    (setup : ManyElectronInfiniteWellSetup)
    (_scenario : MatchesInfiniteWellScenario setup)
    (_figure : MatchesInfiniteWellFigure setup)
    (_physical : HasPhysicalInfiniteWellParameters setup)
    (_laws : SatisfiesIndependentElectronFillingLaws setup) :
    energyInJoules setup.manyElectronGroundStateEnergy =
        186 * infiniteWellEnergyScaleInJoules setup ∧
      energyInJoules setup.manyElectronGroundStateEnergy =
        (displayedGroundEnergyMultiplier recordedAnswerChoice : ℝ) *
          infiniteWellEnergyScaleInJoules setup := by
  have hLevels :
      (Finset.univ : Finset InfiniteWellLevel) =
        {.e3, .e6, .e9, .e11, .e12, .e14} := by
    decide
  obtain ⟨h3, h6, h9, h11, h12, h14⟩ :=
    ground_state_occupation_for_twenty_two_electrons
      setup _scenario _figure _physical _laws
  have hEnergy :
      energyInJoules setup.manyElectronGroundStateEnergy =
        186 * infiniteWellEnergyScaleInJoules setup := by
    calc
      energyInJoules setup.manyElectronGroundStateEnergy =
          occupationEnergyInJoules setup setup.groundStateOccupation +
            energyInJoules setup.electronInteractionEnergyContribution :=
        _laws.totalGroundEnergyIsAdditive
      _ = occupationEnergyInJoules setup setup.groundStateOccupation := by
        rw [_laws.electronInteractionsAreNegligible, add_zero]
      _ = 186 * infiniteWellEnergyScaleInJoules setup := by
        simp only [occupationEnergyInJoules]
        rw [hLevels]
        simp_rw [_laws.oneParticleSpectrumFollowsFigure]
        simp [h3, h6, h9, h11, h12, h14,
          _figure.e3Multiplier, _figure.e6Multiplier,
          _figure.e9Multiplier, _figure.e11Multiplier,
          _figure.e12Multiplier, _figure.e14Multiplier,
          _laws.energyScaleFormula]
        ring
  refine ⟨hEnergy, ?_⟩
  simpa [displayedGroundEnergyMultiplier, recordedAnswerChoice] using hEnergy

end PhyXMiniProblems.ProblemPhyXMini0580
