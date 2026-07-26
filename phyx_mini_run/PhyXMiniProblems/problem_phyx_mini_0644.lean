import Mathlib
import Physlib.Units.WithDim.Energy

/- USER: The assigned source file did not exist when this autoformalization task began. -/

noncomputable section

namespace PhyXMiniProblems.ProblemPhyXMini0644

/-!
# Ionization energy of the fictitious element X

The primary raster shows three bound levels of a fictitious element `X`:
`n = 1` at `-6.50 eV`, `n = 2` at `-3.00 eV`, and `n = 3` at
`-2.00 eV`.  A red dashed line at `0.00 eV` is the continuum threshold.

Physical energies use Physlib's unit-independent `DimEnergy`.  Real numbers
occur only as calibrated electron-volt readouts, schematic vertical
coordinates, and displayed answer values.

Assumption/target split:

* `MatchesElementXScenario` records the element, ground-state, and continuum
  roles stated by the problem;
* `MatchesSuppliedEnergyLevelFigure` records only the labels, line styles,
  colors, order, and energy readouts visible in image `644.png`;
* `HasPhysicalElementXParameters` states the physical ordering and positivity
  conditions;
* `SatisfiesGroundStateIonizationLaw` is the general governing relation that
  the required ionization energy is the continuum-threshold energy minus the
  occupied ground-level energy; and
* there are no previous-part results.  The value `6.5 eV`, answer B, and its
  uniqueness occur only in theorem conclusions and the displayed-answer table.
-/

/-! ## Dimensionful energy and calibrated readouts -/

/-- Coherent-SI readout of a physical energy, in joules. -/
def energyInJoules (energy : DimEnergy) : ℝ :=
  (energy UnitChoices.SI).val

/-!
Electron-volt readout of a physical energy.  The denominator is Physlib's
dimensionful calibrated constant for one electron volt.
-/
def energyInElectronVolts (energy : DimEnergy) : ℝ :=
  energyInJoules energy / energyInJoules DimEnergy.electronVolt

/-! ## Element, level, and primary-figure vocabulary -/

/-- Atomic species represented by the supplied fictitious-element diagram. -/
inductive AtomicSpecies where
  | elementX
  | other
  deriving DecidableEq, Repr

/-!
The three bound levels and the dashed zero-energy continuum reference shown in
the raster.
-/
inductive AtomicEnergyLevel where
  | n1
  | n2
  | n3
  | continuum
  deriving DecidableEq, Fintype, Repr

/-- Line styles used to distinguish bound levels from the continuum threshold. -/
inductive EnergyLevelLineStyle where
  | solid
  | dashed
  deriving DecidableEq, Repr

/-- Line colors visible in the primary raster. -/
inductive EnergyLevelLineColor where
  | brown
  | red
  deriving DecidableEq, Repr

/-!
Presentation-level data transcribed from the supplied energy-level diagram.
Its real-valued fields are displayed coordinates and electron-volt labels,
not replacements for the dimensionful physical energies in the setup.
-/
structure AtomicEnergyLevelFigure where
  lineIsShown : AtomicEnergyLevel → Bool
  lineIsHorizontal : AtomicEnergyLevel → Bool
  lineStyle : AtomicEnergyLevel → EnergyLevelLineStyle
  lineColor : AtomicEnergyLevel → EnergyLevelLineColor
  verticalCoordinate : AtomicEnergyLevel → ℝ
  displayedPrincipalQuantumNumber : AtomicEnergyLevel → Option ℕ
  displayedEnergyElectronVolts : AtomicEnergyLevel → ℝ
  energyAxisTitleShown : Bool
  electronVoltUnitShown : Bool

/-!
Independent physical quantities for the atom.  In particular,
`ionizationEnergy` is an unconstrained dimensionful observable here; it is not
defined from the requested answer or from an answer-choice value.
-/
structure ElementXIonizationSetup where
  species : AtomicSpecies
  levelEnergy : AtomicEnergyLevel → DimEnergy
  groundLevel : AtomicEnergyLevel
  ionizationThreshold : AtomicEnergyLevel
  ionizationEnergy : DimEnergy
  figure : AtomicEnergyLevelFigure

/-! ## Scenario, figure evidence, and governing physics -/

/-- The prose scenario identifies element X, its ground level, and its threshold. -/
structure MatchesElementXScenario (setup : ElementXIonizationSetup) : Prop where
  speciesIsElementX : setup.species = .elementX
  groundStateIsN1 : setup.groundLevel = .n1
  zeroContinuumIsIonizationThreshold :
    setup.ionizationThreshold = .continuum

/-!
Literal and numerical evidence read from the primary raster.  The final four
fields calibrate the physical levels against the printed eV values, but do not
mention the required ionization energy or any answer choice.
-/
structure MatchesSuppliedEnergyLevelFigure
    (setup : ElementXIonizationSetup) : Prop where
  everyLevelLineShown :
    ∀ level : AtomicEnergyLevel, setup.figure.lineIsShown level = true
  everyLevelLineHorizontal :
    ∀ level : AtomicEnergyLevel, setup.figure.lineIsHorizontal level = true
  n1LineIsSolid : setup.figure.lineStyle .n1 = .solid
  n2LineIsSolid : setup.figure.lineStyle .n2 = .solid
  n3LineIsSolid : setup.figure.lineStyle .n3 = .solid
  continuumLineIsDashed : setup.figure.lineStyle .continuum = .dashed
  n1LineIsBrown : setup.figure.lineColor .n1 = .brown
  n2LineIsBrown : setup.figure.lineColor .n2 = .brown
  n3LineIsBrown : setup.figure.lineColor .n3 = .brown
  continuumLineIsRed : setup.figure.lineColor .continuum = .red
  n1BelowN2 :
    setup.figure.verticalCoordinate .n1 < setup.figure.verticalCoordinate .n2
  n2BelowN3 :
    setup.figure.verticalCoordinate .n2 < setup.figure.verticalCoordinate .n3
  n3BelowContinuum :
    setup.figure.verticalCoordinate .n3 <
      setup.figure.verticalCoordinate .continuum
  n1PrincipalQuantumNumber :
    setup.figure.displayedPrincipalQuantumNumber .n1 = some 1
  n2PrincipalQuantumNumber :
    setup.figure.displayedPrincipalQuantumNumber .n2 = some 2
  n3PrincipalQuantumNumber :
    setup.figure.displayedPrincipalQuantumNumber .n3 = some 3
  continuumHasNoPrincipalQuantumNumber :
    setup.figure.displayedPrincipalQuantumNumber .continuum = none
  n1DisplayedEnergy :
    setup.figure.displayedEnergyElectronVolts .n1 = -(13 / 2 : ℝ)
  n2DisplayedEnergy :
    setup.figure.displayedEnergyElectronVolts .n2 = -3
  n3DisplayedEnergy :
    setup.figure.displayedEnergyElectronVolts .n3 = -2
  continuumDisplayedEnergy :
    setup.figure.displayedEnergyElectronVolts .continuum = 0
  energyAxisTitleVisible : setup.figure.energyAxisTitleShown = true
  electronVoltUnitVisible : setup.figure.electronVoltUnitShown = true
  physicalN1EnergyMatchesFigure :
    energyInElectronVolts (setup.levelEnergy .n1) = -(13 / 2 : ℝ)
  physicalN2EnergyMatchesFigure :
    energyInElectronVolts (setup.levelEnergy .n2) = -3
  physicalN3EnergyMatchesFigure :
    energyInElectronVolts (setup.levelEnergy .n3) = -2
  physicalContinuumEnergyMatchesFigure :
    energyInElectronVolts (setup.levelEnergy .continuum) = 0

/-!
Ordering and positivity conditions selecting the intended bound-state branch.
They contain no numerical value for the ionization energy.
-/
structure HasPhysicalElementXParameters
    (setup : ElementXIonizationSetup) : Prop where
  n1BelowN2 :
    energyInJoules (setup.levelEnergy .n1) <
      energyInJoules (setup.levelEnergy .n2)
  n2BelowN3 :
    energyInJoules (setup.levelEnergy .n2) <
      energyInJoules (setup.levelEnergy .n3)
  n3BelowContinuum :
    energyInJoules (setup.levelEnergy .n3) <
      energyInJoules (setup.levelEnergy .continuum)
  ionizationEnergyIsPositive :
    0 < energyInJoules setup.ionizationEnergy

/-!
The ground-state ionization law: the required energy equals the difference
between the continuum threshold and the occupied ground level.  This is a
general relation among independent physical quantities; it contains neither
the specialized value `6.5 eV` nor an answer-choice label.
-/
structure SatisfiesGroundStateIonizationLaw
    (setup : ElementXIonizationSetup) : Prop where
  requiredEnergyIsThresholdGap :
    energyInJoules setup.ionizationEnergy =
      energyInJoules (setup.levelEnergy setup.ionizationThreshold) -
        energyInJoules (setup.levelEnergy setup.groundLevel)

/-! ## Displayed answers and formalization target -/

/-- Labels of the four answer choices printed in the source. -/
inductive AnswerChoice where
  | A
  | B
  | C
  | D
  deriving DecidableEq, Fintype, Repr

/-- Ionization-energy value printed beside each answer, in electron volts. -/
def AnswerChoice.energyElectronVolts : AnswerChoice → ℝ
  | .A => -(13 / 2 : ℝ)
  | .B => 13 / 2
  | .C => -3
  | .D => 3

/-- Dataset metadata recording answer B; this is not a theorem premise. -/
def recordedDatasetAnswer : AnswerChoice := .B

/-- The physical ionization energy agrees exactly with a displayed choice. -/
def MatchesDisplayedIonizationEnergy
    (setup : ElementXIonizationSetup) (choice : AnswerChoice) : Prop :=
  energyInElectronVolts setup.ionizationEnergy = choice.energyElectronVolts

/-- Exactly one displayed answer agrees with the physical ionization energy. -/
def IsUniqueMatchingIonizationEnergyChoice
    (setup : ElementXIonizationSetup) (choice : AnswerChoice) : Prop :=
  MatchesDisplayedIonizationEnergy setup choice ∧
    ∀ alternative : AnswerChoice,
      MatchesDisplayedIonizationEnergy setup alternative →
        alternative = choice

/-!
Ionizing the ground-state electron raises it from `-6.50 eV` to the
`0.00 eV` continuum threshold.  Hence the required energy is `6.5 eV`, which
uniquely selects choice B.

This formalizes blueprint label `thm:physics:phyx_mini_0644:target`.
-/
theorem problem_phyx_mini_0644
    (setup : ElementXIonizationSetup)
    (_scenario : MatchesElementXScenario setup)
    (_figure : MatchesSuppliedEnergyLevelFigure setup)
    (_physical : HasPhysicalElementXParameters setup)
    (_law : SatisfiesGroundStateIonizationLaw setup) :
    energyInElectronVolts setup.ionizationEnergy = (13 / 2 : ℝ) ∧
      MatchesDisplayedIonizationEnergy setup .B ∧
      IsUniqueMatchingIonizationEnergyChoice setup .B := by
  have hIonizationEnergy :
      energyInElectronVolts setup.ionizationEnergy = (13 / 2 : ℝ) := by
    unfold energyInElectronVolts
    rw [_law.requiredEnergyIsThresholdGap,
      _scenario.zeroContinuumIsIonizationThreshold,
      _scenario.groundStateIsN1, sub_div]
    change
      energyInElectronVolts (setup.levelEnergy .continuum) -
          energyInElectronVolts (setup.levelEnergy .n1) =
        (13 / 2 : ℝ)
    rw [_figure.physicalContinuumEnergyMatchesFigure,
      _figure.physicalN1EnergyMatchesFigure]
    norm_num
  have hChoiceB : MatchesDisplayedIonizationEnergy setup .B := by
    simpa [MatchesDisplayedIonizationEnergy, AnswerChoice.energyElectronVolts]
      using hIonizationEnergy
  refine ⟨hIonizationEnergy, hChoiceB, hChoiceB, ?_⟩
  intro alternative hAlternative
  cases alternative with
  | A =>
      norm_num [MatchesDisplayedIonizationEnergy, AnswerChoice.energyElectronVolts,
        hIonizationEnergy] at hAlternative
  | B => rfl
  | C =>
      norm_num [MatchesDisplayedIonizationEnergy, AnswerChoice.energyElectronVolts,
        hIonizationEnergy] at hAlternative
  | D =>
      norm_num [MatchesDisplayedIonizationEnergy, AnswerChoice.energyElectronVolts,
        hIonizationEnergy] at hAlternative

end PhyXMiniProblems.ProblemPhyXMini0644
