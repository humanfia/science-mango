import Mathlib
import Physlib.Units.WithDim.Basic

noncomputable section

namespace PhyXMiniProblems.ProblemPhyXMini0877

open Dimension

/-!
# Equivalent capacitance of a series/parallel three-capacitor circuit

The primary raster `877.png` shows a battery connected to a top `10 μF`
capacitor. After that capacitor, the circuit splits into two branches
containing `20 μF` and `10 μF` capacitors, respectively, before the branches
rejoin at the battery's negative terminal.

Capacitances are represented by unit-independent Physlib quantities. Real
numbers occur only at explicit unit readouts and in literal data printed in the
figure or answer choices. In particular, the parallel-branch capacitance and
the total equivalent capacitance are independent fields of the physical setup;
the governing combination laws relate them to the component capacitances.
-/

/-! ## Dimensionful capacitance and named-unit readouts -/

/-- The dimension `M L² T⁻² C⁻¹` of electric potential difference. -/
def potentialDifferenceDimension : Dimension :=
  M𝓭 * L𝓭 * L𝓭 * T𝓭⁻¹ * T𝓭⁻¹ * C𝓭⁻¹

/-- The dimension `C / V` of electrical capacitance. -/
def capacitanceDimension : Dimension :=
  C𝓭 * potentialDifferenceDimension⁻¹

/-- A nonnegative, unit-independent physical electrical capacitance. -/
abbrev CapacitanceQuantity : Type :=
  Dimensionful (WithDim capacitanceDimension NNReal)

/-- Read a capacitance in the coherent unit induced by a choice of base units. -/
def capacitanceReadout
    (units : UnitChoices) (capacitance : CapacitanceQuantity) : ℝ :=
  ((capacitance units).val : ℝ)

/-- Read a capacitance in coherent-SI farads. -/
def capacitanceInFarads (capacitance : CapacitanceQuantity) : ℝ :=
  capacitanceReadout UnitChoices.SI capacitance

/-- Read a capacitance in microfarads. -/
def capacitanceInMicrofarads (capacitance : CapacitanceQuantity) : ℝ :=
  (10 : ℝ) ^ 6 * capacitanceInFarads capacitance

/-! ## Circuit roles, nodes, and primary-figure content -/

/-- The three capacitor symbols, named by their positions and printed values. -/
inductive CapacitorLabel where
  | topTen
  | lowerLeftTwenty
  | lowerRightTen
  deriving DecidableEq, Fintype, Repr

/-- The three electrically distinct nodes in the depicted ideal circuit. -/
inductive CircuitNode where
  | sourcePositive
  | branchJunction
  | returnNode
  deriving DecidableEq, Fintype, Repr

/-- The two marked terminals of the battery in the raster. -/
inductive BatteryTerminal where
  | positive
  | negative
  deriving DecidableEq, Fintype, Repr

/-- The component idealization used by the combination laws. -/
inductive CapacitorModel where
  | ideal
  | other
  deriving DecidableEq, Repr

/-- The source component shown on the left of the circuit. -/
inductive VoltageSourceModel where
  | battery
  | other
  deriving DecidableEq, Repr

/-!
Literal presentation information from `877.png`. Printed capacitances are
scalar microfarad readouts and are kept distinct from physical capacitance
quantities.
-/
structure ThreeCapacitorCircuitFigure where
  capacitorSymbolShown : CapacitorLabel → Bool
  printedCapacitanceMicrofarads : CapacitorLabel → ℝ
  batteryShown : Bool
  batteryPlusGlyphShown : Bool
  batteryMinusGlyphShown : Bool
  topCapacitorDrawnAboveParallelPair : Bool
  lowerLeftCapacitorDrawnLeftOfLowerRight : Bool
  branchWireSplitShown : Bool
  branchWireRejoinShown : Bool

/-!
Independent physical data for the circuit. Neither equivalent capacitance is
defined from the component values or from the recorded answer.
-/
structure ThreeCapacitorCircuitSetup where
  capacitorModel : CapacitorLabel → CapacitorModel
  voltageSourceModel : VoltageSourceModel
  capacitorCapacitance : CapacitorLabel → CapacitanceQuantity
  parallelBranchCapacitance : CapacitanceQuantity
  equivalentCapacitance : CapacitanceQuantity
  capacitorTerminals : CapacitorLabel → CircuitNode × CircuitNode
  parallelBranchTerminals : CircuitNode × CircuitNode
  equivalentTerminals : CircuitNode × CircuitNode
  batteryTerminalNode : BatteryTerminal → CircuitNode
  figure : ThreeCapacitorCircuitFigure

/-! ## Scenario, topology, figure readouts, and governing laws -/

/-- The ideal battery-and-capacitor interpretation stated by the problem. -/
structure MatchesIdealThreeCapacitorScenario
    (setup : ThreeCapacitorCircuitSetup) : Prop where
  allThreeComponentsAreIdealCapacitors : ∀ label,
    setup.capacitorModel label = .ideal
  leftComponentIsBattery :
    setup.voltageSourceModel = .battery

/-!
The node identifications read from the primary raster. The two lower
capacitors share both terminals and hence form a parallel branch; the top
capacitor lies in series between that branch and the battery's positive node.
-/
structure MatchesSeriesParallelTopology
    (setup : ThreeCapacitorCircuitSetup) : Prop where
  topCapacitorTerminals :
    setup.capacitorTerminals .topTen =
      (.sourcePositive, .branchJunction)
  lowerLeftCapacitorTerminals :
    setup.capacitorTerminals .lowerLeftTwenty =
      (.branchJunction, .returnNode)
  lowerRightCapacitorTerminals :
    setup.capacitorTerminals .lowerRightTen =
      (.branchJunction, .returnNode)
  parallelBranchTerminalPair :
    setup.parallelBranchTerminals = (.branchJunction, .returnNode)
  equivalentTerminalPair :
    setup.equivalentTerminals = (.sourcePositive, .returnNode)
  batteryPositiveTerminal :
    setup.batteryTerminalNode .positive = .sourcePositive
  batteryNegativeTerminal :
    setup.batteryTerminalNode .negative = .returnNode

/-!
Primary-raster evidence and calibration of its printed microfarad labels to the
independent physical component capacitances. This structure contains no
equivalent-capacitance value.
-/
structure MatchesSuppliedThreeCapacitorFigure
    (setup : ThreeCapacitorCircuitSetup) : Prop where
  allCapacitorSymbolsShown : ∀ label,
    setup.figure.capacitorSymbolShown label = true
  batterySymbolShown : setup.figure.batteryShown = true
  batteryPlusShown : setup.figure.batteryPlusGlyphShown = true
  batteryMinusShown : setup.figure.batteryMinusGlyphShown = true
  topCapacitorIsAboveBranches :
    setup.figure.topCapacitorDrawnAboveParallelPair = true
  lowerLeftIsLeftOfLowerRight :
    setup.figure.lowerLeftCapacitorDrawnLeftOfLowerRight = true
  branchSplitShown : setup.figure.branchWireSplitShown = true
  branchRejoinShown : setup.figure.branchWireRejoinShown = true
  printedTopCapacitance :
    setup.figure.printedCapacitanceMicrofarads .topTen = 10
  printedLowerLeftCapacitance :
    setup.figure.printedCapacitanceMicrofarads .lowerLeftTwenty = 20
  printedLowerRightCapacitance :
    setup.figure.printedCapacitanceMicrofarads .lowerRightTen = 10
  labelsCalibratePhysicalCapacitances : ∀ label,
    capacitanceInMicrofarads (setup.capacitorCapacitance label) =
      setup.figure.printedCapacitanceMicrofarads label

/-- Nondegeneracy of every physical capacitance used in reciprocal laws. -/
structure HasPositiveCircuitCapacitances
    (setup : ThreeCapacitorCircuitSetup) : Prop where
  componentCapacitancePositive : ∀ label,
    0 < capacitanceInFarads (setup.capacitorCapacitance label)
  parallelBranchCapacitancePositive :
    0 < capacitanceInFarads setup.parallelBranchCapacitance
  equivalentCapacitancePositive :
    0 < capacitanceInFarads setup.equivalentCapacitance

/-!
The ideal-capacitor combination laws, stated for every coherent unit system:
parallel capacitances add, while reciprocal capacitances add in series. These
are governing relations and contain none of the requested numerical result or
answer-choice data.
-/
structure SatisfiesIdealCapacitorCombinationLaws
    (setup : ThreeCapacitorCircuitSetup) : Prop where
  parallelAdditionLaw : ∀ units,
    capacitanceReadout units setup.parallelBranchCapacitance =
      capacitanceReadout units
          (setup.capacitorCapacitance .lowerLeftTwenty) +
        capacitanceReadout units
          (setup.capacitorCapacitance .lowerRightTen)
  seriesReciprocalLaw : ∀ units,
    1 / capacitanceReadout units setup.equivalentCapacitance =
      1 / capacitanceReadout units
          (setup.capacitorCapacitance .topTen) +
        1 / capacitanceReadout units setup.parallelBranchCapacitance

/-! ## Requested equivalent capacitance and displayed choices -/

/-- The four answer labels supplied with the problem. -/
inductive AnswerChoice where
  | A
  | B
  | C
  | D
  deriving DecidableEq, Fintype, Repr

/-- The equivalent capacitance printed for an answer choice, in microfarads. -/
def AnswerChoice.displayedCapacitanceInMicrofarads : AnswerChoice → ℝ
  | .A => 2.5
  | .B => 3.5
  | .C => 5.5
  | .D => 7.5

/-- The answer label recorded in the source dataset. -/
def recordedDatasetAnswer : AnswerChoice := .D

/-- A displayed choice agrees with the circuit's physical equivalent capacitance. -/
def AnswerMatchesEquivalentCapacitance
    (setup : ThreeCapacitorCircuitSetup) (choice : AnswerChoice) : Prop :=
  capacitanceInMicrofarads setup.equivalentCapacitance =
    choice.displayedCapacitanceInMicrofarads

/-!
The lower capacitors combine to `30 μF`; placing that branch in series with
the top `10 μF` capacitor gives `7.5 μF`, which is recorded choice D.

This declaration formalizes `thm:physics:phyx_mini_0877:target`. The requested
`7.5 μF` value and answer D occur only in the conclusion-side answer data, not
in any setup field, figure calibration, positivity condition, or governing
law.
-/
theorem problem_phyx_mini_0877
    (setup : ThreeCapacitorCircuitSetup)
    (hScenario : MatchesIdealThreeCapacitorScenario setup)
    (hTopology : MatchesSeriesParallelTopology setup)
    (hFigure : MatchesSuppliedThreeCapacitorFigure setup)
    (hPositive : HasPositiveCircuitCapacitances setup)
    (hCombinationLaws : SatisfiesIdealCapacitorCombinationLaws setup) :
    capacitanceInMicrofarads setup.equivalentCapacitance = 7.5 ∧
      AnswerMatchesEquivalentCapacitance setup recordedDatasetAnswer := by
  have hTop :=
    hFigure.labelsCalibratePhysicalCapacitances .topTen
  have hLeft :=
    hFigure.labelsCalibratePhysicalCapacitances .lowerLeftTwenty
  have hRight :=
    hFigure.labelsCalibratePhysicalCapacitances .lowerRightTen
  norm_num [capacitanceInMicrofarads,
    hFigure.printedTopCapacitance] at hTop
  norm_num [capacitanceInMicrofarads,
    hFigure.printedLowerLeftCapacitance] at hLeft
  norm_num [capacitanceInMicrofarads,
    hFigure.printedLowerRightCapacitance] at hRight
  have hParallel :=
    hCombinationLaws.parallelAdditionLaw UnitChoices.SI
  change
    capacitanceInFarads setup.parallelBranchCapacitance =
      capacitanceInFarads
          (setup.capacitorCapacitance .lowerLeftTwenty) +
        capacitanceInFarads
          (setup.capacitorCapacitance .lowerRightTen)
    at hParallel
  have hParallelValue :
      capacitanceInFarads setup.parallelBranchCapacitance =
        (3 : ℝ) / 100000 := by
    nlinarith
  have hSeries :=
    hCombinationLaws.seriesReciprocalLaw UnitChoices.SI
  change
    1 / capacitanceInFarads setup.equivalentCapacitance =
      1 / capacitanceInFarads
          (setup.capacitorCapacitance .topTen) +
        1 / capacitanceInFarads setup.parallelBranchCapacitance
    at hSeries
  rw [show
      capacitanceInFarads (setup.capacitorCapacitance .topTen) =
        (1 : ℝ) / 100000 by
      nlinarith,
    hParallelValue] at hSeries
  norm_num at hSeries
  have hEquivalentValue :
      capacitanceInFarads setup.equivalentCapacitance =
        (3 : ℝ) / 400000 := by
    rw [← inv_inv
      (capacitanceInFarads setup.equivalentCapacitance), hSeries]
    norm_num
  have hMicrofarads :
      capacitanceInMicrofarads setup.equivalentCapacitance = 7.5 := by
    norm_num [capacitanceInMicrofarads, hEquivalentValue]
  exact ⟨hMicrofarads, by
    simpa [AnswerMatchesEquivalentCapacitance, recordedDatasetAnswer,
      AnswerChoice.displayedCapacitanceInMicrofarads] using hMicrofarads⟩

end PhyXMiniProblems.ProblemPhyXMini0877
