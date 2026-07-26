import Mathlib
import Physlib.Units.WithDim.Basic

/- USER: The assigned Lean file did not exist when this autoformalization task began. -/

/-!
# PhyX mini problem 0878: equivalent capacitance of a three-capacitor network

The primary image, rather than its inconsistent auxiliary caption, fixes the
circuit topology.  The `20 μF` and `30 μF` capacitors form the two consecutive
parts of the centre series branch.  That entire branch is in parallel with the
right-hand `13 μF` capacitor.  Both branches are connected between the upper
and lower rails of the battery.

Capacitance is represented as a unit-independent Physlib dimensional
quantity.  Real numbers below are readouts in farads or microfarads, printed
figure values, or displayed answer values.

Assumption/target split:

* governing laws: the reciprocal-addition law for a series pair and the
  addition law for parallel branches;
* previous-part results: none;
* figure/data readouts: the battery terminals, the three named circuit nodes,
  the endpoints of every capacitor, and the printed values `20 μF`, `30 μF`,
  and `13 μF`;
* current target conclusions: the centre branch has equivalent capacitance
  `12 μF`, the whole network has equivalent capacitance `25 μF`, and this is
  displayed answer D.

No governing-law field, topology field, figure-readout field, or local
definition contains the requested `25 μF` conclusion.
-/

noncomputable section

namespace PhyXMiniProblems.ProblemPhyXMini0878

open Dimension

/-! ## Dimensionful capacitance and scalar readouts -/

/--
Capacitance has dimension `C² T² M⁻¹ L⁻²`, since one farad is one coulomb per
volt and voltage has dimension energy per charge.
-/
def capacitanceDimension : Dimension :=
  C𝓭 * C𝓭 * T𝓭 * T𝓭 * M𝓭⁻¹ * L𝓭⁻¹ * L𝓭⁻¹

/-- A nonnegative, unit-independent physical capacitance. -/
abbrev CapacitanceQuantity : Type :=
  Dimensionful (WithDim capacitanceDimension NNReal)

/-- Read a physical capacitance in an arbitrary coherent system of units. -/
def capacitanceReadout
    (units : UnitChoices) (capacitance : CapacitanceQuantity) : ℝ :=
  ((capacitance units).val : ℝ)

/-- Read a physical capacitance in coherent-SI farads. -/
def capacitanceInFarads (capacitance : CapacitanceQuantity) : ℝ :=
  capacitanceReadout UnitChoices.SI capacitance

/-- Read a physical capacitance in microfarads. -/
def capacitanceInMicrofarads (capacitance : CapacitanceQuantity) : ℝ :=
  1000000 * capacitanceInFarads capacitance

/-! ## Primary-image circuit vocabulary -/

/-- The three electrically relevant nodes visible in image `878.png`. -/
inductive CircuitNode where
  | upperRail
  | seriesJunction
  | lowerRail
  deriving DecidableEq, Fintype, Repr

/-- Figure-derived names for the three physical capacitors. -/
inductive CapacitorLabel where
  | centerUpper20
  | centerLower30
  | right13
  deriving DecidableEq, Fintype, Repr

/-- The ideal battery symbol shown on the left of the image. -/
structure IdealBattery where
  positiveTerminal : CircuitNode
  negativeTerminal : CircuitNode

/--
A physical capacitor together with its two endpoints.  `upperTerminal` and
`lowerTerminal` refer only to the orientation in the raster circuit diagram.
-/
structure Capacitor where
  upperTerminal : CircuitNode
  lowerTerminal : CircuitNode
  capacitance : CapacitanceQuantity

/-! ## Abstract network reductions and their governing laws -/

/-- A claimed two-capacitance series reduction, before applying its law. -/
structure SeriesCapacitanceReduction where
  first : CapacitanceQuantity
  second : CapacitanceQuantity
  equivalent : CapacitanceQuantity

/-- A claimed two-branch parallel reduction, before applying its law. -/
structure ParallelCapacitanceReduction where
  firstBranch : CapacitanceQuantity
  secondBranch : CapacitanceQuantity
  equivalent : CapacitanceQuantity

/-!
The elementary physical laws for reducing ideal capacitors.  They are stated
at every coherent unit choice; within each equation all readouts therefore use
one common coordinate and have the same dimensional role.
-/
structure EquivalentCapacitanceLaws : Prop where
  series_reciprocal_addition :
    ∀ (units : UnitChoices) (reduction : SeriesCapacitanceReduction),
      0 < capacitanceReadout units reduction.first →
      0 < capacitanceReadout units reduction.second →
      (1 : ℝ) / capacitanceReadout units reduction.equivalent =
        1 / capacitanceReadout units reduction.first +
          1 / capacitanceReadout units reduction.second
  parallel_addition :
    ∀ (units : UnitChoices) (reduction : ParallelCapacitanceReduction),
      capacitanceReadout units reduction.equivalent =
        capacitanceReadout units reduction.firstBranch +
          capacitanceReadout units reduction.secondBranch

/-!
The circuit quantities to be reduced.  The two equivalent capacitances here
are unknown physical quantities, not numerical answers.
-/
structure ThreeCapacitorCircuit where
  battery : IdealBattery
  capacitor : CapacitorLabel → Capacitor
  centerSeriesReduction : SeriesCapacitanceReduction
  wholeParallelReduction : ParallelCapacitanceReduction

/-!
Endpoint and printed-value observations read from the primary image.  In
particular, these fields encode the centre *series* branch shown in the image,
not the reversed topology asserted by the auxiliary caption.
-/
structure MatchesPrimaryFigure (setup : ThreeCapacitorCircuit) : Prop where
  battery_positive_on_upper_rail :
    setup.battery.positiveTerminal = .upperRail
  battery_negative_on_lower_rail :
    setup.battery.negativeTerminal = .lowerRail
  center_upper_endpoints :
    (setup.capacitor .centerUpper20).upperTerminal = .upperRail ∧
      (setup.capacitor .centerUpper20).lowerTerminal = .seriesJunction
  center_lower_endpoints :
    (setup.capacitor .centerLower30).upperTerminal = .seriesJunction ∧
      (setup.capacitor .centerLower30).lowerTerminal = .lowerRail
  right_endpoints :
    (setup.capacitor .right13).upperTerminal = .upperRail ∧
      (setup.capacitor .right13).lowerTerminal = .lowerRail
  center_upper_readout :
    capacitanceInMicrofarads
        (setup.capacitor .centerUpper20).capacitance = 20
  center_lower_readout :
    capacitanceInMicrofarads
        (setup.capacitor .centerLower30).capacitance = 30
  right_readout :
    capacitanceInMicrofarads
        (setup.capacitor .right13).capacitance = 13

/-!
The reduction order inferred from the endpoint topology: first reduce the two
centre capacitors in series, then put that result in parallel with the right
capacitor.  This predicate contains no numerical value for either output.
-/
structure RepresentsFigureNetworkReduction
    (setup : ThreeCapacitorCircuit) : Prop where
  center_first_is_twenty :
    setup.centerSeriesReduction.first =
      (setup.capacitor .centerUpper20).capacitance
  center_second_is_thirty :
    setup.centerSeriesReduction.second =
      (setup.capacitor .centerLower30).capacitance
  whole_first_is_center_series :
    setup.wholeParallelReduction.firstBranch =
      setup.centerSeriesReduction.equivalent
  whole_second_is_thirteen :
    setup.wholeParallelReduction.secondBranch =
      (setup.capacitor .right13).capacitance

/-! ## Displayed choices -/

/-- Multiple-choice labels in the order printed in the problem. -/
inductive AnswerChoice where
  | A
  | B
  | C
  | D
  deriving DecidableEq, Fintype, Repr

/-- The capacitance value displayed beside each choice, in microfarads. -/
def displayedChoiceInMicrofarads : AnswerChoice → ℝ
  | .A => 5 / 2
  | .B => 35
  | .C => 55
  | .D => 25

/-! ## Consequences of the model -/

/-- The two centre capacitors reduce to `12 μF`. -/
lemma center_series_equivalent_eq_twelve_microfarads
    (setup : ThreeCapacitorCircuit)
    (figure : MatchesPrimaryFigure setup)
    (reduction : RepresentsFigureNetworkReduction setup)
    (laws : EquivalentCapacitanceLaws) :
    capacitanceInMicrofarads setup.centerSeriesReduction.equivalent = 12 := by
  have hfirst :
      capacitanceReadout UnitChoices.SI setup.centerSeriesReduction.first =
        (20 : ℝ) / 1000000 := by
    rw [reduction.center_first_is_twenty]
    have h := figure.center_upper_readout
    simp only [capacitanceInMicrofarads, capacitanceInFarads] at h
    linarith
  have hsecond :
      capacitanceReadout UnitChoices.SI setup.centerSeriesReduction.second =
        (30 : ℝ) / 1000000 := by
    rw [reduction.center_second_is_thirty]
    have h := figure.center_lower_readout
    simp only [capacitanceInMicrofarads, capacitanceInFarads] at h
    linarith
  have hseries := laws.series_reciprocal_addition UnitChoices.SI
    setup.centerSeriesReduction (by rw [hfirst]; norm_num)
      (by rw [hsecond]; norm_num)
  rw [hfirst, hsecond] at hseries
  norm_num at hseries
  have heq :
      (capacitanceReadout UnitChoices.SI
        setup.centerSeriesReduction.equivalent)⁻¹ =
        ((3 : ℝ) / 250000)⁻¹ := by
    calc
      _ = (250000 : ℝ) / 3 := by simpa only [one_div] using hseries
      _ = ((3 : ℝ) / 250000)⁻¹ := by norm_num
  have hvalue :
      capacitanceReadout UnitChoices.SI
        setup.centerSeriesReduction.equivalent = (3 : ℝ) / 250000 :=
    inv_injective heq
  simp only [capacitanceInMicrofarads, capacitanceInFarads]
  rw [hvalue]
  norm_num

/--
Blueprint target `thm:physics:phyx_mini_0878:target`: the equivalent
capacitance of all three capacitors is `25 μF`.
-/
theorem equivalent_capacitance_eq_twenty_five_microfarads
    (setup : ThreeCapacitorCircuit)
    (figure : MatchesPrimaryFigure setup)
    (reduction : RepresentsFigureNetworkReduction setup)
    (laws : EquivalentCapacitanceLaws) :
    capacitanceInMicrofarads setup.wholeParallelReduction.equivalent = 25 := by
  have hcenter :=
    center_series_equivalent_eq_twelve_microfarads setup figure reduction laws
  have hparallel :=
    laws.parallel_addition UnitChoices.SI setup.wholeParallelReduction
  rw [reduction.whole_first_is_center_series,
    reduction.whole_second_is_thirteen] at hparallel
  have hright := figure.right_readout
  simp only [capacitanceInMicrofarads, capacitanceInFarads] at hcenter hright ⊢
  linarith

/-- The computed value uniquely selects displayed answer D. -/
theorem recorded_answer_is_D
    (setup : ThreeCapacitorCircuit)
    (figure : MatchesPrimaryFigure setup)
    (reduction : RepresentsFigureNetworkReduction setup)
    (laws : EquivalentCapacitanceLaws) :
    ∀ choice : AnswerChoice,
      capacitanceInMicrofarads setup.wholeParallelReduction.equivalent =
          displayedChoiceInMicrofarads choice ↔
        choice = .D := by
  intro choice
  rw [equivalent_capacitance_eq_twenty_five_microfarads setup figure reduction laws]
  cases choice <;> norm_num [displayedChoiceInMicrofarads] <;> simp

end PhyXMiniProblems.ProblemPhyXMini0878
