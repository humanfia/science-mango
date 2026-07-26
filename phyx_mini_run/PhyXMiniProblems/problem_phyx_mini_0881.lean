import Mathlib
import Physlib.Units.WithDim.Basic

noncomputable section

namespace PhyXMiniProblems.ProblemPhyXMini0881

open Dimension Filter Topology

/-!
# Battery current after closing a switch in a parallel resistor-inductor circuit

The supplied figure shows a `10 V` battery feeding two parallel branches after
an initially open switch is closed at `t = 0 s`. One branch is a single
`20 Ω` resistor. The other branch is a `20 Ω` resistor in series with a
`10 mH` inductor. The requested observable is the current through the battery
after the switch has remained closed for a long time.

Physical voltage, resistance, inductance, and current magnitudes are represented
by Physlib `Dimensionful` quantities. Real scalars occur only at coherent-SI
readout boundaries, as the time coordinate measured in seconds, and as literal
figure or answer-choice data.
-/

/-! ## Physical dimensions and coherent-SI readouts -/

/-- Energy has dimension `M L² T⁻²`. -/
def energyDimension : Dimension :=
  M𝓭 * L𝓭 * L𝓭 * T𝓭⁻¹ * T𝓭⁻¹

/-- Electric current has dimension charge per time. -/
def electricCurrentDimension : Dimension := C𝓭 * T𝓭⁻¹

/-- Electric potential difference has dimension energy per charge. -/
def electricPotentialDimension : Dimension :=
  energyDimension * C𝓭⁻¹

/-- Electrical resistance has dimension potential difference per current. -/
def electricalResistanceDimension : Dimension :=
  electricPotentialDimension * electricCurrentDimension⁻¹

/-- Inductance has dimension resistance times time. -/
def inductanceDimension : Dimension :=
  electricalResistanceDimension * T𝓭

/-- A nonnegative, unit-independent voltage magnitude. -/
abbrev VoltageQuantity : Type :=
  Dimensionful (WithDim electricPotentialDimension NNReal)

/-- A nonnegative, unit-independent electrical resistance. -/
abbrev ResistanceQuantity : Type :=
  Dimensionful (WithDim electricalResistanceDimension NNReal)

/-- A nonnegative, unit-independent inductance. -/
abbrev InductanceQuantity : Type :=
  Dimensionful (WithDim inductanceDimension NNReal)

/-- A nonnegative, unit-independent current magnitude in a fixed orientation. -/
abbrev ElectricCurrentQuantity : Type :=
  Dimensionful (WithDim electricCurrentDimension NNReal)

/-- Coherent-SI scalar readout of a nonnegative dimensionful quantity. -/
def coherentSIReadout {d : Dimension}
    (quantity : Dimensionful (WithDim d NNReal)) : ℝ :=
  ((quantity UnitChoices.SI).val : ℝ)

/-- Read a voltage magnitude in volts. -/
def voltageInVolts (voltage : VoltageQuantity) : ℝ :=
  coherentSIReadout voltage

/-- Read an electrical resistance in ohms. -/
def resistanceInOhms (resistance : ResistanceQuantity) : ℝ :=
  coherentSIReadout resistance

/-- Read an inductance in henries. -/
def inductanceInHenries (inductance : InductanceQuantity) : ℝ :=
  coherentSIReadout inductance

/-- Read an inductance in millihenries. -/
def inductanceInMillihenries (inductance : InductanceQuantity) : ℝ :=
  1000 * inductanceInHenries inductance

/-- Read a current magnitude in amperes. -/
def currentInAmperes (current : ElectricCurrentQuantity) : ℝ :=
  coherentSIReadout current

/-! ## Figure labels, topology, and physical setup -/

/-- The two resistor positions distinguished by the supplied circuit diagram. -/
inductive ResistorPosition where
  | resistorOnlyBranch
  | resistorInductorBranch
  deriving DecidableEq, Fintype, Repr

/-- Individually identifiable components visible in image `881.png`. -/
inductive CircuitComponent where
  | battery
  | switch
  | resistorOnlyBranch
  | resistorInInductiveBranch
  | inductor
  deriving DecidableEq, Fintype, Repr

/-- The branch connectivity shown in the primary raster. -/
inductive CircuitTopology where
  | parallelResistorAndSeriesResistorInductor
  | other
  deriving DecidableEq, Repr

/-- State of the switch as a function of the time coordinate. -/
inductive SwitchState where
  | openCircuit
  | closedCircuit
  deriving DecidableEq, Repr

/-!
Literal presentation data from the supplied figure. Optional scalar fields
record whether a numerical label is printed; they do not define any physical
quantity in the circuit setup.
-/
structure ParallelRLFigure where
  componentShown : CircuitComponent → Bool
  positiveBatteryTerminalShown : Bool
  negativeBatteryTerminalShown : Bool
  switchDrawnOpen : Bool
  topology : CircuitTopology
  printedBatteryVoltageVolts : Option ℝ
  printedResistanceOhms : ResistorPosition → Option ℝ
  printedInductanceMillihenries : Option ℝ

/-!
Independent physical quantities for the switched circuit. The functions of
real time use seconds as their coordinate. Long-time currents and voltage
drops are fields rather than definitions from the displayed answer.
-/
structure SwitchedParallelRLCircuit where
  batteryVoltage : VoltageQuantity
  resistorOnlyResistance : ResistanceQuantity
  resistorInductorBranchResistance : ResistanceQuantity
  inductorInductance : InductanceQuantity
  switchStateAtSeconds : ℝ → SwitchState
  batteryCurrentAtSeconds : ℝ → ElectricCurrentQuantity
  longTimeBatteryCurrent : ElectricCurrentQuantity
  longTimeResistorOnlyBranchCurrent : ElectricCurrentQuantity
  longTimeResistorInductorBranchCurrent : ElectricCurrentQuantity
  longTimeResistorOnlyVoltageDrop : VoltageQuantity
  longTimeSeriesResistorVoltageDrop : VoltageQuantity
  longTimeInductorVoltageDrop : VoltageQuantity
  figure : ParallelRLFigure

/-! ## Figure/data readouts, switching protocol, and governing laws -/

/-!
Primary-raster evidence and its calibration to independent dimensionful
quantities. This records the `10 V`, two `20 Ω`, and `10 mH` labels together
with the depicted branch connectivity and polarity marks.
-/
structure MatchesSuppliedParallelRLFigure
    (setup : SwitchedParallelRLCircuit) : Prop where
  everyComponentShown : ∀ component,
    setup.figure.componentShown component = true
  positiveTerminalShown :
    setup.figure.positiveBatteryTerminalShown = true
  negativeTerminalShown :
    setup.figure.negativeBatteryTerminalShown = true
  switchShownOpen : setup.figure.switchDrawnOpen = true
  shownTopology :
    setup.figure.topology =
      .parallelResistorAndSeriesResistorInductor
  printedBatteryLabel :
    setup.figure.printedBatteryVoltageVolts = some 10
  printedResistorOnlyLabel :
    setup.figure.printedResistanceOhms .resistorOnlyBranch = some 20
  printedInductiveBranchResistorLabel :
    setup.figure.printedResistanceOhms .resistorInductorBranch = some 20
  printedInductorLabel :
    setup.figure.printedInductanceMillihenries = some 10
  batteryLabelCalibration :
    voltageInVolts setup.batteryVoltage = 10
  resistorOnlyLabelCalibration :
    resistanceInOhms setup.resistorOnlyResistance = 20
  inductiveBranchResistorLabelCalibration :
    resistanceInOhms setup.resistorInductorBranchResistance = 20
  inductorLabelCalibration :
    inductanceInMillihenries setup.inductorInductance = 10

/-!
The switch is idealized as having been open throughout negative times, being
closed at `t = 0 s`, and remaining closed thereafter.
-/
structure MatchesSwitchingProtocol
    (setup : SwitchedParallelRLCircuit) : Prop where
  openBeforeZero : ∀ t : ℝ, t < 0 →
    setup.switchStateAtSeconds t = .openCircuit
  closedFromZero : ∀ t : ℝ, 0 ≤ t →
    setup.switchStateAtSeconds t = .closedCircuit

/-- Positivity conditions for the three passive component parameters. -/
structure HasPhysicalCircuitParameters
    (setup : SwitchedParallelRLCircuit) : Prop where
  batteryVoltagePositive : 0 < voltageInVolts setup.batteryVoltage
  resistorOnlyResistancePositive :
    0 < resistanceInOhms setup.resistorOnlyResistance
  inductiveBranchResistancePositive :
    0 < resistanceInOhms setup.resistorInductorBranchResistance
  inductancePositive : 0 < inductanceInHenries setup.inductorInductance

/-!
The ideal lumped-circuit laws used at long times:

* an open switch disconnects the battery;
* the time-dependent battery current tends to the named long-time current;
* parallel branches share the battery voltage, and Kirchhoff's voltage law
  splits the series-branch voltage between its resistor and inductor;
* both resistors obey Ohm's law;
* an ideal inductor in the long-time DC regime has zero voltage drop; and
* Kirchhoff's current law adds the two branch currents at the battery.

These are uniform physical/model relations and contain no numerical value for
the requested battery current.
-/
structure SatisfiesLongTimeIdealDCCircuitLaws
    (setup : SwitchedParallelRLCircuit) : Prop where
  openSwitchDisconnectsBattery : ∀ t : ℝ,
    setup.switchStateAtSeconds t = .openCircuit →
      currentInAmperes (setup.batteryCurrentAtSeconds t) = 0
  batteryCurrentConvergesToLongTimeValue :
    Tendsto
      (fun t : ℝ => currentInAmperes (setup.batteryCurrentAtSeconds t))
      atTop
      (nhds (currentInAmperes setup.longTimeBatteryCurrent))
  resistorOnlyBranchSharesBatteryVoltage :
    voltageInVolts setup.longTimeResistorOnlyVoltageDrop =
      voltageInVolts setup.batteryVoltage
  seriesBranchKirchhoffVoltageLaw :
    voltageInVolts setup.batteryVoltage =
      voltageInVolts setup.longTimeSeriesResistorVoltageDrop +
        voltageInVolts setup.longTimeInductorVoltageDrop
  resistorOnlyBranchOhmsLaw :
    voltageInVolts setup.longTimeResistorOnlyVoltageDrop =
      currentInAmperes setup.longTimeResistorOnlyBranchCurrent *
        resistanceInOhms setup.resistorOnlyResistance
  seriesResistorOhmsLaw :
    voltageInVolts setup.longTimeSeriesResistorVoltageDrop =
      currentInAmperes setup.longTimeResistorInductorBranchCurrent *
        resistanceInOhms setup.resistorInductorBranchResistance
  idealInductorLongTimeVoltage :
    voltageInVolts setup.longTimeInductorVoltageDrop = 0
  batteryKirchhoffCurrentLaw :
    currentInAmperes setup.longTimeBatteryCurrent =
      currentInAmperes setup.longTimeResistorOnlyBranchCurrent +
        currentInAmperes setup.longTimeResistorInductorBranchCurrent

/-! ## Derived branch currents and displayed answer -/

/-!
Each `20 Ω` branch carries `0.5 A` in the long-time DC regime: the ideal
inductor has become a zero-voltage series element, so each resistor has the
full `10 V` source voltage across it.
-/
lemma longTime_branchCurrents_eq_oneHalfAmpere
    (setup : SwitchedParallelRLCircuit)
    (h_figure : MatchesSuppliedParallelRLFigure setup)
    (h_laws : SatisfiesLongTimeIdealDCCircuitLaws setup) :
    currentInAmperes setup.longTimeResistorOnlyBranchCurrent = 1 / 2 ∧
      currentInAmperes setup.longTimeResistorInductorBranchCurrent = 1 / 2 := by
  constructor
  · have h_share := h_laws.resistorOnlyBranchSharesBatteryVoltage
    rw [h_figure.batteryLabelCalibration] at h_share
    have h_ohm := h_laws.resistorOnlyBranchOhmsLaw
    rw [h_figure.resistorOnlyLabelCalibration] at h_ohm
    norm_num at h_ohm ⊢
    linarith
  · have h_kvl := h_laws.seriesBranchKirchhoffVoltageLaw
    rw [h_figure.batteryLabelCalibration,
      h_laws.idealInductorLongTimeVoltage] at h_kvl
    have h_ohm := h_laws.seriesResistorOhmsLaw
    rw [h_figure.inductiveBranchResistorLabelCalibration] at h_ohm
    norm_num at h_ohm ⊢
    linarith

/-- Labels of the four current choices printed with the source problem. -/
inductive AnswerChoice where
  | A
  | B
  | C
  | D
  deriving DecidableEq, Fintype, Repr

/-- Current in amperes printed beside each answer label. -/
def displayedCurrentInAmperes : AnswerChoice → ℝ
  | .A => 0
  | .B => 4
  | .C => 1
  | .D => 1 / 2

/-- The source dataset's recorded answer label, retained only as metadata. -/
def recordedDatasetAnswer : AnswerChoice := .C

/-- A displayed choice equals the modeled long-time battery current. -/
def MatchesLongTimeBatteryCurrent
    (setup : SwitchedParallelRLCircuit) (choice : AnswerChoice) : Prop :=
  currentInAmperes setup.longTimeBatteryCurrent =
    displayedCurrentInAmperes choice

/-- A displayed choice is the unique exact match for the modeled current. -/
def IsUniqueMatchingAnswer
    (setup : SwitchedParallelRLCircuit) (choice : AnswerChoice) : Prop :=
  MatchesLongTimeBatteryCurrent setup choice ∧
    ∀ other : AnswerChoice,
      MatchesLongTimeBatteryCurrent setup other → other = choice

/-!
After the switch has remained closed for a long time, the ideal inductor has
zero voltage drop. Thus both `20 Ω` resistors are across `10 V`, their
`0.5 A` branch currents add, and the battery supplies `1.0 A` (choice C).

This declaration formalizes `thm:physics:phyx_mini_0881:target`.
-/
theorem problem_phyx_mini_0881
    (setup : SwitchedParallelRLCircuit)
    (h_figure : MatchesSuppliedParallelRLFigure setup)
    (h_switching : MatchesSwitchingProtocol setup)
    (h_physical : HasPhysicalCircuitParameters setup)
    (h_laws : SatisfiesLongTimeIdealDCCircuitLaws setup) :
    currentInAmperes setup.longTimeBatteryCurrent = 1 ∧
      IsUniqueMatchingAnswer setup .C := by
  have h_branches :=
    longTime_branchCurrents_eq_oneHalfAmpere setup h_figure h_laws
  have h_current : currentInAmperes setup.longTimeBatteryCurrent = 1 := by
    nlinarith [h_laws.batteryKirchhoffCurrentLaw, h_branches.1, h_branches.2]
  refine ⟨h_current, ?_⟩
  constructor
  · simpa [MatchesLongTimeBatteryCurrent, displayedCurrentInAmperes] using h_current
  · intro other h_other
    cases other with
    | A =>
        norm_num [MatchesLongTimeBatteryCurrent, displayedCurrentInAmperes,
          h_current] at h_other
    | B =>
        norm_num [MatchesLongTimeBatteryCurrent, displayedCurrentInAmperes,
          h_current] at h_other
    | C => rfl
    | D =>
        norm_num [MatchesLongTimeBatteryCurrent, displayedCurrentInAmperes,
          h_current] at h_other

end PhyXMiniProblems.ProblemPhyXMini0881
