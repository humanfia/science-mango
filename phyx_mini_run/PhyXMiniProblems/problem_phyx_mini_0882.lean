import Mathlib
import Physlib.SpaceAndTime.Time.Derivatives
import Physlib.Units.WithDim.Basic

/- USER: The assigned Lean file did not exist when this autoformalization task began. -/

noncomputable section

namespace PhyXMiniProblems.ProblemPhyXMini0882

open Dimension Filter

/-!
# Long-time current in an ideal series RL circuit

The supplied raster shows one series loop containing, in order, a battery,
an initially open switch, a resistor, and an inductor.  The switch closes at
the time-coordinate origin.  We choose seconds as the coordinate unit of
Physlib's `Time`, so `Time.deriv` below has the readout unit amperes per second.

Assumption/target split:

* governing laws: an open switch carries no current, the resistor obeys
  Ohm's law, the inductor voltage is `L dI/dt`, and Kirchhoff's voltage law
  holds around the closed series loop;
* previous-part results: none;
* figure/data readouts: battery label `Delta V_bat`, resistor label `R`,
  inductor label `L`, battery polarity, the initially open switch, the
  component order, and the four displayed answer formulas;
* current target conclusions: the long-time current is
  `Delta V_bat / R`, and this is uniquely displayed by choice C.

The physical quantities are unit-independent `Dimensionful` Physlib values.
Real numbers occur only as coherent-SI readouts, a time-coordinate readout,
or displayed answer values.  In particular, `longTimeCurrent` is independent
data characterized only as the limit of the circuit current; it is not
defined to be the requested answer.
-/

/-! ## Dimensionful electrical quantities and coherent-SI readouts -/

/-- The dimension `C T⁻¹` of electric current. -/
def electricCurrentDimension : Dimension := C𝓭 * T𝓭⁻¹

/-- The dimension `M L² T⁻² C⁻¹` of electric potential difference. -/
def potentialDifferenceDimension : Dimension :=
  M𝓭 * L𝓭 * L𝓭 * T𝓭⁻¹ * T𝓭⁻¹ * C𝓭⁻¹

/-- The dimension `V I⁻¹` of electrical resistance. -/
def resistanceDimension : Dimension :=
  potentialDifferenceDimension * electricCurrentDimension⁻¹

/-- The dimension `V T I⁻¹` of electrical inductance. -/
def inductanceDimension : Dimension :=
  potentialDifferenceDimension * T𝓭 * electricCurrentDimension⁻¹

/-- A signed, unit-independent electric current. -/
abbrev ElectricCurrentQuantity : Type :=
  Dimensionful (WithDim electricCurrentDimension ℝ)

/-- A signed, unit-independent electric potential difference. -/
abbrev PotentialDifferenceQuantity : Type :=
  Dimensionful (WithDim potentialDifferenceDimension ℝ)

/-- A nonnegative, unit-independent electrical resistance. -/
abbrev ResistanceQuantity : Type :=
  Dimensionful (WithDim resistanceDimension NNReal)

/-- A nonnegative, unit-independent electrical inductance. -/
abbrev InductanceQuantity : Type :=
  Dimensionful (WithDim inductanceDimension NNReal)

/-- Read a signed current in coherent-SI amperes. -/
def currentInAmperes (current : ElectricCurrentQuantity) : ℝ :=
  (current UnitChoices.SI).val

/-- Read a signed potential difference in coherent-SI volts. -/
def potentialDifferenceInVolts
    (potentialDifference : PotentialDifferenceQuantity) : ℝ :=
  (potentialDifference UnitChoices.SI).val

/-- Read a nonnegative resistance in coherent-SI ohms. -/
def resistanceInOhms (resistance : ResistanceQuantity) : ℝ :=
  ((resistance UnitChoices.SI).val : ℝ)

/-- Read a nonnegative inductance in coherent-SI henries. -/
def inductanceInHenries (inductance : InductanceQuantity) : ℝ :=
  ((inductance UnitChoices.SI).val : ℝ)

/-! ## Circuit roles, nodes, switch state, and primary-figure content -/

/-- The four physical components visible in the single series loop. -/
inductive CircuitComponent where
  | battery
  | switch
  | resistor
  | inductor
  deriving DecidableEq, Fintype, Repr

/-- Electrically distinct nodes encountered while traversing the loop. -/
inductive CircuitNode where
  | batteryNegative
  | batteryPositive
  | afterSwitch
  | afterResistor
  deriving DecidableEq, Fintype, Repr

/-- The two ideal states of the switch. -/
inductive SwitchPosition where
  | open
  | closed
  deriving DecidableEq, Repr

/-- The marked terminals of the battery symbol. -/
inductive BatteryTerminal where
  | negative
  | positive
  deriving DecidableEq, Fintype, Repr

/-!
Literal qualitative and text data transcribed from image `882.png`.  Printed
labels are kept separate from the dimensionful component values.
-/
structure SeriesRLCircuitFigure where
  componentSymbolShown : CircuitComponent → Bool
  printedLabel : CircuitComponent → Option String
  switchDrawnAs : SwitchPosition
  batteryPlusGlyphShown : Bool
  batteryMinusGlyphShown : Bool
  componentOrderAroundLoop : List CircuitComponent
  singleLoopGeometryShown : Bool

/-!
Independent physical data for the switched series RL circuit.  The two
voltage-drop waveforms allow Ohm's law, the inductor constitutive law, and
Kirchhoff's loop law to be stated separately.  `longTimeCurrent` is not
defined from the battery or resistance.
-/
structure SeriesRLCircuitSetup where
  batteryVoltage : PotentialDifferenceQuantity
  resistance : ResistanceQuantity
  inductance : InductanceQuantity
  loopCurrent : Time → ElectricCurrentQuantity
  resistorVoltageDrop : Time → PotentialDifferenceQuantity
  inductorVoltageDrop : Time → PotentialDifferenceQuantity
  longTimeCurrent : ElectricCurrentQuantity
  switchPosition : Time → SwitchPosition
  componentTerminals : CircuitComponent → CircuitNode × CircuitNode
  batteryTerminalNode : BatteryTerminal → CircuitNode
  figure : SeriesRLCircuitFigure

/-- The SI current readout as a function of Physlib time. -/
def currentWaveformInAmperes (setup : SeriesRLCircuitSetup) : Time → ℝ :=
  fun t => currentInAmperes (setup.loopCurrent t)

/-- The time derivative of the current readout, in amperes per second. -/
def currentDerivativeInAmperesPerSecond
    (setup : SeriesRLCircuitSetup) : Time → ℝ :=
  Time.deriv (currentWaveformInAmperes setup)

/-! ## Figure, topology, switching, and governing-law assumptions -/

/-- The symbols, polarity marks, labels, and ordering visible in the raster. -/
structure MatchesSuppliedSeriesRLFigure
    (setup : SeriesRLCircuitSetup) : Prop where
  allFourSymbolsShown : ∀ component,
    setup.figure.componentSymbolShown component = true
  batteryLabel : setup.figure.printedLabel .battery = some "ΔV_bat"
  switchHasNoPrintedLabel : setup.figure.printedLabel .switch = none
  resistorLabel : setup.figure.printedLabel .resistor = some "R"
  inductorLabel : setup.figure.printedLabel .inductor = some "L"
  switchInitiallyDrawnOpen : setup.figure.switchDrawnAs = .open
  batteryPlusShown : setup.figure.batteryPlusGlyphShown = true
  batteryMinusShown : setup.figure.batteryMinusGlyphShown = true
  oneLoopShown : setup.figure.singleLoopGeometryShown = true
  orderAroundLoop :
    setup.figure.componentOrderAroundLoop =
      [.battery, .switch, .resistor, .inductor]

/-- Node incidences expressing that all four components form one series loop. -/
structure MatchesSeriesRLTopology
    (setup : SeriesRLCircuitSetup) : Prop where
  batteryTerminals :
    setup.componentTerminals .battery =
      (.batteryNegative, .batteryPositive)
  switchTerminals :
    setup.componentTerminals .switch =
      (.batteryPositive, .afterSwitch)
  resistorTerminals :
    setup.componentTerminals .resistor =
      (.afterSwitch, .afterResistor)
  inductorTerminals :
    setup.componentTerminals .inductor =
      (.afterResistor, .batteryNegative)
  batteryNegativeTerminal :
    setup.batteryTerminalNode .negative = .batteryNegative
  batteryPositiveTerminal :
    setup.batteryTerminalNode .positive = .batteryPositive

/-!
The switch has been open throughout negative time and is closed at `t = 0 s`
and thereafter, exactly as stipulated in the problem statement.
-/
structure MatchesClosingExperiment
    (setup : SeriesRLCircuitSetup) : Prop where
  openBeforeZero : ∀ t : Time, t < 0 → setup.switchPosition t = .open
  closedFromZero : ∀ t : Time, 0 ≤ t → setup.switchPosition t = .closed

/-!
Ideal lumped-element dynamics.  These are governing laws, not the requested
long-time formula: the resistor and inductor drops remain independent fields,
and the battery/resistance quotient appears nowhere in this structure.
-/
structure SatisfiesIdealSeriesRLDynamics
    (setup : SeriesRLCircuitSetup) : Prop where
  positiveBatteryVoltage :
    0 < potentialDifferenceInVolts setup.batteryVoltage
  positiveResistance : 0 < resistanceInOhms setup.resistance
  positiveInductance : 0 < inductanceInHenries setup.inductance
  openSwitchBlocksCurrent : ∀ t : Time, t < 0 →
    currentWaveformInAmperes setup t = 0
  resistorOhmLaw : ∀ t : Time, 0 ≤ t →
    potentialDifferenceInVolts (setup.resistorVoltageDrop t) =
      resistanceInOhms setup.resistance * currentWaveformInAmperes setup t
  inductorVoltageLaw : ∀ t : Time, 0 ≤ t →
    potentialDifferenceInVolts (setup.inductorVoltageDrop t) =
      inductanceInHenries setup.inductance *
        currentDerivativeInAmperesPerSecond setup t
  kirchhoffLoopLaw : ∀ t : Time, 0 ≤ t →
    potentialDifferenceInVolts setup.batteryVoltage =
      potentialDifferenceInVolts (setup.resistorVoltageDrop t) +
        potentialDifferenceInVolts (setup.inductorVoltageDrop t)

/-!
The mathematical meaning of "after the switch has been closed for a long
time": current approaches the independently stored steady current and its
time derivative approaches zero.  No value for that steady current is
assumed.
-/
structure HasLongTimeSeriesRLSteadyState
    (setup : SeriesRLCircuitSetup) : Prop where
  currentConverges :
    Tendsto (currentWaveformInAmperes setup) atTop
      (nhds (currentInAmperes setup.longTimeCurrent))
  currentDerivativeConvergesToZero :
    Tendsto (currentDerivativeInAmperesPerSecond setup) atTop (nhds 0)

/-! ## Displayed choices and current target -/

/-- Labels of the four answer choices in the source. -/
inductive AnswerChoice where
  | A
  | B
  | C
  | D
  deriving DecidableEq, Fintype, Repr

/-- The four displayed current readouts, interpreted in amperes. -/
def displayedCurrentInAmperes
    (setup : SeriesRLCircuitSetup) : AnswerChoice → ℝ
  | .A =>
      potentialDifferenceInVolts setup.batteryVoltage /
        (2 * resistanceInOhms setup.resistance)
  | .B =>
      2 * potentialDifferenceInVolts setup.batteryVoltage /
        resistanceInOhms setup.resistance
  | .C =>
      potentialDifferenceInVolts setup.batteryVoltage /
        resistanceInOhms setup.resistance
  | .D =>
      potentialDifferenceInVolts setup.batteryVoltage /
        (3 * resistanceInOhms setup.resistance)

/-!
After the switch has been closed for a long time, the ideal inductor has zero
voltage drop and the series current is `Delta V_bat / R`.  Positivity makes C
the unique displayed choice with that value.

Blueprint label: `thm:physics:phyx_mini_0882:target`.
-/
theorem longTimeCurrent_eq_batteryVoltage_div_resistance
    (setup : SeriesRLCircuitSetup)
    (_hFigure : MatchesSuppliedSeriesRLFigure setup)
    (_hTopology : MatchesSeriesRLTopology setup)
    (_hSwitching : MatchesClosingExperiment setup)
    (hDynamics : SatisfiesIdealSeriesRLDynamics setup)
    (hSteady : HasLongTimeSeriesRLSteadyState setup) :
    currentInAmperes setup.longTimeCurrent =
        potentialDifferenceInVolts setup.batteryVoltage /
          resistanceInOhms setup.resistance ∧
      currentInAmperes setup.longTimeCurrent =
        displayedCurrentInAmperes setup .C ∧
      ∀ choice,
        currentInAmperes setup.longTimeCurrent =
            displayedCurrentInAmperes setup choice →
          choice = .C := by
  letI : IsDirectedOrder Time :=
    ⟨fun a b => by
      refine ⟨⟨max a.val b.val⟩, ?_, ?_⟩
      · change a.val ≤ max a.val b.val
        exact le_max_left _ _
      · change b.val ≤ max a.val b.val
        exact le_max_right _ _⟩
  have hRne := ne_of_gt hDynamics.positiveResistance
  have hCircuit : ∀ᶠ t : Time in atTop,
      potentialDifferenceInVolts setup.batteryVoltage =
        resistanceInOhms setup.resistance * currentWaveformInAmperes setup t +
        inductanceInHenries setup.inductance *
          currentDerivativeInAmperesPerSecond setup t := by
    filter_upwards [eventually_ge_atTop (0 : Time)] with t ht
    rw [hDynamics.kirchhoffLoopLaw t ht,
      hDynamics.resistorOhmLaw t ht,
      hDynamics.inductorVoltageLaw t ht]
  have hRhs :=
    (hSteady.currentConverges.const_mul
        (resistanceInOhms setup.resistance)).add
      (hSteady.currentDerivativeConvergesToZero.const_mul
        (inductanceInHenries setup.inductance))
  have hConst :=
    hRhs.congr' (hCircuit.mono fun _ ht => ht.symm)
  have hEq : potentialDifferenceInVolts setup.batteryVoltage =
      resistanceInOhms setup.resistance *
        currentInAmperes setup.longTimeCurrent := by
    simpa only [mul_zero, add_zero] using
      (tendsto_nhds_unique tendsto_const_nhds hConst)
  have hMain : currentInAmperes setup.longTimeCurrent =
      potentialDifferenceInVolts setup.batteryVoltage /
        resistanceInOhms setup.resistance :=
    (eq_div_iff hRne).2 (by nlinarith [hEq])
  refine ⟨hMain, by simpa [displayedCurrentInAmperes] using hMain, ?_⟩
  intro choice hChoice
  rw [hMain] at hChoice
  fin_cases choice
  · simp only [displayedCurrentInAmperes] at hChoice
    field_simp [hRne] at hChoice
    nlinarith [hDynamics.positiveBatteryVoltage]
  · simp only [displayedCurrentInAmperes] at hChoice
    field_simp [hRne] at hChoice
    nlinarith [hDynamics.positiveBatteryVoltage]
  · rfl
  · simp only [displayedCurrentInAmperes] at hChoice
    field_simp [hRne] at hChoice
    nlinarith [hDynamics.positiveBatteryVoltage]

end PhyXMiniProblems.ProblemPhyXMini0882
