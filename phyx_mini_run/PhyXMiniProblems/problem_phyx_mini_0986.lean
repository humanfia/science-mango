import Mathlib.Analysis.SpecialFunctions.Exp
import Physlib.Units.WithDim.Basic

/- USER: The assigned Lean file did not exist when this autoformalization task began. -/

noncomputable section

namespace PhyXMiniProblems.ProblemPhyXMini0986

open Dimension

/-!
# Switched parallel-inductor circuit

Image `986.png` shows a `20.0 V` ideal battery, switch `S`, ammeter `A`,
`50.0 Ω` and `25.0 Ω` resistors, and a voltmeter `V` across two parallel
inductive branches.  One branch is the vertical `18.0 mH` inductor.  The
other runs through the `12.0 mH` and `15.0 mH` inductors in series via the
right-hand junction.  The switch has been open for a long time and closes at
time zero.  The requested observation time is `0.115 ms` after closing.

Physical magnitudes below are unit-independent Physlib `Dimensionful`
quantities.  Real numbers are used only for coherent-SI readouts and for the
number of volts printed by the meter.

Assumption/target split:

* governing laws: ideal component behavior, KCL/KVL for the displayed
  topology, series/parallel reduction, the standard ideal RL step-response
  law, and generic rounding of a one-decimal voltmeter;
* previous-part results: none;
* figure/data readouts: the component labels and terminals, `20.0 V`,
  `50.0 Ω`, `25.0 Ω`, `12.0 mH`, `18.0 mH`, `15.0 mH`, zero parasitic
  resistance, and the `0.115 ms` observation time;
* current target conclusion: the displayed reading at the observation time
  is `9.0 V` (answer B).

Neither the target display value nor the target-time voltage appears in any
premise structure.
-/

/-! ## Dimensionful electrical quantities and unit readouts -/

/-- The dimension `M L² T⁻² C⁻¹` of electric potential difference. -/
def voltageDimension : Dimension :=
  M𝓭 * L𝓭 * L𝓭 * T𝓭⁻¹ * T𝓭⁻¹ * C𝓭⁻¹

/-- The dimension `C T⁻¹` of electric current. -/
def electricCurrentDimension : Dimension :=
  C𝓭 * T𝓭⁻¹

/-- The dimension `M L² T⁻¹ C⁻²` of electrical resistance. -/
def electricalResistanceDimension : Dimension :=
  M𝓭 * L𝓭 * L𝓭 * T𝓭⁻¹ * C𝓭⁻¹ * C𝓭⁻¹

/-- The dimension `M L² C⁻²` of self-inductance. -/
def inductanceDimension : Dimension :=
  M𝓭 * L𝓭 * L𝓭 * C𝓭⁻¹ * C𝓭⁻¹

/-- A signed, unit-independent voltage. -/
abbrev VoltageQuantity : Type :=
  Dimensionful (WithDim voltageDimension ℝ)

/-- A signed, unit-independent electric current. -/
abbrev ElectricCurrentQuantity : Type :=
  Dimensionful (WithDim electricCurrentDimension ℝ)

/-- A nonnegative, unit-independent electrical resistance. -/
abbrev ResistanceMagnitude : Type :=
  Dimensionful (WithDim electricalResistanceDimension NNReal)

/-- A nonnegative, unit-independent self-inductance. -/
abbrev InductanceMagnitude : Type :=
  Dimensionful (WithDim inductanceDimension NNReal)

/-- A signed, unit-independent time coordinate relative to switch closing. -/
abbrev TimeQuantity : Type :=
  Dimensionful (WithDim T𝓭 ℝ)

/-- Coherent-SI voltage readout, in volts. -/
def voltageInVolts (voltage : VoltageQuantity) : ℝ :=
  (voltage UnitChoices.SI).val

/-- Coherent-SI current readout, in amperes. -/
def currentInAmperes (current : ElectricCurrentQuantity) : ℝ :=
  (current UnitChoices.SI).val

/-- Coherent-SI resistance readout, in ohms. -/
def resistanceInOhms (resistance : ResistanceMagnitude) : ℝ :=
  ((resistance UnitChoices.SI).val : ℝ)

/-- Coherent-SI inductance readout, in henries. -/
def inductanceInHenries (inductance : InductanceMagnitude) : ℝ :=
  ((inductance UnitChoices.SI).val : ℝ)

/-- Inductance readout in millihenries. -/
def inductanceInMillihenries (inductance : InductanceMagnitude) : ℝ :=
  1000 * inductanceInHenries inductance

/-- Coherent-SI time readout, in seconds. -/
def timeInSeconds (time : TimeQuantity) : ℝ :=
  (time UnitChoices.SI).val

/-- Time readout in milliseconds. -/
def timeInMilliseconds (time : TimeQuantity) : ℝ :=
  1000 * timeInSeconds time

/-! ## Primary-figure labels and apparatus -/

/-- Electrically distinct nodes visible in image `986.png`. -/
inductive CircuitNode where
  | batteryPositive
  | batteryNegative
  | afterSwitch
  | afterAmmeter
  | upperRail
  | lowerRail
  | rightJunction
  deriving DecidableEq, Fintype, Repr

/-- Every labeled circuit element visible in image `986.png`. -/
inductive ComponentLabel where
  | battery20V
  | switchS
  | ammeterA
  | resistor50Ohm
  | resistor25Ohm
  | voltmeterV
  | inductor12mH
  | inductor18mH
  | inductor15mH
  deriving DecidableEq, Fintype, Repr

/-- The endpoint data read directly from the supplied circuit diagram. -/
structure CircuitFigure where
  terminals : ComponentLabel → CircuitNode × CircuitNode

/-!
The independent physical quantities and time histories of the experiment.
The equivalent resistance and inductances are included as figure-derived
physical quantities; their reduction equations are laws rather than
definitions.
-/
structure SwitchedInductorCircuit where
  sourceVoltage : VoltageQuantity
  resistor50 : ResistanceMagnitude
  resistor25 : ResistanceMagnitude
  inductor12 : InductanceMagnitude
  inductor18 : InductanceMagnitude
  inductor15 : InductanceMagnitude
  batteryInternalResistance : ResistanceMagnitude
  ammeterInternalResistance : ResistanceMagnitude
  inductor12WindingResistance : ResistanceMagnitude
  inductor18WindingResistance : ResistanceMagnitude
  inductor15WindingResistance : ResistanceMagnitude
  totalSeriesResistance : ResistanceMagnitude
  rightBranchEquivalentInductance : InductanceMagnitude
  parallelEquivalentInductance : InductanceMagnitude
  closingTime : TimeQuantity
  observationTime : TimeQuantity
  switchClosed : TimeQuantity → Prop
  totalCurrent : TimeQuantity → ElectricCurrentQuantity
  ammeterCurrent : TimeQuantity → ElectricCurrentQuantity
  voltmeterCurrent : TimeQuantity → ElectricCurrentQuantity
  inductor12Current : TimeQuantity → ElectricCurrentQuantity
  inductor18Current : TimeQuantity → ElectricCurrentQuantity
  inductor15Current : TimeQuantity → ElectricCurrentQuantity
  voltmeterVoltage : TimeQuantity → VoltageQuantity
  inductor12Voltage : TimeQuantity → VoltageQuantity
  inductor18Voltage : TimeQuantity → VoltageQuantity
  inductor15Voltage : TimeQuantity → VoltageQuantity
  /-- The scalar number of volts printed by the one-decimal display. -/
  voltmeterDisplayedVolts : TimeQuantity → ℝ
  figure : CircuitFigure

/-! ## Figure evidence and numerical data -/

/-- Exact component incidences transcribed from the primary raster. -/
structure MatchesPrimaryCircuitFigure
    (circuit : SwitchedInductorCircuit) : Prop where
  batteryTerminals :
    circuit.figure.terminals .battery20V =
      (.batteryNegative, .batteryPositive)
  switchTerminals :
    circuit.figure.terminals .switchS =
      (.batteryPositive, .afterSwitch)
  ammeterTerminals :
    circuit.figure.terminals .ammeterA =
      (.batteryNegative, .afterAmmeter)
  resistor50Terminals :
    circuit.figure.terminals .resistor50Ohm =
      (.afterSwitch, .upperRail)
  resistor25Terminals :
    circuit.figure.terminals .resistor25Ohm =
      (.afterAmmeter, .lowerRail)
  voltmeterTerminals :
    circuit.figure.terminals .voltmeterV =
      (.upperRail, .lowerRail)
  inductor18Terminals :
    circuit.figure.terminals .inductor18mH =
      (.upperRail, .lowerRail)
  inductor12Terminals :
    circuit.figure.terminals .inductor12mH =
      (.upperRail, .rightJunction)
  inductor15Terminals :
    circuit.figure.terminals .inductor15mH =
      (.lowerRail, .rightJunction)

/-- All numerical labels shown in the problem and its primary figure. -/
structure MatchesCircuitNumericalData
    (circuit : SwitchedInductorCircuit) : Prop where
  sourceVoltageIs20Volts :
    voltageInVolts circuit.sourceVoltage = 20
  resistor50Is50Ohms :
    resistanceInOhms circuit.resistor50 = 50
  resistor25Is25Ohms :
    resistanceInOhms circuit.resistor25 = 25
  inductor12Is12Millihenries :
    inductanceInMillihenries circuit.inductor12 = 12
  inductor18Is18Millihenries :
    inductanceInMillihenries circuit.inductor18 = 18
  inductor15Is15Millihenries :
    inductanceInMillihenries circuit.inductor15 = 15
  closingTimeIsZero :
    timeInSeconds circuit.closingTime = 0
  observationIsPoint115Milliseconds :
    timeInMilliseconds circuit.observationTime = 0.115

/-! ## Governing physical laws -/

/--
The negligible-resistance assumptions stated in the prose, together with the
standard ideal-meter behavior used by the circuit diagram.
-/
structure HasIdealComponentPhysics
    (circuit : SwitchedInductorCircuit) : Prop where
  batteryHasNoInternalResistance :
    resistanceInOhms circuit.batteryInternalResistance = 0
  ammeterHasNoInternalResistance :
    resistanceInOhms circuit.ammeterInternalResistance = 0
  inductor12HasNoWindingResistance :
    resistanceInOhms circuit.inductor12WindingResistance = 0
  inductor18HasNoWindingResistance :
    resistanceInOhms circuit.inductor18WindingResistance = 0
  inductor15HasNoWindingResistance :
    resistanceInOhms circuit.inductor15WindingResistance = 0
  voltmeterDrawsNoCurrent :
    ∀ time, currentInAmperes (circuit.voltmeterCurrent time) = 0
  ammeterReadsTotalCurrent :
    ∀ time,
      currentInAmperes (circuit.ammeterCurrent time) =
        currentInAmperes (circuit.totalCurrent time)

/-- The switch history and zero-current state produced by being open a long time. -/
structure IsOpenLongThenClosed
    (circuit : SwitchedInductorCircuit) : Prop where
  openBeforeClosing :
    ∀ time,
      timeInSeconds time < timeInSeconds circuit.closingTime →
        ¬ circuit.switchClosed time
  closedFromClosing :
    ∀ time,
      timeInSeconds circuit.closingTime ≤ timeInSeconds time →
        circuit.switchClosed time
  totalCurrentInitiallyZero :
    currentInAmperes (circuit.totalCurrent circuit.closingTime) = 0
  inductor12CurrentInitiallyZero :
    currentInAmperes (circuit.inductor12Current circuit.closingTime) = 0
  inductor18CurrentInitiallyZero :
    currentInAmperes (circuit.inductor18Current circuit.closingTime) = 0
  inductor15CurrentInitiallyZero :
    currentInAmperes (circuit.inductor15Current circuit.closingTime) = 0

/--
Kirchhoff laws, series/parallel reduction, and the standard closed-form
voltage response for an ideal RL network after a DC step.  The response law is
uniform in time and in all component values; it contains neither the requested
time nor the answer choice.
-/
structure SatisfiesIdealRLTransientLaws
    (circuit : SwitchedInductorCircuit) : Prop where
  totalResistanceIsSeriesSum :
    resistanceInOhms circuit.totalSeriesResistance =
      resistanceInOhms circuit.resistor50 +
        resistanceInOhms circuit.resistor25
  rightBranchInductorsAreSeries :
    inductanceInHenries circuit.rightBranchEquivalentInductance =
      inductanceInHenries circuit.inductor12 +
        inductanceInHenries circuit.inductor15
  parallelInductanceLaw :
    1 / inductanceInHenries circuit.parallelEquivalentInductance =
      1 / inductanceInHenries circuit.inductor18 +
        1 / inductanceInHenries circuit.rightBranchEquivalentInductance
  totalResistancePositive :
    0 < resistanceInOhms circuit.totalSeriesResistance
  equivalentInductancePositive :
    0 < inductanceInHenries circuit.parallelEquivalentInductance
  rightBranchCurrentIsCommon :
    ∀ time,
      currentInAmperes (circuit.inductor12Current time) =
        currentInAmperes (circuit.inductor15Current time)
  currentNodeLaw :
    ∀ time, circuit.switchClosed time →
      currentInAmperes (circuit.totalCurrent time) =
        currentInAmperes (circuit.inductor18Current time) +
          currentInAmperes (circuit.inductor12Current time) +
            currentInAmperes (circuit.voltmeterCurrent time)
  voltmeterSpansInductor18 :
    ∀ time,
      voltageInVolts (circuit.voltmeterVoltage time) =
        voltageInVolts (circuit.inductor18Voltage time)
  voltmeterSpansRightBranch :
    ∀ time,
      voltageInVolts (circuit.voltmeterVoltage time) =
        voltageInVolts (circuit.inductor12Voltage time) +
          voltageInVolts (circuit.inductor15Voltage time)
  networkVoltageStepResponse :
    ∀ time,
      timeInSeconds circuit.closingTime ≤ timeInSeconds time →
        voltageInVolts (circuit.voltmeterVoltage time) =
          voltageInVolts circuit.sourceVoltage *
            Real.exp
              (-((resistanceInOhms circuit.totalSeriesResistance *
                    (timeInSeconds time -
                      timeInSeconds circuit.closingTime)) /
                  inductanceInHenries circuit.parallelEquivalentInductance))

/-- Generic calibration law for a voltmeter displaying volts to one decimal place. -/
structure HasOneDecimalVoltmeterDisplay
    (circuit : SwitchedInductorCircuit) : Prop where
  displayedValueLiesOnTenthVoltGrid :
    ∀ time, ∃ tick : ℤ,
      circuit.voltmeterDisplayedVolts time = (tick : ℝ) / 10
  displayedValueIsWithinHalfATenthVolt :
    ∀ time,
      |voltageInVolts (circuit.voltmeterVoltage time) -
          circuit.voltmeterDisplayedVolts time| < 1 / 20

/-! ## Figure-derived values and requested conclusion -/

/-- The two visible series resistors have equivalent resistance `75 Ω`. -/
lemma total_series_resistance_is_75_ohms
    (circuit : SwitchedInductorCircuit)
    (data : MatchesCircuitNumericalData circuit)
    (laws : SatisfiesIdealRLTransientLaws circuit) :
    resistanceInOhms circuit.totalSeriesResistance = 75 := by
  rw [laws.totalResistanceIsSeriesSum, data.resistor50Is50Ohms,
    data.resistor25Is25Ohms]
  norm_num

/-- The parallel combination `18 mH ∥ (12 mH + 15 mH)` is `10.8 mH`. -/
lemma parallel_equivalent_inductance_is_10_8_millihenries
    (circuit : SwitchedInductorCircuit)
    (data : MatchesCircuitNumericalData circuit)
    (laws : SatisfiesIdealRLTransientLaws circuit) :
    inductanceInMillihenries circuit.parallelEquivalentInductance = 10.8 := by
  have h12 :
      inductanceInHenries circuit.inductor12 = (12 / 1000 : ℝ) := by
    have h := data.inductor12Is12Millihenries
    rw [inductanceInMillihenries] at h
    linarith
  have h18 :
      inductanceInHenries circuit.inductor18 = (18 / 1000 : ℝ) := by
    have h := data.inductor18Is18Millihenries
    rw [inductanceInMillihenries] at h
    linarith
  have h15 :
      inductanceInHenries circuit.inductor15 = (15 / 1000 : ℝ) := by
    have h := data.inductor15Is15Millihenries
    rw [inductanceInMillihenries] at h
    linarith
  have hRight :
      inductanceInHenries circuit.rightBranchEquivalentInductance =
        (27 / 1000 : ℝ) := by
    rw [laws.rightBranchInductorsAreSeries, h12, h15]
    norm_num
  have hParallel :
      inductanceInHenries circuit.parallelEquivalentInductance =
        (27 / 2500 : ℝ) := by
    have h := laws.parallelInductanceLaw
    rw [h18, hRight] at h
    have hne :
        inductanceInHenries circuit.parallelEquivalentInductance ≠ 0 :=
      ne_of_gt laws.equivalentInductancePositive
    field_simp [hne] at h ⊢
    linarith
  rw [inductanceInMillihenries, hParallel]
  norm_num

/-- At `0.115 ms`, the physical voltage is within `0.001 V` of `9 V`. -/
lemma observation_voltage_is_within_one_millivolt_of_nine
    (circuit : SwitchedInductorCircuit)
    (data : MatchesCircuitNumericalData circuit)
    (switchHistory : IsOpenLongThenClosed circuit)
    (laws : SatisfiesIdealRLTransientLaws circuit) :
    |voltageInVolts (circuit.voltmeterVoltage circuit.observationTime) - 9| <
      1 / 1000 := by
  have hResistance :=
    total_series_resistance_is_75_ohms circuit data laws
  have hInductanceMillihenries :=
    parallel_equivalent_inductance_is_10_8_millihenries circuit data laws
  have hInductance :
      inductanceInHenries circuit.parallelEquivalentInductance =
        (27 / 2500 : ℝ) := by
    rw [inductanceInMillihenries] at hInductanceMillihenries
    linarith
  have hObservation :
      timeInSeconds circuit.observationTime = (115 / 1000000 : ℝ) := by
    have h := data.observationIsPoint115Milliseconds
    rw [timeInMilliseconds] at h
    norm_num at h ⊢
    linarith
  have hTime :
      timeInSeconds circuit.closingTime ≤
        timeInSeconds circuit.observationTime := by
    rw [data.closingTimeIsZero, hObservation]
    norm_num
  have hVoltage :=
    laws.networkVoltageStepResponse circuit.observationTime hTime
  rw [data.sourceVoltageIs20Volts, hResistance, hObservation,
    data.closingTimeIsZero, hInductance] at hVoltage
  norm_num at hVoltage
  rw [hVoltage]
  have hExp :=
    Real.exp_bound (x := (-115 / 144 : ℝ)) (n := 10)
      (by norm_num [abs_of_nonpos]) (by norm_num)
  rw [abs_le] at hExp
  norm_num [Finset.sum_range_succ, Nat.factorial, abs_of_nonpos] at hExp
  rw [abs_lt]
  constructor <;> linarith

/--
The voltmeter reads `9.0 V` at `0.115 ms` after the switch closes (answer B).

This is the Lean declaration corresponding to blueprint label
`thm:physics:phyx_mini_0986:target`.
-/
theorem voltmeter_reads_nine_volts_at_point115_milliseconds
    (circuit : SwitchedInductorCircuit)
    (figure : MatchesPrimaryCircuitFigure circuit)
    (data : MatchesCircuitNumericalData circuit)
    (idealComponents : HasIdealComponentPhysics circuit)
    (switchHistory : IsOpenLongThenClosed circuit)
    (laws : SatisfiesIdealRLTransientLaws circuit)
    (meter : HasOneDecimalVoltmeterDisplay circuit) :
    circuit.voltmeterDisplayedVolts circuit.observationTime = 9 := by
  have hVoltage :=
    observation_voltage_is_within_one_millivolt_of_nine
      circuit data switchHistory laws
  obtain ⟨tick, hTick⟩ :=
    meter.displayedValueLiesOnTenthVoltGrid circuit.observationTime
  have hMeter :=
    meter.displayedValueIsWithinHalfATenthVolt circuit.observationTime
  rw [abs_lt] at hVoltage hMeter
  rw [hTick] at hMeter ⊢
  have hTickLowerReal : (89 : ℝ) < (tick : ℝ) := by
    norm_num at hVoltage hMeter ⊢
    linarith
  have hTickUpperReal : (tick : ℝ) < (91 : ℝ) := by
    norm_num at hVoltage hMeter ⊢
    linarith
  have hTickLower : (89 : ℤ) < tick := by
    exact_mod_cast hTickLowerReal
  have hTickUpper : tick < (91 : ℤ) := by
    exact_mod_cast hTickUpperReal
  have : tick = 90 := by omega
  subst tick
  norm_num

end PhyXMiniProblems.ProblemPhyXMini0986
