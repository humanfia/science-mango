import Mathlib
import Physlib.Units.WithDim.Basic

/- USER: The assigned source file did not exist when this autoformalization task began. -/

noncomputable section

namespace PhyXMiniProblems.ProblemPhyXMini0889

open Dimension

/-!
# Resonance frequency of the pictured series RLC circuit

The primary raster `889.png` depicts one closed series loop containing a
sinusoidal voltage source, a resistor, an inductor, and a capacitor.  Its
printed values are `10 V`, `10 Ω`, `1.0 mH`, and `1.0 μF`; the source label is
`(10 V) cos (ω t)`.

Physical component values below use Physlib's unit-independent
`Dimensionful (WithDim _ _)` representation.  Real numbers occur only as
explicit coherent-unit readouts, printed figure data, and displayed answer
frequencies.
-/

/-! ## Dimensions and physical quantities -/

/-- The dimension `M L² T⁻² C⁻¹` of electric potential difference. -/
def electricPotentialDimension : Dimension :=
  M𝓭 * L𝓭 * L𝓭 * T𝓭⁻¹ * T𝓭⁻¹ * C𝓭⁻¹

/-- The dimension `V T C⁻¹` of electrical resistance. -/
def electricalResistanceDimension : Dimension :=
  electricPotentialDimension * T𝓭 * C𝓭⁻¹

/-- The dimension `V T² C⁻¹` of electrical inductance. -/
def electricalInductanceDimension : Dimension :=
  electricPotentialDimension * T𝓭 * T𝓭 * C𝓭⁻¹

/-- The dimension `C V⁻¹` of electrical capacitance. -/
def electricalCapacitanceDimension : Dimension :=
  C𝓭 * electricPotentialDimension⁻¹

/-- A nonnegative physical voltage amplitude. -/
abbrev VoltageAmplitudeQuantity : Type :=
  Dimensionful (WithDim electricPotentialDimension NNReal)

/-- A signed instantaneous voltage. -/
abbrev SignedVoltageQuantity : Type :=
  Dimensionful (WithDim electricPotentialDimension ℝ)

/-- A nonnegative physical electrical resistance. -/
abbrev ResistanceQuantity : Type :=
  Dimensionful (WithDim electricalResistanceDimension NNReal)

/-- A nonnegative physical electrical inductance. -/
abbrev InductanceQuantity : Type :=
  Dimensionful (WithDim electricalInductanceDimension NNReal)

/-- A nonnegative physical electrical capacitance. -/
abbrev CapacitanceQuantity : Type :=
  Dimensionful (WithDim electricalCapacitanceDimension NNReal)

/-- A nonnegative ordinary frequency, with inverse-time dimension. -/
abbrev FrequencyQuantity : Type :=
  Dimensionful (WithDim T𝓭⁻¹ NNReal)

/-- A nonnegative angular frequency; radians are dimensionless. -/
abbrev AngularFrequencyQuantity : Type :=
  Dimensionful (WithDim T𝓭⁻¹ NNReal)

/-- A signed physical time coordinate used in the source waveform. -/
abbrev TimeQuantity : Type :=
  Dimensionful (WithDim T𝓭 ℝ)

/-- Read a nonnegative dimensionful scalar in a coherent unit system. -/
def nonnegativeReadout
    {d : Dimension} (units : UnitChoices)
    (quantity : Dimensionful (WithDim d NNReal)) : ℝ :=
  ((quantity units).val : ℝ)

/-- Read a signed dimensionful scalar in a coherent unit system. -/
def signedReadout
    {d : Dimension} (units : UnitChoices)
    (quantity : Dimensionful (WithDim d ℝ)) : ℝ :=
  (quantity units).val

/-- Read a voltage amplitude in coherent SI volts. -/
def voltageAmplitudeInVolts (voltage : VoltageAmplitudeQuantity) : ℝ :=
  nonnegativeReadout UnitChoices.SI voltage

/-- Read a resistance in coherent SI ohms. -/
def resistanceInOhms (resistance : ResistanceQuantity) : ℝ :=
  nonnegativeReadout UnitChoices.SI resistance

/-- Read an inductance in coherent SI henries. -/
def inductanceInHenries (inductance : InductanceQuantity) : ℝ :=
  nonnegativeReadout UnitChoices.SI inductance

/-- Read an inductance in millihenries. -/
def inductanceInMillihenries (inductance : InductanceQuantity) : ℝ :=
  (10 : ℝ) ^ 3 * inductanceInHenries inductance

/-- Read a capacitance in coherent SI farads. -/
def capacitanceInFarads (capacitance : CapacitanceQuantity) : ℝ :=
  nonnegativeReadout UnitChoices.SI capacitance

/-- Read a capacitance in microfarads. -/
def capacitanceInMicrofarads (capacitance : CapacitanceQuantity) : ℝ :=
  (10 : ℝ) ^ 6 * capacitanceInFarads capacitance

/-- Read an ordinary frequency in coherent SI hertz. -/
def frequencyInHertz (frequency : FrequencyQuantity) : ℝ :=
  nonnegativeReadout UnitChoices.SI frequency

/-! ## Source, circuit topology, and figure content -/

/-- The physical sinusoidal source, including its symbolic drive frequency. -/
structure SinusoidalVoltageSource where
  amplitude : VoltageAmplitudeQuantity
  driveAngularFrequency : AngularFrequencyQuantity
  instantaneousVoltage : TimeQuantity → SignedVoltageQuantity

/-- The four component roles shown in the single loop. -/
inductive CircuitElement where
  | voltageSource
  | resistor
  | inductor
  | capacitor
  deriving DecidableEq, Fintype, Repr

/-- Junctions between consecutive components in the pictured loop. -/
inductive CircuitNode where
  | sourcePositive
  | resistorInductorJunction
  | inductorCapacitorJunction
  | sourceReturn
  deriving DecidableEq, Fintype, Repr

/-- Idealizations assigned to the four standard component symbols. -/
inductive ComponentModel where
  | idealSinusoidalVoltageSource
  | idealOhmicResistor
  | idealInductor
  | idealCapacitor
  | other
  deriving DecidableEq, Repr

/-- Literal presentation data read from the primary raster. -/
structure SeriesRLCCircuitFigure where
  componentSymbolShown : CircuitElement → Bool
  clockwiseOrderFromSource : List CircuitElement
  closedLoopWireShown : Bool
  sourceCosineOmegaTimeLabelShown : Bool
  printedSourceAmplitudeVolts : ℝ
  printedResistanceOhms : ℝ
  printedInductanceMillihenries : ℝ
  printedCapacitanceMicrofarads : ℝ

/-!
Independent physical data for the pictured circuit.  The resonant ordinary and
angular frequencies are fields rather than definitions from the component
values, so neither the requested numerical value nor an answer choice is
built into the setup.
-/
structure SeriesRLCCircuitSetup where
  source : SinusoidalVoltageSource
  componentModel : CircuitElement → ComponentModel
  resistance : ResistanceQuantity
  inductance : InductanceQuantity
  capacitance : CapacitanceQuantity
  resonantFrequency : FrequencyQuantity
  resonantAngularFrequency : AngularFrequencyQuantity
  terminals : CircuitElement → CircuitNode × CircuitNode
  figure : SeriesRLCCircuitFigure

/-! ## Scenario assumptions, figure readouts, and governing laws -/

/-- The standard ideal lumped-component interpretation of the symbols. -/
structure MatchesIdealSeriesRLCScenario
    (setup : SeriesRLCCircuitSetup) : Prop where
  sourceModel :
    setup.componentModel .voltageSource = .idealSinusoidalVoltageSource
  resistorModel :
    setup.componentModel .resistor = .idealOhmicResistor
  inductorModel :
    setup.componentModel .inductor = .idealInductor
  capacitorModel :
    setup.componentModel .capacitor = .idealCapacitor

/-- The terminal identifications making the four components one series loop. -/
structure MatchesSeriesClosedLoopTopology
    (setup : SeriesRLCCircuitSetup) : Prop where
  sourceTerminals :
    setup.terminals .voltageSource = (.sourceReturn, .sourcePositive)
  resistorTerminals :
    setup.terminals .resistor =
      (.sourcePositive, .resistorInductorJunction)
  inductorTerminals :
    setup.terminals .inductor =
      (.resistorInductorJunction, .inductorCapacitorJunction)
  capacitorTerminals :
    setup.terminals .capacitor =
      (.inductorCapacitorJunction, .sourceReturn)

/-!
Primary-raster evidence and calibration of every printed component value to
the corresponding physical quantity.  This contains no resonance-frequency
readout and no answer-choice information.
-/
structure MatchesSuppliedSeriesRLCFigure
    (setup : SeriesRLCCircuitSetup) : Prop where
  allComponentSymbolsShown : ∀ element,
    setup.figure.componentSymbolShown element = true
  clockwiseComponentOrder :
    setup.figure.clockwiseOrderFromSource =
      [.voltageSource, .resistor, .inductor, .capacitor]
  loopWireIsClosed : setup.figure.closedLoopWireShown = true
  sourceLabelShowsCosineOmegaTime :
    setup.figure.sourceCosineOmegaTimeLabelShown = true
  printedSourceAmplitude : setup.figure.printedSourceAmplitudeVolts = 10
  printedResistance : setup.figure.printedResistanceOhms = 10
  printedInductance : setup.figure.printedInductanceMillihenries = 1
  printedCapacitance : setup.figure.printedCapacitanceMicrofarads = 1
  sourceLabelCalibratesAmplitude :
    voltageAmplitudeInVolts setup.source.amplitude =
      setup.figure.printedSourceAmplitudeVolts
  resistorLabelCalibratesResistance :
    resistanceInOhms setup.resistance = setup.figure.printedResistanceOhms
  inductorLabelCalibratesInductance :
    inductanceInMillihenries setup.inductance =
      setup.figure.printedInductanceMillihenries
  capacitorLabelCalibratesCapacitance :
    capacitanceInMicrofarads setup.capacitance =
      setup.figure.printedCapacitanceMicrofarads

/-- Positivity and nondegeneracy of the physical parameters used below. -/
structure HasPhysicalSeriesRLCParameters
    (setup : SeriesRLCCircuitSetup) : Prop where
  sourceAmplitudePositive : 0 < voltageAmplitudeInVolts setup.source.amplitude
  resistancePositive : 0 < resistanceInOhms setup.resistance
  inductancePositive : 0 < inductanceInHenries setup.inductance
  capacitancePositive : 0 < capacitanceInFarads setup.capacitance
  driveAngularFrequencyPositive :
    0 < nonnegativeReadout UnitChoices.SI
      setup.source.driveAngularFrequency
  resonantFrequencyPositive : 0 < frequencyInHertz setup.resonantFrequency
  resonantAngularFrequencyPositive :
    0 < nonnegativeReadout UnitChoices.SI setup.resonantAngularFrequency

/-!
The cosine law expressed by the label `(10 V) cos (ω t)`.  The amplitude and
angular frequency remain physical dimensionful quantities, while the product
`ω t` is dimensionless in every coherent unit system.
-/
def ObeysIdealSinusoidalVoltageLaw
    (source : SinusoidalVoltageSource) : Prop :=
  ∀ (units : UnitChoices) (time : TimeQuantity),
    signedReadout units (source.instantaneousVoltage time) =
      nonnegativeReadout units source.amplitude *
        Real.cos
          (nonnegativeReadout units source.driveAngularFrequency *
            signedReadout units time)

/-!
Governing laws for ideal series-RLC resonance.  Ordinary and angular
frequencies satisfy `ω₀ = 2π f₀`, and at resonance the inductive and capacitive
reactance magnitudes cancel: `ω₀ L = 1 / (ω₀ C)`.  These relations are stated
for every coherent unit system and contain neither a requested hertz value nor
an answer choice.
-/
structure SatisfiesIdealSeriesRLCResonanceLaws
    (setup : SeriesRLCCircuitSetup) : Prop where
  angularFrequencyRelation : ∀ units,
    nonnegativeReadout units setup.resonantAngularFrequency =
      2 * Real.pi * nonnegativeReadout units setup.resonantFrequency
  resonantReactancesCancel : ∀ units,
    nonnegativeReadout units setup.resonantAngularFrequency *
        nonnegativeReadout units setup.inductance =
      1 /
        (nonnegativeReadout units setup.resonantAngularFrequency *
          nonnegativeReadout units setup.capacitance)

/-! ## Displayed answers and requested conclusion -/

/-- Labels of the four answer choices printed with the problem. -/
inductive AnswerChoice where
  | A
  | B
  | C
  | D
  deriving DecidableEq, Fintype, Repr

/-- The frequency in hertz printed beside each answer choice. -/
def AnswerChoice.displayedFrequencyHertz : AnswerChoice → ℝ
  | .A => 5 * 10 ^ 4
  | .B => 7 * 10 ^ 3
  | .C => 5 * 10 ^ 3
  | .D => 7 * 10 ^ 4

/-- The answer label recorded in the source dataset. -/
def recordedDatasetAnswer : AnswerChoice := .C

/-!
A displayed multiple-choice value is correct when it is strictly closer to
the exact physical resonance frequency than every other displayed value.  A
nearest-choice predicate is needed because the exact ideal value is about
`5033 Hz`, whereas the problem displays two-significant-figure choices.
-/
def IsUniqueClosestResonanceFrequencyChoice
    (setup : SeriesRLCCircuitSetup) (choice : AnswerChoice) : Prop :=
  ∀ other : AnswerChoice, other ≠ choice →
    |frequencyInHertz setup.resonantFrequency -
        choice.displayedFrequencyHertz| <
      |frequencyInHertz setup.resonantFrequency -
        other.displayedFrequencyHertz|

/-!
For `L = 1.0 mH` and `C = 1.0 μF`, ideal series-RLC resonance gives
`f₀ = 1 / (2π√(LC)) ≈ 5.03 × 10³ Hz`.  Thus the uniquely closest displayed
frequency is `5.0 × 10³ Hz`, recorded choice C.

This formalizes blueprint label `thm:physics:phyx_mini_0889:target`.
-/
theorem problem_phyx_mini_0889
    (setup : SeriesRLCCircuitSetup)
    (_scenario : MatchesIdealSeriesRLCScenario setup)
    (_topology : MatchesSeriesClosedLoopTopology setup)
    (_figure : MatchesSuppliedSeriesRLCFigure setup)
    (_physical : HasPhysicalSeriesRLCParameters setup)
    (_sourceLaw : ObeysIdealSinusoidalVoltageLaw setup.source)
    (_resonanceLaws : SatisfiesIdealSeriesRLCResonanceLaws setup) :
    IsUniqueClosestResonanceFrequencyChoice setup recordedDatasetAnswer := by
  have hL_scaled :
      (10 : ℝ) ^ 3 * inductanceInHenries setup.inductance = 1 := by
    calc
      (10 : ℝ) ^ 3 * inductanceInHenries setup.inductance =
          inductanceInMillihenries setup.inductance := by
            rfl
      _ = setup.figure.printedInductanceMillihenries :=
        _figure.inductorLabelCalibratesInductance
      _ = 1 := _figure.printedInductance
  have hC_scaled :
      (10 : ℝ) ^ 6 * capacitanceInFarads setup.capacitance = 1 := by
    calc
      (10 : ℝ) ^ 6 * capacitanceInFarads setup.capacitance =
          capacitanceInMicrofarads setup.capacitance := by
            rfl
      _ = setup.figure.printedCapacitanceMicrofarads :=
        _figure.capacitorLabelCalibratesCapacitance
      _ = 1 := _figure.printedCapacitance
  have hL : inductanceInHenries setup.inductance = (1 : ℝ) / 1000 := by
    norm_num at hL_scaled ⊢
    linarith
  have hC : capacitanceInFarads setup.capacitance = (1 : ℝ) / 1000000 := by
    norm_num at hC_scaled ⊢
    linarith
  let f : ℝ := frequencyInHertz setup.resonantFrequency
  let ω : ℝ :=
    nonnegativeReadout UnitChoices.SI setup.resonantAngularFrequency
  have hf_pos : 0 < f := by
    exact _physical.resonantFrequencyPositive
  have hω_pos : 0 < ω := by
    exact _physical.resonantAngularFrequencyPositive
  have hωf : ω = 2 * Real.pi * f := by
    exact _resonanceLaws.angularFrequencyRelation UnitChoices.SI
  have hres :
      ω * inductanceInHenries setup.inductance =
        1 / (ω * capacitanceInFarads setup.capacitance) := by
    exact _resonanceLaws.resonantReactancesCancel UnitChoices.SI
  have hden :
      ω * capacitanceInFarads setup.capacitance ≠ 0 :=
    mul_ne_zero (ne_of_gt hω_pos)
      (ne_of_gt _physical.capacitancePositive)
  have hproduct :
      (ω * inductanceInHenries setup.inductance) *
          (ω * capacitanceInFarads setup.capacitance) = 1 := by
    rw [hres]
    field_simp
  have hω_sq : ω ^ 2 = (10 : ℝ) ^ 9 := by
    rw [hL, hC] at hproduct
    norm_num at hproduct ⊢
    nlinarith
  have hf_lower : 5000 < f := by
    by_contra hnot
    have hf_le : f ≤ 5000 := le_of_not_gt hnot
    have hpif : Real.pi * f < (3.15 : ℝ) * 5000 := by
      calc
        Real.pi * f < (3.15 : ℝ) * f :=
          mul_lt_mul_of_pos_right Real.pi_lt_d2 hf_pos
        _ ≤ (3.15 : ℝ) * 5000 :=
          mul_le_mul_of_nonneg_left hf_le (by norm_num)
    have hω_lt : ω < 31500 := by
      rw [hωf]
      nlinarith
    have hsq_lt : ω * ω < (31500 : ℝ) * 31500 :=
      mul_self_lt_mul_self hω_pos.le hω_lt
    nlinarith [hω_sq]
  have hf_upper : f < 6000 := by
    by_contra hnot
    have hf_ge : 6000 ≤ f := le_of_not_gt hnot
    have hpif : (3 : ℝ) * 6000 < Real.pi * f := by
      calc
        (3 : ℝ) * 6000 ≤ 3 * f :=
          mul_le_mul_of_nonneg_left hf_ge (by norm_num)
        _ < Real.pi * f :=
          mul_lt_mul_of_pos_right Real.pi_gt_three hf_pos
    have hω_gt : 36000 < ω := by
      rw [hωf]
      nlinarith
    have hsq_gt : (36000 : ℝ) * 36000 < ω * ω :=
      mul_self_lt_mul_self (by norm_num) hω_gt
    nlinarith [hω_sq]
  unfold IsUniqueClosestResonanceFrequencyChoice
  intro other hother
  change
    |f - recordedDatasetAnswer.displayedFrequencyHertz| <
      |f - other.displayedFrequencyHertz|
  cases other with
  | A =>
      norm_num [recordedDatasetAnswer, AnswerChoice.displayedFrequencyHertz]
      rw [abs_of_pos (by linarith), abs_of_neg (by linarith)]
      linarith
  | B =>
      norm_num [recordedDatasetAnswer, AnswerChoice.displayedFrequencyHertz]
      rw [abs_of_pos (by linarith), abs_of_neg (by linarith)]
      linarith
  | C =>
      exact (hother rfl).elim
  | D =>
      norm_num [recordedDatasetAnswer, AnswerChoice.displayedFrequencyHertz]
      rw [abs_of_pos (by linarith), abs_of_neg (by linarith)]
      linarith

end PhyXMiniProblems.ProblemPhyXMini0889
