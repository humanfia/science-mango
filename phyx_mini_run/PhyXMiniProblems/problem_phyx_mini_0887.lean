import Mathlib
import Physlib.Units.WithDim.Basic

/- USER: The assigned source file did not exist when this autoformalization task began. -/

noncomputable section

namespace PhyXMiniProblems.ProblemPhyXMini0887

open Dimension

/-!
# Capacitor-voltage amplitude in a sinusoidally driven series RC circuit

The primary raster `887.png` shows one closed loop containing a source labelled
`(10 V) cos ωt`, a `150 Ω` resistor, and an `80 nF` capacitor.  The resistor
and capacitor are consecutive components in the same branch, so they are in
series rather than in parallel.  The prose supplies the source frequency of
`10 kHz` and asks for the amplitude `V_C` across the capacitor.

Physical frequencies, voltages, resistances, and capacitances are represented
by unit-independent Physlib quantities.  Real numbers occur only as explicit
unit readouts, time coordinates measured in seconds, and printed numerical
data.  The requested capacitor voltage is an independent field of the setup;
the steady-state RC laws relate it to the source and components.
-/

/-! ## Dimensionful electrical quantities and named-unit readouts -/

/-- Frequency and angular frequency have inverse-time dimension. -/
def frequencyDimension : Dimension := T𝓭⁻¹

/-- Electric potential difference has the dimension energy per charge. -/
def electricPotentialDimension : Dimension :=
  M𝓭 * L𝓭 * L𝓭 * T𝓭⁻¹ * T𝓭⁻¹ * C𝓭⁻¹

/-- Electric current has the dimension charge per time. -/
def electricCurrentDimension : Dimension := C𝓭 * T𝓭⁻¹

/-- Electrical resistance and reactance have the dimension voltage per current. -/
def electricalResistanceDimension : Dimension :=
  electricPotentialDimension * electricCurrentDimension⁻¹

/-- Electrical capacitance has the dimension charge per voltage. -/
def electricalCapacitanceDimension : Dimension :=
  C𝓭 * electricPotentialDimension⁻¹

/-- A nonnegative, unit-independent physical frequency. -/
abbrev FrequencyQuantity : Type :=
  Dimensionful (WithDim frequencyDimension NNReal)

/-- A nonnegative, unit-independent voltage amplitude. -/
abbrev VoltageAmplitudeQuantity : Type :=
  Dimensionful (WithDim electricPotentialDimension NNReal)

/-- A nonnegative, unit-independent resistance or reactance magnitude. -/
abbrev ResistanceMagnitudeQuantity : Type :=
  Dimensionful (WithDim electricalResistanceDimension NNReal)

/-- A nonnegative, unit-independent capacitance. -/
abbrev CapacitanceQuantity : Type :=
  Dimensionful (WithDim electricalCapacitanceDimension NNReal)

/-- Coherent-SI readout of a nonnegative dimensionful quantity. -/
def nonnegativeSIReadout {d : Dimension}
    (quantity : Dimensionful (WithDim d NNReal)) : ℝ :=
  ((quantity UnitChoices.SI).val : ℝ)

/-- Read an ordinary frequency in hertz. -/
def frequencyInHertz (frequency : FrequencyQuantity) : ℝ :=
  nonnegativeSIReadout frequency

/-- Read an ordinary frequency in kilohertz. -/
def frequencyInKilohertz (frequency : FrequencyQuantity) : ℝ :=
  frequencyInHertz frequency / 1000

/-- Read an angular frequency in radians per second (radians are dimensionless). -/
def angularFrequencyInRadiansPerSecond (frequency : FrequencyQuantity) : ℝ :=
  nonnegativeSIReadout frequency

/-- Read a voltage amplitude in volts. -/
def voltageAmplitudeInVolts (voltage : VoltageAmplitudeQuantity) : ℝ :=
  nonnegativeSIReadout voltage

/-- Read a resistance, reactance, or impedance magnitude in ohms. -/
def resistanceMagnitudeInOhms
    (resistance : ResistanceMagnitudeQuantity) : ℝ :=
  nonnegativeSIReadout resistance

/-- Read a capacitance in farads. -/
def capacitanceInFarads (capacitance : CapacitanceQuantity) : ℝ :=
  nonnegativeSIReadout capacitance

/-- Read a capacitance in nanofarads. -/
def capacitanceInNanofarads (capacitance : CapacitanceQuantity) : ℝ :=
  (10 : ℝ) ^ 9 * capacitanceInFarads capacitance

/-! ## Physical components, circuit nodes, and primary-figure content -/

/-- Idealizations relevant to the source shown in the figure. -/
inductive VoltageSourceModel where
  | idealSinusoidal
  | other
  deriving DecidableEq, Repr

/-- Idealizations relevant to the resistor and capacitor. -/
inductive PassiveComponentModel where
  | idealLumped
  | other
  deriving DecidableEq, Repr

/-- Component identities encountered in one traversal of the depicted loop. -/
inductive CircuitComponent where
  | voltageSource
  | resistor
  | capacitor
  deriving DecidableEq, Fintype, Repr

/-- The three electrically distinct nodes of the depicted series circuit. -/
inductive CircuitNode where
  | sourceHigh
  | resistorCapacitorJunction
  | sourceReturn
  deriving DecidableEq, Fintype, Repr

/-- The sinusoidal source and its independent physical parameters. -/
structure SinusoidalVoltageSource where
  model : VoltageSourceModel
  voltageAmplitude : VoltageAmplitudeQuantity
  ordinaryFrequency : FrequencyQuantity
  angularFrequency : FrequencyQuantity
  /-- Signed instantaneous voltage, with the argument read in seconds. -/
  instantaneousVoltageInVolts : ℝ → ℝ

/-- The idealized resistor shown on the upper right. -/
structure Resistor where
  model : PassiveComponentModel
  resistance : ResistanceMagnitudeQuantity

/-- The idealized capacitor shown below the resistor. -/
structure Capacitor where
  model : PassiveComponentModel
  capacitance : CapacitanceQuantity
  /-- The requested steady-state voltage amplitude, not fixed by definition. -/
  voltageAmplitude : VoltageAmplitudeQuantity

/-!
Literal presentation data from the primary raster.  Printed values are scalar
readouts in the units named by their fields and remain distinct from physical
quantities.
-/
structure SeriesRCFigure where
  componentAt : Fin 3 → CircuitComponent
  componentTerminals : CircuitComponent → CircuitNode × CircuitNode
  formsSingleClosedLoop : Bool
  sourceCosineLabelShown : Bool
  sourcePrintedFormula : String
  sourcePrintedAmplitudeInVolts : ℝ
  resistorPrintedResistanceInOhms : ℝ
  capacitorPrintedCapacitanceInNanofarads : ℝ

/-!
Independent physical data for the circuit.  Reactance and impedance are fields
rather than definitions, so their governing laws carry the physical content.
-/
structure SeriesRCCircuitSetup where
  source : SinusoidalVoltageSource
  resistor : Resistor
  capacitor : Capacitor
  capacitiveReactance : ResistanceMagnitudeQuantity
  seriesImpedanceMagnitude : ResistanceMagnitudeQuantity
  figure : SeriesRCFigure

/-! ## Scenario, topology, readouts, and governing laws -/

/-- The ideal lumped-element interpretation and the prose-supplied frequency. -/
structure MatchesStatedSeriesRCScenario
    (setup : SeriesRCCircuitSetup) : Prop where
  sourceIsIdealSinusoidal : setup.source.model = .idealSinusoidal
  resistorIsIdealLumped : setup.resistor.model = .idealLumped
  capacitorIsIdealLumped : setup.capacitor.model = .idealLumped
  suppliedFrequencyInKilohertz :
    frequencyInKilohertz setup.source.ordinaryFrequency = 10

/-!
Topology and annotations transcribed from `887.png`.  The resistor and
capacitor share only their intermediate junction and therefore occur in
series in the single loop.
-/
structure MatchesSuppliedSeriesRCFigure
    (setup : SeriesRCCircuitSetup) : Prop where
  firstComponent : setup.figure.componentAt 0 = .voltageSource
  secondComponent : setup.figure.componentAt 1 = .resistor
  thirdComponent : setup.figure.componentAt 2 = .capacitor
  sourceTerminals :
    setup.figure.componentTerminals .voltageSource =
      (.sourceReturn, .sourceHigh)
  resistorTerminals :
    setup.figure.componentTerminals .resistor =
      (.sourceHigh, .resistorCapacitorJunction)
  capacitorTerminals :
    setup.figure.componentTerminals .capacitor =
      (.resistorCapacitorJunction, .sourceReturn)
  oneClosedLoop : setup.figure.formsSingleClosedLoop = true
  cosineLabelShown : setup.figure.sourceCosineLabelShown = true
  printedSourceFormula : setup.figure.sourcePrintedFormula = "(10 V) cos ωt"
  printedSourceAmplitude : setup.figure.sourcePrintedAmplitudeInVolts = 10
  printedResistance : setup.figure.resistorPrintedResistanceInOhms = 150
  printedCapacitance :
    setup.figure.capacitorPrintedCapacitanceInNanofarads = 80
  sourceAmplitudeMatchesFigure :
    voltageAmplitudeInVolts setup.source.voltageAmplitude =
      setup.figure.sourcePrintedAmplitudeInVolts
  resistorValueMatchesFigure :
    resistanceMagnitudeInOhms setup.resistor.resistance =
      setup.figure.resistorPrintedResistanceInOhms
  capacitorValueMatchesFigure :
    capacitanceInNanofarads setup.capacitor.capacitance =
      setup.figure.capacitorPrintedCapacitanceInNanofarads

/-- Positivity needed for the reciprocal and voltage-divider relations. -/
structure HasPositiveSeriesRCParameters
    (setup : SeriesRCCircuitSetup) : Prop where
  sourceFrequencyPositive :
    0 < frequencyInHertz setup.source.ordinaryFrequency
  sourceAmplitudePositive :
    0 < voltageAmplitudeInVolts setup.source.voltageAmplitude
  resistancePositive :
    0 < resistanceMagnitudeInOhms setup.resistor.resistance
  capacitancePositive :
    0 < capacitanceInFarads setup.capacitor.capacitance
  capacitiveReactancePositive :
    0 < resistanceMagnitudeInOhms setup.capacitiveReactance
  impedanceMagnitudePositive :
    0 < resistanceMagnitudeInOhms setup.seriesImpedanceMagnitude

/-!
Standard sinusoidal steady-state laws for an ideal series RC circuit.  These
relations are generic: they contain neither the requested `8 V` result nor any
answer-choice label.
-/
structure SatisfiesSinusoidalSteadyStateRCLaws
    (setup : SeriesRCCircuitSetup) : Prop where
  angularFrequencyLaw :
    angularFrequencyInRadiansPerSecond setup.source.angularFrequency =
      2 * Real.pi * frequencyInHertz setup.source.ordinaryFrequency
  sourceWaveformLaw : ∀ timeInSeconds,
    setup.source.instantaneousVoltageInVolts timeInSeconds =
      voltageAmplitudeInVolts setup.source.voltageAmplitude *
        Real.cos
          (angularFrequencyInRadiansPerSecond setup.source.angularFrequency *
            timeInSeconds)
  capacitiveReactanceLaw :
    resistanceMagnitudeInOhms setup.capacitiveReactance =
      1 /
        (angularFrequencyInRadiansPerSecond setup.source.angularFrequency *
          capacitanceInFarads setup.capacitor.capacitance)
  seriesImpedanceMagnitudeLaw :
    resistanceMagnitudeInOhms setup.seriesImpedanceMagnitude =
      Real.sqrt
        (resistanceMagnitudeInOhms setup.resistor.resistance ^ 2 +
          resistanceMagnitudeInOhms setup.capacitiveReactance ^ 2)
  capacitorVoltageDividerLaw :
    voltageAmplitudeInVolts setup.capacitor.voltageAmplitude =
      voltageAmplitudeInVolts setup.source.voltageAmplitude *
        resistanceMagnitudeInOhms setup.capacitiveReactance /
          resistanceMagnitudeInOhms setup.seriesImpedanceMagnitude

/-! ## Displayed answer choices and target -/

/-- Labels of the four voltage-valued answer choices. -/
inductive AnswerChoice where
  | A
  | B
  | C
  | D
  deriving DecidableEq, Fintype, Repr

/-- Voltage amplitude printed beside each answer-choice label, in volts. -/
def AnswerChoice.displayedVoltageInVolts : AnswerChoice → ℝ
  | .A => 12
  | .B => 6
  | .C => 8
  | .D => 5

/-- Half of the `0.1 V` display unit used by the answer choices. -/
def displayedVoltageToleranceInVolts : ℝ := 1 / 20

/-- A choice agrees with the physical capacitor amplitude to displayed precision. -/
def AnswerMatchesCapacitorVoltageAmplitude
    (setup : SeriesRCCircuitSetup) (choice : AnswerChoice) : Prop :=
  |voltageAmplitudeInVolts setup.capacitor.voltageAmplitude -
      choice.displayedVoltageInVolts| < displayedVoltageToleranceInVolts

/-- A choice is the unique displayed option matching the physical amplitude. -/
def IsUniqueMatchingAnswer
    (setup : SeriesRCCircuitSetup) (choice : AnswerChoice) : Prop :=
  AnswerMatchesCapacitorVoltageAmplitude setup choice ∧
    ∀ otherChoice,
      AnswerMatchesCapacitorVoltageAmplitude setup otherChoice →
        otherChoice = choice

/-- The answer label recorded in the source dataset. -/
def recordedDatasetAnswer : AnswerChoice := .C

/-!
At `10 kHz`, the `80 nF` capacitor has reactance about `199 Ω`; with the
`150 Ω` series resistor, the capacitor receives about `7.98 V`, displayed as
`8.0 V`.  Thus the recorded choice C is the unique displayed match.

This declaration formalizes `thm:physics:phyx_mini_0887:target`.  The requested
numerical value and answer label occur only in conclusion-side answer data,
not in the scenario, figure calibration, positivity, or governing-law fields.
-/
theorem problem_phyx_mini_0887
    (setup : SeriesRCCircuitSetup)
    (hScenario : MatchesStatedSeriesRCScenario setup)
    (hFigure : MatchesSuppliedSeriesRCFigure setup)
    (hPositive : HasPositiveSeriesRCParameters setup)
    (hLaws : SatisfiesSinusoidalSteadyStateRCLaws setup) :
    |voltageAmplitudeInVolts setup.capacitor.voltageAmplitude - 8| <
        displayedVoltageToleranceInVolts ∧
      IsUniqueMatchingAnswer setup recordedDatasetAnswer := by
  let x : ℝ :=
    resistanceMagnitudeInOhms setup.capacitiveReactance
  let z : ℝ :=
    resistanceMagnitudeInOhms setup.seriesImpedanceMagnitude
  let v : ℝ :=
    voltageAmplitudeInVolts setup.capacitor.voltageAmplitude
  have hFrequency :
      frequencyInHertz setup.source.ordinaryFrequency = 10000 := by
    have h := hScenario.suppliedFrequencyInKilohertz
    unfold frequencyInKilohertz at h
    linarith
  have hSourceAmplitude :
      voltageAmplitudeInVolts setup.source.voltageAmplitude = 10 := by
    calc
      voltageAmplitudeInVolts setup.source.voltageAmplitude =
          setup.figure.sourcePrintedAmplitudeInVolts :=
        hFigure.sourceAmplitudeMatchesFigure
      _ = 10 := hFigure.printedSourceAmplitude
  have hResistance :
      resistanceMagnitudeInOhms setup.resistor.resistance = 150 := by
    calc
      resistanceMagnitudeInOhms setup.resistor.resistance =
          setup.figure.resistorPrintedResistanceInOhms :=
        hFigure.resistorValueMatchesFigure
      _ = 150 := hFigure.printedResistance
  have hCapacitance :
      capacitanceInFarads setup.capacitor.capacitance =
        (1 / 12500000 : ℝ) := by
    have h := hFigure.capacitorValueMatchesFigure
    rw [hFigure.printedCapacitance] at h
    unfold capacitanceInNanofarads at h
    norm_num at h ⊢
    linarith
  have hAngularFrequency :
      angularFrequencyInRadiansPerSecond setup.source.angularFrequency =
        20000 * Real.pi := by
    calc
      angularFrequencyInRadiansPerSecond setup.source.angularFrequency =
          2 * Real.pi *
            frequencyInHertz setup.source.ordinaryFrequency :=
        hLaws.angularFrequencyLaw
      _ = 20000 * Real.pi := by rw [hFrequency]; ring
  have hxFormula : x = 625 / Real.pi := by
    calc
      x = 1 /
          (angularFrequencyInRadiansPerSecond
              setup.source.angularFrequency *
            capacitanceInFarads setup.capacitor.capacitance) := by
        simpa [x] using hLaws.capacitiveReactanceLaw
      _ = 625 / Real.pi := by
        rw [hAngularFrequency, hCapacitance]
        field_simp [ne_of_gt Real.pi_pos]
        all_goals ring
  have hxPositive : 0 < x := by
    simpa [x] using hPositive.capacitiveReactancePositive
  have hxLower : (198 : ℝ) < x := by
    rw [hxFormula, lt_div_iff₀ Real.pi_pos]
    nlinarith [Real.pi_lt_d2]
  have hxUpper : x < (200 : ℝ) := by
    rw [hxFormula, div_lt_iff₀ Real.pi_pos]
    nlinarith [Real.pi_gt_d2]
  have hzPositive : 0 < z := by
    simpa [z] using hPositive.impedanceMagnitudePositive
  have hzFormula :
      z = Real.sqrt ((150 : ℝ) ^ 2 + x ^ 2) := by
    simpa [z, x, hResistance] using
      hLaws.seriesImpedanceMagnitudeLaw
  have hzSquare :
      z ^ 2 = (150 : ℝ) ^ 2 + x ^ 2 := by
    rw [hzFormula, Real.sq_sqrt]
    positivity
  have hvFormula : v = 10 * x / z := by
    simpa [v, x, z, hSourceAmplitude] using
      hLaws.capacitorVoltageDividerLaw
  have hvPositive : 0 < v := by
    rw [hvFormula]
    positivity
  have hvTimesImpedance : v * z = 10 * x := by
    rw [hvFormula]
    field_simp [ne_of_gt hzPositive]
  have hvSquareRelation :
      v ^ 2 * ((150 : ℝ) ^ 2 + x ^ 2) = 100 * x ^ 2 := by
    calc
      v ^ 2 * ((150 : ℝ) ^ 2 + x ^ 2) = (v * z) ^ 2 := by
        rw [mul_pow, hzSquare]
      _ = (10 * x) ^ 2 := by rw [hvTimesImpedance]
      _ = 100 * x ^ 2 := by ring
  have hvLower : (159 / 20 : ℝ) < v := by
    by_contra h
    have hvLe : v ≤ (159 / 20 : ℝ) := le_of_not_gt h
    have hvSquareLe :
        v ^ 2 ≤ (159 / 20 : ℝ) ^ 2 :=
      (sq_le_sq₀ hvPositive.le (by norm_num)).2 hvLe
    have hRadicandNonnegative :
        0 ≤ (150 : ℝ) ^ 2 + x ^ 2 := by positivity
    have hProductLe := mul_le_mul_of_nonneg_right
      hvSquareLe hRadicandNonnegative
    have hxSquareLower : (198 : ℝ) ^ 2 < x ^ 2 := by
      nlinarith
    nlinarith [hvSquareRelation, hProductLe, hxSquareLower]
  have hvUpper : v < (8 : ℝ) := by
    by_contra h
    have hvGe : (8 : ℝ) ≤ v := le_of_not_gt h
    have hvSquareGe : (8 : ℝ) ^ 2 ≤ v ^ 2 :=
      (sq_le_sq₀ (by norm_num) hvPositive.le).2 hvGe
    have hRadicandNonnegative :
        0 ≤ (150 : ℝ) ^ 2 + x ^ 2 := by positivity
    have hProductGe := mul_le_mul_of_nonneg_right
      hvSquareGe hRadicandNonnegative
    have hxSquareUpper : x ^ 2 < (200 : ℝ) ^ 2 := by
      nlinarith
    nlinarith [hvSquareRelation, hProductGe, hxSquareUpper]
  have hChoiceC :
      |v - 8| < (1 / 20 : ℝ) := by
    rw [abs_lt]
    constructor <;> nlinarith
  constructor
  · simpa [v, displayedVoltageToleranceInVolts] using hChoiceC
  · unfold IsUniqueMatchingAnswer
    constructor
    · simpa [AnswerMatchesCapacitorVoltageAmplitude,
        recordedDatasetAnswer, AnswerChoice.displayedVoltageInVolts,
        displayedVoltageToleranceInVolts, v] using hChoiceC
    · intro otherChoice hOther
      change |v - otherChoice.displayedVoltageInVolts| <
        (1 / 20 : ℝ) at hOther
      change otherChoice = AnswerChoice.C
      cases otherChoice with
      | A =>
          simp only [AnswerChoice.displayedVoltageInVolts] at hOther
          rw [abs_lt] at hOther
          exfalso
          nlinarith
      | B =>
          simp only [AnswerChoice.displayedVoltageInVolts] at hOther
          rw [abs_lt] at hOther
          exfalso
          nlinarith
      | C => rfl
      | D =>
          simp only [AnswerChoice.displayedVoltageInVolts] at hOther
          rw [abs_lt] at hOther
          exfalso
          nlinarith

end PhyXMiniProblems.ProblemPhyXMini0887
