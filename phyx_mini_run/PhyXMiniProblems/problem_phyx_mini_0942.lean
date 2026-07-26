import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Physlib.Units.WithDim.Basic

/- USER: The assigned Lean file did not exist when this autoformalization task began. -/

noncomputable section

namespace PhyXMiniProblems.ProblemPhyXMini0942

open Dimension

/-!
# Capacitive reactance in a series RC circuit

The primary figure shows a `200 Ω` resistor and a `5.0 μF` capacitor in one
closed series loop with a sinusoidal voltage source.  The resistor voltage is
printed as

`v_R(t) = (1.20 V) cos ((2500 rad/s) t)`.

Physical magnitudes are represented by unit-independent Physlib
`Dimensionful` quantities.  Real numbers occur only as coherent-SI readouts
or as literal scalar data printed in the figure.

Assumption/target split:

* governing law: the ideal-capacitor reactance relation `X_C = 1 / (ω C)`;
* previous-part results: none;
* figure/data readouts: the series-loop topology and component/voltage labels,
  the left-pointing current arrow, `R = 200 Ω`, `C = 5.0 μF`, and the displayed
  resistor-voltage waveform with amplitude `1.20 V` and angular frequency
  `2500 rad/s`;
* current target conclusion: the capacitive reactance is `80 Ω` (choice B).

The capacitive reactance is an independent field of the physical setup.  It
is not defined to be the requested answer, and no premise below states its
value as `80 Ω`.
-/

/-! ## Dimensionful electrical quantities and coherent-SI readouts -/

/-- The dimension `M L² T⁻² C⁻¹` of electric potential (volt). -/
def electricPotentialDimension : Dimension :=
  M𝓭 * L𝓭 * L𝓭 * T𝓭⁻¹ * T𝓭⁻¹ * C𝓭⁻¹

/-- The dimension `C T⁻¹` of electric current (ampere). -/
def electricCurrentDimension : Dimension :=
  C𝓭 * T𝓭⁻¹

/-- The dimension `M L² T⁻¹ C⁻²` of electrical resistance (ohm). -/
def electricalResistanceDimension : Dimension :=
  M𝓭 * L𝓭 * L𝓭 * T𝓭⁻¹ * C𝓭⁻¹ * C𝓭⁻¹

/-- The dimension `M⁻¹ L⁻² T² C²` of capacitance (farad). -/
def capacitanceDimension : Dimension :=
  M𝓭⁻¹ * L𝓭⁻¹ * L𝓭⁻¹ * T𝓭 * T𝓭 * C𝓭 * C𝓭

/-- A nonnegative, unit-independent electrical resistance magnitude. -/
abbrev ResistanceMagnitude : Type :=
  Dimensionful (WithDim electricalResistanceDimension NNReal)

/-- A nonnegative, unit-independent capacitance magnitude. -/
abbrev CapacitanceMagnitude : Type :=
  Dimensionful (WithDim capacitanceDimension NNReal)

/-- A nonnegative, unit-independent angular-frequency magnitude. -/
abbrev AngularFrequencyMagnitude : Type :=
  Dimensionful (WithDim T𝓭⁻¹ NNReal)

/-- A signed, unit-independent electric-potential quantity. -/
abbrev ElectricPotentialQuantity : Type :=
  Dimensionful (WithDim electricPotentialDimension ℝ)

/-- A signed, unit-independent electric-current quantity. -/
abbrev ElectricCurrentQuantity : Type :=
  Dimensionful (WithDim electricCurrentDimension ℝ)

/-- A signed, unit-independent time coordinate. -/
abbrev TimeQuantity : Type :=
  Dimensionful (WithDim T𝓭 ℝ)

/-- Coherent-SI readout of a nonnegative dimensionful quantity. -/
def nonnegativeSIReadout {d : Dimension}
    (quantity : Dimensionful (WithDim d NNReal)) : ℝ :=
  ((quantity UnitChoices.SI).val : ℝ)

/-- Coherent-SI readout of a signed dimensionful quantity. -/
def signedSIReadout {d : Dimension}
    (quantity : Dimensionful (WithDim d ℝ)) : ℝ :=
  (quantity UnitChoices.SI).val

/-- Coherent-SI resistance readout, in ohms. -/
def resistanceInOhms (resistance : ResistanceMagnitude) : ℝ :=
  nonnegativeSIReadout resistance

/-- Coherent-SI capacitance readout, in farads. -/
def capacitanceInFarads (capacitance : CapacitanceMagnitude) : ℝ :=
  nonnegativeSIReadout capacitance

/-- Coherent-SI angular-frequency readout, in radians per second. -/
def angularFrequencyInRadiansPerSecond
    (angularFrequency : AngularFrequencyMagnitude) : ℝ :=
  nonnegativeSIReadout angularFrequency

/-- Coherent-SI electric-potential readout, in volts. -/
def electricPotentialInVolts (potential : ElectricPotentialQuantity) : ℝ :=
  signedSIReadout potential

/-- Coherent-SI electric-current readout, in amperes. -/
def electricCurrentInAmperes (current : ElectricCurrentQuantity) : ℝ :=
  signedSIReadout current

/-- Coherent-SI time-coordinate readout, in seconds. -/
def timeInSeconds (time : TimeQuantity) : ℝ :=
  signedSIReadout time

/-! ## Circuit roles and primary-figure labels -/

/-- The three components visible in the supplied circuit schematic. -/
inductive CircuitComponent where
  | acVoltageSource
  | capacitor
  | resistor
  deriving DecidableEq, Fintype, Repr

/-- The two explicitly named component-voltage symbols in the figure. -/
inductive VoltageSymbol where
  | vC
  | vR
  deriving DecidableEq, Repr

/-- Horizontal directions used by the current arrow in the schematic. -/
inductive HorizontalDirection where
  | left
  | right
  deriving DecidableEq, Repr

/-!
Literal information visible in image `942.png`.  Numerical fields record the
numbers printed beside the physical quantities; their units are specified by
their field names and tied to dimensionful quantities below.
-/
structure SeriesRCFigure where
  componentShown : CircuitComponent → Bool
  componentsLieOnOneClosedSeriesPath : Bool
  sourceSymbolIsSinusoidal : Bool
  currentArrowDirection : HorizontalDirection
  voltageSymbol : CircuitComponent → Option VoltageSymbol
  capacitanceLabelMicrofarads : ℝ
  resistanceLabelOhms : ℝ
  resistorVoltageAmplitudeLabelVolts : ℝ
  angularFrequencyLabelRadiansPerSecond : ℝ

/-!
The physical objects and time-dependent observables in the displayed circuit.
The capacitive reactance is independent data here, rather than an expansion of
the answer formula.
-/
structure SeriesRCCircuitSetup where
  resistorResistance : ResistanceMagnitude
  capacitorCapacitance : CapacitanceMagnitude
  angularFrequency : AngularFrequencyMagnitude
  resistorVoltageAmplitude : ElectricPotentialQuantity
  capacitiveReactance : ResistanceMagnitude
  sourceVoltage : TimeQuantity → ElectricPotentialQuantity
  capacitorVoltage : TimeQuantity → ElectricPotentialQuantity
  resistorVoltage : TimeQuantity → ElectricPotentialQuantity
  seriesCurrent : TimeQuantity → ElectricCurrentQuantity
  figure : SeriesRCFigure

/-! ## Scenario, figure evidence, physical parameters, and governing law -/

/-- The prose and schematic specify a closed series circuit with an AC source. -/
structure MatchesSeriesRCScenario (setup : SeriesRCCircuitSetup) : Prop where
  sourceShown : setup.figure.componentShown .acVoltageSource = true
  capacitorShown : setup.figure.componentShown .capacitor = true
  resistorShown : setup.figure.componentShown .resistor = true
  oneClosedSeriesPath :
    setup.figure.componentsLieOnOneClosedSeriesPath = true
  sinusoidalSource : setup.figure.sourceSymbolIsSinusoidal = true

/-!
Primary-raster evidence: component labels, the current arrow, and every
numerical annotation printed in the image.  The waveform equality is a
calibrated transcription of the displayed `v_R(t)` expression.  It does not
state the requested reactance.
-/
structure MatchesPrimarySeriesRCFigure
    (setup : SeriesRCCircuitSetup) : Prop where
  currentPointsLeft : setup.figure.currentArrowDirection = .left
  capacitorVoltageLabel :
    setup.figure.voltageSymbol .capacitor = some .vC
  resistorVoltageLabel :
    setup.figure.voltageSymbol .resistor = some .vR
  capacitanceLabel : setup.figure.capacitanceLabelMicrofarads = 5
  resistanceLabel : setup.figure.resistanceLabelOhms = 200
  resistorVoltageAmplitudeLabel :
    setup.figure.resistorVoltageAmplitudeLabelVolts = 1.20
  angularFrequencyLabel :
    setup.figure.angularFrequencyLabelRadiansPerSecond = 2500
  capacitanceCalibration :
    capacitanceInFarads setup.capacitorCapacitance =
      setup.figure.capacitanceLabelMicrofarads / 10 ^ 6
  resistanceCalibration :
    resistanceInOhms setup.resistorResistance =
      setup.figure.resistanceLabelOhms
  amplitudeCalibration :
    electricPotentialInVolts setup.resistorVoltageAmplitude =
      setup.figure.resistorVoltageAmplitudeLabelVolts
  angularFrequencyCalibration :
    angularFrequencyInRadiansPerSecond setup.angularFrequency =
      setup.figure.angularFrequencyLabelRadiansPerSecond
  displayedResistorVoltageWaveform : ∀ time,
    electricPotentialInVolts (setup.resistorVoltage time) =
      electricPotentialInVolts setup.resistorVoltageAmplitude *
        Real.cos
          (angularFrequencyInRadiansPerSecond setup.angularFrequency *
            timeInSeconds time)

/-- Positivity conditions for the nondegenerate physical circuit data. -/
structure HasPhysicalSeriesRCParameters
    (setup : SeriesRCCircuitSetup) : Prop where
  resistancePositive : 0 < resistanceInOhms setup.resistorResistance
  capacitancePositive : 0 < capacitanceInFarads setup.capacitorCapacitance
  angularFrequencyPositive :
    0 < angularFrequencyInRadiansPerSecond setup.angularFrequency
  voltageAmplitudePositive :
    0 < electricPotentialInVolts setup.resistorVoltageAmplitude

/-!
For an ideal capacitor driven sinusoidally at angular frequency `ω`, the
capacitive-reactance magnitude is `1 / (ω C)`.  This is the governing physical
law, relating three independent observables; it does not assert the target
numeric value.
-/
structure SatisfiesIdealCapacitiveReactanceLaw
    (setup : SeriesRCCircuitSetup) : Prop where
  reactanceLaw :
    resistanceInOhms setup.capacitiveReactance =
      1 /
        (angularFrequencyInRadiansPerSecond setup.angularFrequency *
          capacitanceInFarads setup.capacitorCapacitance)

/-!
The capacitor's reactance is `80 Ω`, corresponding to answer choice B.

Blueprint label: `thm:physics:phyx_mini_0942:target`.
-/
theorem capacitive_reactance_eq_eighty_ohms
    (setup : SeriesRCCircuitSetup)
    (_scenario : MatchesSeriesRCScenario setup)
    (_figure : MatchesPrimarySeriesRCFigure setup)
    (_physical : HasPhysicalSeriesRCParameters setup)
    (_law : SatisfiesIdealCapacitiveReactanceLaw setup) :
    resistanceInOhms setup.capacitiveReactance = 80 := by
  have h_capacitance :
      capacitanceInFarads setup.capacitorCapacitance = 5 / 10 ^ 6 := by
    calc
      capacitanceInFarads setup.capacitorCapacitance =
          setup.figure.capacitanceLabelMicrofarads / 10 ^ 6 :=
        _figure.capacitanceCalibration
      _ = 5 / 10 ^ 6 := by rw [_figure.capacitanceLabel]
  have h_angularFrequency :
      angularFrequencyInRadiansPerSecond setup.angularFrequency = 2500 := by
    calc
      angularFrequencyInRadiansPerSecond setup.angularFrequency =
          setup.figure.angularFrequencyLabelRadiansPerSecond :=
        _figure.angularFrequencyCalibration
      _ = 2500 := _figure.angularFrequencyLabel
  rw [_law.reactanceLaw, h_angularFrequency, h_capacitance]
  norm_num

end PhyXMiniProblems.ProblemPhyXMini0942
