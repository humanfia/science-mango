import Mathlib
import Physlib.Units.WithDim.Basic

noncomputable section

namespace PhyXMiniProblems.ProblemPhyXMini0888

open Dimension
open Filter

/-!
# Low-frequency resistor voltage in a series RL circuit

The supplied figure shows one closed series loop containing a sinusoidal
voltage source, a resistor labelled `R`, and an inductor labelled `L`.  The
source is labelled `ℰ₀ cos(ω t)`.  Thus `ℰ₀` is a voltage amplitude, `ω` is an
angular frequency, and `t` is time.  The requested observable is the amplitude
`V_R` of the voltage across the resistor as the nonnegative frequency tends to
zero.

All physical quantities are represented by Physlib's unit-independent
`Dimensionful` type.  Real numbers and `NNReal` occur only as coherent-SI
readouts and as the scalar parameter used to express the frequency limit.

Assumption/target split:

* governing laws: the cosine source waveform, the magnitude of the series-RL
  impedance, the source-amplitude/current relation, and Ohm's amplitude law
  across `R`;
* previous-part results: none;
* figure/data readouts: one series loop, the three component identities, the
  labels `ℰ₀`, `ω`, `t`, `R`, and `L`, the cosine waveform symbol, and a
  coherent-SI calibration of nonnegative angular frequency;
* current target: the resistor-voltage amplitude tends to `ℰ₀` as `ω → 0`.

The resistor-voltage response is an independent field of the setup.  No
premise states its low-frequency limit.
-/

/-! ## Dimensionful electrical quantities and coherent-SI readouts -/

/-- Electric current has physical dimension charge per time. -/
def electricCurrentDimension : Dimension := C𝓭 * T𝓭⁻¹

/-- Electric potential has physical dimension energy per charge. -/
def electricPotentialDimension : Dimension :=
  M𝓭 * L𝓭 * L𝓭 * T𝓭⁻¹ * T𝓭⁻¹ * C𝓭⁻¹

/-- Electrical resistance, and hence impedance magnitude, is voltage per current. -/
def electricalResistanceDimension : Dimension :=
  electricPotentialDimension * electricCurrentDimension⁻¹

/-- Inductance is voltage times time per current, as in `V_L = L dI/dt`. -/
def inductanceDimension : Dimension :=
  electricPotentialDimension * T𝓭 * electricCurrentDimension⁻¹

/-- Angular frequency has inverse-time dimension; radians are dimensionless. -/
def angularFrequencyDimension : Dimension := T𝓭⁻¹

/-- A signed, unit-independent physical time. -/
abbrev TimeQuantity : Type := Dimensionful (WithDim T𝓭 ℝ)

/-- A nonnegative, unit-independent angular frequency. -/
abbrev AngularFrequencyQuantity : Type :=
  Dimensionful (WithDim angularFrequencyDimension NNReal)

/-- A nonnegative, unit-independent electric-current amplitude. -/
abbrev ElectricCurrentAmplitudeQuantity : Type :=
  Dimensionful (WithDim electricCurrentDimension NNReal)

/-- A signed, unit-independent instantaneous electric potential. -/
abbrev ElectricPotentialQuantity : Type :=
  Dimensionful (WithDim electricPotentialDimension ℝ)

/-- A nonnegative, unit-independent electric-potential amplitude. -/
abbrev ElectricPotentialAmplitudeQuantity : Type :=
  Dimensionful (WithDim electricPotentialDimension NNReal)

/-- A nonnegative, unit-independent electrical resistance. -/
abbrev ElectricalResistanceQuantity : Type :=
  Dimensionful (WithDim electricalResistanceDimension NNReal)

/-- A nonnegative, unit-independent inductance. -/
abbrev InductanceQuantity : Type :=
  Dimensionful (WithDim inductanceDimension NNReal)

/-- A nonnegative, unit-independent impedance magnitude. -/
abbrev ElectricalImpedanceMagnitudeQuantity : Type :=
  Dimensionful (WithDim electricalResistanceDimension NNReal)

/-- Coherent-SI readout of a signed dimensionful quantity. -/
def signedSIReadout {d : Dimension}
    (quantity : Dimensionful (WithDim d ℝ)) : ℝ :=
  (quantity UnitChoices.SI).val

/-- Coherent-SI readout of a nonnegative dimensionful quantity. -/
def nonnegativeSIReadout {d : Dimension}
    (quantity : Dimensionful (WithDim d NNReal)) : ℝ :=
  ((quantity UnitChoices.SI).val : ℝ)

/-- Read time in seconds. -/
def timeInSeconds (time : TimeQuantity) : ℝ := signedSIReadout time

/-- Read angular frequency in radians per second. -/
def angularFrequencyInRadiansPerSecond
    (frequency : AngularFrequencyQuantity) : ℝ :=
  nonnegativeSIReadout frequency

/-- Read an electric-current amplitude in amperes. -/
def currentAmplitudeInAmperes
    (current : ElectricCurrentAmplitudeQuantity) : ℝ :=
  nonnegativeSIReadout current

/-- Read a signed instantaneous electric potential in volts. -/
def potentialInVolts (potential : ElectricPotentialQuantity) : ℝ :=
  signedSIReadout potential

/-- Read an electric-potential amplitude in volts. -/
def potentialAmplitudeInVolts
    (amplitude : ElectricPotentialAmplitudeQuantity) : ℝ :=
  nonnegativeSIReadout amplitude

/-- Read an electrical resistance in ohms. -/
def resistanceInOhms (resistance : ElectricalResistanceQuantity) : ℝ :=
  nonnegativeSIReadout resistance

/-- Read an inductance in henries. -/
def inductanceInHenries (inductance : InductanceQuantity) : ℝ :=
  nonnegativeSIReadout inductance

/-- Read an impedance magnitude in ohms. -/
def impedanceMagnitudeInOhms
    (impedance : ElectricalImpedanceMagnitudeQuantity) : ℝ :=
  nonnegativeSIReadout impedance

/-! ## Physical components and primary-figure labels -/

/-- The waveform name printed beside the source symbol. -/
inductive SourceWaveformShape where
  | cosine
  | other
  deriving DecidableEq, Repr

/-- Typed presentation data for the source label `ℰ₀ cos(ω t)`. -/
structure SourceFormulaLabel where
  amplitudeSymbol : String
  waveformShape : SourceWaveformShape
  angularFrequencySymbol : String
  timeSymbol : String

/-- The sinusoidal source and its independent voltage waveform. -/
structure SinusoidalVoltageSource where
  amplitude : ElectricPotentialAmplitudeQuantity
  instantaneousPotentialAt :
    AngularFrequencyQuantity → TimeQuantity → ElectricPotentialQuantity

/-- The resistor marked `R`, including its independent voltage response. -/
structure Resistor where
  printedLabel : String
  resistance : ElectricalResistanceQuantity
  voltageAmplitudeAt :
    AngularFrequencyQuantity → ElectricPotentialAmplitudeQuantity

/-- The inductor marked `L`. -/
structure Inductor where
  printedLabel : String
  inductance : InductanceQuantity

/-- The three component identities encountered in one traversal of the loop. -/
inductive CircuitComponent where
  | voltageSource
  | resistorR
  | inductorL
  deriving DecidableEq, Fintype, Repr

/-- Literal topology and annotations transcribed from image `888.png`. -/
structure SeriesRLCircuitFigure where
  componentAt : Fin 3 → CircuitComponent
  formsSingleClosedLoop : Bool
  componentsConnectedInSeries : Bool
  sourceSymbolShowsSineWave : Bool
  sourceLabel : SourceFormulaLabel
  resistorLabel : String
  inductorLabel : String

/-!
The complete physical setup.  The frequency-indexed current, impedance, and
resistor voltage are observables, not definitions made from the answer.
`physicalFrequencyAt` associates the nonnegative scalar used in the limit with
a genuine dimensionful angular frequency.
-/
structure SeriesRLCircuitSetup where
  source : SinusoidalVoltageSource
  resistor : Resistor
  inductor : Inductor
  currentAmplitudeAt :
    AngularFrequencyQuantity → ElectricCurrentAmplitudeQuantity
  impedanceMagnitudeAt :
    AngularFrequencyQuantity → ElectricalImpedanceMagnitudeQuantity
  physicalFrequencyAt : NNReal → AngularFrequencyQuantity
  figure : SeriesRLCircuitFigure

/-! ## Figure evidence, calibration, and governing laws -/

/-- The topology and printed annotations visible in the supplied bitmap. -/
structure MatchesSuppliedSeriesRLCircuitFigure
    (setup : SeriesRLCircuitSetup) : Prop where
  firstComponent : setup.figure.componentAt 0 = .voltageSource
  secondComponent : setup.figure.componentAt 1 = .resistorR
  thirdComponent : setup.figure.componentAt 2 = .inductorL
  oneClosedLoop : setup.figure.formsSingleClosedLoop = true
  seriesConnection : setup.figure.componentsConnectedInSeries = true
  sourceHasACSymbol : setup.figure.sourceSymbolShowsSineWave = true
  sourceAmplitudeLabel : setup.figure.sourceLabel.amplitudeSymbol = "ℰ₀"
  sourceWaveformLabel : setup.figure.sourceLabel.waveformShape = .cosine
  sourceAngularFrequencyLabel :
    setup.figure.sourceLabel.angularFrequencySymbol = "ω"
  sourceTimeLabel : setup.figure.sourceLabel.timeSymbol = "t"
  figureResistorLabel : setup.figure.resistorLabel = "R"
  figureInductorLabel : setup.figure.inductorLabel = "L"
  componentResistorLabelAgrees :
    setup.resistor.printedLabel = setup.figure.resistorLabel
  componentInductorLabelAgrees :
    setup.inductor.printedLabel = setup.figure.inductorLabel

/-- The scalar limit parameter is the coherent-SI readout of physical `ω`. -/
structure CalibratesAngularFrequencyParameter
    (setup : SeriesRLCircuitSetup) : Prop where
  frequencyReadout : ∀ ω : NNReal,
    angularFrequencyInRadiansPerSecond (setup.physicalFrequencyAt ω) = (ω : ℝ)

/-- Positivity and nonnegativity conditions for a physical passive RL circuit. -/
structure HasPhysicalSeriesRLParameters
    (setup : SeriesRLCircuitSetup) : Prop where
  positiveResistance : 0 < resistanceInOhms setup.resistor.resistance
  nonnegativeInductance : 0 ≤ inductanceInHenries setup.inductor.inductance
  nonnegativeSourceAmplitude :
    0 ≤ potentialAmplitudeInVolts setup.source.amplitude

/-!
The source formula shown in the figure: its instantaneous potential is
`ℰ₀ cos(ω t)` for every physical frequency and time.  This general waveform
law does not constrain the requested resistor voltage.
-/
structure SatisfiesCosineSourceLaw (setup : SeriesRLCircuitSetup) : Prop where
  sourceWaveform : ∀ frequency time,
    potentialInVolts (setup.source.instantaneousPotentialAt frequency time) =
      potentialAmplitudeInVolts setup.source.amplitude *
        Real.cos
          (angularFrequencyInRadiansPerSecond frequency * timeInSeconds time)

/-!
Standard steady-state amplitude laws for a series RL circuit.  The impedance
magnitude is `sqrt (R² + (ωL)²)`, the source amplitude is `I₀ |Z|`, and the
resistor amplitude is `I₀ R`.  These are governing relations at every physical
frequency, not the low-frequency limit asked for in the problem.
-/
structure SatisfiesSeriesRLCircuitLaws
    (setup : SeriesRLCircuitSetup) : Prop where
  impedanceMagnitudeLaw : ∀ frequency,
    impedanceMagnitudeInOhms (setup.impedanceMagnitudeAt frequency) =
      Real.sqrt
        (resistanceInOhms setup.resistor.resistance ^ 2 +
          (angularFrequencyInRadiansPerSecond frequency *
            inductanceInHenries setup.inductor.inductance) ^ 2)
  sourceAmplitudeLaw : ∀ frequency,
    potentialAmplitudeInVolts setup.source.amplitude =
      currentAmplitudeInAmperes (setup.currentAmplitudeAt frequency) *
        impedanceMagnitudeInOhms (setup.impedanceMagnitudeAt frequency)
  resistorOhmAmplitudeLaw : ∀ frequency,
    potentialAmplitudeInVolts
        (setup.resistor.voltageAmplitudeAt frequency) =
      currentAmplitudeInAmperes (setup.currentAmplitudeAt frequency) *
        resistanceInOhms setup.resistor.resistance

/-! ## Displayed answer choices and low-frequency target -/

/-- Labels of the four displayed answer choices. -/
inductive AnswerChoice where
  | A
  | B
  | C
  | D
  deriving DecidableEq, Fintype, Repr

/-!
Scalar voltage-limit expressions printed beside the choices.  The unitless
numbers in A and D are retained exactly as printed and interpreted as volt
readouts; choice C repeats the source-amplitude symbol `ℰ₀`.
-/
def AnswerChoice.displayedLimitInVolts
    (sourceAmplitudeInVolts : ℝ) : AnswerChoice → ℝ
  | .A => 2
  | .B => 0
  | .C => sourceAmplitudeInVolts
  | .D => 3

/-- The answer label recorded in the supplied dataset metadata. -/
def recordedDatasetAnswer : AnswerChoice := .C

/-!
At a calibrated angular-frequency readout `ω`, the governing amplitude laws
give the usual closed form for `V_R`.  This is an intermediate general-frequency
relation, not the requested low-frequency answer.
-/
lemma resistorVoltageAmplitude_eq_seriesRLFormula
    (setup : SeriesRLCircuitSetup)
    (_calibration : CalibratesAngularFrequencyParameter setup)
    (_physical : HasPhysicalSeriesRLParameters setup)
    (_laws : SatisfiesSeriesRLCircuitLaws setup)
    (ω : NNReal) :
    potentialAmplitudeInVolts
        (setup.resistor.voltageAmplitudeAt (setup.physicalFrequencyAt ω)) =
      potentialAmplitudeInVolts setup.source.amplitude *
        resistanceInOhms setup.resistor.resistance /
          Real.sqrt
            (resistanceInOhms setup.resistor.resistance ^ 2 +
              ((ω : ℝ) * inductanceInHenries setup.inductor.inductance) ^ 2) := by
  have h_impedance :=
    _laws.impedanceMagnitudeLaw (setup.physicalFrequencyAt ω)
  rw [_calibration.frequencyReadout ω] at h_impedance
  have h_source :=
    _laws.sourceAmplitudeLaw (setup.physicalFrequencyAt ω)
  rw [h_impedance] at h_source
  rw [_laws.resistorOhmAmplitudeLaw]
  have h_radicand_pos :
      0 <
        resistanceInOhms setup.resistor.resistance ^ 2 +
          ((ω : ℝ) * inductanceInHenries setup.inductor.inductance) ^ 2 := by
    nlinarith [_physical.positiveResistance, sq_nonneg
      ((ω : ℝ) * inductanceInHenries setup.inductor.inductance)]
  have h_sqrt_ne :
      Real.sqrt
          (resistanceInOhms setup.resistor.resistance ^ 2 +
            ((ω : ℝ) * inductanceInHenries setup.inductor.inductance) ^ 2) ≠ 0 :=
    ne_of_gt (Real.sqrt_pos.2 h_radicand_pos)
  apply (eq_div_iff h_sqrt_ne).2
  rw [h_source]
  ring

/-!
Blueprint label: `thm:physics:phyx_mini_0888:target`.

For the depicted passive series RL circuit, the resistor-voltage amplitude
tends to the source amplitude `ℰ₀` when the nonnegative angular frequency tends
to zero.  This is displayed answer C.
-/
theorem problem_phyx_mini_0888
    (setup : SeriesRLCircuitSetup)
    (_figure : MatchesSuppliedSeriesRLCircuitFigure setup)
    (_calibration : CalibratesAngularFrequencyParameter setup)
    (_physical : HasPhysicalSeriesRLParameters setup)
    (_sourceLaw : SatisfiesCosineSourceLaw setup)
    (_circuitLaws : SatisfiesSeriesRLCircuitLaws setup) :
    Tendsto
      (fun ω : NNReal =>
        potentialAmplitudeInVolts
          (setup.resistor.voltageAmplitudeAt (setup.physicalFrequencyAt ω)))
      (nhds 0)
      (nhds (potentialAmplitudeInVolts setup.source.amplitude)) := by
  simp_rw [resistorVoltageAmplitude_eq_seriesRLFormula
    setup _calibration _physical _circuitLaws]
  have h_coe : ContinuousAt (fun ω : NNReal => (ω : ℝ)) 0 :=
    NNReal.continuous_coe.continuousAt
  have h_denominator :
      ContinuousAt
        (fun ω : NNReal =>
          Real.sqrt
            (resistanceInOhms setup.resistor.resistance ^ 2 +
              ((ω : ℝ) *
                inductanceInHenries setup.inductor.inductance) ^ 2))
        0 :=
    (continuousAt_const.add
      ((h_coe.mul continuousAt_const).pow 2)).sqrt
  have h_denominator_ne :
      Real.sqrt
          (resistanceInOhms setup.resistor.resistance ^ 2 +
            (((0 : NNReal) : ℝ) *
              inductanceInHenries setup.inductor.inductance) ^ 2) ≠ 0 := by
    simp [Real.sqrt_sq_eq_abs,
      abs_of_pos _physical.positiveResistance,
      ne_of_gt _physical.positiveResistance]
  have h_continuous :
      ContinuousAt
        (fun ω : NNReal =>
          potentialAmplitudeInVolts setup.source.amplitude *
              resistanceInOhms setup.resistor.resistance /
            Real.sqrt
              (resistanceInOhms setup.resistor.resistance ^ 2 +
                ((ω : ℝ) *
                  inductanceInHenries setup.inductor.inductance) ^ 2))
        0 :=
    (continuousAt_const.mul continuousAt_const).div
      h_denominator h_denominator_ne
  convert h_continuous.tendsto using 1
  all_goals
    simp [Real.sqrt_sq_eq_abs,
      abs_of_pos _physical.positiveResistance,
      ne_of_gt _physical.positiveResistance]

end PhyXMiniProblems.ProblemPhyXMini0888
