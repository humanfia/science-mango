import Mathlib
import Physlib.Thermodynamics.Temperature.Basic
import Physlib.Thermodynamics.Temperature.TemperatureUnits
import Physlib.Units.WithDim.Pressure

/- USER: The assigned source file did not exist when this autoformalization task began. -/

noncomputable section

namespace PhyXMiniProblems.ProblemPhyXMini0373

open Dimension

/-!
# Final temperature of oxygen in a two-state ideal-gas process

A `4.0 g` sample of oxygen starts at `20 °C` and follows the straight process
`1 → 2` in the supplied pressure-volume diagram.  The primary image labels
state `1` by the first pressure and volume ticks `p₁` and `V₁`.  State `2`
lies at the third pressure and volume ticks, so the intended readouts are
`p₂ = 3 p₁` and `V₂ = 3 V₁`.  The slight leftward displacement of the
second raster point from the third volume tick is treated as drawing
imprecision; these ratios are also the ones compatible with the recorded
answer.

Pressure, volume, mass, and the molar gas constant retain physical dimensions
through Physlib.  Amount of substance is an explicitly named real readout in
moles because Physlib's current `Dimension` has no amount-of-substance base
component.  Temperatures use Physlib's nonnegative absolute `Temperature`.
-/

/-! ## Dimensionful physical quantities and calibrated readouts -/

/-- A physical gas volume, carrying the dimension `L³`. -/
abbrev VolumeQuantity : Type :=
  Dimensionful (WithDim (L𝓭 * L𝓭 * L𝓭) ℝ)

/-- A physical sample mass. -/
abbrev MassQuantity : Type :=
  Dimensionful (WithDim M𝓭 ℝ)

/-!
The molar gas constant has energy-per-temperature dimension.  Its inverse-mole
role is represented by the name of its scalar readout and by the explicit
amount-of-substance factor in the ideal-gas law below.
-/
abbrev MolarGasConstantQuantity : Type :=
  Dimensionful
    (WithDim (M𝓭 * L𝓭 * L𝓭 * T𝓭⁻¹ * T𝓭⁻¹ * Θ𝓭⁻¹) ℝ)

/-- SI pressure readout in pascals. -/
def pressureInPascals (pressure : DimPressure) : ℝ :=
  (pressure UnitChoices.SI).val

/-- SI volume readout in cubic metres. -/
def volumeInCubicMeters (volume : VolumeQuantity) : ℝ :=
  (volume UnitChoices.SI).val

/-- Mass readout in grams. -/
def massInGrams (mass : MassQuantity) : ℝ :=
  1000 * (mass UnitChoices.SI).val

/-- Absolute-temperature readout in kelvins. -/
def temperatureInKelvins (temperature : Temperature) : ℝ :=
  temperature.toReal

/-!
Celsius readout using the textbook offset `273 K` employed by the answer
choices.  With the more precise offset `273.15 K`, the displayed integer
answer would instead differ by `1.2 °C`.
-/
def temperatureInCelsius (temperature : Temperature) : ℝ :=
  temperatureInKelvins temperature - 273

/-- SI readout of the molar gas constant in joules per mole-kelvin. -/
def molarGasConstantInJoulesPerMoleKelvin
    (gasConstant : MolarGasConstantQuantity) : ℝ :=
  (gasConstant UnitChoices.SI).val

/-! ## Gas, state, process, and figure vocabulary -/

/-- The chemical species named in the problem. -/
inductive GasSpecies where
  | molecularOxygen
  deriving DecidableEq, Repr

/-- The equation-of-state model used to interpret the process. -/
inductive GasModel where
  | idealGas
  deriving DecidableEq, Repr

/-- The two numbered equilibrium states in the figure. -/
inductive StateLabel where
  | one
  | two
  deriving DecidableEq, Repr

/-- Physical quantity printed on a diagram axis. -/
inductive AxisQuantity where
  | volumeV
  | pressureP
  deriving DecidableEq, Repr

/-- Geometry of the directed path drawn between the two states. -/
inductive PathGeometry where
  | straightSegment
  deriving DecidableEq, Repr

/-- A dimensionful equilibrium state of the gas. -/
structure ThermodynamicState where
  pressure : DimPressure
  volume : VolumeQuantity
  temperature : Temperature

/-!
The fixed oxygen sample, its two states, and the labels transcribed from the
pressure-volume figure.  Coordinate values are not built into this structure;
they occur only in the separate data predicates below.
-/
structure OxygenIdealGasProcess where
  gasSpecies : GasSpecies
  gasModel : GasModel
  sampleMass : MassQuantity
  oxygenMolarMassGramsPerMole : ℝ
  amountOfSubstanceMoles : ℝ
  molarGasConstant : MolarGasConstantQuantity
  absoluteTemperatureUnit : TemperatureUnit
  stateAt : StateLabel → ThermodynamicState
  referencePressureP1 : DimPressure
  referenceVolumeV1 : VolumeQuantity
  processStart : StateLabel
  processFinish : StateLabel
  pathGeometry : PathGeometry
  horizontalAxis : AxisQuantity
  verticalAxis : AxisQuantity
  originLabelVisible : Bool
  stateLabelVisible : StateLabel → Bool

/-! ## Stated data, primary-figure readouts, and governing laws -/

/-!
The data stated in the prose, together with the standard molar mass of
molecular oxygen and the kelvin calibration needed for the absolute
temperature readout.  No value of the final temperature occurs here.
-/
structure MatchesOxygenProblemData
    (setup : OxygenIdealGasProcess) : Prop where
  gas_is_molecular_oxygen : setup.gasSpecies = .molecularOxygen
  gas_is_ideal : setup.gasModel = .idealGas
  sample_mass_grams : massInGrams setup.sampleMass = 4
  oxygen_molar_mass_grams_per_mole :
    setup.oxygenMolarMassGramsPerMole = 32
  absolute_temperature_unit_is_kelvin :
    setup.absoluteTemperatureUnit = TemperatureUnit.kelvin
  initial_temperature_celsius :
    temperatureInCelsius (setup.stateAt .one).temperature = 20

/-!
Transcription of the primary `p`-`V` image.  The point labelled `1` is at
`(V₁,p₁)`, the arrow runs from `1` to `2`, and point `2` is on the third
pressure and volume ticks.  These are figure/data readouts, not the requested
temperature conclusion.
-/
structure MatchesPrimaryPVDiagram
    (setup : OxygenIdealGasProcess) : Prop where
  horizontal_axis_is_volume : setup.horizontalAxis = .volumeV
  vertical_axis_is_pressure : setup.verticalAxis = .pressureP
  origin_label_is_visible : setup.originLabelVisible = true
  state_one_label_is_visible : setup.stateLabelVisible .one = true
  state_two_label_is_visible : setup.stateLabelVisible .two = true
  process_starts_at_one : setup.processStart = .one
  process_finishes_at_two : setup.processFinish = .two
  path_is_straight : setup.pathGeometry = .straightSegment
  state_one_pressure_is_p1 :
    (setup.stateAt .one).pressure = setup.referencePressureP1
  state_one_volume_is_V1 :
    (setup.stateAt .one).volume = setup.referenceVolumeV1
  state_two_pressure_is_third_tick :
    pressureInPascals (setup.stateAt .two).pressure =
      3 * pressureInPascals setup.referencePressureP1
  state_two_volume_is_third_tick :
    volumeInCubicMeters (setup.stateAt .two).volume =
      3 * volumeInCubicMeters setup.referenceVolumeV1

/-- Positivity conditions selecting physically meaningful gas parameters and
equilibrium states. -/
structure HasPhysicalOxygenGasParameters
    (setup : OxygenIdealGasProcess) : Prop where
  sample_mass_positive : 0 < massInGrams setup.sampleMass
  molar_mass_positive : 0 < setup.oxygenMolarMassGramsPerMole
  amount_of_substance_positive : 0 < setup.amountOfSubstanceMoles
  molar_gas_constant_positive :
    0 < molarGasConstantInJoulesPerMoleKelvin setup.molarGasConstant
  pressure_positive :
    ∀ state, 0 < pressureInPascals (setup.stateAt state).pressure
  volume_positive :
    ∀ state, 0 < volumeInCubicMeters (setup.stateAt state).volume
  absolute_temperature_positive :
    ∀ state, 0 < temperatureInKelvins (setup.stateAt state).temperature

/-!
The governing relations for this fixed ideal-gas sample:

* sample mass equals amount of substance times oxygen's molar mass;
* every labelled equilibrium state satisfies `pV = nRT` in coherent SI
  readouts.

Neither law supplies a final temperature or a pressure-volume ratio specific
to the current question.
-/
structure SatisfiesMolarIdealGasLaws
    (setup : OxygenIdealGasProcess) : Prop where
  amount_of_substance_from_mass :
    massInGrams setup.sampleMass =
      setup.amountOfSubstanceMoles * setup.oxygenMolarMassGramsPerMole
  ideal_gas_state_equation : ∀ state,
    pressureInPascals (setup.stateAt state).pressure *
        volumeInCubicMeters (setup.stateAt state).volume =
      setup.amountOfSubstanceMoles *
        molarGasConstantInJoulesPerMoleKelvin setup.molarGasConstant *
        temperatureInKelvins (setup.stateAt state).temperature

/-! ## Displayed answer choices and requested conclusion -/

/-- Labels of the four displayed multiple-choice answers. -/
inductive AnswerChoice where
  | A
  | B
  | C
  | D
  deriving DecidableEq, Repr

/-- Celsius value printed beside each answer label. -/
def answerTemperatureCelsius : AnswerChoice → ℝ
  | .A => 2364
  | .B => 556
  | .C => 636
  | .D => 784

/-- The answer label recorded by the dataset. -/
def recordedAnswerChoice : AnswerChoice := .A

/-!
The final state has temperature `2364 °C`, the value displayed as answer A.

Blueprint label: `thm:physics:phyx_mini_0373:target`.
-/
theorem temperature_at_state_two_eq_2364_celsius
    (setup : OxygenIdealGasProcess)
    (_data : MatchesOxygenProblemData setup)
    (_figure : MatchesPrimaryPVDiagram setup)
    (_physical : HasPhysicalOxygenGasParameters setup)
    (_laws : SatisfiesMolarIdealGasLaws setup) :
    temperatureInCelsius (setup.stateAt .two).temperature = 2364 := by
  have hT1 :
      temperatureInKelvins (setup.stateAt .one).temperature = 293 := by
    have h := _data.initial_temperature_celsius
    simp only [temperatureInCelsius] at h
    linarith
  have hstate1 := _laws.ideal_gas_state_equation .one
  rw [_figure.state_one_pressure_is_p1, _figure.state_one_volume_is_V1] at hstate1
  have hstate2 := _laws.ideal_gas_state_equation .two
  rw [_figure.state_two_pressure_is_third_tick,
    _figure.state_two_volume_is_third_tick] at hstate2
  have hnR :
      0 < setup.amountOfSubstanceMoles *
        molarGasConstantInJoulesPerMoleKelvin setup.molarGasConstant :=
    mul_pos _physical.amount_of_substance_positive
      _physical.molar_gas_constant_positive
  simp only [temperatureInCelsius]
  nlinarith

end PhyXMiniProblems.ProblemPhyXMini0373
