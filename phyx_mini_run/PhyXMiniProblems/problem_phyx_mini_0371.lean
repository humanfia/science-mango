import Mathlib
import Physlib.Thermodynamics.Temperature.Basic
import Physlib.Thermodynamics.Temperature.TemperatureUnits
import Physlib.Units.WithDim.Pressure

/- USER: The assigned source file did not exist when this autoformalization task began. -/

/-!
# Initial temperature of helium in an isobaric expansion

This file models problem `phyx_mini_0371`.  A `0.10 g` helium sample moves
from state `1` to state `2` along the horizontal segment in the supplied
pressure--volume diagram.  The primary bitmap places the states at
`(1000 cm³, 1 atm)` and `(3000 cm³, 1 atm)`, respectively.

The stated mass, helium molar mass, state-`1` coordinates, and molar ideal-gas
law imply `T₁ = 40000000 / 82057 K`, or approximately `214.316 °C`.  This is
inconsistent with the recorded answer `-152 °C` and all four displayed answer
choices.  The physical conclusion below therefore states the value implied by
the source data and records the answer-table mismatch explicitly.

Mass, pressure, volume, and absolute temperature remain physical quantities.
Real numbers occur only as explicitly unit-labelled readouts, including moles,
the molar mass, the molar gas constant, and the displayed Celsius answers.
-/

noncomputable section

namespace PhyXMiniProblems.ProblemPhyXMini0371

open Dimension

/-! ## Dimensionful quantities and named-unit readouts -/

/-- A nonnegative physical mass, independent of the chosen unit. -/
abbrev MassQuantity : Type := Dimensionful (WithDim M𝓭 NNReal)

/-- A nonnegative physical volume carrying dimension `length ^ 3`. -/
abbrev VolumeQuantity : Type :=
  Dimensionful (WithDim (L𝓭 * L𝓭 * L𝓭) NNReal)

/-- A physical pressure, represented by Physlib's dimensionful pressure. -/
abbrev PressureQuantity : Type := DimPressure

/-- Read a physical mass in grams using Physlib's gram unit. -/
def massInGrams (mass : MassQuantity) : ℝ :=
  ((mass {UnitChoices.SI with mass := MassUnit.grams}).val : ℝ)

/-- Read a physical pressure in coherent SI pascals. -/
def pressureInPascals (pressure : PressureQuantity) : ℝ :=
  (pressure UnitChoices.SI).val

/-- Read a physical pressure in standard atmospheres. -/
def pressureInAtmospheres (pressure : PressureQuantity) : ℝ :=
  pressureInPascals pressure /
    pressureInPascals DimPressure.standardAtmosphere

/-- Read a physical volume in cubic centimetres. -/
def volumeInCubicCentimeters (volume : VolumeQuantity) : ℝ :=
  ((volume {UnitChoices.SI with length := LengthUnit.centimeters}).val : ℝ)

/-- Read a physical volume in litres. -/
def volumeInLiters (volume : VolumeQuantity) : ℝ :=
  volumeInCubicCentimeters volume / 1000

/--
Kelvin readout of a Physlib absolute temperature stored in an explicitly
chosen zero-preserving temperature unit.
-/
def temperatureInKelvin
    (storageUnit : TemperatureUnit) (temperature : Temperature) : ℝ :=
  let unitRatio : NNReal := storageUnit / TemperatureUnit.kelvin
  temperature.toReal * (unitRatio : ℝ)

/-- Celsius readout obtained from the absolute kelvin readout. -/
def temperatureInDegreesCelsius
    (storageUnit : TemperatureUnit) (temperature : Temperature) : ℝ :=
  temperatureInKelvin storageUnit temperature - 27315 / 100

/-! ## Gas identity, thermodynamic states, and diagram vocabulary -/

/-- Chemical species named in the problem statement. -/
inductive GasSpecies where
  | helium
  | other
  deriving DecidableEq, Repr

/-- Equation-of-state model used for the sample. -/
inductive GasModel where
  | ideal
  | other
  deriving DecidableEq, Repr

/-- The two numbered points in the supplied pressure--volume diagram. -/
inductive DiagramState where
  | one
  | two
  deriving DecidableEq, Fintype, Repr

/-- The directed process segment drawn in the figure. -/
inductive DiagramSegment where
  | oneToTwo
  deriving DecidableEq, Fintype, Repr

/-- Initial endpoint of the arrowed process segment. -/
def DiagramSegment.startState : DiagramSegment → DiagramState
  | .oneToTwo => .one

/-- Final endpoint of the arrowed process segment. -/
def DiagramSegment.endState : DiagramSegment → DiagramState
  | .oneToTwo => .two

/-- Thermodynamic constraint conveyed by the segment geometry. -/
inductive ProcessConstraint where
  | constantPressure
  deriving DecidableEq, Repr

/-- Text and numerical roles printed in the primary bitmap. -/
inductive DiagramLabel where
  | pressureAxisAtmospheres
  | volumeAxisCubicCentimeters
  | stateOne
  | stateTwo
  deriving DecidableEq, Fintype, Repr

/-- Pressure, volume, and absolute temperature at one physical state. -/
structure ThermodynamicState where
  pressure : PressureQuantity
  volume : VolumeQuantity
  temperature : Temperature

/--
Qualitative marks and calibrated axis information visible in the primary
pressure--volume bitmap.
-/
structure PressureVolumeFigure where
  showsStatePoint : DiagramState → Bool
  showsDirectedArrow : DiagramSegment → Bool
  drawsSegmentHorizontal : DiagramSegment → Bool
  segmentConstraint : DiagramSegment → ProcessConstraint
  showsLabel : DiagramLabel → Bool
  pressureAxisMinimumAtmospheres : ℝ
  pressureAxisMaximumAtmospheres : ℝ
  pressureAxisTickSpacingAtmospheres : ℝ
  volumeAxisMinimumCubicCentimeters : ℝ
  volumeAxisMaximumCubicCentimeters : ℝ
  volumeAxisTickSpacingCubicCentimeters : ℝ

/-!
The physical helium sample and its two thermodynamic states.  The amount of
substance is kept abstract; only its explicitly named mole readout is scalar.
Physlib currently has no amount-of-substance component in `Dimension`.
-/
structure HeliumExpansionSetup (AmountOfSubstance : Type) where
  species : GasSpecies
  gasModel : GasModel
  sampleMass : MassQuantity
  amountOfGas : AmountOfSubstance
  amountInMoles : AmountOfSubstance → ℝ
  heliumMolarMassGramsPerMole : ℝ
  universalGasConstantLiterAtmospherePerMoleKelvin : ℝ
  temperatureStorageUnit : TemperatureUnit
  state : DiagramState → ThermodynamicState
  figure : PressureVolumeFigure

/-- Mole readout of the physical helium sample. -/
def moleAmountOfGas
    {AmountOfSubstance : Type}
    (setup : HeliumExpansionSetup AmountOfSubstance) : ℝ :=
  setup.amountInMoles setup.amountOfGas

/-- Kelvin readout at a numbered diagram state. -/
def gasTemperatureInKelvin
    {AmountOfSubstance : Type}
    (setup : HeliumExpansionSetup AmountOfSubstance)
    (state : DiagramState) : ℝ :=
  temperatureInKelvin setup.temperatureStorageUnit
    (setup.state state).temperature

/-- Celsius readout at a numbered diagram state. -/
def gasTemperatureInDegreesCelsius
    {AmountOfSubstance : Type}
    (setup : HeliumExpansionSetup AmountOfSubstance)
    (state : DiagramState) : ℝ :=
  temperatureInDegreesCelsius setup.temperatureStorageUnit
    (setup.state state).temperature

/-! ## Problem data, primary-image readouts, and governing laws -/

/--
Prose data and standard physical-constant readouts for the helium sample.
No temperature value or answer choice occurs in this structure.
-/
structure MatchesHeliumSampleData
    {AmountOfSubstance : Type}
    (setup : HeliumExpansionSetup AmountOfSubstance) : Prop where
  speciesIsHelium : setup.species = .helium
  gasUsesIdealModel : setup.gasModel = .ideal
  sampleMassIsPointOneGram : massInGrams setup.sampleMass = 1 / 10
  heliumMolarMassReadout : setup.heliumMolarMassGramsPerMole = 4
  gasConstantReadout :
    setup.universalGasConstantLiterAtmospherePerMoleKelvin =
      82057 / 1000000

/--
Numerical coordinates, labels, and directed horizontal geometry read from the
primary bitmap.  In particular, state `2` is at the `3000 cm³` tick; the
auxiliary caption's `2000 cm³` estimate is not used.
-/
structure MatchesPrimaryPressureVolumeFigure
    {AmountOfSubstance : Type}
    (setup : HeliumExpansionSetup AmountOfSubstance) : Prop where
  everyStatePointShown : ∀ state, setup.figure.showsStatePoint state = true
  processArrowShown : setup.figure.showsDirectedArrow .oneToTwo = true
  processSegmentHorizontal :
    setup.figure.drawsSegmentHorizontal .oneToTwo = true
  processIsConstantPressure :
    setup.figure.segmentConstraint .oneToTwo = .constantPressure
  everyPrintedRoleShown : ∀ label, setup.figure.showsLabel label = true
  pressureAxisStartsAtZero :
    setup.figure.pressureAxisMinimumAtmospheres = 0
  pressureAxisEndsAtThree :
    setup.figure.pressureAxisMaximumAtmospheres = 3
  pressureAxisTicksEveryAtmosphere :
    setup.figure.pressureAxisTickSpacingAtmospheres = 1
  volumeAxisStartsAtZero :
    setup.figure.volumeAxisMinimumCubicCentimeters = 0
  volumeAxisEndsAtThreeThousand :
    setup.figure.volumeAxisMaximumCubicCentimeters = 3000
  volumeAxisTicksEveryThousand :
    setup.figure.volumeAxisTickSpacingCubicCentimeters = 1000
  stateOnePressureAtmospheres :
    pressureInAtmospheres (setup.state .one).pressure = 1
  stateTwoPressureAtmospheres :
    pressureInAtmospheres (setup.state .two).pressure = 1
  stateOneVolumeCubicCentimeters :
    volumeInCubicCentimeters (setup.state .one).volume = 1000
  stateTwoVolumeCubicCentimeters :
    volumeInCubicCentimeters (setup.state .two).volume = 3000
  volumeIncreasesFromOneToTwo :
    volumeInCubicCentimeters (setup.state .one).volume <
      volumeInCubicCentimeters (setup.state .two).volume

/-- Positivity conditions selecting physically meaningful gas states. -/
structure HasPhysicalIdealGasParameters
    {AmountOfSubstance : Type}
    (setup : HeliumExpansionSetup AmountOfSubstance) : Prop where
  sampleMassPositive : 0 < massInGrams setup.sampleMass
  amountPositive : 0 < moleAmountOfGas setup
  molarMassPositive : 0 < setup.heliumMolarMassGramsPerMole
  gasConstantPositive :
    0 < setup.universalGasConstantLiterAtmospherePerMoleKelvin
  pressurePositive : ∀ state,
    0 < pressureInAtmospheres (setup.state state).pressure
  volumePositive : ∀ state,
    0 < volumeInLiters (setup.state state).volume
  absoluteTemperaturePositive : ∀ state,
    0 < gasTemperatureInKelvin setup state

/--
The mass-to-moles relation and the molar ideal-gas equation `p V = n R T`.
These are general governing laws; neither field fixes the requested initial
temperature or mentions a displayed answer.
-/
structure SatisfiesHeliumIdealGasLaws
    {AmountOfSubstance : Type}
    (setup : HeliumExpansionSetup AmountOfSubstance) : Prop where
  amountFromMassAndMolarMass :
    moleAmountOfGas setup =
      massInGrams setup.sampleMass / setup.heliumMolarMassGramsPerMole
  idealGasEquationAt : ∀ state,
    pressureInAtmospheres (setup.state state).pressure *
        volumeInLiters (setup.state state).volume =
      moleAmountOfGas setup *
        setup.universalGasConstantLiterAtmospherePerMoleKelvin *
          gasTemperatureInKelvin setup state

/-! ## Displayed answers and formalization target -/

/-- Labels of the four multiple-choice answers in the source. -/
inductive AnswerChoice where
  | A
  | B
  | C
  | D
  deriving DecidableEq, Fintype, Repr

/-- Celsius value printed beside each answer label. -/
def displayedTemperatureCelsius : AnswerChoice → ℝ
  | .A => -152
  | .B => 556
  | .C => 636
  | .D => 784

/-- The answer label recorded in the supplied dataset metadata. -/
def recordedAnswerChoice : AnswerChoice := .A

/-- A computed Celsius temperature agrees with a displayed answer. -/
def IsDisplayedTemperatureAnswer
    (actualTemperatureCelsius : ℝ) (choice : AnswerChoice) : Prop :=
  actualTemperatureCelsius = displayedTemperatureCelsius choice

/-- A computed Celsius temperature rounds to a displayed whole-degree answer. -/
def RoundsToDisplayedWholeDegree
    (actualTemperatureCelsius : ℝ) (choice : AnswerChoice) : Prop :=
  |actualTemperatureCelsius - displayedTemperatureCelsius choice| < 1 / 2

/--
The stated `0.10 g` sample and `4 g/mol` helium calibration give exactly
`0.025 mol`.  This is an intermediate consequence, not an input datum.
-/
lemma mole_amount_from_stated_mass
    {AmountOfSubstance : Type}
    (setup : HeliumExpansionSetup AmountOfSubstance)
    (_sample : MatchesHeliumSampleData setup)
    (_laws : SatisfiesHeliumIdealGasLaws setup) :
    moleAmountOfGas setup = (1 / 40 : ℝ) := by
  rw [_laws.amountFromMassAndMolarMass,
    _sample.sampleMassIsPointOneGram,
    _sample.heliumMolarMassReadout]
  norm_num

/--
At state `1`, the primary image gives `p₁ = 1 atm` and `V₁ = 1 L`.
Combining those readouts with the mass-derived mole amount and the molar
ideal-gas law gives the exact absolute temperature below.
-/
lemma initial_temperature_in_kelvin_from_stated_data
    {AmountOfSubstance : Type}
    (setup : HeliumExpansionSetup AmountOfSubstance)
    (_sample : MatchesHeliumSampleData setup)
    (_figure : MatchesPrimaryPressureVolumeFigure setup)
    (_physical : HasPhysicalIdealGasParameters setup)
    (_laws : SatisfiesHeliumIdealGasLaws setup) :
    gasTemperatureInKelvin setup .one = (40000000 / 82057 : ℝ) := by
  have h := _laws.idealGasEquationAt .one
  rw [_figure.stateOnePressureAtmospheres] at h
  simp only [volumeInLiters] at h
  rw [_figure.stateOneVolumeCubicCentimeters,
    mole_amount_from_stated_mass setup _sample _laws,
    _sample.gasConstantReadout] at h
  norm_num at h ⊢
  linarith

/--
The source asks for `T₁`.  Its stated data imply
`T₁ = 40000000 / 82057 K ≈ 214.316 °C`, and no displayed whole-degree choice
is within half a degree of that value.

The premises contain only sample data, primary-image readouts, positivity,
and the governing mass/ideal-gas laws.  Neither the computed temperature nor
an answer-choice selection occurs in a premise.

Blueprint label: `thm:physics:phyx_mini_0371:target`.
-/
theorem problem_phyx_mini_0371
    {AmountOfSubstance : Type}
    (setup : HeliumExpansionSetup AmountOfSubstance)
    (_sample : MatchesHeliumSampleData setup)
    (_figure : MatchesPrimaryPressureVolumeFigure setup)
    (_physical : HasPhysicalIdealGasParameters setup)
    (_laws : SatisfiesHeliumIdealGasLaws setup) :
    gasTemperatureInKelvin setup .one = (40000000 / 82057 : ℝ) ∧
      gasTemperatureInDegreesCelsius setup .one =
        (40000000 / 82057 : ℝ) - 27315 / 100 ∧
      ∀ choice : AnswerChoice,
        ¬ RoundsToDisplayedWholeDegree
          (gasTemperatureInDegreesCelsius setup .one) choice := by
  have hKelvin :=
    initial_temperature_in_kelvin_from_stated_data
      setup _sample _figure _physical _laws
  constructor
  · exact hKelvin
  constructor
  · simpa only [gasTemperatureInDegreesCelsius,
      temperatureInDegreesCelsius, gasTemperatureInKelvin] using
      congrArg (fun temperature => temperature - 27315 / 100) hKelvin
  · intro choice
    have hCelsius :
        gasTemperatureInDegreesCelsius setup .one =
          (40000000 / 82057 : ℝ) - 27315 / 100 := by
      simpa only [gasTemperatureInDegreesCelsius,
        temperatureInDegreesCelsius, gasTemperatureInKelvin] using
        congrArg (fun temperature => temperature - 27315 / 100) hKelvin
    rw [hCelsius]
    cases choice <;>
      norm_num [RoundsToDisplayedWholeDegree, displayedTemperatureCelsius,
        abs_lt]

end PhyXMiniProblems.ProblemPhyXMini0371
