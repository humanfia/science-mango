import Mathlib
import Physlib.Thermodynamics.Temperature.Basic
import Physlib.Thermodynamics.Temperature.TemperatureUnits
import Physlib.Units.WithDim.Pressure

noncomputable section

namespace PhyXMiniProblems.ProblemPhyXMini0361

open Dimension

/-!
# Final temperature of an ideal gas heated at constant volume

The pressure--volume diagram shows `0.0040 mol` of gas moving from state 1 to
state 2 along a vertical path.  Both states have volume `200 cm³`; pressure
rises from `1 atm` to `3 atm`.  The requested final temperature is displayed
in degrees Celsius.

Pressure, volume, temperature, and amount of substance are retained as
physical quantities.  Real numbers occur only as named unit readouts,
figure coordinates, physical-constant calibrations, or displayed answers.
-/

/-! ## Physical quantities and unit readouts -/

/-- A nonnegative physical volume with dimension length cubed. -/
abbrev VolumeQuantity : Type :=
  Dimensionful (WithDim (L𝓭 * L𝓭 * L𝓭) NNReal)

/-!
Physlib does not currently supply an amount-of-substance base dimension.  This
interface keeps amount of substance abstract and exposes only its calibrated
mole readout.
-/
structure AmountOfSubstanceScale where
  Quantity : Type
  inMoles : Quantity → ℝ

/-- Read a physical volume in cubic metres. -/
def volumeInCubicMeters (volume : VolumeQuantity) : ℝ :=
  ((volume UnitChoices.SI).val : ℝ)

/-- Read a physical volume in cubic centimetres, the horizontal-axis unit. -/
def volumeInCubicCentimeters (volume : VolumeQuantity) : ℝ :=
  1000000 * volumeInCubicMeters volume

/-- Read a physical volume in litres, for the chosen gas-constant units. -/
def volumeInLiters (volume : VolumeQuantity) : ℝ :=
  1000 * volumeInCubicMeters volume

/-- Read a dimensionful pressure in pascals. -/
def pressureInPascals (pressure : DimPressure) : ℝ :=
  (pressure UnitChoices.SI).val

/-- Read pressure in standard atmospheres. -/
def pressureInAtmospheres (pressure : DimPressure) : ℝ :=
  pressureInPascals pressure /
    pressureInPascals DimPressure.standardAtmosphere

/-! ## States, process, and primary-image data -/

/-- The equilibrium states labelled `1` and `2` in the figure. -/
inductive ThermodynamicPoint where
  | state1
  | state2
  deriving DecidableEq, Fintype, Repr

/-- The equation-of-state model chosen for the gas. -/
inductive GasModel where
  | ideal
  | nonIdeal
  deriving DecidableEq, Repr

/-- The physical constraint on the directed process. -/
inductive ProcessKind where
  | constantVolume
  | other
  deriving DecidableEq, Repr

/-- Physical quantities represented by the two graph axes. -/
inductive DiagramAxisQuantity where
  | volume
  | pressure
  deriving DecidableEq, Repr

/-- Units printed beside the graph axes. -/
inductive DiagramAxisUnit where
  | cubicCentimeter
  | atmosphere
  deriving DecidableEq, Repr

/-- Qualitative shape of the directed path in the pressure--volume plane. -/
inductive DiagramPathShape where
  | vertical
  | other
  deriving DecidableEq, Repr

/-- A thermodynamic equilibrium state with physical observables. -/
structure ThermodynamicState where
  pressure : DimPressure
  volume : VolumeQuantity
  temperature : Temperature

/-!
Numerical and qualitative information visible in the primary raster.  The
coordinate functions are scalar readouts in the explicitly recorded axis
units; the corresponding physical states are stored separately in the setup.
-/
structure PressureVolumeDiagram where
  horizontalAxisQuantity : DiagramAxisQuantity
  horizontalAxisUnit : DiagramAxisUnit
  horizontalAxisMinimum : ℝ
  horizontalAxisMaximum : ℝ
  verticalAxisQuantity : DiagramAxisQuantity
  verticalAxisUnit : DiagramAxisUnit
  verticalAxisMinimum : ℝ
  verticalAxisMaximum : ℝ
  showsPointLabel : ThermodynamicPoint → Bool
  pointVolumeCubicCentimeters : ThermodynamicPoint → ℝ
  pointPressureAtmospheres : ThermodynamicPoint → ℝ
  showsDirectedArrow : Bool
  arrowStart : ThermodynamicPoint
  arrowEnd : ThermodynamicPoint
  arrowPointsUpward : Bool
  pathShape : DiagramPathShape

/-!
Independent physical data for the gas and process.  The molar gas constant is
a scalar readout in `L·atm·mol⁻¹·K⁻¹`; its governing role is imposed only by
`SatisfiesIdealGasLaw` below.
-/
structure IsochoricHeatingSetup (amountScale : AmountOfSubstanceScale) where
  gasModel : GasModel
  gasAmount : amountScale.Quantity
  stateAt : ThermodynamicPoint → ThermodynamicState
  processKind : ProcessKind
  temperatureStorageUnit : TemperatureUnit
  molarGasConstantInLiterAtmospheresPerMoleKelvin : ℝ
  figure : PressureVolumeDiagram

/-- Kelvin readout of the stored absolute temperature. -/
def temperatureInKelvin
    {amountScale : AmountOfSubstanceScale}
    (setup : IsochoricHeatingSetup amountScale)
    (point : ThermodynamicPoint) : ℝ :=
  let unitRatio : NNReal :=
    setup.temperatureStorageUnit / TemperatureUnit.kelvin
  (setup.stateAt point).temperature.toReal * (unitRatio : ℝ)

/-- Degree-Celsius readout, using `0 °C = 273.15 K`. -/
def temperatureInDegreesCelsius
    {amountScale : AmountOfSubstanceScale}
    (setup : IsochoricHeatingSetup amountScale)
    (point : ThermodynamicPoint) : ℝ :=
  temperatureInKelvin setup point - (5463 / 20 : ℝ)

/-- Mole readout of the amount of gas in the process. -/
def gasAmountInMoles
    {amountScale : AmountOfSubstanceScale}
    (setup : IsochoricHeatingSetup amountScale) : ℝ :=
  amountScale.inMoles setup.gasAmount

/-! ## Assumptions supplied by the problem and physical model -/

/-!
Problem-prose data and the interpretation of the vertical path.  No numerical
temperature occurs in this structure.
-/
structure MatchesProblemDescription
    {amountScale : AmountOfSubstanceScale}
    (setup : IsochoricHeatingSetup amountScale) : Prop where
  idealGasModelSelected : setup.gasModel = .ideal
  gasAmountMoles : gasAmountInMoles setup = (1 / 250 : ℝ)
  processIsConstantVolume : setup.processKind = .constantVolume

/-!
All information read from the primary pressure--volume raster: axis meanings
and ranges, labelled coordinates, and the upward arrow.  The scalar diagram
coordinates are explicitly connected to the corresponding physical readouts.
-/
structure MatchesSuppliedPressureVolumeDiagram
    {amountScale : AmountOfSubstanceScale}
    (setup : IsochoricHeatingSetup amountScale) : Prop where
  horizontalAxisIsVolume :
    setup.figure.horizontalAxisQuantity = .volume
  horizontalAxisUsesCubicCentimeters :
    setup.figure.horizontalAxisUnit = .cubicCentimeter
  horizontalAxisRange :
    setup.figure.horizontalAxisMinimum = 0 ∧
      setup.figure.horizontalAxisMaximum = 300
  verticalAxisIsPressure :
    setup.figure.verticalAxisQuantity = .pressure
  verticalAxisUsesAtmospheres :
    setup.figure.verticalAxisUnit = .atmosphere
  verticalAxisRange :
    setup.figure.verticalAxisMinimum = 0 ∧
      setup.figure.verticalAxisMaximum = 3
  bothPointLabelsShown :
    ∀ point : ThermodynamicPoint,
      setup.figure.showsPointLabel point = true
  state1FigureCoordinate :
    setup.figure.pointVolumeCubicCentimeters .state1 = 200 ∧
      setup.figure.pointPressureAtmospheres .state1 = 1
  state2FigureCoordinate :
    setup.figure.pointVolumeCubicCentimeters .state2 = 200 ∧
      setup.figure.pointPressureAtmospheres .state2 = 3
  coordinatesRepresentPhysicalStates :
    ∀ point : ThermodynamicPoint,
      setup.figure.pointVolumeCubicCentimeters point =
          volumeInCubicCentimeters (setup.stateAt point).volume ∧
        setup.figure.pointPressureAtmospheres point =
          pressureInAtmospheres (setup.stateAt point).pressure
  directedArrowShown : setup.figure.showsDirectedArrow = true
  arrowEndpoints :
    setup.figure.arrowStart = .state1 ∧
      setup.figure.arrowEnd = .state2
  arrowIsUpward : setup.figure.arrowPointsUpward = true
  pathIsVertical : setup.figure.pathShape = .vertical

/-- Positivity conditions selecting physically admissible gas states. -/
structure HasPhysicalParameters
    {amountScale : AmountOfSubstanceScale}
    (setup : IsochoricHeatingSetup amountScale) : Prop where
  positiveAmount : 0 < gasAmountInMoles setup
  positiveGasConstant :
    0 < setup.molarGasConstantInLiterAtmospheresPerMoleKelvin
  positivePressure :
    ∀ point : ThermodynamicPoint,
      0 < pressureInAtmospheres (setup.stateAt point).pressure
  positiveVolume :
    ∀ point : ThermodynamicPoint,
      0 < volumeInLiters (setup.stateAt point).volume
  positiveAbsoluteTemperature :
    ∀ point : ThermodynamicPoint, 0 < temperatureInKelvin setup point

/-!
The ideal-gas equation of state `pV = nRT`, imposed uniformly rather than only
at the requested final state.  All factors use compatible litre, atmosphere,
mole, and kelvin readouts.  This general law contains no answer-choice value.
-/
structure SatisfiesIdealGasLaw
    {amountScale : AmountOfSubstanceScale}
    (setup : IsochoricHeatingSetup amountScale) : Prop where
  stateEquation :
    ∀ point : ThermodynamicPoint,
      pressureInAtmospheres (setup.stateAt point).pressure *
          volumeInLiters (setup.stateAt point).volume =
        gasAmountInMoles setup *
          setup.molarGasConstantInLiterAtmospheresPerMoleKelvin *
            temperatureInKelvin setup point

/-!
The conventional textbook calibration `R = 0.082 L·atm·mol⁻¹·K⁻¹` used for
the integer-valued choices.  It is separate from the gas law and does not by
itself determine the final temperature.
-/
structure UsesTextbookGasConstant
    {amountScale : AmountOfSubstanceScale}
    (setup : IsochoricHeatingSetup amountScale) : Prop where
  gasConstantValue :
    setup.molarGasConstantInLiterAtmospheresPerMoleKelvin = (41 / 500 : ℝ)

/-! ## Target answer and its rounding semantics -/

/-- The four answer labels printed with the problem. -/
inductive AnswerChoice where
  | A
  | B
  | C
  | D
  deriving DecidableEq, Fintype, Repr

/-- The displayed temperature in degrees Celsius beside each answer label. -/
def displayedTemperatureDegreesCelsius : AnswerChoice → ℝ
  | .A => 1556
  | .B => 1756
  | .C => 3556
  | .D => 1584

/-- Dataset metadata recording the supplied answer label. -/
def recordedDatasetAnswer : AnswerChoice := .A

/-- The physical final-temperature readout in degrees Celsius. -/
def finalTemperatureInDegreesCelsius
    {amountScale : AmountOfSubstanceScale}
    (setup : IsochoricHeatingSetup amountScale) : ℝ :=
  temperatureInDegreesCelsius setup .state2

/-- The computed final temperature rounds to a displayed whole degree. -/
def RoundsToDisplayedWholeDegree
    {amountScale : AmountOfSubstanceScale}
    (setup : IsochoricHeatingSetup amountScale)
    (choice : AnswerChoice) : Prop :=
  |finalTemperatureInDegreesCelsius setup -
      displayedTemperatureDegreesCelsius choice| < (1 / 2 : ℝ)

/-- The selected displayed temperature is closer than every alternative. -/
def IsUniqueClosestDisplayedTemperature
    {amountScale : AmountOfSubstanceScale}
    (setup : IsochoricHeatingSetup amountScale)
    (choice : AnswerChoice) : Prop :=
  ∀ other : AnswerChoice, other ≠ choice →
    |finalTemperatureInDegreesCelsius setup -
        displayedTemperatureDegreesCelsius choice| <
      |finalTemperatureInDegreesCelsius setup -
        displayedTemperatureDegreesCelsius other|

/-!
At state 2 the figure gives `p₂ = 3 atm` and `V₂ = 0.200 L`.
Using `n = 0.0040 mol` and the textbook gas constant gives the exact
calculation-model result `T₂ = 75000/41 K`.
-/
lemma final_temperature_in_kelvin_exact
    {amountScale : AmountOfSubstanceScale}
    (setup : IsochoricHeatingSetup amountScale)
    (hDescription : MatchesProblemDescription setup)
    (hFigure : MatchesSuppliedPressureVolumeDiagram setup)
    (hPhysical : HasPhysicalParameters setup)
    (hCalibration : UsesTextbookGasConstant setup)
    (hIdealGas : SatisfiesIdealGasLaw setup) :
    temperatureInKelvin setup .state2 = (75000 / 41 : ℝ) := by
  have hCoordinates :=
    hFigure.coordinatesRepresentPhysicalStates ThermodynamicPoint.state2
  have hVolumeCubicCentimeters :
      volumeInCubicCentimeters (setup.stateAt .state2).volume = 200 := by
    calc
      volumeInCubicCentimeters (setup.stateAt .state2).volume =
          setup.figure.pointVolumeCubicCentimeters .state2 :=
        hCoordinates.1.symm
      _ = 200 := hFigure.state2FigureCoordinate.1
  have hPressureAtmospheres :
      pressureInAtmospheres (setup.stateAt .state2).pressure = 3 := by
    calc
      pressureInAtmospheres (setup.stateAt .state2).pressure =
          setup.figure.pointPressureAtmospheres .state2 :=
        hCoordinates.2.symm
      _ = 3 := hFigure.state2FigureCoordinate.2
  have hVolumeLiters :
      volumeInLiters (setup.stateAt .state2).volume = (1 / 5 : ℝ) := by
    simp only [volumeInCubicCentimeters, volumeInLiters] at hVolumeCubicCentimeters ⊢
    linarith
  have hEquation := hIdealGas.stateEquation ThermodynamicPoint.state2
  rw [hPressureAtmospheres, hVolumeLiters, hDescription.gasAmountMoles,
    hCalibration.gasConstantValue] at hEquation
  have hTemperaturePositive :=
    hPhysical.positiveAbsoluteTemperature ThermodynamicPoint.state2
  norm_num at hEquation ⊢
  linarith [hTemperaturePositive]

/-!
After converting absolute temperature to Celsius, the model gives about
`1556.12 °C`.  Thus it rounds to `1556 °C`, answer A, which is strictly closer
than every other displayed choice.
-/
theorem final_temperature_is_answer_A
    {amountScale : AmountOfSubstanceScale}
    (setup : IsochoricHeatingSetup amountScale)
    (hDescription : MatchesProblemDescription setup)
    (hFigure : MatchesSuppliedPressureVolumeDiagram setup)
    (hPhysical : HasPhysicalParameters setup)
    (hCalibration : UsesTextbookGasConstant setup)
    (hIdealGas : SatisfiesIdealGasLaw setup) :
    RoundsToDisplayedWholeDegree setup .A ∧
      IsUniqueClosestDisplayedTemperature setup .A := by
  have hKelvin :=
    final_temperature_in_kelvin_exact setup hDescription hFigure hPhysical
      hCalibration hIdealGas
  constructor
  · simp only [RoundsToDisplayedWholeDegree,
      finalTemperatureInDegreesCelsius, temperatureInDegreesCelsius,
      displayedTemperatureDegreesCelsius]
    rw [hKelvin]
    norm_num [abs_of_nonneg, abs_of_nonpos]
  · intro other hOther
    fin_cases other
    · exact (hOther rfl).elim
    all_goals
      simp only [finalTemperatureInDegreesCelsius,
        temperatureInDegreesCelsius, displayedTemperatureDegreesCelsius]
      rw [hKelvin]
      norm_num [abs_of_nonneg, abs_of_nonpos]

end PhyXMiniProblems.ProblemPhyXMini0361
