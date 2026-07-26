import Mathlib.Data.Real.Basic
import Physlib.Thermodynamics.Temperature.Basic
import Physlib.Thermodynamics.Temperature.TemperatureUnits
import Physlib.Units.WithDim.Pressure

/-!
# Final temperature in an isobaric ideal-gas expansion

This file formalizes problem `phyx_mini_0362`.  The primary p-V bitmap shows
an arrow from state `1` at `(100 cm³, 2 atm)` to state `2` at
`(300 cm³, 2 atm)`.  In particular, the second volume is `300 cm³`; the
auxiliary caption's claim that it is `200 cm³` conflicts with the bitmap and
with the recorded answer.

Pressure, volume, and absolute temperature are represented by dimensionful
Physlib quantities.  Real numbers occur only as explicitly unit-labelled
readouts, the fixed-sample `nR` readout, and displayed answer values.
-/

noncomputable section

namespace PhyXMiniProblems.ProblemPhyXMini0362

open Dimension

/-! ## Physical quantities and named-unit readouts -/

/-- Physical gas volume, carrying dimension `L³` and a nonnegative value. -/
abbrev VolumeQuantity : Type :=
  Dimensionful (WithDim (L𝓭 * L𝓭 * L𝓭) NNReal)

/-- Physical gas pressure, represented by Physlib's dimensionful type. -/
abbrev PressureQuantity : Type := DimPressure

/-- Absolute thermodynamic temperature. -/
abbrev TemperatureQuantity : Type := Temperature

/-- Coherent-SI pressure readout in pascals. -/
def pressureInPascals (pressure : PressureQuantity) : ℝ :=
  (pressure UnitChoices.SI).val

/-- Pressure readout in standard atmospheres. -/
def pressureInAtmospheres (pressure : PressureQuantity) : ℝ :=
  pressureInPascals pressure /
    pressureInPascals DimPressure.standardAtmosphere

/-- Volume readout in cubic centimetres; `1 m³ = 10⁶ cm³`. -/
def volumeInCubicCentimeters (volume : VolumeQuantity) : ℝ :=
  1000000 * ((volume UnitChoices.SI).val : ℝ)

/--
Read a stored absolute temperature in kelvins.  Physlib's `Temperature` stores
an absolute nonnegative value, while the ratio of temperature units converts
the storage scale to `TemperatureUnit.kelvin`.
-/
def temperatureInKelvins
    (storageUnit : TemperatureUnit)
    (temperature : TemperatureQuantity) : ℝ :=
  let unitRatio : NNReal := storageUnit / TemperatureUnit.kelvin
  temperature.toReal * (unitRatio : ℝ)

/--
The whole-degree Celsius-to-kelvin offset used by the supplied textbook answer
choices.  This convention is made explicit because using `273.15` would give
`3246.30 °C` rather than the displayed whole-number answer.
-/
def textbookCelsiusOffset : ℝ := 273

/-- Celsius readout under the whole-degree textbook convention. -/
def temperatureInDegreesCelsius
    (storageUnit : TemperatureUnit)
    (temperature : TemperatureQuantity) : ℝ :=
  temperatureInKelvins storageUnit temperature - textbookCelsiusOffset

/-! ## Gas, states, and the supplied p-V diagram -/

/-- The two numerical labels printed beside the process endpoints. -/
inductive DiagramPoint where
  | state1
  | state2
  deriving DecidableEq, Repr

/-- Physical quantities assigned to the two graph axes. -/
inductive AxisQuantity where
  | volume
  | pressure
  deriving DecidableEq, Repr

/-- Unit printed on the horizontal axis. -/
inductive VolumeDisplayUnit where
  | cubicCentimeter
  deriving DecidableEq, Repr

/-- Unit printed on the vertical axis. -/
inductive PressureDisplayUnit where
  | atmosphere
  deriving DecidableEq, Repr

/-- Qualitative shape of the directed segment in the bitmap. -/
inductive SegmentShape where
  | horizontal
  | vertical
  | curved
  deriving DecidableEq, Repr

/-- Thermodynamic process classification. -/
inductive ProcessKind where
  | constantPressure
  | constantVolume
  | other
  deriving DecidableEq, Repr

/-- Equation-of-state model for the gas sample. -/
inductive EquationOfStateModel where
  | idealGas
  | nonIdealGas
  deriving DecidableEq, Repr

/-- Pressure, volume, and absolute temperature at one endpoint. -/
structure ThermodynamicState where
  pressure : PressureQuantity
  volume : VolumeQuantity
  temperature : TemperatureQuantity

/-!
A fixed gas sample.  The numerical `nR` field is a readout in
`atm·cm³/K`; it is not used as a replacement type for the gas itself.
-/
structure GasSample where
  equationOfState : EquationOfStateModel
  amountTimesGasConstantAtmosphereCubicCentimeterPerKelvin : ℝ

/-- Raw labels, coordinate scales, point coordinates, and arrow from the image. -/
structure PressureVolumeDiagram where
  horizontalAxisQuantity : AxisQuantity
  verticalAxisQuantity : AxisQuantity
  horizontalAxisUnit : VolumeDisplayUnit
  verticalAxisUnit : PressureDisplayUnit
  horizontalAxisMinimum : ℝ
  horizontalAxisMaximum : ℝ
  verticalAxisMinimum : ℝ
  verticalAxisMaximum : ℝ
  volumeCoordinate : DiagramPoint → ℝ
  pressureCoordinate : DiagramPoint → ℝ
  labelShown : DiagramPoint → Bool
  arrowStart : DiagramPoint
  arrowEnd : DiagramPoint
  segmentShape : SegmentShape

/-- The fixed gas, its endpoint states, process type, and supplied diagram. -/
structure IdealGasExpansionSetup where
  gas : GasSample
  state : DiagramPoint → ThermodynamicState
  temperatureStorageUnit : TemperatureUnit
  processKind : ProcessKind
  figure : PressureVolumeDiagram

/-! ## Problem statement and figure/data readouts -/

/-!
Information stated in the prose.  The initial temperature occurs here, while
the requested final temperature deliberately does not.
-/
structure MatchesProblemStatement
    (setup : IdealGasExpansionSetup) : Prop where
  gasUsesIdealEquationOfState : setup.gas.equationOfState = .idealGas
  processIsConstantPressure : setup.processKind = .constantPressure
  absoluteTemperatureStorageIsKelvin :
    setup.temperatureStorageUnit = TemperatureUnit.kelvin
  initialTemperatureCelsius :
    temperatureInDegreesCelsius setup.temperatureStorageUnit
      (setup.state .state1).temperature = 900

/-!
Primary-image evidence.  The fields record the printed axes and ranges, both
point coordinates, the horizontal segment, and its direction.  State `2` is
at `300 cm³`, as shown by the bitmap.
-/
structure MatchesPrimaryPressureVolumeDiagram
    (setup : IdealGasExpansionSetup) : Prop where
  horizontalAxisIsVolume :
    setup.figure.horizontalAxisQuantity = .volume
  verticalAxisIsPressure :
    setup.figure.verticalAxisQuantity = .pressure
  horizontalAxisUsesCubicCentimeters :
    setup.figure.horizontalAxisUnit = .cubicCentimeter
  verticalAxisUsesAtmospheres :
    setup.figure.verticalAxisUnit = .atmosphere
  horizontalAxisRange :
    setup.figure.horizontalAxisMinimum = 0 ∧
      setup.figure.horizontalAxisMaximum = 300
  verticalAxisRange :
    setup.figure.verticalAxisMinimum = 0 ∧
      setup.figure.verticalAxisMaximum = 3
  bothPointLabelsShown :
    setup.figure.labelShown .state1 = true ∧
      setup.figure.labelShown .state2 = true
  state1Coordinates :
    setup.figure.volumeCoordinate .state1 = 100 ∧
      setup.figure.pressureCoordinate .state1 = 2
  state2Coordinates :
    setup.figure.volumeCoordinate .state2 = 300 ∧
      setup.figure.pressureCoordinate .state2 = 2
  coordinatesAgreeWithPhysicalReadouts :
    ∀ point : DiagramPoint,
      setup.figure.volumeCoordinate point =
          volumeInCubicCentimeters (setup.state point).volume ∧
        setup.figure.pressureCoordinate point =
          pressureInAtmospheres (setup.state point).pressure
  displayedSegmentIsHorizontal : setup.figure.segmentShape = .horizontal
  arrowRunsFromState1ToState2 :
    setup.figure.arrowStart = .state1 ∧
      setup.figure.arrowEnd = .state2

/-! ## Physical-domain conditions and governing laws -/

/-- Positivity conditions selecting physically meaningful gas states. -/
structure HasPhysicalIdealGasParameters
    (setup : IdealGasExpansionSetup) : Prop where
  amountTimesGasConstantPositive :
    0 < setup.gas.amountTimesGasConstantAtmosphereCubicCentimeterPerKelvin
  pressurePositive : ∀ point : DiagramPoint,
    0 < pressureInAtmospheres (setup.state point).pressure
  volumePositive : ∀ point : DiagramPoint,
    0 < volumeInCubicCentimeters (setup.state point).volume
  absoluteTemperaturePositive : ∀ point : DiagramPoint,
    0 < temperatureInKelvins setup.temperatureStorageUnit
      (setup.state point).temperature

/-!
The molar ideal-gas equation `pV = (nR)T` at every labelled state, together
with the physical meaning of an isobaric endpoint process.  These are general
governing relations and contain no numerical final temperature.
-/
structure SatisfiesFixedSampleIdealGasLaws
    (setup : IdealGasExpansionSetup) : Prop where
  idealGasLawAt : ∀ point : DiagramPoint,
    pressureInAtmospheres (setup.state point).pressure *
        volumeInCubicCentimeters (setup.state point).volume =
      setup.gas.amountTimesGasConstantAtmosphereCubicCentimeterPerKelvin *
        temperatureInKelvins setup.temperatureStorageUnit
          (setup.state point).temperature
  constantPressureLaw :
    setup.processKind = .constantPressure →
      (setup.state .state1).pressure = (setup.state .state2).pressure

/-! ## Derived temperature and displayed answer -/

/-!
The constant pressure and threefold volume increase make the absolute final
temperature `3519 K`, since the initial `900 °C` is `1173 K` under the stated
textbook convention.
-/
lemma finalAbsoluteTemperatureInKelvins_eq_3519
    (setup : IdealGasExpansionSetup)
    (_problem : MatchesProblemStatement setup)
    (_figure : MatchesPrimaryPressureVolumeDiagram setup)
    (_physical : HasPhysicalIdealGasParameters setup)
    (_laws : SatisfiesFixedSampleIdealGasLaws setup) :
    temperatureInKelvins setup.temperatureStorageUnit
      (setup.state .state2).temperature = 3519 := by
  have hV1 : volumeInCubicCentimeters (setup.state .state1).volume = 100 :=
    (((_figure.coordinatesAgreeWithPhysicalReadouts .state1).1).symm.trans
      _figure.state1Coordinates.1)
  have hP1 : pressureInAtmospheres (setup.state .state1).pressure = 2 :=
    (((_figure.coordinatesAgreeWithPhysicalReadouts .state1).2).symm.trans
      _figure.state1Coordinates.2)
  have hV2 : volumeInCubicCentimeters (setup.state .state2).volume = 300 :=
    (((_figure.coordinatesAgreeWithPhysicalReadouts .state2).1).symm.trans
      _figure.state2Coordinates.1)
  have hP2 : pressureInAtmospheres (setup.state .state2).pressure = 2 :=
    (((_figure.coordinatesAgreeWithPhysicalReadouts .state2).2).symm.trans
      _figure.state2Coordinates.2)
  have hT1C := _problem.initialTemperatureCelsius
  have hT1 : temperatureInKelvins setup.temperatureStorageUnit
      (setup.state .state1).temperature = 1173 := by
    dsimp [temperatureInDegreesCelsius, textbookCelsiusOffset] at hT1C
    linarith
  have hLaw1 := _laws.idealGasLawAt .state1
  have hLaw2 := _laws.idealGasLawAt .state2
  rw [hP1, hV1, hT1] at hLaw1
  rw [hP2, hV2] at hLaw2
  norm_num at hLaw1 hLaw2
  have hnR :
      setup.gas.amountTimesGasConstantAtmosphereCubicCentimeterPerKelvin =
        200 / 1173 := by
    linarith
  rw [hnR] at hLaw2
  linarith

/-- Labels printed beside the four displayed answer choices. -/
inductive AnswerChoice where
  | A
  | B
  | C
  | D
  deriving DecidableEq, Repr

/-- Celsius value printed beside each answer label. -/
def AnswerChoice.celsiusValue : AnswerChoice → ℝ
  | .A => 3246
  | .B => 1856
  | .C => 1596
  | .D => 2556

/-- Answer label recorded in the supplied dataset metadata. -/
def recordedAnswerChoice : AnswerChoice := .A

/-!
At constant pressure, `T₂/T₁ = V₂/V₁ = 300/100`.  Thus the final absolute
temperature is `3519 K`, whose textbook Celsius readout is `3246 °C`, answer
choice A.

Blueprint label: `thm:physics:phyx_mini_0362:target`.
-/
theorem finalTemperature_matches_recordedAnswerA
    (setup : IdealGasExpansionSetup)
    (_problem : MatchesProblemStatement setup)
    (_figure : MatchesPrimaryPressureVolumeDiagram setup)
    (_physical : HasPhysicalIdealGasParameters setup)
    (_laws : SatisfiesFixedSampleIdealGasLaws setup) :
    temperatureInDegreesCelsius setup.temperatureStorageUnit
          (setup.state .state2).temperature = 3246 ∧
      temperatureInDegreesCelsius setup.temperatureStorageUnit
          (setup.state .state2).temperature =
        recordedAnswerChoice.celsiusValue := by
  have hT2 := finalAbsoluteTemperatureInKelvins_eq_3519
    setup _problem _figure _physical _laws
  constructor
  · dsimp [temperatureInDegreesCelsius, textbookCelsiusOffset]
    rw [hT2]
    norm_num
  · dsimp [temperatureInDegreesCelsius, textbookCelsiusOffset,
      recordedAnswerChoice, AnswerChoice.celsiusValue]
    rw [hT2]
    norm_num

end PhyXMiniProblems.ProblemPhyXMini0362
