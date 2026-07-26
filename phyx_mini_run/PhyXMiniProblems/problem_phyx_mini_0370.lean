import Mathlib
import Physlib.Thermodynamics.Temperature.Basic
import Physlib.Thermodynamics.Temperature.TemperatureUnits
import Physlib.Units.WithDim.Pressure

/- USER: The assigned source file did not exist when this autoformalization task began. -/

noncomputable section

namespace PhyXMiniProblems.ProblemPhyXMini0370

open Dimension

/-!
# Maximum temperature on a straight pressure--volume path

Eighty moles of an ideal gas can move from state `1` to state `2` either
along the red dashed isotherm or along the solid straight chord in the
supplied pressure--volume diagram.  The primary image places state `1` at
`(2 m³, 100 kPa)` and state `2` at `(1 m³, 200 kPa)`; these exact plotted
coordinates take precedence over the auxiliary caption's approximate
`110 kPa` and `220 kPa` transcription.

Pressure, volume, absolute temperature, and amount of substance remain
physical quantities.  Real numbers below are explicitly named unit readouts,
diagram coordinates, a physical-constant calibration, path parameters, or
displayed answer values.
-/

/-! ## Physical quantities and named-unit readouts -/

/-- A nonnegative physical volume with length-cubed dimension. -/
abbrev VolumeQuantity : Type :=
  Dimensionful (WithDim (L𝓭 * L𝓭 * L𝓭) NNReal)

/-!
Physlib does not currently provide an amount-of-substance base dimension.
This interface keeps the gas amount abstract and exposes only its calibrated
mole readout.
-/
structure AmountOfSubstanceScale where
  Quantity : Type
  inMoles : Quantity → ℝ

/-- Read a physical volume in coherent SI cubic metres. -/
def volumeInCubicMeters (volume : VolumeQuantity) : ℝ :=
  ((volume UnitChoices.SI).val : ℝ)

/-- Read a physical pressure in coherent SI pascals. -/
def pressureInPascals (pressure : DimPressure) : ℝ :=
  (pressure UnitChoices.SI).val

/-- Read a physical pressure in the kilopascals printed on the diagram. -/
def pressureInKilopascals (pressure : DimPressure) : ℝ :=
  pressureInPascals pressure / 1000

/-- Convert a stored Physlib absolute temperature to a kelvin readout. -/
def temperatureInKelvin
    (storageUnit : TemperatureUnit) (temperature : Temperature) : ℝ :=
  let unitRatio : NNReal := storageUnit / TemperatureUnit.kelvin
  temperature.toReal * (unitRatio : ℝ)

/-! ## Gas states, process labels, and diagram vocabulary -/

/-- The equation-of-state model named by the problem. -/
inductive GasModel where
  | ideal
  | other
  deriving DecidableEq, Repr

/-- The two black endpoint labels in the primary image. -/
inductive Endpoint where
  | state1
  | state2
  deriving DecidableEq, Fintype, Repr

/-- The two alternative paths connecting the endpoint states. -/
inductive ProcessPath where
  | straightLine
  | isotherm
  deriving DecidableEq, Fintype, Repr

/-- Physical quantity represented by a diagram axis. -/
inductive AxisQuantity where
  | volume
  | pressure
  deriving DecidableEq, Repr

/-- Unit printed next to a diagram axis. -/
inductive AxisUnit where
  | cubicMeter
  | kilopascal
  deriving DecidableEq, Repr

/-- Visual style used to distinguish the two plotted processes. -/
inductive PathStyle where
  | solidStraight
  | redDashedCurve
  deriving DecidableEq, Repr

/-- A thermodynamic equilibrium state with dimensionful observables. -/
structure ThermodynamicState where
  pressure : DimPressure
  volume : VolumeQuantity
  temperature : Temperature

/-!
Scalar fields in this structure are literal coordinate readouts from the
supplied raster; physical states are stored separately in the experiment and
are connected to these coordinates below.
-/
structure PressureVolumeDiagram where
  horizontalAxisQuantity : AxisQuantity
  horizontalAxisUnit : AxisUnit
  horizontalAxisMinimum : ℝ
  horizontalAxisMaximum : ℝ
  verticalAxisQuantity : AxisQuantity
  verticalAxisUnit : AxisUnit
  verticalAxisMinimum : ℝ
  verticalAxisMaximum : ℝ
  pointVolumeCubicMeters : Endpoint → ℝ
  pointPressureKilopascals : Endpoint → ℝ
  showsPointLabel : Endpoint → Bool
  showsPath : ProcessPath → Bool
  pathStyle : ProcessPath → PathStyle
  showsDirectedArrow : ProcessPath → Bool
  arrowStart : ProcessPath → Endpoint
  arrowFinish : ProcessPath → Endpoint
  showsIsothermLabel : Bool

/-!
The physical gas sample and both processes.  A path parameter of `0`
corresponds to state `1`, and a parameter of `1` corresponds to state `2`.
Only parameters in the closed unit interval describe the plotted processes.
-/
structure IdealGasTwoPathSetup (amountScale : AmountOfSubstanceScale) where
  gasModel : GasModel
  gasAmount : amountScale.Quantity
  molarGasConstantJoulesPerMoleKelvin : ℝ
  temperatureStorageUnit : TemperatureUnit
  endpointState : Endpoint → ThermodynamicState
  stateAlong : ProcessPath → ℝ → ThermodynamicState
  figure : PressureVolumeDiagram

/-- Mole readout of the physical gas amount. -/
def gasAmountInMoles
    {amountScale : AmountOfSubstanceScale}
    (setup : IdealGasTwoPathSetup amountScale) : ℝ :=
  amountScale.inMoles setup.gasAmount

/-- Kelvin readout at a parameter value on either process. -/
def processTemperatureInKelvin
    {amountScale : AmountOfSubstanceScale}
    (setup : IdealGasTwoPathSetup amountScale)
    (path : ProcessPath) (parameter : ℝ) : ℝ :=
  temperatureInKelvin setup.temperatureStorageUnit
    (setup.stateAlong path parameter).temperature

/-! ## Problem data, primary-image evidence, and governing laws -/

/-!
Prose data: an 80-mole ideal gas and two named alternative processes.
No maximum temperature or answer choice is fixed here.
-/
structure MatchesProblemDescription
    {amountScale : AmountOfSubstanceScale}
    (setup : IdealGasTwoPathSetup amountScale) : Prop where
  idealGasModelSelected : setup.gasModel = .ideal
  gasAmountIsEightyMoles : gasAmountInMoles setup = 80

/-!
Exact information transcribed from the primary raster: axis meanings and
ranges, endpoint coordinates, path styles, labels, and the arrows from state
`1` to state `2`.  The coordinate readouts are explicitly connected to the
dimensionful endpoint states, and both plotted paths share those endpoints.
-/
structure MatchesPrimaryPressureVolumeDiagram
    {amountScale : AmountOfSubstanceScale}
    (setup : IdealGasTwoPathSetup amountScale) : Prop where
  horizontalAxisIsVolume :
    setup.figure.horizontalAxisQuantity = .volume
  horizontalAxisUsesCubicMeters :
    setup.figure.horizontalAxisUnit = .cubicMeter
  horizontalAxisRange :
    setup.figure.horizontalAxisMinimum = 0 ∧
      setup.figure.horizontalAxisMaximum = 3
  verticalAxisIsPressure :
    setup.figure.verticalAxisQuantity = .pressure
  verticalAxisUsesKilopascals :
    setup.figure.verticalAxisUnit = .kilopascal
  verticalAxisRange :
    setup.figure.verticalAxisMinimum = 0 ∧
      setup.figure.verticalAxisMaximum = 200
  state1Coordinate :
    setup.figure.pointVolumeCubicMeters .state1 = 2 ∧
      setup.figure.pointPressureKilopascals .state1 = 100
  state2Coordinate :
    setup.figure.pointVolumeCubicMeters .state2 = 1 ∧
      setup.figure.pointPressureKilopascals .state2 = 200
  coordinatesRepresentPhysicalEndpoints :
    ∀ endpoint : Endpoint,
      setup.figure.pointVolumeCubicMeters endpoint =
          volumeInCubicMeters (setup.endpointState endpoint).volume ∧
        setup.figure.pointPressureKilopascals endpoint =
          pressureInKilopascals (setup.endpointState endpoint).pressure
  everyEndpointLabelShown :
    ∀ endpoint : Endpoint, setup.figure.showsPointLabel endpoint = true
  bothPathsShown :
    ∀ path : ProcessPath, setup.figure.showsPath path = true
  straightPathStyle :
    setup.figure.pathStyle .straightLine = .solidStraight
  isothermPathStyle :
    setup.figure.pathStyle .isotherm = .redDashedCurve
  isothermLabelShown : setup.figure.showsIsothermLabel = true
  bothDirectedArrowsShown :
    ∀ path : ProcessPath, setup.figure.showsDirectedArrow path = true
  arrowDirection :
    ∀ path : ProcessPath,
      setup.figure.arrowStart path = .state1 ∧
        setup.figure.arrowFinish path = .state2
  pathsStartAtState1 :
    ∀ path : ProcessPath,
      setup.stateAlong path 0 = setup.endpointState .state1
  pathsFinishAtState2 :
    ∀ path : ProcessPath,
      setup.stateAlong path 1 = setup.endpointState .state2

/-! Positivity assumptions selecting physically admissible process states. -/
structure HasPhysicalProcessParameters
    {amountScale : AmountOfSubstanceScale}
    (setup : IdealGasTwoPathSetup amountScale) : Prop where
  amountPositive : 0 < gasAmountInMoles setup
  molarGasConstantPositive :
    0 < setup.molarGasConstantJoulesPerMoleKelvin
  pressurePositive :
    ∀ path parameter, parameter ∈ Set.Icc (0 : ℝ) 1 →
      0 < pressureInPascals (setup.stateAlong path parameter).pressure
  volumePositive :
    ∀ path parameter, parameter ∈ Set.Icc (0 : ℝ) 1 →
      0 < volumeInCubicMeters (setup.stateAlong path parameter).volume
  absoluteTemperaturePositive :
    ∀ path parameter, parameter ∈ Set.Icc (0 : ℝ) 1 →
      0 < processTemperatureInKelvin setup path parameter

/-!
Macroscopic laws used by the calculation:

* the SI molar ideal-gas equation `pV = nRT` at every state of both paths;
* affine pressure and volume coordinates along the solid straight chord;
* constant absolute temperature along the dashed isotherm.

These are governing laws for the two processes.  In particular, none states
where the straight-path maximum occurs or what its value is.
-/
structure SatisfiesIdealGasAndProcessLaws
    {amountScale : AmountOfSubstanceScale}
    (setup : IdealGasTwoPathSetup amountScale) : Prop where
  idealGasEquation :
    ∀ path parameter, parameter ∈ Set.Icc (0 : ℝ) 1 →
      pressureInPascals (setup.stateAlong path parameter).pressure *
          volumeInCubicMeters (setup.stateAlong path parameter).volume =
        gasAmountInMoles setup *
          setup.molarGasConstantJoulesPerMoleKelvin *
            processTemperatureInKelvin setup path parameter
  straightLineVolumeInterpolation :
    ∀ parameter, parameter ∈ Set.Icc (0 : ℝ) 1 →
      volumeInCubicMeters
          (setup.stateAlong .straightLine parameter).volume =
        (1 - parameter) *
            volumeInCubicMeters (setup.endpointState .state1).volume +
          parameter *
            volumeInCubicMeters (setup.endpointState .state2).volume
  straightLinePressureInterpolation :
    ∀ parameter, parameter ∈ Set.Icc (0 : ℝ) 1 →
      pressureInKilopascals
          (setup.stateAlong .straightLine parameter).pressure =
        (1 - parameter) *
            pressureInKilopascals (setup.endpointState .state1).pressure +
          parameter *
            pressureInKilopascals (setup.endpointState .state2).pressure
  isothermHasConstantTemperature :
    ∀ parameter, parameter ∈ Set.Icc (0 : ℝ) 1 →
      processTemperatureInKelvin setup .isotherm parameter =
        processTemperatureInKelvin setup .isotherm 0

/-!
The standard textbook SI calibration `R = 8.314 J mol⁻¹ K⁻¹`.  It is kept
separate from the general equation of state and contains no temperature
answer.
-/
structure UsesTextbookMolarGasConstant
    {amountScale : AmountOfSubstanceScale}
    (setup : IdealGasTwoPathSetup amountScale) : Prop where
  molarGasConstantValue :
    setup.molarGasConstantJoulesPerMoleKelvin = (4157 / 500 : ℝ)

/-! ## Maximum-temperature and answer-choice predicates -/

/-- Temperature readout along the solid straight-line process. -/
def straightLineTemperatureInKelvin
    {amountScale : AmountOfSubstanceScale}
    (setup : IdealGasTwoPathSetup amountScale) (parameter : ℝ) : ℝ :=
  processTemperatureInKelvin setup .straightLine parameter

/-! A parameter attains the maximum temperature on the plotted chord. -/
def IsMaximumStraightLineTemperatureAt
    {amountScale : AmountOfSubstanceScale}
    (setup : IdealGasTwoPathSetup amountScale) (maximizingParameter : ℝ) : Prop :=
  maximizingParameter ∈ Set.Icc (0 : ℝ) 1 ∧
    ∀ parameter, parameter ∈ Set.Icc (0 : ℝ) 1 →
      straightLineTemperatureInKelvin setup parameter ≤
        straightLineTemperatureInKelvin setup maximizingParameter

/-- Labels of the four printed multiple-choice answers. -/
inductive AnswerChoice where
  | A
  | B
  | C
  | D
  deriving DecidableEq, Fintype, Repr

/-- Whole-kelvin temperature printed beside each answer label. -/
def displayedTemperatureKelvin : AnswerChoice → ℝ
  | .A => 338
  | .B => 556
  | .C => 636
  | .D => 784

/-- Answer label recorded in the supplied dataset metadata. -/
def recordedDatasetAnswer : AnswerChoice := .A

/-- The physical maximum is compatible with a displayed whole kelvin. -/
def RoundsToDisplayedWholeKelvin
    (actualTemperatureKelvin : ℝ) (choice : AnswerChoice) : Prop :=
  |actualTemperatureKelvin - displayedTemperatureKelvin choice| < (1 / 2 : ℝ)

/-- The selected displayed temperature is closer than every alternative. -/
def IsUniqueClosestDisplayedTemperature
    (actualTemperatureKelvin : ℝ) (choice : AnswerChoice) : Prop :=
  ∀ other : AnswerChoice, other ≠ choice →
    |actualTemperatureKelvin - displayedTemperatureKelvin choice| <
      |actualTemperatureKelvin - displayedTemperatureKelvin other|

/-!
On the straight chord the affine coordinate laws give
`p(t) = 100 + 100t` kPa and `V(t) = 2 - t` m³.  Their product is maximized
at `t = 1/2`, where `pV = 225000 J`.  With `n = 80 mol` and
`R = 8.314 J mol⁻¹ K⁻¹`, the exact model value is `1406250 / 4157 K`, about
`338.29 K`.  Thus the maximum rounds to `338 K`, uniquely selecting the
recorded answer A.
-/
theorem maximum_temperature_on_straight_line_is_answer_A
    {amountScale : AmountOfSubstanceScale}
    (setup : IdealGasTwoPathSetup amountScale)
    (hDescription : MatchesProblemDescription setup)
    (hFigure : MatchesPrimaryPressureVolumeDiagram setup)
    (hPhysical : HasPhysicalProcessParameters setup)
    (hCalibration : UsesTextbookMolarGasConstant setup)
    (hLaws : SatisfiesIdealGasAndProcessLaws setup) :
    IsMaximumStraightLineTemperatureAt setup (1 / 2 : ℝ) ∧
      straightLineTemperatureInKelvin setup (1 / 2 : ℝ) =
        (1406250 / 4157 : ℝ) ∧
      RoundsToDisplayedWholeKelvin
        (straightLineTemperatureInKelvin setup (1 / 2 : ℝ))
        recordedDatasetAnswer ∧
      IsUniqueClosestDisplayedTemperature
        (straightLineTemperatureInKelvin setup (1 / 2 : ℝ))
        recordedDatasetAnswer := by
  have hVolumeAtState1 :
      volumeInCubicMeters (setup.endpointState .state1).volume = 2 := by
    calc
      volumeInCubicMeters (setup.endpointState .state1).volume =
          setup.figure.pointVolumeCubicMeters .state1 :=
        (hFigure.coordinatesRepresentPhysicalEndpoints .state1).1.symm
      _ = 2 := hFigure.state1Coordinate.1
  have hPressureAtState1 :
      pressureInKilopascals (setup.endpointState .state1).pressure = 100 := by
    calc
      pressureInKilopascals (setup.endpointState .state1).pressure =
          setup.figure.pointPressureKilopascals .state1 :=
        (hFigure.coordinatesRepresentPhysicalEndpoints .state1).2.symm
      _ = 100 := hFigure.state1Coordinate.2
  have hVolumeAtState2 :
      volumeInCubicMeters (setup.endpointState .state2).volume = 1 := by
    calc
      volumeInCubicMeters (setup.endpointState .state2).volume =
          setup.figure.pointVolumeCubicMeters .state2 :=
        (hFigure.coordinatesRepresentPhysicalEndpoints .state2).1.symm
      _ = 1 := hFigure.state2Coordinate.1
  have hPressureAtState2 :
      pressureInKilopascals (setup.endpointState .state2).pressure = 200 := by
    calc
      pressureInKilopascals (setup.endpointState .state2).pressure =
          setup.figure.pointPressureKilopascals .state2 :=
        (hFigure.coordinatesRepresentPhysicalEndpoints .state2).2.symm
      _ = 200 := hFigure.state2Coordinate.2
  have hVolumeAlongStraightLine
      (parameter : ℝ) (hParameter : parameter ∈ Set.Icc (0 : ℝ) 1) :
      volumeInCubicMeters
          (setup.stateAlong .straightLine parameter).volume =
        2 - parameter := by
    rw [hLaws.straightLineVolumeInterpolation parameter hParameter,
      hVolumeAtState1, hVolumeAtState2]
    ring
  have hPressureKilopascalsAlongStraightLine
      (parameter : ℝ) (hParameter : parameter ∈ Set.Icc (0 : ℝ) 1) :
      pressureInKilopascals
          (setup.stateAlong .straightLine parameter).pressure =
        100 + 100 * parameter := by
    rw [hLaws.straightLinePressureInterpolation parameter hParameter,
      hPressureAtState1, hPressureAtState2]
    ring
  have hPressurePascalsAlongStraightLine
      (parameter : ℝ) (hParameter : parameter ∈ Set.Icc (0 : ℝ) 1) :
      pressureInPascals
          (setup.stateAlong .straightLine parameter).pressure =
        100000 + 100000 * parameter := by
    have hPressure :=
      hPressureKilopascalsAlongStraightLine parameter hParameter
    unfold pressureInKilopascals at hPressure
    linarith
  have hTemperatureEquation
      (parameter : ℝ) (hParameter : parameter ∈ Set.Icc (0 : ℝ) 1) :
      (100000 + 100000 * parameter) * (2 - parameter) =
        80 * (4157 / 500 : ℝ) *
          straightLineTemperatureInKelvin setup parameter := by
    have hEquation :=
      hLaws.idealGasEquation .straightLine parameter hParameter
    rw [hPressurePascalsAlongStraightLine parameter hParameter,
      hVolumeAlongStraightLine parameter hParameter,
      hDescription.gasAmountIsEightyMoles,
      hCalibration.molarGasConstantValue] at hEquation
    simpa [straightLineTemperatureInKelvin] using hEquation
  have hHalfInDomain : (1 / 2 : ℝ) ∈ Set.Icc (0 : ℝ) 1 := by
    constructor <;> norm_num
  have hHalfEquation := hTemperatureEquation (1 / 2 : ℝ) hHalfInDomain
  have hHalfTemperature :
      straightLineTemperatureInKelvin setup (1 / 2 : ℝ) =
        (1406250 / 4157 : ℝ) := by
    nlinarith [hHalfEquation]
  have hMaximum :
      IsMaximumStraightLineTemperatureAt setup (1 / 2 : ℝ) := by
    refine ⟨hHalfInDomain, ?_⟩
    intro parameter hParameter
    have hParameterEquation :=
      hTemperatureEquation parameter hParameter
    nlinarith [hHalfEquation,
      sq_nonneg (parameter - (1 / 2 : ℝ))]
  refine ⟨hMaximum, hHalfTemperature, ?_, ?_⟩
  · rw [hHalfTemperature]
    norm_num [RoundsToDisplayedWholeKelvin, recordedDatasetAnswer,
      displayedTemperatureKelvin, abs_lt]
  · rw [hHalfTemperature]
    intro other hOther
    cases other with
    | A => exact (hOther rfl).elim
    | B =>
        norm_num [recordedDatasetAnswer, displayedTemperatureKelvin]
    | C =>
        norm_num [recordedDatasetAnswer, displayedTemperatureKelvin]
    | D =>
        norm_num [recordedDatasetAnswer, displayedTemperatureKelvin]

end PhyXMiniProblems.ProblemPhyXMini0370
