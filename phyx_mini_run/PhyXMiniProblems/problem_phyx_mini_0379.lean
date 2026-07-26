import Mathlib
import Physlib.Thermodynamics.Temperature.Basic
import Physlib.Units.WithDim.Energy

/- USER: The assigned source file did not exist when this autoformalization task began. -/

noncomputable section

namespace PhyXMiniProblems.ProblemPhyXMini0379

/-!
# Constant-volume molar heat capacity from a thermal-energy graph

The supplied graph plots the thermal energy of a `0.14 mol` gas sample against
temperature in degrees Celsius.  Physlib's `Temperature` and `DimEnergy` retain
the physical roles of absolute temperature and energy.  Amount of substance
and molar heat capacity are explicit SI scalar readouts because Physlib's
dimension system has no amount-of-substance component.

The graph readouts and the governing law are kept separate from the requested
value of `C_V`.
-/

/-! ## Physical readouts and figure labels -/

/-- Read a dimensionful thermal energy in SI joules. -/
def energyInJoules (energy : DimEnergy) : ℝ :=
  (energy UnitChoices.SI).val

/--
Read an absolute Physlib temperature in degrees Celsius.  Celsius and kelvin
increments have the same numerical size, which is used by the difference law
below.
-/
def temperatureInCelsius (temperature : Temperature) : ℝ :=
  temperature.toReal - 27315 / 100

/-- The three temperature coordinates singled out by the graph. -/
inductive TemperatureMark where
  | zeroCelsius
  | oneHundredCelsius
  | twoHundredCelsius
  deriving DecidableEq, Repr

/-- Literal roles of the labels on the horizontal and vertical axes. -/
inductive AxisLabel where
  | temperatureDegreesCelsius
  | thermalEnergyJoules
  deriving DecidableEq, Repr

/-- The thermodynamic heat-capacity distinction relevant to the question. -/
inductive HeatCapacityKind where
  | constantVolume
  | constantPressure
  deriving DecidableEq, Repr

/-- The shape of the orange data curve drawn in the primary image. -/
inductive CurveShape where
  | straightLine
  deriving DecidableEq, Repr

/--
The plotted curve together with the numerical scale and visible guide marks.
The curve itself maps physical absolute temperatures to dimensionful thermal
energies; reals in the remaining fields are explicitly labeled axis readouts.
-/
structure ThermalEnergyTemperatureGraph where
  temperatureAt : TemperatureMark → Temperature
  thermalEnergy : Temperature → DimEnergy
  xAxisMinimumCelsius : ℝ
  xAxisMaximumCelsius : ℝ
  xAxisTickSpacingCelsius : ℝ
  yAxisOriginLabelJoules : ℝ
  yAxisLowerDisplayedJoules : ℝ
  yAxisMiddleDisplayedJoules : ℝ
  yAxisUpperDisplayedJoules : ℝ
  curveShape : CurveShape
  axisLabelVisible : AxisLabel → Bool
  dashedGuideVisibleAt : TemperatureMark → Bool
  yAxisBreakVisible : Bool

/-! ## Gas sample, assumptions, and governing law -/

/--
The gas sample whose molar heat capacity is to be inferred.  The two real
fields are named numerical readouts in `mol` and `J/(mol K)`; they are not
transparent aliases for physical temperature or energy.
-/
structure GasThermalEnergyExperiment where
  amountOfGasMoles : ℝ
  constantVolumeMolarHeatCapacityJoulesPerMoleKelvin : ℝ
  requestedHeatCapacityKind : HeatCapacityKind
  graph : ThermalEnergyTemperatureGraph

/-- The prose setup, excluding the graph's measured energy values. -/
structure MatchesGasThermalEnergyScenario
    (setup : GasThermalEnergyExperiment) : Prop where
  amountIsPointFourteenMoles :
    setup.amountOfGasMoles = 14 / 100
  asksForConstantVolumeHeatCapacity :
    setup.requestedHeatCapacityKind = .constantVolume

/-- Positivity and nondegeneracy conditions for the physical branch. -/
structure HasPhysicalThermalParameters
    (setup : GasThermalEnergyExperiment) : Prop where
  gasAmountPositive :
    0 < setup.amountOfGasMoles
  molarHeatCapacityPositive :
    0 < setup.constantVolumeMolarHeatCapacityJoulesPerMoleKelvin
  displayedTemperaturesIncrease :
    (setup.graph.temperatureAt .zeroCelsius).toReal <
        (setup.graph.temperatureAt .oneHundredCelsius).toReal ∧
      (setup.graph.temperatureAt .oneHundredCelsius).toReal <
        (setup.graph.temperatureAt .twoHundredCelsius).toReal

/-!
The constant-volume thermal-energy law
`ΔE_th = n C_V ΔT`.  It is stated for arbitrary pairs of temperatures on the
sample's curve and does not assign a numerical value to `C_V`.
-/
structure ObeysConstantVolumeThermalEnergyLaw
    (setup : GasThermalEnergyExperiment) : Prop where
  thermalEnergyDifferenceLaw :
    ∀ initialTemperature finalTemperature,
      energyInJoules
            (setup.graph.thermalEnergy finalTemperature) -
          energyInJoules
            (setup.graph.thermalEnergy initialTemperature) =
        setup.amountOfGasMoles *
          setup.constantVolumeMolarHeatCapacityJoulesPerMoleKelvin *
            (finalTemperature.toReal - initialTemperature.toReal)

/-!
Exact scalar readouts and visible features transcribed from the primary image.
The plotted points are `(0,1092)`, `(100,1492)`, and `(200,1892)` in
`(°C,J)`.  No heat-capacity value occurs in this figure-data structure.
-/
structure MatchesPrimaryThermalEnergyFigure
    (setup : GasThermalEnergyExperiment) : Prop where
  zeroTemperatureReadout :
    temperatureInCelsius
        (setup.graph.temperatureAt .zeroCelsius) = 0
  oneHundredTemperatureReadout :
    temperatureInCelsius
        (setup.graph.temperatureAt .oneHundredCelsius) = 100
  twoHundredTemperatureReadout :
    temperatureInCelsius
        (setup.graph.temperatureAt .twoHundredCelsius) = 200
  zeroTemperatureEnergyReadout :
    energyInJoules
        (setup.graph.thermalEnergy
          (setup.graph.temperatureAt .zeroCelsius)) = 1092
  oneHundredTemperatureEnergyReadout :
    energyInJoules
        (setup.graph.thermalEnergy
          (setup.graph.temperatureAt .oneHundredCelsius)) = 1492
  twoHundredTemperatureEnergyReadout :
    energyInJoules
        (setup.graph.thermalEnergy
          (setup.graph.temperatureAt .twoHundredCelsius)) = 1892
  xAxisStartsAtZero :
    setup.graph.xAxisMinimumCelsius = 0
  xAxisEndsAtTwoHundred :
    setup.graph.xAxisMaximumCelsius = 200
  xAxisTicksEveryHundredDegrees :
    setup.graph.xAxisTickSpacingCelsius = 100
  yAxisOriginLabelIsZero :
    setup.graph.yAxisOriginLabelJoules = 0
  yAxisLowerDisplayedValue :
    setup.graph.yAxisLowerDisplayedJoules = 1092
  yAxisMiddleDisplayedValue :
    setup.graph.yAxisMiddleDisplayedJoules = 1492
  yAxisUpperDisplayedValue :
    setup.graph.yAxisUpperDisplayedJoules = 1892
  curveIsStraight :
    setup.graph.curveShape = .straightLine
  bothAxisLabelsVisible :
    ∀ label, setup.graph.axisLabelVisible label = true
  oneHundredGuideVisible :
    setup.graph.dashedGuideVisibleAt .oneHundredCelsius = true
  twoHundredGuideVisible :
    setup.graph.dashedGuideVisibleAt .twoHundredCelsius = true
  skippedYAxisScaleMarked :
    setup.graph.yAxisBreakVisible = true

/-! ## Displayed answer choices and target -/

/-- The four answer labels printed in the source. -/
inductive AnswerChoice where
  | A
  | B
  | C
  | D
  deriving DecidableEq, Repr

/-- Numerical value beside each answer, in joules per mole-kelvin. -/
def answerMolarHeatCapacityJoulesPerMoleKelvin : AnswerChoice → ℝ
  | .A => 29
  | .B => 297 / 100
  | .C => 29 / 10
  | .D => 129

/-- The dataset metadata records answer choice A. -/
def recordedAnswerChoice : AnswerChoice := .A

/-!
The graph has slope `4 J/K`; dividing by `0.14 mol` gives the exact inferred
readout `200/7 J/(mol K)`, which rounds to `29` and therefore matches answer A.

Neither the exact value nor its rounded value is assumed by the scenario,
physical-parameter, governing-law, or figure-data structures.

Blueprint label: `thm:physics:phyx_mini_0379:target`.
-/
theorem constantVolumeMolarHeatCapacity_from_thermalEnergyGraph
    (setup : GasThermalEnergyExperiment)
    (_scenario : MatchesGasThermalEnergyScenario setup)
    (_physical : HasPhysicalThermalParameters setup)
    (_laws : ObeysConstantVolumeThermalEnergyLaw setup)
    (_figure : MatchesPrimaryThermalEnergyFigure setup) :
    setup.constantVolumeMolarHeatCapacityJoulesPerMoleKelvin = 200 / 7 ∧
      round setup.constantVolumeMolarHeatCapacityJoulesPerMoleKelvin =
        (29 : ℤ) ∧
      round setup.constantVolumeMolarHeatCapacityJoulesPerMoleKelvin =
        round (answerMolarHeatCapacityJoulesPerMoleKelvin .A) := by
  have hzero := _figure.zeroTemperatureReadout
  have hone := _figure.oneHundredTemperatureReadout
  norm_num [temperatureInCelsius] at hzero hone
  have hlaw := _laws.thermalEnergyDifferenceLaw
    (setup.graph.temperatureAt .zeroCelsius)
    (setup.graph.temperatureAt .oneHundredCelsius)
  rw [_figure.oneHundredTemperatureEnergyReadout,
    _figure.zeroTemperatureEnergyReadout,
    _scenario.amountIsPointFourteenMoles] at hlaw
  have hcapacity :
      setup.constantVolumeMolarHeatCapacityJoulesPerMoleKelvin = 200 / 7 := by
    norm_num at hlaw ⊢
    nlinarith
  constructor
  · exact hcapacity
  constructor
  · rw [hcapacity]
    norm_num [Int.fract]
  · rw [hcapacity]
    norm_num [answerMolarHeatCapacityJoulesPerMoleKelvin, Int.fract]

end PhyXMiniProblems.ProblemPhyXMini0379
