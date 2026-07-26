import Mathlib
import Physlib.SpaceAndTime.Space.LengthUnit
import Physlib.SpaceAndTime.Time.TimeUnit
import Physlib.Thermodynamics.Temperature.Basic
import Physlib.Thermodynamics.Temperature.TemperatureUnits
import Physlib.Units.WithDim.Energy
import Physlib.Units.WithDim.Pressure

noncomputable section

namespace PhyXMiniProblems.ProblemPhyXMini0426

open Dimension

/-!
# Power output from a triangular pressure--volume cycle

A heat engine containing a diatomic gas follows the clockwise cycle
`1 → 2 → 3 → 1` in the supplied pressure--volume raster.  Reading the image
itself gives the states

* state `1`: `(10 cm³, 0.5 atm)`,
* state `2`: `(40 cm³, 1.5 atm)`, and
* state `3`: `(40 cm³, 0.5 atm)`.

Thus the `2 → 3` leg is vertical at `40 cm³`.  This follows the primary image
rather than the inconsistent auxiliary caption, which says both that state 2
has volume `30 cm³` and that the `2 → 3` leg has constant volume.

Pressure, volume, temperature, work, frequency, and power are represented as
physical quantities.  Real numbers are used only for calibrated readouts,
dimensionless ratios, and displayed numerical answers.  The idealized exact
power is `4053 / 320 W = 12.665625 W`, so the recorded `13 W` answer is modeled
as a nearest-whole-watt display.

Assumption/target split:

* governing laws: triangular boundary work, shaft-to-cycle frequency coupling,
  and average power as work per cycle times cycle frequency;
* previous-part results: none;
* data and figure evidence: gas/device character, `20 °C`, `500 rpm`, the
  labeled raster axes, arrows, segment shapes, and plotted coordinates;
* target conclusions: the exact watt readout, nearest-watt result, and unique
  multiple-choice selection.
-/

/-! ## Dimensionful quantities and calibrated readouts -/

/-- A nonnegative physical volume, of dimension `length³`. -/
abbrev VolumeQuantity : Type :=
  Dimensionful (WithDim (L𝓭 * L𝓭 * L𝓭) NNReal)

/-- A nonnegative rotation or thermodynamic-cycle frequency. -/
abbrev FrequencyQuantity : Type :=
  Dimensionful (WithDim T𝓭⁻¹ NNReal)

/-- The physical dimension of power, `mass * length² / time³`. -/
def powerDimension : Dimension :=
  M𝓭 * L𝓭 * L𝓭 * T𝓭⁻¹ * T𝓭⁻¹ * T𝓭⁻¹

/-- A nonnegative engine power output, whose coherent SI unit is the watt. -/
abbrev PowerQuantity : Type :=
  Dimensionful (WithDim powerDimension NNReal)

/-- Read a physical pressure in coherent SI pascals. -/
def pressureInPascals (pressure : DimPressure) : ℝ :=
  (pressure UnitChoices.SI).val

/-- Read pressure in standard atmospheres. -/
def pressureInAtmospheres (pressure : DimPressure) : ℝ :=
  pressureInPascals pressure /
    pressureInPascals DimPressure.standardAtmosphere

/-- Read a physical volume using the cube of a selected length unit. -/
def volumeReadout (unit : LengthUnit) (volume : VolumeQuantity) : ℝ :=
  ((volume {UnitChoices.SI with length := unit}).val : ℝ)

/-- Read a physical volume in coherent SI cubic metres. -/
def volumeInCubicMeters (volume : VolumeQuantity) : ℝ :=
  volumeReadout LengthUnit.meters volume

/-- Read a physical volume in the cubic-centimetre unit printed in the raster. -/
def volumeInCubicCentimeters (volume : VolumeQuantity) : ℝ :=
  volumeReadout LengthUnit.centimeters volume

/-- Read signed work or energy in coherent SI joules. -/
def energyInJoules (energy : DimEnergy) : ℝ :=
  (energy UnitChoices.SI).val

/-- Read an inverse-time quantity using a selected time unit. -/
def frequencyReadout
    (unit : TimeUnit) (frequency : FrequencyQuantity) : ℝ :=
  ((frequency {UnitChoices.SI with time := unit}).val : ℝ)

/-- Cycles or revolutions per SI second. -/
def frequencyInHertz (frequency : FrequencyQuantity) : ℝ :=
  frequencyReadout TimeUnit.seconds frequency

/-- Cycles or revolutions per minute; for the shaft this is an rpm readout. -/
def frequencyPerMinute (frequency : FrequencyQuantity) : ℝ :=
  frequencyReadout TimeUnit.minutes frequency

/-- Read physical power in coherent SI watts. -/
def powerInWatts (power : PowerQuantity) : ℝ :=
  ((power UnitChoices.SI).val : ℝ)

/-- Read absolute temperature in kelvins from a zero-preserving storage unit. -/
def temperatureInKelvin
    (storageUnit : TemperatureUnit) (temperature : Temperature) : ℝ :=
  let unitRatio : NNReal := storageUnit / TemperatureUnit.kelvin
  temperature.toReal * (unitRatio : ℝ)

/-- Celsius is an affine readout of physical absolute temperature. -/
def temperatureInDegreesCelsius
    (storageUnit : TemperatureUnit) (temperature : Temperature) : ℝ :=
  temperatureInKelvin storageUnit temperature - (5463 / 20 : ℝ)

/-!
These three declarations are general unit-conversion facts.  They are not
assumptions about this engine's requested work, frequency, or power.
-/

lemma pressureInPascals_eq_atmospheres_mul_standardAtmosphere
    (pressure : DimPressure) :
    pressureInPascals pressure =
      pressureInAtmospheres pressure * 101325 := by
  have hStandardAtmosphere :
      pressureInPascals DimPressure.standardAtmosphere = 101325 := by
    norm_num [pressureInPascals, DimPressure.standardAtmosphere,
      CarriesDimension.toDimensionful_apply_apply]
  rw [pressureInAtmospheres, hStandardAtmosphere]
  ring

lemma volumeInCubicMeters_eq_cubicCentimeters_div_million
    (volume : VolumeQuantity) :
    volumeInCubicMeters volume =
      volumeInCubicCentimeters volume / 1000000 := by
  let meterUnits : UnitChoices :=
    {UnitChoices.SI with length := LengthUnit.meters}
  let centimeterUnits : UnitChoices :=
    {UnitChoices.SI with length := LengthUnit.centimeters}
  have hLengthScale :
      UnitChoices.dimScale meterUnits centimeterUnits L𝓭 = 100 := by
    apply NNReal.eq
    norm_num [meterUnits, centimeterUnits, UnitChoices.dimScale,
      UnitChoices.SI, Dimension.L𝓭, LengthUnit.centimeters,
      LengthUnit.meters, LengthUnit.scale, LengthUnit.div_eq_val]
    rfl
  have hVolumeScale :
      UnitChoices.dimScale meterUnits centimeterUnits (L𝓭 * L𝓭 * L𝓭) =
        1000000 := by
    simp only [map_mul, hLengthScale]
    norm_num
  unfold volumeInCubicMeters volumeInCubicCentimeters volumeReadout
  change ((volume meterUnits).val : ℝ) =
    ((volume centimeterUnits).val : ℝ) / 1000000
  rw [volume.property meterUnits centimeterUnits]
  change ((volume meterUnits).val : ℝ) =
    ((UnitChoices.dimScale meterUnits centimeterUnits (L𝓭 * L𝓭 * L𝓭) *
      (volume meterUnits).val : NNReal) : ℝ) / 1000000
  rw [hVolumeScale]
  norm_num

lemma frequencyInHertz_eq_perMinute_div_sixty
    (frequency : FrequencyQuantity) :
    frequencyInHertz frequency = frequencyPerMinute frequency / 60 := by
  have hPerMinute :
      frequencyPerMinute frequency = 60 * frequencyInHertz frequency := by
    have hChange := congrArg (fun value => ((value.val : NNReal) : ℝ))
      (frequency.property UnitChoices.SI
        {UnitChoices.SI with time := TimeUnit.minutes})
    norm_num [frequencyInHertz, frequencyPerMinute, frequencyReadout,
      UnitChoices.dimScale, TimeUnit.minutes, TimeUnit.seconds, TimeUnit.scale,
      TimeUnit.div_eq_val, NNReal.rpow_neg_one, NNReal.smul_def,
      smul_eq_mul] at hChange ⊢
    rw [hChange]
    congr 1
    change (1 / 60 : ℝ)⁻¹ = 60
    norm_num
  rw [hPerMinute]
  ring

/-! ## Cycle states, legs, and primary-figure labels -/

/-- The three numbered thermodynamic equilibrium states in the raster. -/
inductive CycleState where
  | state1
  | state2
  | state3
  deriving DecidableEq, Fintype, Repr

/-- The three directed legs of the closed cycle. -/
inductive CycleLeg where
  | oneToTwo
  | twoToThree
  | threeToOne
  deriving DecidableEq, Fintype, Repr

/-- Initial state of a directed cycle leg. -/
def CycleLeg.initialState : CycleLeg → CycleState
  | .oneToTwo => .state1
  | .twoToThree => .state2
  | .threeToOne => .state3

/-- Final state of a directed cycle leg. -/
def CycleLeg.finalState : CycleLeg → CycleState
  | .oneToTwo => .state2
  | .twoToThree => .state3
  | .threeToOne => .state1

/-- A physical equilibrium state of the working gas. -/
structure ThermodynamicStateData where
  pressure : DimPressure
  volume : VolumeQuantity
  absoluteTemperature : Temperature

/-- Horizontal or vertical orientation of a displayed axis. -/
inductive FigureAxis where
  | horizontal
  | vertical
  deriving DecidableEq, Fintype, Repr

/-- Physical quantity named on a displayed axis. -/
inductive FigureAxisQuantity where
  | volumeV
  | pressureP
  deriving DecidableEq, Repr

/-- Unit text printed beside a displayed axis. -/
inductive FigureAxisUnit where
  | cubicCentimeter
  | atmosphere
  deriving DecidableEq, Repr

/-- Geometric shape and direction of a straight segment in the raster. -/
inductive PVSegmentShape where
  | risingDiagonal
  | verticalDownward
  | horizontalLeftward
  deriving DecidableEq, Repr

/--
Primary-image evidence, including axes, ticks, labels, plotted physical
coordinates, segment geometry, and arrow endpoints.
-/
structure PressureVolumeFigure where
  axisQuantity : FigureAxis → FigureAxisQuantity
  axisUnit : FigureAxis → FigureAxisUnit
  printedTickReadouts : FigureAxis → List ℝ
  statePointShown : CycleState → Bool
  stateLabelShown : CycleState → Bool
  plottedPressure : CycleState → DimPressure
  plottedVolume : CycleState → VolumeQuantity
  segmentShown : CycleLeg → Bool
  segmentShape : CycleLeg → PVSegmentShape
  arrowStart : CycleLeg → CycleState
  arrowEnd : CycleLeg → CycleState

/-! ## Heat-engine model -/

/-- Molecular character of the gas stated in the prose. -/
inductive WorkingGasModel where
  | diatomicGas
  | other
  deriving DecidableEq, Repr

/-- Thermodynamic role of the cyclic device. -/
inductive EngineModel where
  | heatEngine
  | other
  deriving DecidableEq, Repr

/-- Regime in which the plotted path supports boundary-work area. -/
inductive ProcessRegime where
  | quasistaticEquilibriumCycle
  | other
  deriving DecidableEq, Repr

/-- Sign convention for the positive clockwise-cycle work. -/
inductive WorkSignConvention where
  | positiveWhenDoneByGas
  | positiveWhenDoneOnGas
  deriving DecidableEq, Repr

/--
Independent physical objects and observables of the engine.  Shaft frequency
and thermodynamic-cycle frequency are kept separate, making their coupling an
explicit law rather than a hidden definition.
-/
structure DiatomicHeatEngineSetup where
  engineModel : EngineModel
  workingGasModel : WorkingGasModel
  processRegime : ProcessRegime
  workSignConvention : WorkSignConvention
  temperatureStorageUnit : TemperatureUnit
  stateAt : CycleState → ThermodynamicStateData
  figure : PressureVolumeFigure
  netWorkDoneByGasPerCycle : DimEnergy
  shaftRotationFrequency : FrequencyQuantity
  thermodynamicCycleFrequency : FrequencyQuantity
  cyclesPerShaftRevolution : ℝ
  averagePowerOutput : PowerQuantity

/-! ## Scenario, operating data, and primary-figure evidence -/

/-- Qualitative physical interpretation stated or implied by the scenario. -/
structure MatchesDiatomicHeatEngineScenario
    (setup : DiatomicHeatEngineSetup) : Prop where
  deviceIsHeatEngine : setup.engineModel = .heatEngine
  gasIsDiatomic : setup.workingGasModel = .diatomicGas
  cycleIsQuasistatic : setup.processRegime = .quasistaticEquilibriumCycle
  clockwiseWorkIsPositive :
    setup.workSignConvention = .positiveWhenDoneByGas
  absoluteTemperatureStoredInKelvin :
    setup.temperatureStorageUnit = TemperatureUnit.kelvin

/--
Numerical prose data.  The one-cycle-per-revolution field states the textbook
coupling needed to turn shaft rpm into traversals of the displayed cycle.
It contains no work or power answer.
-/
structure MatchesProblemOperatingData
    (setup : DiatomicHeatEngineSetup) : Prop where
  state1TemperatureCelsius :
    temperatureInDegreesCelsius setup.temperatureStorageUnit
      (setup.stateAt .state1).absoluteTemperature = 20
  shaftSpeedRotationsPerMinute :
    frequencyPerMinute setup.shaftRotationFrequency = 500
  oneThermodynamicCyclePerShaftRevolution :
    setup.cyclesPerShaftRevolution = 1

/--
Exact evidence from the primary raster.  In particular, state 2 is at
`40 cm³`, so the `2 → 3` segment really is vertical.
-/
structure MatchesSuppliedPressureVolumeFigure
    (setup : DiatomicHeatEngineSetup) : Prop where
  horizontalAxisIsVolume :
    setup.figure.axisQuantity .horizontal = .volumeV
  verticalAxisIsPressure :
    setup.figure.axisQuantity .vertical = .pressureP
  horizontalAxisUsesCubicCentimeters :
    setup.figure.axisUnit .horizontal = .cubicCentimeter
  verticalAxisUsesAtmospheres :
    setup.figure.axisUnit .vertical = .atmosphere
  horizontalTickReadouts :
    setup.figure.printedTickReadouts .horizontal = [0, 10, 20, 30, 40]
  verticalTickReadouts :
    setup.figure.printedTickReadouts .vertical = [0, 1 / 2, 1, 3 / 2]
  everyStatePointShown :
    ∀ state, setup.figure.statePointShown state = true
  everyStateLabelShown :
    ∀ state, setup.figure.stateLabelShown state = true
  everySegmentShown :
    ∀ leg, setup.figure.segmentShown leg = true
  arrowsFollowCycleOrder : ∀ leg,
    setup.figure.arrowStart leg = leg.initialState ∧
      setup.figure.arrowEnd leg = leg.finalState
  oneToTwoIsRisingDiagonal :
    setup.figure.segmentShape .oneToTwo = .risingDiagonal
  twoToThreeIsVerticalDownward :
    setup.figure.segmentShape .twoToThree = .verticalDownward
  threeToOneIsHorizontalLeftward :
    setup.figure.segmentShape .threeToOne = .horizontalLeftward
  plottedCoordinatesArePhysicalStates : ∀ state,
    setup.figure.plottedPressure state = (setup.stateAt state).pressure ∧
      setup.figure.plottedVolume state = (setup.stateAt state).volume
  state1PressureAtmospheres :
    pressureInAtmospheres (setup.figure.plottedPressure .state1) = 1 / 2
  state1VolumeCubicCentimeters :
    volumeInCubicCentimeters (setup.figure.plottedVolume .state1) = 10
  state2PressureAtmospheres :
    pressureInAtmospheres (setup.figure.plottedPressure .state2) = 3 / 2
  state2VolumeCubicCentimeters :
    volumeInCubicCentimeters (setup.figure.plottedVolume .state2) = 40
  state3PressureAtmospheres :
    pressureInAtmospheres (setup.figure.plottedPressure .state3) = 1 / 2
  state3VolumeCubicCentimeters :
    volumeInCubicCentimeters (setup.figure.plottedVolume .state3) = 40

/-- Positivity and nondegeneracy conditions for the physical cycle. -/
structure HasPhysicalHeatEngineParameters
    (setup : DiatomicHeatEngineSetup) : Prop where
  everyPressurePositive : ∀ state,
    0 < pressureInPascals (setup.stateAt state).pressure
  everyVolumePositive : ∀ state,
    0 < volumeInCubicMeters (setup.stateAt state).volume
  state1AbsoluteTemperaturePositive :
    0 < temperatureInKelvin setup.temperatureStorageUnit
      (setup.stateAt .state1).absoluteTemperature
  shaftRotationFrequencyPositive :
    0 < frequencyInHertz setup.shaftRotationFrequency
  cycleFrequencyPositive :
    0 < frequencyInHertz setup.thermodynamicCycleFrequency
  cyclesPerRevolutionPositive :
    0 < setup.cyclesPerShaftRevolution
  clockwiseTriangleHasPositiveWidth :
    volumeInCubicMeters (setup.stateAt .state1).volume <
      volumeInCubicMeters (setup.stateAt .state3).volume
  clockwiseTriangleHasPositiveHeight :
    pressureInPascals (setup.stateAt .state1).pressure <
      pressureInPascals (setup.stateAt .state2).pressure

/-! ## Governing laws -/

/--
The governing relations used by the calculation.  These relate independent
physical fields and contain neither the exact requested output, its rounded
display, nor an answer-choice selection.
-/
structure SatisfiesTriangularHeatEngineLaws
    (setup : DiatomicHeatEngineSetup) : Prop where
  clockwiseTriangleBoundaryWork :
    energyInJoules setup.netWorkDoneByGasPerCycle =
      (1 / 2 : ℝ) *
        (volumeInCubicMeters (setup.stateAt .state3).volume -
          volumeInCubicMeters (setup.stateAt .state1).volume) *
        (pressureInPascals (setup.stateAt .state2).pressure -
          pressureInPascals (setup.stateAt .state1).pressure)
  shaftRateDeterminesCycleRate :
    frequencyInHertz setup.thermodynamicCycleFrequency =
      setup.cyclesPerShaftRevolution *
        frequencyPerMinute setup.shaftRotationFrequency / 60
  averagePowerIsWorkPerCycleTimesCycleRate :
    powerInWatts setup.averagePowerOutput =
      energyInJoules setup.netWorkDoneByGasPerCycle *
        frequencyInHertz setup.thermodynamicCycleFrequency

/-! ## Derived quantities and the displayed-answer target -/

/-- Labels of the four displayed answers. -/
inductive AnswerChoice where
  | A
  | B
  | C
  | D
  deriving DecidableEq, Fintype, Repr

/-- Watt value printed beside each answer label. -/
def displayedPowerInWatts : AnswerChoice → ℝ
  | .A => 13 / 100
  | .B => 38 / 25
  | .C => 26
  | .D => 13

/-- Dataset answer-label metadata; it does not determine the physical output. -/
def recordedDatasetAnswer : AnswerChoice := .D

/-- A physical watt readout rounds to a stated nearest whole watt. -/
def RoundsToNearestWatt (power : PowerQuantity) (displayed : ℝ) : Prop :=
  |powerInWatts power - displayed| < (1 / 2 : ℝ)

/-- The selected displayed value is strictly closer than every alternative. -/
def IsUniqueClosestDisplayedPower
    (power : PowerQuantity) (choice : AnswerChoice) : Prop :=
  ∀ other, other ≠ choice →
    |powerInWatts power - displayedPowerInWatts choice| <
      |powerInWatts power - displayedPowerInWatts other|

/--
The clockwise triangular area gives `12159 / 8000 J` per cycle.  This is a
derived conclusion from figure readouts, unit conversion, and boundary work.
-/
lemma netWorkDoneByGasPerCycle_eq
    (setup : DiatomicHeatEngineSetup)
    (hFigure : MatchesSuppliedPressureVolumeFigure setup)
    (hPhysical : HasPhysicalHeatEngineParameters setup)
    (hLaws : SatisfiesTriangularHeatEngineLaws setup) :
    energyInJoules setup.netWorkDoneByGasPerCycle = 12159 / 8000 := by
  have hState1Pressure :
      pressureInAtmospheres (setup.stateAt .state1).pressure = 1 / 2 := by
    rw [← (hFigure.plottedCoordinatesArePhysicalStates .state1).1]
    exact hFigure.state1PressureAtmospheres
  have hState2Pressure :
      pressureInAtmospheres (setup.stateAt .state2).pressure = 3 / 2 := by
    rw [← (hFigure.plottedCoordinatesArePhysicalStates .state2).1]
    exact hFigure.state2PressureAtmospheres
  have hState1Volume :
      volumeInCubicCentimeters (setup.stateAt .state1).volume = 10 := by
    rw [← (hFigure.plottedCoordinatesArePhysicalStates .state1).2]
    exact hFigure.state1VolumeCubicCentimeters
  have hState3Volume :
      volumeInCubicCentimeters (setup.stateAt .state3).volume = 40 := by
    rw [← (hFigure.plottedCoordinatesArePhysicalStates .state3).2]
    exact hFigure.state3VolumeCubicCentimeters
  have hState1PressureSI :=
    pressureInPascals_eq_atmospheres_mul_standardAtmosphere
      (setup.stateAt .state1).pressure
  have hState2PressureSI :=
    pressureInPascals_eq_atmospheres_mul_standardAtmosphere
      (setup.stateAt .state2).pressure
  have hState1VolumeSI :=
    volumeInCubicMeters_eq_cubicCentimeters_div_million
      (setup.stateAt .state1).volume
  have hState3VolumeSI :=
    volumeInCubicMeters_eq_cubicCentimeters_div_million
      (setup.stateAt .state3).volume
  rw [hState1Pressure] at hState1PressureSI
  rw [hState2Pressure] at hState2PressureSI
  rw [hState1Volume] at hState1VolumeSI
  rw [hState3Volume] at hState3VolumeSI
  have hWork := hLaws.clockwiseTriangleBoundaryWork
  rw [hState1PressureSI, hState2PressureSI,
    hState1VolumeSI, hState3VolumeSI] at hWork
  norm_num at hWork ⊢
  exact hWork

/-- At `500 rpm`, one cycle per revolution gives `25 / 3 Hz`. -/
lemma thermodynamicCycleFrequencyInHertz_eq
    (setup : DiatomicHeatEngineSetup)
    (hData : MatchesProblemOperatingData setup)
    (hLaws : SatisfiesTriangularHeatEngineLaws setup) :
    frequencyInHertz setup.thermodynamicCycleFrequency = 25 / 3 := by
  rw [hLaws.shaftRateDeterminesCycleRate,
    hData.oneThermodynamicCyclePerShaftRevolution,
    hData.shaftSpeedRotationsPerMinute]
  norm_num

/--
The idealized average output is exactly `4053 / 320 W = 12.665625 W`, hence
it rounds to `13 W` and uniquely selects answer D.

This declaration formalizes `thm:physics:phyx_mini_0426:target`.  Its exact
output, rounding conclusion, and answer selection occur only in the theorem
conclusion, never in a scenario, data, figure, physicality, or law field.
-/
theorem problem_phyx_mini_0426
    (setup : DiatomicHeatEngineSetup)
    (hScenario : MatchesDiatomicHeatEngineScenario setup)
    (hData : MatchesProblemOperatingData setup)
    (hFigure : MatchesSuppliedPressureVolumeFigure setup)
    (hPhysical : HasPhysicalHeatEngineParameters setup)
    (hLaws : SatisfiesTriangularHeatEngineLaws setup) :
    powerInWatts setup.averagePowerOutput = 4053 / 320 ∧
      RoundsToNearestWatt setup.averagePowerOutput 13 ∧
      IsUniqueClosestDisplayedPower setup.averagePowerOutput .D := by
  have hWork := netWorkDoneByGasPerCycle_eq setup hFigure hPhysical hLaws
  have hCycleRate := thermodynamicCycleFrequencyInHertz_eq setup hData hLaws
  have hPower := hLaws.averagePowerIsWorkPerCycleTimesCycleRate
  rw [hWork, hCycleRate] at hPower
  norm_num at hPower
  refine ⟨hPower, ?_, ?_⟩
  · norm_num [RoundsToNearestWatt, hPower, abs_of_nonpos]
  · unfold IsUniqueClosestDisplayedPower
    intro other hOther
    rw [hPower]
    cases other
    · norm_num [displayedPowerInWatts, abs_of_nonneg, abs_of_nonpos]
    · norm_num [displayedPowerInWatts, abs_of_nonneg, abs_of_nonpos]
    · norm_num [displayedPowerInWatts, abs_of_nonneg, abs_of_nonpos]
    · exact (hOther rfl).elim

end PhyXMiniProblems.ProblemPhyXMini0426
