import Mathlib
import Physlib.Thermodynamics.Temperature.Basic
import Physlib.Thermodynamics.Temperature.TemperatureUnits
import Physlib.Units.WithDim.Energy
import Physlib.Units.WithDim.Pressure

noncomputable section

namespace PhyXMiniProblems.ProblemPhyXMini0355

open Dimension

/-!
# Power output of an ideal Stirling engine

The primary `p`--`V` raster shows the directed cycle

`a → b → c → d → a`.

In that image, `a → b` is the lower isothermal compression, `b → c` is
vertical isochoric heating, `c → d` is the upper isothermal expansion, and
`d → a` is vertical isochoric cooling. This agrees with the process order in
the scenario text. The auxiliary caption shifts the process names by one leg,
so this formalization follows the primary image as requested by the blueprint.

Pressure and work use Physlib's dimensionful types, and temperature uses
Physlib's absolute `Temperature`. Volume, cycle frequency, and power are built
with Physlib's generic `Dimensionful` interface. Real numbers occur only as
calibrated unit readouts, dimensionless ratios, qualitative figure
coordinates, or displayed answer values.
-/

/-! ## Dimensionful physical quantities and calibrated readouts -/

/-- A nonnegative physical volume, of dimension `length^3`. -/
abbrev VolumeQuantity : Type :=
  Dimensionful (WithDim (L𝓭 * L𝓭 * L𝓭) NNReal)

/-- A nonnegative cycle frequency, of dimension `time⁻¹`. -/
abbrev FrequencyQuantity : Type :=
  Dimensionful (WithDim T𝓭⁻¹ NNReal)

/-- The physical dimension `mass * length^2 / time^3` of power. -/
def powerDimension : Dimension :=
  M𝓭 * L𝓭 * L𝓭 * T𝓭⁻¹ * T𝓭⁻¹ * T𝓭⁻¹

/-- A nonnegative physical power output, whose SI unit is the watt. -/
abbrev PowerQuantity : Type :=
  Dimensionful (WithDim powerDimension NNReal)

/-!
Physlib currently has no amount-of-substance dimension. This abstract carrier
and its calibrated mole readout preserve the physical role of the gas amount
without identifying the quantity itself with a real number.
-/
structure AmountOfSubstanceScale where
  Quantity : Type
  inMoles : Quantity → ℝ

/-- Read a physical pressure in SI pascals. -/
def pressureInPascals (pressure : DimPressure) : ℝ :=
  (pressure UnitChoices.SI).val

/-- Read a physical volume in SI cubic metres. -/
def volumeInCubicMeters (volume : VolumeQuantity) : ℝ :=
  ((volume UnitChoices.SI).val : ℝ)

/-- Read physical work or energy in SI joules. -/
def energyInJoules (energy : DimEnergy) : ℝ :=
  (energy UnitChoices.SI).val

/-- Read a physical operating frequency in cycles per SI second (hertz). -/
def frequencyInHertz (frequency : FrequencyQuantity) : ℝ :=
  ((frequency {UnitChoices.SI with time := TimeUnit.seconds}).val : ℝ)

/-- Read a physical power in SI watts. -/
def powerInWatts (power : PowerQuantity) : ℝ :=
  ((power UnitChoices.SI).val : ℝ)

/-- Read a physical power in kilowatts. -/
def powerInKilowatts (power : PowerQuantity) : ℝ :=
  powerInWatts power / 1000

/-!
The scenario below fixes Physlib's arbitrary absolute-temperature scale to
kelvin. Under that calibration, `Temperature.toReal` is the kelvin readout.
-/
def temperatureInKelvin (temperature : Temperature) : ℝ :=
  Temperature.toReal temperature

/-- Celsius readout obtained from an absolute kelvin readout. -/
def temperatureInCelsius (temperature : Temperature) : ℝ :=
  temperatureInKelvin temperature - (27315 / 100 : ℝ)

/-!
The SI readout of the universal molar gas constant, in joules per mole-kelvin.
The rational value `8.314` is the precision used by the displayed calculation.
-/
def universalMolarGasConstant_J_per_mol_K : ℝ :=
  8314 / 1000

/-! ## Cycle states, directed legs, and primary-figure labels -/

/-- The four equilibrium states labelled in the supplied raster. -/
inductive CycleState where
  | a
  | b
  | c
  | d
  deriving DecidableEq, Repr

/-- The four directed legs shown by the arrows in the supplied raster. -/
inductive CycleLeg where
  | ab
  | bc
  | cd
  | da
  deriving DecidableEq, Repr

/-- Initial state of each directed cycle leg. -/
def CycleLeg.initialState : CycleLeg → CycleState
  | .ab => .a
  | .bc => .b
  | .cd => .c
  | .da => .d

/-- Final state of each directed cycle leg. -/
def CycleLeg.finalState : CycleLeg → CycleState
  | .ab => .b
  | .bc => .c
  | .cd => .d
  | .da => .a

/-- Physical role of a leg of the ideal Stirling cycle. -/
inductive ProcessKind where
  | isothermalCompression
  | isochoricHeating
  | isothermalExpansion
  | isochoricCooling
  deriving DecidableEq, Repr

/-- Whether a process kind is one of the two isothermal legs. -/
def ProcessKind.IsIsothermal : ProcessKind → Prop
  | .isothermalCompression => True
  | .isothermalExpansion => True
  | .isochoricHeating => False
  | .isochoricCooling => False

/-- Whether a process kind is one of the two constant-volume legs. -/
def ProcessKind.IsIsochoric : ProcessKind → Prop
  | .isothermalCompression => False
  | .isothermalExpansion => False
  | .isochoricHeating => True
  | .isochoricCooling => True

/-- The physical quantities assigned to the two plotted axes. -/
inductive FigureAxisQuantity where
  | pressureP
  | volumeV
  deriving DecidableEq, Repr

/-- Horizontal or vertical orientation of a plotted axis. -/
inductive FigureAxis where
  | horizontal
  | vertical
  deriving DecidableEq, Repr

/-- Qualitative geometric shape of a process segment in the raster. -/
inductive PVSegmentShape where
  | curved
  | vertical
  deriving DecidableEq, Repr

/-- Thermodynamic model of the working gas. -/
inductive GasModel where
  | idealGas
  | nonidealGas
  deriving DecidableEq, Repr

/-- Working substance named in the question. -/
inductive WorkingSubstance where
  | helium
  | other
  deriving DecidableEq, Repr

/-- Engine idealization stated in the problem. -/
inductive EngineModel where
  | idealStirling
  | nonidealStirling
  deriving DecidableEq, Repr

/-- Physical data at one equilibrium state on the `p`--`V` cycle. -/
structure ThermodynamicStateData where
  pressure : DimPressure
  volume : VolumeQuantity
  temperature : Temperature

/-!
Qualitative evidence retained from the primary image. The coordinate functions
record relative placement in the drawing; the dimensionful state quantities
are stored independently in `StirlingEngineSetup`.
-/
structure PressureVolumeFigure where
  axisQuantity : FigureAxis → FigureAxisQuantity
  originLabelOShown : Bool
  statePointShown : CycleState → Bool
  stateLabelShown : CycleState → Bool
  processSegmentShown : CycleLeg → Bool
  arrowStart : CycleLeg → CycleState
  arrowEnd : CycleLeg → CycleState
  segmentShape : CycleLeg → PVSegmentShape
  horizontalCoordinate : CycleState → ℝ
  verticalCoordinate : CycleState → ℝ

/-!
Independent physical quantities and observables of the engine. In particular,
neither `netWorkDoneByGasPerCycle` nor `powerOutput` is defined from the desired
answer; governing laws below relate them to the cycle data.
-/
structure StirlingEngineSetup (amountScale : AmountOfSubstanceScale) where
  engineModel : EngineModel
  gasModel : GasModel
  workingSubstance : WorkingSubstance
  temperatureUnit : TemperatureUnit
  gasAmount : amountScale.Quantity
  coldReservoirTemperature : Temperature
  hotReservoirTemperature : Temperature
  stateAt : CycleState → ThermodynamicStateData
  processKind : CycleLeg → ProcessKind
  workDoneByGasOnLeg : CycleLeg → DimEnergy
  netWorkDoneByGasPerCycle : DimEnergy
  operatingFrequency : FrequencyQuantity
  powerOutput : PowerQuantity
  figure : PressureVolumeFigure

/-! ## Scenario, figure/data readouts, and governing laws -/

/-!
The ideal Stirling interpretation from the prose. It identifies the working
substance, temperature scale, four process roles, and reservoir contact. It
contains no work or power conclusion.
-/
structure MatchesIdealStirlingScenario
    {amountScale : AmountOfSubstanceScale}
    (setup : StirlingEngineSetup amountScale) : Prop where
  engineIsIdealStirling : setup.engineModel = .idealStirling
  gasIsIdeal : setup.gasModel = .idealGas
  gasIsHelium : setup.workingSubstance = .helium
  absoluteTemperatureUnitIsKelvin :
    setup.temperatureUnit = TemperatureUnit.kelvin
  legABIsIsothermalCompression :
    setup.processKind .ab = .isothermalCompression
  legBCIsIsochoricHeating : setup.processKind .bc = .isochoricHeating
  legCDIsIsothermalExpansion : setup.processKind .cd = .isothermalExpansion
  legDAIsIsochoricCooling : setup.processKind .da = .isochoricCooling
  coldIsothermTemperatures :
    (setup.stateAt .a).temperature = setup.coldReservoirTemperature ∧
      (setup.stateAt .b).temperature = setup.coldReservoirTemperature
  hotIsothermTemperatures :
    (setup.stateAt .c).temperature = setup.hotReservoirTemperature ∧
      (setup.stateAt .d).temperature = setup.hotReservoirTemperature

/-!
Primary-image evidence. The raster makes `a → b` and `c → d` curved and
`b → c` and `d → a` vertical. It puts `b,c` in the left column and `a,d` in
the right column.
-/
structure MatchesSuppliedPressureVolumeFigure
    {amountScale : AmountOfSubstanceScale}
    (setup : StirlingEngineSetup amountScale) : Prop where
  horizontalAxisIsVolume :
    setup.figure.axisQuantity .horizontal = .volumeV
  verticalAxisIsPressure :
    setup.figure.axisQuantity .vertical = .pressureP
  originLabelShown : setup.figure.originLabelOShown = true
  everyStatePointShown :
    ∀ state : CycleState, setup.figure.statePointShown state = true
  everyStateLabelShown :
    ∀ state : CycleState, setup.figure.stateLabelShown state = true
  everyProcessSegmentShown :
    ∀ leg : CycleLeg, setup.figure.processSegmentShown leg = true
  arrowsFollowCycleOrder : ∀ leg : CycleLeg,
    setup.figure.arrowStart leg = leg.initialState ∧
      setup.figure.arrowEnd leg = leg.finalState
  legABIsCurved : setup.figure.segmentShape .ab = .curved
  legBCIsVertical : setup.figure.segmentShape .bc = .vertical
  legCDIsCurved : setup.figure.segmentShape .cd = .curved
  legDAIsVertical : setup.figure.segmentShape .da = .vertical
  leftColumnInFigure :
    setup.figure.horizontalCoordinate .b =
      setup.figure.horizontalCoordinate .c
  rightColumnInFigure :
    setup.figure.horizontalCoordinate .a =
      setup.figure.horizontalCoordinate .d
  leftColumnPrecedesRightColumn :
    setup.figure.horizontalCoordinate .b <
      setup.figure.horizontalCoordinate .a
  pointCAbovePointB :
    setup.figure.verticalCoordinate .b < setup.figure.verticalCoordinate .c
  pointDAbovePointA :
    setup.figure.verticalCoordinate .a < setup.figure.verticalCoordinate .d
  leftStatesHaveEqualVolume :
    (setup.stateAt .b).volume = (setup.stateAt .c).volume
  rightStatesHaveEqualVolume :
    (setup.stateAt .a).volume = (setup.stateAt .d).volume
  rightVolumeIsLarger :
    volumeInCubicMeters (setup.stateAt .b).volume <
      volumeInCubicMeters (setup.stateAt .a).volume
  pressureRisesFromBToC :
    pressureInPascals (setup.stateAt .b).pressure <
      pressureInPascals (setup.stateAt .c).pressure
  pressureFallsFromDToA :
    pressureInPascals (setup.stateAt .a).pressure <
      pressureInPascals (setup.stateAt .d).pressure

/-- The dimensionless maximum-to-minimum volume ratio of the engine. -/
def compressionRatio
    {amountScale : AmountOfSubstanceScale}
    (setup : StirlingEngineSetup amountScale) : ℝ :=
  volumeInCubicMeters (setup.stateAt .a).volume /
    volumeInCubicMeters (setup.stateAt .b).volume

/-!
Numerical readouts supplied in the question: one mole of helium, compression
ratio ten, reservoir temperatures `100 °C` and `20 °C`, and operation at
`100 Hz`. There is no work or power value in this record.
-/
structure MatchesProblemReadouts
    {amountScale : AmountOfSubstanceScale}
    (setup : StirlingEngineSetup amountScale) : Prop where
  gasAmountMoles : amountScale.inMoles setup.gasAmount = 1
  compressionRatioIsTen : compressionRatio setup = 10
  hotReservoirCelsius :
    temperatureInCelsius setup.hotReservoirTemperature = 100
  coldReservoirCelsius :
    temperatureInCelsius setup.coldReservoirTemperature = 20
  operatingFrequencyHertz :
    frequencyInHertz setup.operatingFrequency = 100

/-- Positivity and nondegeneracy conditions for the physical setup. -/
structure HasPhysicalStirlingParameters
    {amountScale : AmountOfSubstanceScale}
    (setup : StirlingEngineSetup amountScale) : Prop where
  amountPositive : 0 < amountScale.inMoles setup.gasAmount
  everyPressurePositive : ∀ state : CycleState,
    0 < pressureInPascals (setup.stateAt state).pressure
  everyVolumePositive : ∀ state : CycleState,
    0 < volumeInCubicMeters (setup.stateAt state).volume
  coldTemperaturePositive :
    0 < temperatureInKelvin setup.coldReservoirTemperature
  hotTemperatureExceedsCold :
    temperatureInKelvin setup.coldReservoirTemperature <
      temperatureInKelvin setup.hotReservoirTemperature
  frequencyPositive : 0 < frequencyInHertz setup.operatingFrequency
  compressionRatioExceedsOne : 1 < compressionRatio setup

/-!
Governing laws for the calculation: the ideal-gas equation of state,
quasistatic isothermal boundary work, zero isochoric boundary work, additivity
of the four leg works, and average power as work per cycle times cycles per
second. These fields contain neither the requested `153 kW` conclusion nor an
answer-choice selection.
-/
structure SatisfiesIdealGasStirlingLaws
    {amountScale : AmountOfSubstanceScale}
    (setup : StirlingEngineSetup amountScale) : Prop where
  idealGasEquationOfState : ∀ state : CycleState,
    pressureInPascals (setup.stateAt state).pressure *
        volumeInCubicMeters (setup.stateAt state).volume =
      amountScale.inMoles setup.gasAmount *
        universalMolarGasConstant_J_per_mol_K *
          temperatureInKelvin (setup.stateAt state).temperature
  isothermalBoundaryWork : ∀ leg : CycleLeg,
    (setup.processKind leg).IsIsothermal →
      energyInJoules (setup.workDoneByGasOnLeg leg) =
        amountScale.inMoles setup.gasAmount *
          universalMolarGasConstant_J_per_mol_K *
            temperatureInKelvin (setup.stateAt leg.initialState).temperature *
              Real.log
                (volumeInCubicMeters (setup.stateAt leg.finalState).volume /
                  volumeInCubicMeters (setup.stateAt leg.initialState).volume)
  isochoricBoundaryWork : ∀ leg : CycleLeg,
    (setup.processKind leg).IsIsochoric →
      energyInJoules (setup.workDoneByGasOnLeg leg) = 0
  cycleWorkIsAdditive :
    energyInJoules setup.netWorkDoneByGasPerCycle =
      energyInJoules (setup.workDoneByGasOnLeg .ab) +
        energyInJoules (setup.workDoneByGasOnLeg .bc) +
          energyInJoules (setup.workDoneByGasOnLeg .cd) +
            energyInJoules (setup.workDoneByGasOnLeg .da)
  averagePowerIsCycleWorkTimesFrequency :
    powerInWatts setup.powerOutput =
      frequencyInHertz setup.operatingFrequency *
        energyInJoules setup.netWorkDoneByGasPerCycle

/-! ## Derived formula and displayed multiple-choice conclusion -/

/-!
The ideal Stirling power formula in calibrated physical readouts. This is not
the definition of `setup.powerOutput`; the theorem must relate that independent
physical observable to this formula using the governing laws.
-/
def idealStirlingPowerFormulaWatts
    {amountScale : AmountOfSubstanceScale}
    (setup : StirlingEngineSetup amountScale) : ℝ :=
  frequencyInHertz setup.operatingFrequency *
    amountScale.inMoles setup.gasAmount *
      universalMolarGasConstant_J_per_mol_K *
        (temperatureInKelvin setup.hotReservoirTemperature -
          temperatureInKelvin setup.coldReservoirTemperature) *
            Real.log (compressionRatio setup)

/-- Labels of the four displayed answers in the source. -/
inductive AnswerChoice where
  | A
  | B
  | C
  | D
  deriving DecidableEq, Repr

/-- Kilowatt value printed beside each displayed answer label. -/
def displayedPowerKilowatts : AnswerChoice → ℝ
  | .A => 203
  | .B => 153
  | .C => 156
  | .D => 143

/-- The dataset's recorded answer label, retained only as metadata. -/
def recordedDatasetAnswer : AnswerChoice := .B

/-- The physical power rounds to a displayed whole-kilowatt value. -/
def RoundsToDisplayedKilowatt
    {amountScale : AmountOfSubstanceScale}
    (setup : StirlingEngineSetup amountScale) (choice : AnswerChoice) : Prop :=
  |powerInKilowatts setup.powerOutput - displayedPowerKilowatts choice| <
    (1 / 2 : ℝ)

/-- The selected display is strictly closer than every alternative. -/
def IsUniqueClosestDisplayedPower
    {amountScale : AmountOfSubstanceScale}
    (setup : StirlingEngineSetup amountScale) (choice : AnswerChoice) : Prop :=
  ∀ other : AnswerChoice, other ≠ choice →
    |powerInKilowatts setup.powerOutput - displayedPowerKilowatts choice| <
      |powerInKilowatts setup.powerOutput - displayedPowerKilowatts other|

/-!
The net cycle work is the hot-isotherm work minus the cold-isotherm work:
`n R (T_H - T_C) log(CR)`.
-/
lemma netWorkPerCycle_eq_idealStirlingFormula
    {amountScale : AmountOfSubstanceScale}
    (setup : StirlingEngineSetup amountScale)
    (hScenario : MatchesIdealStirlingScenario setup)
    (hFigure : MatchesSuppliedPressureVolumeFigure setup)
    (hPhysical : HasPhysicalStirlingParameters setup)
    (hLaws : SatisfiesIdealGasStirlingLaws setup) :
    energyInJoules setup.netWorkDoneByGasPerCycle =
      amountScale.inMoles setup.gasAmount *
        universalMolarGasConstant_J_per_mol_K *
          (temperatureInKelvin setup.hotReservoirTemperature -
            temperatureInKelvin setup.coldReservoirTemperature) *
              Real.log (compressionRatio setup) := by
  have hABIsothermal : (setup.processKind .ab).IsIsothermal := by
    simp [ProcessKind.IsIsothermal, hScenario.legABIsIsothermalCompression]
  have hCDIsothermal : (setup.processKind .cd).IsIsothermal := by
    simp [ProcessKind.IsIsothermal, hScenario.legCDIsIsothermalExpansion]
  have hBCIsochoric : (setup.processKind .bc).IsIsochoric := by
    simp [ProcessKind.IsIsochoric, hScenario.legBCIsIsochoricHeating]
  have hDAIsochoric : (setup.processKind .da).IsIsochoric := by
    simp [ProcessKind.IsIsochoric, hScenario.legDAIsIsochoricCooling]
  have hAB :
      energyInJoules (setup.workDoneByGasOnLeg .ab) =
        amountScale.inMoles setup.gasAmount *
          universalMolarGasConstant_J_per_mol_K *
            temperatureInKelvin setup.coldReservoirTemperature *
              Real.log
                (volumeInCubicMeters (setup.stateAt .b).volume /
                  volumeInCubicMeters (setup.stateAt .a).volume) := by
    simpa [CycleLeg.initialState, CycleLeg.finalState,
      hScenario.coldIsothermTemperatures.1] using
        hLaws.isothermalBoundaryWork .ab hABIsothermal
  have hCD :
      energyInJoules (setup.workDoneByGasOnLeg .cd) =
        amountScale.inMoles setup.gasAmount *
          universalMolarGasConstant_J_per_mol_K *
            temperatureInKelvin setup.hotReservoirTemperature *
              Real.log
                (volumeInCubicMeters (setup.stateAt .a).volume /
                  volumeInCubicMeters (setup.stateAt .b).volume) := by
    simpa [CycleLeg.initialState, CycleLeg.finalState,
      hScenario.hotIsothermTemperatures.1,
      ← hFigure.leftStatesHaveEqualVolume,
      ← hFigure.rightStatesHaveEqualVolume] using
        hLaws.isothermalBoundaryWork .cd hCDIsothermal
  have hBC :
      energyInJoules (setup.workDoneByGasOnLeg .bc) = 0 :=
    hLaws.isochoricBoundaryWork .bc hBCIsochoric
  have hDA :
      energyInJoules (setup.workDoneByGasOnLeg .da) = 0 :=
    hLaws.isochoricBoundaryWork .da hDAIsochoric
  have hVolumeA :
      0 < volumeInCubicMeters (setup.stateAt .a).volume :=
    hPhysical.everyVolumePositive .a
  have hVolumeB :
      0 < volumeInCubicMeters (setup.stateAt .b).volume :=
    hPhysical.everyVolumePositive .b
  have hCompressionLog :
      Real.log
          (volumeInCubicMeters (setup.stateAt .b).volume /
            volumeInCubicMeters (setup.stateAt .a).volume) =
        -Real.log
          (volumeInCubicMeters (setup.stateAt .a).volume /
            volumeInCubicMeters (setup.stateAt .b).volume) := by
    rw [Real.log_div hVolumeB.ne' hVolumeA.ne',
      Real.log_div hVolumeA.ne' hVolumeB.ne']
    ring
  rw [hLaws.cycleWorkIsAdditive, hAB, hBC, hCD, hDA, hCompressionLog]
  simp only [add_zero]
  unfold compressionRatio
  ring

/-!
At one mole, `CR = 10`, `T_H - T_C = 80 K`, and `100 cycles/s`, the ideal
Stirling formula is approximately `153.15 kW`. Hence the physical output
rounds to the displayed `153 kW` and uniquely selects answer B.

This formalizes `thm:physics:phyx_mini_0355:target`. Neither the formula for
the independent power field, its rounding to `153 kW`, nor the selection of B
appears in a scenario, readout, figure, physicality, or governing-law field.
-/
theorem problem_phyx_mini_0355
    {amountScale : AmountOfSubstanceScale}
    (setup : StirlingEngineSetup amountScale)
    (hScenario : MatchesIdealStirlingScenario setup)
    (hReadouts : MatchesProblemReadouts setup)
    (hFigure : MatchesSuppliedPressureVolumeFigure setup)
    (hPhysical : HasPhysicalStirlingParameters setup)
    (hLaws : SatisfiesIdealGasStirlingLaws setup) :
    powerInWatts setup.powerOutput = idealStirlingPowerFormulaWatts setup ∧
      RoundsToDisplayedKilowatt setup .B ∧
      IsUniqueClosestDisplayedPower setup .B := by
  have hWorkFormula :=
    netWorkPerCycle_eq_idealStirlingFormula setup hScenario hFigure hPhysical hLaws
  have hPowerFormula :
      powerInWatts setup.powerOutput =
        idealStirlingPowerFormulaWatts setup := by
    rw [hLaws.averagePowerIsCycleWorkTimesFrequency, hWorkFormula]
    unfold idealStirlingPowerFormulaWatts
    ring
  have hHotReadout := hReadouts.hotReservoirCelsius
  have hColdReadout := hReadouts.coldReservoirCelsius
  unfold temperatureInCelsius at hHotReadout hColdReadout
  have hKelvinDifference :
      temperatureInKelvin setup.hotReservoirTemperature -
          temperatureInKelvin setup.coldReservoirTemperature =
        80 := by
    linarith
  have hPowerKilowatts :
      powerInKilowatts setup.powerOutput =
        (8314 / 125 : ℝ) * Real.log 10 := by
    unfold powerInKilowatts
    rw [hPowerFormula]
    unfold idealStirlingPowerFormulaWatts
    rw [hReadouts.operatingFrequencyHertz, hReadouts.gasAmountMoles,
      hKelvinDifference, hReadouts.compressionRatioIsTen]
    unfold universalMolarGasConstant_J_per_mol_K
    ring
  have hLogTen :
      Real.log (10 : ℝ) = Real.log 2 + Real.log 5 := by
    calc
      Real.log (10 : ℝ) = Real.log ((2 : ℝ) * 5) := by norm_num
      _ = Real.log 2 + Real.log 5 :=
        Real.log_mul (by norm_num) (by norm_num)
  have hLogTenLower : (23 / 10 : ℝ) < Real.log 10 := by
    rw [hLogTen]
    linarith [Real.log_two_gt_d9, Real.log_five_gt_d9]
  have hLogTenUpper : Real.log 10 < (2303 / 1000 : ℝ) := by
    rw [hLogTen]
    linarith [Real.log_two_lt_d9, Real.log_five_lt_d9]
  have hRounds : RoundsToDisplayedKilowatt setup .B := by
    unfold RoundsToDisplayedKilowatt
    simp only [displayedPowerKilowatts]
    rw [hPowerKilowatts, abs_lt]
    constructor <;> nlinarith
  have hRoundAbs :
      |powerInKilowatts setup.powerOutput - 153| < (1 / 2 : ℝ) := by
    simpa [RoundsToDisplayedKilowatt, displayedPowerKilowatts] using hRounds
  refine ⟨hPowerFormula, hRounds, ?_⟩
  unfold IsUniqueClosestDisplayedPower
  intro other hOther
  cases other with
  | A =>
      change
        |powerInKilowatts setup.powerOutput - 153| <
          |powerInKilowatts setup.powerOutput - 203|
      have hNonpositive :
          powerInKilowatts setup.powerOutput - 203 ≤ 0 := by
        linarith [(abs_lt.mp hRoundAbs).2]
      rw [abs_of_nonpos hNonpositive]
      linarith [(abs_lt.mp hRoundAbs).2]
  | B =>
      exact (hOther rfl).elim
  | C =>
      change
        |powerInKilowatts setup.powerOutput - 153| <
          |powerInKilowatts setup.powerOutput - 156|
      have hNonpositive :
          powerInKilowatts setup.powerOutput - 156 ≤ 0 := by
        linarith [(abs_lt.mp hRoundAbs).2]
      rw [abs_of_nonpos hNonpositive]
      linarith [(abs_lt.mp hRoundAbs).2]
  | D =>
      change
        |powerInKilowatts setup.powerOutput - 153| <
          |powerInKilowatts setup.powerOutput - 143|
      have hNonnegative :
          0 ≤ powerInKilowatts setup.powerOutput - 143 := by
        linarith [(abs_lt.mp hRoundAbs).1]
      rw [abs_of_nonneg hNonnegative]
      linarith [(abs_lt.mp hRoundAbs).1]

end PhyXMiniProblems.ProblemPhyXMini0355
