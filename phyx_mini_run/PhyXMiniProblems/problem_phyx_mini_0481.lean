import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Physlib.Thermodynamics.Temperature.Basic
import Physlib.Thermodynamics.Temperature.TemperatureUnits
import Physlib.Units.WithDim.Energy
import Physlib.Units.WithDim.Pressure

/- USER: The assigned source file did not exist when this autoformalization task began. -/

noncomputable section

namespace PhyXMiniProblems.ProblemPhyXMini0481

open Dimension

/-!
# Power input of a reversed-Brayton helium refrigerator

The primary pressure--volume bitmap shows the directed reversed-Brayton cycle

`4 → 3 → 2 → 1 → 4`.

The two curved arrows are the isentropic compression `4 → 3` and isentropic
expansion `2 → 1`.  The upper and lower horizontal legs are isobaric heat
exchange.  The upward `Q_H` arrow leaves the working gas on `3 → 2`, whereas
the upward `Q_C` arrow enters the gas on `1 → 4`.

Pressure, volume, absolute temperature, energy, cycle frequency, and power
retain physical dimensions.  Real numbers occur only as calibrated unit
readouts, dimensionless ratios, figure coordinates, or displayed answer
values.  In particular, the refrigerator's power input is an independent
physical observable and is not defined from the recorded answer.
-/

/-! ## Dimensionful physical quantities and calibrated readouts -/

/-- A nonnegative gas volume carrying physical dimension `L³`. -/
abbrev VolumeQuantity : Type :=
  Dimensionful (WithDim (L𝓭 * L𝓭 * L𝓭) NNReal)

/-- A nonnegative operating frequency carrying dimension `T⁻¹`. -/
abbrev FrequencyQuantity : Type :=
  Dimensionful (WithDim T𝓭⁻¹ NNReal)

/-- The physical dimension `M L² T⁻³` of power. -/
def powerDimension : Dimension :=
  M𝓭 * L𝓭 * L𝓭 * T𝓭⁻¹ * T𝓭⁻¹ * T𝓭⁻¹

/-- A nonnegative physical power whose SI unit is the watt. -/
abbrev PowerQuantity : Type :=
  Dimensionful (WithDim powerDimension NNReal)

/--
Calibrated mole readout for an abstract amount-of-substance carrier.  Physlib's
unit system has no amount-of-substance base dimension, so the physical amount
is not identified with a bare real number.
-/
structure MolarMeasurement (AmountOfSubstance : Type) where
  inMoles : AmountOfSubstance → ℝ

/-- Read a dimensionful pressure in SI pascals. -/
def pressureInPascals (pressure : DimPressure) : ℝ :=
  (pressure UnitChoices.SI).val /
    (DimPressure.pascal UnitChoices.SI).val

/-- Read a dimensionful pressure in kilopascals. -/
def pressureInKilopascals (pressure : DimPressure) : ℝ :=
  pressureInPascals pressure / 1000

/-- Read a dimensionful gas volume in SI cubic metres. -/
def volumeInCubicMeters (volume : VolumeQuantity) : ℝ :=
  ((volume UnitChoices.SI).val : ℝ)

/-- Read a dimensionful gas volume in cubic centimetres. -/
def volumeInCubicCentimeters (volume : VolumeQuantity) : ℝ :=
  1000000 * volumeInCubicMeters volume

/-- Read signed heat or work in SI joules. -/
def energyInJoules (energy : DimEnergy) : ℝ :=
  (energy UnitChoices.SI).val /
    (DimEnergy.joule UnitChoices.SI).val

/-- Read a physical cycle rate in cycles per SI second (hertz). -/
def frequencyInHertz (frequency : FrequencyQuantity) : ℝ :=
  ((frequency UnitChoices.SI).val : ℝ)

/-- Read physical power in SI watts. -/
def powerInWatts (power : PowerQuantity) : ℝ :=
  ((power UnitChoices.SI).val : ℝ)

/-- Read Physlib's absolute temperature in kelvins. -/
def temperatureInKelvins
    (storageUnit : TemperatureUnit) (temperature : Temperature) : ℝ :=
  let unitRatio : NNReal := storageUnit / TemperatureUnit.kelvin
  temperature.toReal * (unitRatio : ℝ)

/-- The affine Celsius readout corresponding to an absolute temperature. -/
def temperatureInDegreesCelsius
    (storageUnit : TemperatureUnit) (temperature : Temperature) : ℝ :=
  temperatureInKelvins storageUnit temperature - 27315 / 100

/-! ## Gas, cycle states, directed legs, and primary-figure vocabulary -/

/-- Molecular species used as the working substance. -/
inductive WorkingSubstance where
  | helium
  | other
  deriving DecidableEq, Repr

/-- Constitutive model selected for the working gas. -/
inductive GasModel where
  | caloricallyPerfectIdealGas
  | other
  deriving DecidableEq, Repr

/-- Molecular degrees-of-freedom class relevant to the heat capacities. -/
inductive MolecularType where
  | monatomic
  | other
  deriving DecidableEq, Repr

/-- Thermodynamic role of the cyclic device. -/
inductive DeviceRole where
  | refrigerator
  | heatEngine
  deriving DecidableEq, Repr

/-- Cycle idealization named in the problem. -/
inductive CycleModel where
  | reversedBrayton
  | other
  deriving DecidableEq, Repr

/-- The four numerical state labels printed in the bitmap. -/
inductive StateLabel where
  | one
  | two
  | three
  | four
  deriving DecidableEq, Fintype, Repr

/-- Directed process legs in the order shown by the refrigerator cycle. -/
inductive CycleLeg where
  | fourToThree
  | threeToTwo
  | twoToOne
  | oneToFour
  deriving DecidableEq, Fintype, Repr

/-- Initial state of a directed cycle leg. -/
def CycleLeg.initialState : CycleLeg → StateLabel
  | .fourToThree => .four
  | .threeToTwo => .three
  | .twoToOne => .two
  | .oneToFour => .one

/-- Final state of a directed cycle leg. -/
def CycleLeg.finalState : CycleLeg → StateLabel
  | .fourToThree => .three
  | .threeToTwo => .two
  | .twoToOne => .one
  | .oneToFour => .four

/-- Physical process performed on each leg of the reversed Brayton cycle. -/
inductive ProcessKind where
  | isentropicCompression
  | isobaricHeatRejection
  | isentropicExpansion
  | isobaricHeatAbsorption
  deriving DecidableEq, Repr

/-- Physical quantity associated with a plotted axis. -/
inductive AxisQuantity where
  | volume
  | pressure
  deriving DecidableEq, Repr

/-- Orientation of an axis in the supplied plot. -/
inductive FigureAxis where
  | horizontal
  | vertical
  deriving DecidableEq, Repr

/-- Unit text printed beside an axis. -/
inductive AxisUnit where
  | cubicCentimeter
  | kilopascal
  deriving DecidableEq, Repr

/-- Qualitative geometry of a process segment in the bitmap. -/
inductive SegmentShape where
  | curved
  | horizontal
  deriving DecidableEq, Repr

/-- The two heat-transfer labels printed in the bitmap. -/
inductive HeatLabel where
  | QH
  | QC
  deriving DecidableEq, Fintype, Repr

/-- Thermodynamic direction represented by a heat-transfer arrow. -/
inductive HeatTransferDirection where
  | intoWorkingGas
  | outOfWorkingGas
  deriving DecidableEq, Repr

/-- Geometric direction of the two purple heat arrows. -/
inductive ArrowOrientation where
  | upward
  deriving DecidableEq, Repr

/-- Pressure, volume, and absolute temperature at one equilibrium state. -/
structure ThermodynamicState where
  pressure : DimPressure
  volume : VolumeQuantity
  temperature : Temperature

/--
Raw axes, coordinates, labels, cycle segments, arrows, and temperature
annotation transcribed from the primary pressure--volume bitmap.
-/
structure PressureVolumeDiagram where
  axisQuantity : FigureAxis → AxisQuantity
  axisUnit : FigureAxis → AxisUnit
  horizontalAxisMinimumCubicCentimeters : ℝ
  horizontalAxisRightmostTickCubicCentimeters : ℝ
  verticalAxisMinimumKilopascals : ℝ
  statePointShown : StateLabel → Bool
  stateLabelShown : StateLabel → Bool
  volumeCoordinateCubicCentimeters : StateLabel → ℝ
  pressureCoordinateKilopascals : StateLabel → ℝ
  cycleSegmentShown : CycleLeg → Bool
  segmentShape : CycleLeg → SegmentShape
  drawnCycleArrowStart : CycleLeg → Option StateLabel
  drawnCycleArrowFinish : CycleLeg → Option StateLabel
  heatLabelShown : HeatLabel → Bool
  heatLabelAttachedToLeg : HeatLabel → CycleLeg
  heatTransferDirection : HeatLabel → HeatTransferDirection
  heatArrowOrientation : HeatLabel → ArrowOrientation
  temperatureAnnotationState : StateLabel
  temperatureAnnotationCelsius : ℝ
  temperatureAnnotationKelvin : ℝ

/--
The helium sample and its calibrated constitutive readouts.  The gas constant
and constant-pressure molar heat capacity are read in `J/(mol·K)`; the
adiabatic index is dimensionless.
-/
structure GasSample (AmountOfSubstance : Type) where
  workingSubstance : WorkingSubstance
  model : GasModel
  molecularType : MolecularType
  amount : AmountOfSubstance
  amountMeasurement : MolarMeasurement AmountOfSubstance
  molarGasConstantJoulesPerMoleKelvin : ℝ
  molarHeatCapacityAtConstantPressureJoulesPerMoleKelvin : ℝ
  adiabaticIndex : ℝ

/-- Molar readout of the abstract physical amount of working gas. -/
def GasSample.amountInMoles {AmountOfSubstance : Type}
    (gas : GasSample AmountOfSubstance) : ℝ :=
  gas.amountMeasurement.inMoles gas.amount

/-!
The complete refrigerator setup.  Compressor work, expander work, net cycle
work, and power input are independent physical observables.  The governing
laws below relate them; none is defined from the requested `410 W` answer.
-/
structure ReversedBraytonRefrigerator (AmountOfSubstance : Type) where
  deviceRole : DeviceRole
  cycleModel : CycleModel
  gas : GasSample AmountOfSubstance
  temperatureStorageUnit : TemperatureUnit
  state : StateLabel → ThermodynamicState
  processKind : CycleLeg → ProcessKind
  heatTransferredToGas : CycleLeg → DimEnergy
  heatRejectedToHotReservoir : DimEnergy
  heatAbsorbedFromColdReservoir : DimEnergy
  compressorWorkInput : DimEnergy
  expanderWorkOutput : DimEnergy
  netWorkInputPerCycle : DimEnergy
  operatingFrequency : FrequencyQuantity
  powerInput : PowerQuantity
  figure : PressureVolumeDiagram

/-! ## Scenario, figure/data readouts, and governing laws -/

/--
Qualitative information from the problem statement.  It identifies the
working substance, cycle model, and process roles but supplies no work or
power conclusion.
-/
structure MatchesReversedBraytonHeliumScenario
    {AmountOfSubstance : Type}
    (setup : ReversedBraytonRefrigerator AmountOfSubstance) : Prop where
  deviceIsRefrigerator : setup.deviceRole = .refrigerator
  cycleIsReversedBrayton : setup.cycleModel = .reversedBrayton
  workingSubstanceIsHelium : setup.gas.workingSubstance = .helium
  heliumIsMonatomic : setup.gas.molecularType = .monatomic
  gasIsCaloricallyPerfectAndIdeal :
    setup.gas.model = .caloricallyPerfectIdealGas
  temperaturesStoredInKelvins :
    setup.temperatureStorageUnit = TemperatureUnit.kelvin
  fourToThreeIsIsentropicCompression :
    setup.processKind .fourToThree = .isentropicCompression
  threeToTwoIsIsobaricHeatRejection :
    setup.processKind .threeToTwo = .isobaricHeatRejection
  twoToOneIsIsentropicExpansion :
    setup.processKind .twoToOne = .isentropicExpansion
  oneToFourIsIsobaricHeatAbsorption :
    setup.processKind .oneToFour = .isobaricHeatAbsorption

/-- Pressure ratio from the low-pressure state 4 to high-pressure state 3. -/
def pressureRatio
    {AmountOfSubstance : Type}
    (setup : ReversedBraytonRefrigerator AmountOfSubstance) : ℝ :=
  pressureInPascals (setup.state .three).pressure /
    pressureInPascals (setup.state .four).pressure

/-!
Numerical data supplied in the prose: pressure ratio `5.0`, state 4 before
compression at `150 kPa`, `100 cm³`, and approximately `-23 °C`, state 1 at
the end of expansion with volume `80 cm³`, and operation at `60 Hz`.

The Celsius datum is recorded as a whole-degree readout because the primary
image explicitly calibrates the same state as `250 K` (`-23.15 °C` exactly).
-/
structure MatchesProblemReadouts
    {AmountOfSubstance : Type}
    (setup : ReversedBraytonRefrigerator AmountOfSubstance) : Prop where
  pressureRatioIsFive : pressureRatio setup = 5
  preCompressionPressureKilopascals :
    pressureInKilopascals (setup.state .four).pressure = 150
  preCompressionVolumeCubicCentimeters :
    volumeInCubicCentimeters (setup.state .four).volume = 100
  preCompressionCelsiusRoundsToMinusTwentyThree :
    |temperatureInDegreesCelsius setup.temperatureStorageUnit
        (setup.state .four).temperature - (-23)| < 1 / 2
  postExpansionVolumeCubicCentimeters :
    volumeInCubicCentimeters (setup.state .one).volume = 80
  operatingFrequencyHertz :
    frequencyInHertz setup.operatingFrequency = 60

/-!
Primary-image evidence.  The bitmap fixes the four low/high pressures and the
two supplied low-pressure volumes, displays only the two curved cycle arrows,
and identifies `Q_H` as heat leaving and `Q_C` as heat entering the gas.
-/
structure MatchesPrimaryPressureVolumeFigure
    {AmountOfSubstance : Type}
    (setup : ReversedBraytonRefrigerator AmountOfSubstance) : Prop where
  horizontalAxisIsVolume :
    setup.figure.axisQuantity .horizontal = .volume
  verticalAxisIsPressure :
    setup.figure.axisQuantity .vertical = .pressure
  horizontalAxisUsesCubicCentimeters :
    setup.figure.axisUnit .horizontal = .cubicCentimeter
  verticalAxisUsesKilopascals :
    setup.figure.axisUnit .vertical = .kilopascal
  horizontalAxisRangeShown :
    setup.figure.horizontalAxisMinimumCubicCentimeters = 0 ∧
      setup.figure.horizontalAxisRightmostTickCubicCentimeters = 100
  verticalAxisStartsAtZero :
    setup.figure.verticalAxisMinimumKilopascals = 0
  everyStatePointIsShown :
    ∀ label : StateLabel, setup.figure.statePointShown label = true
  everyStateLabelIsShown :
    ∀ label : StateLabel, setup.figure.stateLabelShown label = true
  everyCycleSegmentIsShown :
    ∀ leg : CycleLeg, setup.figure.cycleSegmentShown leg = true
  lowPressureCoordinates :
    setup.figure.pressureCoordinateKilopascals .one = 150 ∧
      setup.figure.pressureCoordinateKilopascals .four = 150
  highPressureCoordinates :
    setup.figure.pressureCoordinateKilopascals .two = 750 ∧
      setup.figure.pressureCoordinateKilopascals .three = 750
  suppliedVolumeCoordinates :
    setup.figure.volumeCoordinateCubicCentimeters .one = 80 ∧
      setup.figure.volumeCoordinateCubicCentimeters .four = 100
  unlabeledHighPressureVolumesHaveShownOrder :
    setup.figure.volumeCoordinateCubicCentimeters .two <
        setup.figure.volumeCoordinateCubicCentimeters .three ∧
      setup.figure.volumeCoordinateCubicCentimeters .three <
        setup.figure.volumeCoordinateCubicCentimeters .one
  coordinatesAgreeWithPhysicalStateReadouts :
    ∀ label : StateLabel,
      setup.figure.pressureCoordinateKilopascals label =
          pressureInKilopascals (setup.state label).pressure ∧
        setup.figure.volumeCoordinateCubicCentimeters label =
          volumeInCubicCentimeters (setup.state label).volume
  compressionCurveIsShown :
    setup.figure.segmentShape .fourToThree = .curved ∧
      setup.figure.drawnCycleArrowStart .fourToThree = some .four ∧
        setup.figure.drawnCycleArrowFinish .fourToThree = some .three
  expansionCurveIsShown :
    setup.figure.segmentShape .twoToOne = .curved ∧
      setup.figure.drawnCycleArrowStart .twoToOne = some .two ∧
        setup.figure.drawnCycleArrowFinish .twoToOne = some .one
  heatExchangeLegsAreHorizontal :
    setup.figure.segmentShape .threeToTwo = .horizontal ∧
      setup.figure.segmentShape .oneToFour = .horizontal
  noHorizontalCycleArrowheadsAreDrawn :
    setup.figure.drawnCycleArrowStart .threeToTwo = none ∧
      setup.figure.drawnCycleArrowFinish .threeToTwo = none ∧
        setup.figure.drawnCycleArrowStart .oneToFour = none ∧
          setup.figure.drawnCycleArrowFinish .oneToFour = none
  bothHeatLabelsAreShown :
    ∀ label : HeatLabel, setup.figure.heatLabelShown label = true
  hotHeatArrowEvidence :
    setup.figure.heatLabelAttachedToLeg .QH = .threeToTwo ∧
      setup.figure.heatTransferDirection .QH = .outOfWorkingGas ∧
        setup.figure.heatArrowOrientation .QH = .upward
  coldHeatArrowEvidence :
    setup.figure.heatLabelAttachedToLeg .QC = .oneToFour ∧
      setup.figure.heatTransferDirection .QC = .intoWorkingGas ∧
        setup.figure.heatArrowOrientation .QC = .upward
  stateFourTemperatureAnnotation :
    setup.figure.temperatureAnnotationState = .four ∧
      setup.figure.temperatureAnnotationCelsius = -23 ∧
        setup.figure.temperatureAnnotationKelvin = 250
  annotationAgreesWithStateFourKelvinReadout :
    temperatureInKelvins setup.temperatureStorageUnit
      (setup.state .four).temperature =
        setup.figure.temperatureAnnotationKelvin

/-- Positivity and sign conditions selecting an operating refrigerator. -/
structure HasPhysicalRefrigeratorParameters
    {AmountOfSubstance : Type}
    (setup : ReversedBraytonRefrigerator AmountOfSubstance) : Prop where
  amountPositive : 0 < setup.gas.amountInMoles
  molarGasConstantPositive :
    0 < setup.gas.molarGasConstantJoulesPerMoleKelvin
  constantPressureHeatCapacityPositive :
    0 < setup.gas.molarHeatCapacityAtConstantPressureJoulesPerMoleKelvin
  adiabaticIndexGreaterThanOne : 1 < setup.gas.adiabaticIndex
  everyPressurePositive : ∀ label : StateLabel,
    0 < pressureInPascals (setup.state label).pressure
  everyVolumePositive : ∀ label : StateLabel,
    0 < volumeInCubicMeters (setup.state label).volume
  everyAbsoluteTemperaturePositive : ∀ label : StateLabel,
    0 < temperatureInKelvins setup.temperatureStorageUnit
      (setup.state label).temperature
  compressorWorkPositive :
    0 < energyInJoules setup.compressorWorkInput
  expanderWorkPositive :
    0 < energyInJoules setup.expanderWorkOutput
  netWorkInputPositive :
    0 < energyInJoules setup.netWorkInputPerCycle
  hotSideHeatPositive :
    0 < energyInJoules setup.heatRejectedToHotReservoir
  coldSideHeatPositive :
    0 < energyInJoules setup.heatAbsorbedFromColdReservoir
  frequencyPositive : 0 < frequencyInHertz setup.operatingFrequency
  powerInputPositive : 0 < powerInWatts setup.powerInput

/-!
Governing relations for a calorically perfect monatomic ideal gas in an ideal
reversed Brayton refrigerator.  The compressor and expander relations use
steady-flow enthalpy changes `n Cₚ ΔT`, not closed-system boundary work.  The
fields contain neither `410 W` nor the derived closed form for this dataset.
-/
structure SatisfiesIdealReversedBraytonLaws
    {AmountOfSubstance : Type}
    (setup : ReversedBraytonRefrigerator AmountOfSubstance) : Prop where
  monatomicAdiabaticIndex :
    setup.gas.adiabaticIndex = 5 / 3
  monatomicConstantPressureHeatCapacity :
    setup.gas.molarHeatCapacityAtConstantPressureJoulesPerMoleKelvin =
      (5 / 2) * setup.gas.molarGasConstantJoulesPerMoleKelvin
  idealGasEquationOfState : ∀ label : StateLabel,
    pressureInPascals (setup.state label).pressure *
        volumeInCubicMeters (setup.state label).volume =
      setup.gas.amountInMoles *
        setup.gas.molarGasConstantJoulesPerMoleKelvin *
          temperatureInKelvins setup.temperatureStorageUnit
            (setup.state label).temperature
  highPressureLegIsIsobaric :
    (setup.state .three).pressure = (setup.state .two).pressure
  lowPressureLegIsIsobaric :
    (setup.state .one).pressure = (setup.state .four).pressure
  isentropicCompressionTemperaturePressureRelation :
    temperatureInKelvins setup.temperatureStorageUnit
        (setup.state .three).temperature =
      temperatureInKelvins setup.temperatureStorageUnit
          (setup.state .four).temperature *
        Real.rpow
          (pressureInPascals (setup.state .three).pressure /
            pressureInPascals (setup.state .four).pressure)
          ((setup.gas.adiabaticIndex - 1) / setup.gas.adiabaticIndex)
  isentropicExpansionTemperaturePressureRelation :
    temperatureInKelvins setup.temperatureStorageUnit
        (setup.state .two).temperature =
      temperatureInKelvins setup.temperatureStorageUnit
          (setup.state .one).temperature *
        Real.rpow
          (pressureInPascals (setup.state .two).pressure /
            pressureInPascals (setup.state .one).pressure)
          ((setup.gas.adiabaticIndex - 1) / setup.gas.adiabaticIndex)
  isentropicLegsTransferNoHeat :
    energyInJoules (setup.heatTransferredToGas .fourToThree) = 0 ∧
      energyInJoules (setup.heatTransferredToGas .twoToOne) = 0
  compressorSteadyFlowWorkLaw :
    energyInJoules setup.compressorWorkInput =
      setup.gas.amountInMoles *
        setup.gas.molarHeatCapacityAtConstantPressureJoulesPerMoleKelvin *
          (temperatureInKelvins setup.temperatureStorageUnit
              (setup.state .three).temperature -
            temperatureInKelvins setup.temperatureStorageUnit
              (setup.state .four).temperature)
  expanderSteadyFlowWorkLaw :
    energyInJoules setup.expanderWorkOutput =
      setup.gas.amountInMoles *
        setup.gas.molarHeatCapacityAtConstantPressureJoulesPerMoleKelvin *
          (temperatureInKelvins setup.temperatureStorageUnit
              (setup.state .two).temperature -
            temperatureInKelvins setup.temperatureStorageUnit
              (setup.state .one).temperature)
  hotSideIsobaricHeatLaw :
    energyInJoules setup.heatRejectedToHotReservoir =
      setup.gas.amountInMoles *
        setup.gas.molarHeatCapacityAtConstantPressureJoulesPerMoleKelvin *
          (temperatureInKelvins setup.temperatureStorageUnit
              (setup.state .three).temperature -
            temperatureInKelvins setup.temperatureStorageUnit
              (setup.state .two).temperature)
  hotSideHeatSignConvention :
    energyInJoules (setup.heatTransferredToGas .threeToTwo) =
      -energyInJoules setup.heatRejectedToHotReservoir
  coldSideIsobaricHeatLaw :
    energyInJoules setup.heatAbsorbedFromColdReservoir =
      setup.gas.amountInMoles *
        setup.gas.molarHeatCapacityAtConstantPressureJoulesPerMoleKelvin *
          (temperatureInKelvins setup.temperatureStorageUnit
              (setup.state .four).temperature -
            temperatureInKelvins setup.temperatureStorageUnit
              (setup.state .one).temperature)
  coldSideHeatSignConvention :
    energyInJoules (setup.heatTransferredToGas .oneToFour) =
      energyInJoules setup.heatAbsorbedFromColdReservoir
  netWorkInputIsCompressorMinusExpander :
    energyInJoules setup.netWorkInputPerCycle =
      energyInJoules setup.compressorWorkInput -
        energyInJoules setup.expanderWorkOutput
  cycleEnergyBalance :
    energyInJoules setup.netWorkInputPerCycle =
      energyInJoules setup.heatRejectedToHotReservoir -
        energyInJoules setup.heatAbsorbedFromColdReservoir
  averagePowerIsWorkPerCycleTimesFrequency :
    powerInWatts setup.powerInput =
      frequencyInHertz setup.operatingFrequency *
        energyInJoules setup.netWorkInputPerCycle

/-! ## Derived state values, exact power, and displayed answer -/

/-- State 1 is at `200 K`, as follows from the two low-pressure `pV=nRT` states. -/
lemma stateOneTemperatureInKelvins_eq_200
    {AmountOfSubstance : Type}
    (setup : ReversedBraytonRefrigerator AmountOfSubstance)
    (_scenario : MatchesReversedBraytonHeliumScenario setup)
    (_data : MatchesProblemReadouts setup)
    (_figure : MatchesPrimaryPressureVolumeFigure setup)
    (_physical : HasPhysicalRefrigeratorParameters setup)
    (_laws : SatisfiesIdealReversedBraytonLaws setup) :
    temperatureInKelvins setup.temperatureStorageUnit
      (setup.state .one).temperature = 200 := by
  have hTemperatureFour :
      temperatureInKelvins setup.temperatureStorageUnit
          (setup.state .four).temperature = 250 := by
    calc
      temperatureInKelvins setup.temperatureStorageUnit
          (setup.state .four).temperature =
          setup.figure.temperatureAnnotationKelvin :=
        _figure.annotationAgreesWithStateFourKelvinReadout
      _ = 250 := _figure.stateFourTemperatureAnnotation.2.2
  have hPressure :
      pressureInPascals (setup.state .one).pressure =
        pressureInPascals (setup.state .four).pressure :=
    congrArg pressureInPascals _laws.lowPressureLegIsIsobaric
  have hVolumeOne := _data.postExpansionVolumeCubicCentimeters
  have hVolumeFour := _data.preCompressionVolumeCubicCentimeters
  rw [volumeInCubicCentimeters] at hVolumeOne hVolumeFour
  have hStateOne := _laws.idealGasEquationOfState .one
  have hStateFour := _laws.idealGasEquationOfState .four
  rw [hPressure] at hStateOne
  rw [hTemperatureFour] at hStateFour
  have hAmountGasConstant :
      0 < setup.gas.amountInMoles *
          setup.gas.molarGasConstantJoulesPerMoleKelvin :=
    mul_pos _physical.amountPositive _physical.molarGasConstantPositive
  apply mul_left_cancel₀ (ne_of_gt hAmountGasConstant)
  nlinarith

/-!
Both isentropic legs have pressure ratio five and exponent
`(γ-1)/γ = 2/5`.
-/
lemma isentropicEndpointTemperatures
    {AmountOfSubstance : Type}
    (setup : ReversedBraytonRefrigerator AmountOfSubstance)
    (_scenario : MatchesReversedBraytonHeliumScenario setup)
    (_data : MatchesProblemReadouts setup)
    (_figure : MatchesPrimaryPressureVolumeFigure setup)
    (_physical : HasPhysicalRefrigeratorParameters setup)
    (_laws : SatisfiesIdealReversedBraytonLaws setup) :
    temperatureInKelvins setup.temperatureStorageUnit
          (setup.state .three).temperature =
        250 * Real.rpow 5 (2 / 5) ∧
      temperatureInKelvins setup.temperatureStorageUnit
          (setup.state .two).temperature =
        200 * Real.rpow 5 (2 / 5) := by
  have hTemperatureFour :
      temperatureInKelvins setup.temperatureStorageUnit
          (setup.state .four).temperature = 250 := by
    calc
      temperatureInKelvins setup.temperatureStorageUnit
          (setup.state .four).temperature =
          setup.figure.temperatureAnnotationKelvin :=
        _figure.annotationAgreesWithStateFourKelvinReadout
      _ = 250 := _figure.stateFourTemperatureAnnotation.2.2
  have hTemperatureOne :
      temperatureInKelvins setup.temperatureStorageUnit
          (setup.state .one).temperature = 200 :=
    stateOneTemperatureInKelvins_eq_200
      setup _scenario _data _figure _physical _laws
  have hCompressionRatio :
      pressureInPascals (setup.state .three).pressure /
          pressureInPascals (setup.state .four).pressure = 5 := by
    simpa [pressureRatio] using _data.pressureRatioIsFive
  have hHighPressure :
      pressureInPascals (setup.state .three).pressure =
        pressureInPascals (setup.state .two).pressure :=
    congrArg pressureInPascals _laws.highPressureLegIsIsobaric
  have hLowPressure :
      pressureInPascals (setup.state .one).pressure =
        pressureInPascals (setup.state .four).pressure :=
    congrArg pressureInPascals _laws.lowPressureLegIsIsobaric
  have hExpansionRatio :
      pressureInPascals (setup.state .two).pressure /
          pressureInPascals (setup.state .one).pressure = 5 := by
    calc
      pressureInPascals (setup.state .two).pressure /
          pressureInPascals (setup.state .one).pressure =
          pressureInPascals (setup.state .three).pressure /
            pressureInPascals (setup.state .four).pressure := by
              rw [hHighPressure, hLowPressure]
      _ = 5 := hCompressionRatio
  have hExponent :
      (setup.gas.adiabaticIndex - 1) / setup.gas.adiabaticIndex =
        (2 / 5 : ℝ) := by
    rw [_laws.monatomicAdiabaticIndex]
    norm_num
  constructor
  · calc
      temperatureInKelvins setup.temperatureStorageUnit
          (setup.state .three).temperature =
          temperatureInKelvins setup.temperatureStorageUnit
              (setup.state .four).temperature *
            Real.rpow
              (pressureInPascals (setup.state .three).pressure /
                pressureInPascals (setup.state .four).pressure)
              ((setup.gas.adiabaticIndex - 1) /
                setup.gas.adiabaticIndex) :=
        _laws.isentropicCompressionTemperaturePressureRelation
      _ = 250 * Real.rpow 5 (2 / 5) := by
        rw [hTemperatureFour, hCompressionRatio, hExponent]
  · calc
      temperatureInKelvins setup.temperatureStorageUnit
          (setup.state .two).temperature =
          temperatureInKelvins setup.temperatureStorageUnit
              (setup.state .one).temperature *
            Real.rpow
              (pressureInPascals (setup.state .two).pressure /
                pressureInPascals (setup.state .one).pressure)
              ((setup.gas.adiabaticIndex - 1) /
                setup.gas.adiabaticIndex) :=
        _laws.isentropicExpansionTemperaturePressureRelation
      _ = 200 * Real.rpow 5 (2 / 5) := by
        rw [hTemperatureOne, hExpansionRatio, hExponent]

/-- Exact net work input per cycle, in joules. -/
lemma netWorkInputPerCycle_exact
    {AmountOfSubstance : Type}
    (setup : ReversedBraytonRefrigerator AmountOfSubstance)
    (_scenario : MatchesReversedBraytonHeliumScenario setup)
    (_data : MatchesProblemReadouts setup)
    (_figure : MatchesPrimaryPressureVolumeFigure setup)
    (_physical : HasPhysicalRefrigeratorParameters setup)
    (_laws : SatisfiesIdealReversedBraytonLaws setup) :
    energyInJoules setup.netWorkInputPerCycle =
      (15 / 2) * (Real.rpow 5 (2 / 5) - 1) := by
  have hPressureFour :
      pressureInPascals (setup.state .four).pressure = 150000 := by
    have h := _data.preCompressionPressureKilopascals
    rw [pressureInKilopascals] at h
    linarith
  have hVolumeFour :
      volumeInCubicMeters (setup.state .four).volume = (1 / 10000 : ℝ) := by
    have h := _data.preCompressionVolumeCubicCentimeters
    rw [volumeInCubicCentimeters] at h
    norm_num at h ⊢
    linarith
  have hTemperatureFour :
      temperatureInKelvins setup.temperatureStorageUnit
          (setup.state .four).temperature = 250 := by
    calc
      temperatureInKelvins setup.temperatureStorageUnit
          (setup.state .four).temperature =
          setup.figure.temperatureAnnotationKelvin :=
        _figure.annotationAgreesWithStateFourKelvinReadout
      _ = 250 := _figure.stateFourTemperatureAnnotation.2.2
  have hAmountGasConstant :
      setup.gas.amountInMoles *
          setup.gas.molarGasConstantJoulesPerMoleKelvin = (3 / 50 : ℝ) := by
    have hStateFour := _laws.idealGasEquationOfState .four
    rw [hPressureFour, hVolumeFour, hTemperatureFour] at hStateFour
    norm_num at hStateFour ⊢
    nlinarith
  have hAmountHeatCapacity :
      setup.gas.amountInMoles *
          setup.gas.molarHeatCapacityAtConstantPressureJoulesPerMoleKelvin =
        (3 / 20 : ℝ) := by
    rw [_laws.monatomicConstantPressureHeatCapacity]
    calc
      setup.gas.amountInMoles *
          ((5 / 2) * setup.gas.molarGasConstantJoulesPerMoleKelvin) =
          (5 / 2) *
            (setup.gas.amountInMoles *
              setup.gas.molarGasConstantJoulesPerMoleKelvin) := by ring
      _ = 3 / 20 := by rw [hAmountGasConstant]; norm_num
  have hTemperatureOne :
      temperatureInKelvins setup.temperatureStorageUnit
          (setup.state .one).temperature = 200 :=
    stateOneTemperatureInKelvins_eq_200
      setup _scenario _data _figure _physical _laws
  have hEndpointTemperatures :=
    isentropicEndpointTemperatures
      setup _scenario _data _figure _physical _laws
  calc
    energyInJoules setup.netWorkInputPerCycle =
        energyInJoules setup.compressorWorkInput -
          energyInJoules setup.expanderWorkOutput :=
      _laws.netWorkInputIsCompressorMinusExpander
    _ =
        setup.gas.amountInMoles *
            setup.gas.molarHeatCapacityAtConstantPressureJoulesPerMoleKelvin *
              (temperatureInKelvins setup.temperatureStorageUnit
                  (setup.state .three).temperature -
                temperatureInKelvins setup.temperatureStorageUnit
                  (setup.state .four).temperature) -
          setup.gas.amountInMoles *
            setup.gas.molarHeatCapacityAtConstantPressureJoulesPerMoleKelvin *
              (temperatureInKelvins setup.temperatureStorageUnit
                  (setup.state .two).temperature -
                temperatureInKelvins setup.temperatureStorageUnit
                  (setup.state .one).temperature) := by
      rw [_laws.compressorSteadyFlowWorkLaw,
        _laws.expanderSteadyFlowWorkLaw]
    _ = (15 / 2) * (Real.rpow 5 (2 / 5) - 1) := by
      rw [hAmountHeatCapacity, hEndpointTemperatures.1, hTemperatureFour,
        hEndpointTemperatures.2, hTemperatureOne]
      ring

/-- Exact power determined by the four-state Brayton model and the `60 Hz` rate. -/
def exactPowerInputWatts : ℝ :=
  450 * (Real.rpow 5 (2 / 5) - 1)

/-- The four power values printed beside answer labels A--D. -/
inductive AnswerChoice where
  | A
  | B
  | C
  | D
  deriving DecidableEq, Fintype, Repr

/-- Displayed input power in watts for each multiple-choice answer. -/
def AnswerChoice.displayedPowerWatts : AnswerChoice → ℝ
  | .A => 390
  | .B => 400
  | .C => 410
  | .D => 420

/-- Dataset metadata records answer C; this is not a theorem premise. -/
def recordedAnswerChoice : AnswerChoice := .C

/-- The physical power rounds to a displayed multiple of ten watts. -/
def RoundsToDisplayedTenWatts
    (power : PowerQuantity) (choice : AnswerChoice) : Prop :=
  |powerInWatts power - choice.displayedPowerWatts| < 5

/-- The selected display is strictly closer than every alternative. -/
def IsUniqueClosestDisplayedPower
    (power : PowerQuantity) (choice : AnswerChoice) : Prop :=
  ∀ other : AnswerChoice, other ≠ choice →
    |powerInWatts power - choice.displayedPowerWatts| <
      |powerInWatts power - other.displayedPowerWatts|

/-!
The model gives

`P_in = 450 (5^(2/5) - 1) W ≈ 406.6 W`,

which rounds to `410 W` and is uniquely answer C.

Blueprint label: `thm:physics:phyx_mini_0481:target`.
-/
theorem reversedBraytonRefrigerator_powerInput_eq_recordedAnswerC
    {AmountOfSubstance : Type}
    (setup : ReversedBraytonRefrigerator AmountOfSubstance)
    (_scenario : MatchesReversedBraytonHeliumScenario setup)
    (_data : MatchesProblemReadouts setup)
    (_figure : MatchesPrimaryPressureVolumeFigure setup)
    (_physical : HasPhysicalRefrigeratorParameters setup)
    (_laws : SatisfiesIdealReversedBraytonLaws setup) :
    powerInWatts setup.powerInput = exactPowerInputWatts ∧
      RoundsToDisplayedTenWatts setup.powerInput .C ∧
        IsUniqueClosestDisplayedPower setup.powerInput .C := by
  have hWork :=
    netWorkInputPerCycle_exact
      setup _scenario _data _figure _physical _laws
  have hPower : powerInWatts setup.powerInput = exactPowerInputWatts := by
    calc
      powerInWatts setup.powerInput =
          frequencyInHertz setup.operatingFrequency *
            energyInJoules setup.netWorkInputPerCycle :=
        _laws.averagePowerIsWorkPerCycleTimesFrequency
      _ = exactPowerInputWatts := by
        rw [_data.operatingFrequencyHertz, hWork]
        unfold exactPowerInputWatts
        ring
  have hRpowPower :
      (((5 : ℝ) ^ (2 / 5 : ℝ)) ^ (5 : ℕ)) = (25 : ℝ) := by
    rw [← Real.rpow_mul_natCast (by norm_num : (0 : ℝ) ≤ 5)]
    norm_num [Real.rpow_natCast]
  have hRpowLower : (19 / 10 : ℝ) < Real.rpow 5 (2 / 5) := by
    change (19 / 10 : ℝ) < (5 : ℝ) ^ (2 / 5 : ℝ)
    apply lt_of_pow_lt_pow_left₀ 5 (Real.rpow_nonneg (by norm_num) _)
    rw [hRpowPower]
    norm_num
  have hRpowUpper : Real.rpow 5 (2 / 5) < (173 / 90 : ℝ) := by
    change (5 : ℝ) ^ (2 / 5 : ℝ) < (173 / 90 : ℝ)
    apply lt_of_pow_lt_pow_left₀ 5
      (by norm_num : (0 : ℝ) ≤ 173 / 90)
    rw [hRpowPower]
    norm_num
  have hPowerLower : 405 < powerInWatts setup.powerInput := by
    rw [hPower]
    unfold exactPowerInputWatts
    nlinarith
  have hPowerUpper : powerInWatts setup.powerInput < 415 := by
    rw [hPower]
    unfold exactPowerInputWatts
    nlinarith
  have hRounds :
      RoundsToDisplayedTenWatts setup.powerInput .C := by
    rw [RoundsToDisplayedTenWatts, AnswerChoice.displayedPowerWatts, abs_lt]
    constructor <;> linarith
  refine ⟨hPower, hRounds, ?_⟩
  intro other hOther
  have hDistanceToC :
      |powerInWatts setup.powerInput - 410| < 5 :=
    hRounds
  cases other with
  | A =>
      have hFarther :
          5 < |powerInWatts setup.powerInput - 390| := by
        rw [abs_of_pos]
        all_goals linarith
      exact hDistanceToC.trans hFarther
  | B =>
      have hFarther :
          5 < |powerInWatts setup.powerInput - 400| := by
        rw [abs_of_pos]
        all_goals linarith
      exact hDistanceToC.trans hFarther
  | C =>
      exact False.elim (hOther rfl)
  | D =>
      have hFarther :
          5 < |powerInWatts setup.powerInput - 420| := by
        rw [abs_of_neg]
        all_goals linarith
      exact hDistanceToC.trans hFarther

end PhyXMiniProblems.ProblemPhyXMini0481
