import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Physlib.Thermodynamics.Temperature.Basic
import Physlib.Thermodynamics.Temperature.TemperatureUnits
import Physlib.Units.WithDim.Energy
import Physlib.Units.WithDim.Pressure

/- USER: The assigned source file did not exist when this autoformalization task began. -/

noncomputable section

namespace PhyXMiniProblems.ProblemPhyXMini0431

open Dimension

/-!
# Power input of a reversed helium refrigerator cycle

The primary pressure-volume image shows a reversed cycle with two adiabatic
curves joined by constant-volume legs. The right-hand volume is 100 cm³, the
left-hand volume is 40 cm³, and the upper-right state has pressure 150 kPa.
The two right-hand temperatures printed in the raster are -23 °C and -73 °C.
The visible minus sign on -23 °C corrects the lossy auxiliary caption.

The helium is modeled as a monatomic ideal gas and the cycle is run at
60 cycles per second. Pressure, volume, temperature, energy, frequency, and
power remain physical quantities. Real numbers below are only calibrated unit
readouts, dimensionless exponents and ratios, or displayed answer values.
-/

/-! ## Dimensionful physical quantities and calibrated readouts -/

/-- A nonnegative physical volume with dimension length cubed. -/
abbrev VolumeQuantity : Type :=
  Dimensionful (WithDim (L𝓭 * L𝓭 * L𝓭) NNReal)

/-- A nonnegative cycle frequency with inverse-time dimension. -/
abbrev FrequencyQuantity : Type :=
  Dimensionful (WithDim T𝓭⁻¹ NNReal)

/-- The physical dimension of power, mass times length squared per time cubed. -/
def powerDimension : Dimension :=
  M𝓭 * L𝓭 * L𝓭 * T𝓭⁻¹ * T𝓭⁻¹ * T𝓭⁻¹

/-- A nonnegative physical input power with SI unit watt. -/
abbrev PowerQuantity : Type :=
  Dimensionful (WithDim powerDimension NNReal)

/-!
Physlib has no amount-of-substance base dimension. This interface keeps an
abstract physical amount carrier and exposes only its calibrated mole readout.
-/
structure AmountOfSubstanceScale where
  Quantity : Type
  inMoles : Quantity → ℝ

/-!
The molar gas constant also carries an inverse amount dimension unavailable in
Physlib. This interface preserves its physical role and exposes only a
coherent joule-per-mole-kelvin readout.
-/
structure MolarGasConstantScale where
  Quantity : Type
  inJoulesPerMoleKelvin : Quantity → ℝ

/-- SI pressure readout in pascals. -/
def pressureInPascals (pressure : DimPressure) : ℝ :=
  (pressure UnitChoices.SI).val

/-- Pressure readout in the kilopascals printed on the vertical axis. -/
def pressureInKilopascals (pressure : DimPressure) : ℝ :=
  pressureInPascals pressure / 1000

/-- SI volume readout in cubic metres. -/
def volumeInCubicMeters (volume : VolumeQuantity) : ℝ :=
  ((volume UnitChoices.SI).val : ℝ)

/-- Volume readout in the cubic centimetres printed on the horizontal axis. -/
def volumeInCubicCentimeters (volume : VolumeQuantity) : ℝ :=
  1000000 * volumeInCubicMeters volume

/-- SI energy readout in joules. -/
def energyInJoules (energy : DimEnergy) : ℝ :=
  (energy UnitChoices.SI).val

/-- Cycle frequency readout in hertz, i.e. cycles per second. -/
def frequencyInHertz (frequency : FrequencyQuantity) : ℝ :=
  ((frequency UnitChoices.SI).val : ℝ)

/-- SI input-power readout in watts. -/
def powerInWatts (power : PowerQuantity) : ℝ :=
  ((power UnitChoices.SI).val : ℝ)

/-!
Read an absolute temperature in kelvin. The storage unit is explicit because
Temperature may use any zero-preserving temperature scale.
-/
def temperatureInKelvin
    (storageUnit : TemperatureUnit) (temperature : Temperature) : ℝ :=
  let unitRatio : NNReal := storageUnit / TemperatureUnit.kelvin
  temperature.toReal * (unitRatio : ℝ)

/-!
The associated Celsius readout. Celsius is affine, so the 273.15 K offset is
applied only at the readout boundary.
-/
def temperatureInDegreesCelsius
    (storageUnit : TemperatureUnit) (temperature : Temperature) : ℝ :=
  temperatureInKelvin storageUnit temperature - 5463 / 20

/-! ## Gas states, directed legs, and primary-image vocabulary -/

/-- Gas species stated in the scenario. -/
inductive GasSpecies where
  | helium
  | other
  deriving DecidableEq, Repr

/-- Molecular model governing heat capacity and the adiabatic exponent. -/
inductive MolecularModel where
  | monatomicIdealGas
  | other
  deriving DecidableEq, Repr

/-- Operating role and direction of the depicted cycle. -/
inductive CycleOperation where
  | reversedRefrigerator
  | other
  deriving DecidableEq, Repr

/-- Idealization needed for the reversible adiabatic relation. -/
inductive CycleIdealization where
  | reversibleEquilibrium
  | other
  deriving DecidableEq, Repr

/-!
The right points carry the two temperature labels; the left points are their
adiabatically compressed partners on the upper and lower curves.
-/
inductive CyclePoint where
  | rightCold
  | rightWarm
  | leftHot
  | leftCool
  deriving DecidableEq, Repr

/-- Directed cycle legs in the order shown by the arrows. -/
inductive CycleLeg where
  | rightIsochoricHeating
  | upperAdiabaticCompression
  | leftIsochoricCooling
  | lowerAdiabaticExpansion
  deriving DecidableEq, Repr

/-- Initial point of a directed cycle leg. -/
def legStart : CycleLeg → CyclePoint
  | .rightIsochoricHeating => .rightCold
  | .upperAdiabaticCompression => .rightWarm
  | .leftIsochoricCooling => .leftHot
  | .lowerAdiabaticExpansion => .leftCool

/-- Final point of a directed cycle leg. -/
def legFinish : CycleLeg → CyclePoint
  | .rightIsochoricHeating => .rightWarm
  | .upperAdiabaticCompression => .leftHot
  | .leftIsochoricCooling => .leftCool
  | .lowerAdiabaticExpansion => .rightCold

/-- Thermodynamic character of a drawn process leg. -/
inductive ProcessKind where
  | isochoric
  | adiabatic
  | other
  deriving DecidableEq, Repr

/-- A pressure-volume-temperature equilibrium state with internal energy. -/
structure ThermodynamicState where
  pressure : DimPressure
  volume : VolumeQuantity
  temperature : Temperature
  internalEnergy : DimEnergy

/-- Physical quantity assigned to a plotted axis. -/
inductive DiagramAxisQuantity where
  | volume
  | pressure
  deriving DecidableEq, Repr

/-- Unit label printed beside a plotted axis. -/
inductive DiagramAxisUnit where
  | cubicCentimeters
  | kilopascals
  | other
  deriving DecidableEq, Repr

/-!
Axis assignments, coordinates, labels, curves, and arrows extracted from the
primary raster. No energy, power, or answer-choice value is stored here.
-/
structure ReversedCycleFigure where
  horizontalAxis : DiagramAxisQuantity
  verticalAxis : DiagramAxisQuantity
  axisUnit : DiagramAxisQuantity → DiagramAxisUnit
  pointVolumeInCubicCentimeters : CyclePoint → ℝ
  pointPressureInKilopascals : CyclePoint → ℝ
  temperatureLabelInDegreesCelsius : CyclePoint → Option ℝ
  legKind : CycleLeg → ProcessKind
  arrowStart : CycleLeg → CyclePoint
  arrowFinish : CycleLeg → CyclePoint
  directionArrowShown : CycleLeg → Bool
  adiabaticAnnotationPointsTo : CycleLeg → Bool

/-!
Physical observables for the helium refrigerator. Heat is positive into the
gas and work is positive when done by the gas. Thus refrigerator work input
is the negative of the gas's net cyclic work.
-/
structure HeliumRefrigeratorSetup
    (amountScale : AmountOfSubstanceScale)
    (gasConstantScale : MolarGasConstantScale) where
  gasSpecies : GasSpecies
  molecularModel : MolecularModel
  cycleOperation : CycleOperation
  cycleIdealization : CycleIdealization
  gasAmount : amountScale.Quantity
  universalGasConstant : gasConstantScale.Quantity
  adiabaticExponent : ℝ
  temperatureStorageUnit : TemperatureUnit
  stateAt : CyclePoint → ThermodynamicState
  heatAbsorbedByGas : CycleLeg → DimEnergy
  workDoneByGas : CycleLeg → DimEnergy
  netWorkInputPerCycle : DimEnergy
  operatingFrequency : FrequencyQuantity
  inputPower : PowerQuantity
  figure : ReversedCycleFigure

/-- Kelvin readout at a cycle point. -/
def stateTemperatureInKelvin
    {amountScale : AmountOfSubstanceScale}
    {gasConstantScale : MolarGasConstantScale}
    (setup : HeliumRefrigeratorSetup amountScale gasConstantScale)
    (point : CyclePoint) : ℝ :=
  temperatureInKelvin setup.temperatureStorageUnit
    (setup.stateAt point).temperature

/-- Celsius readout at a cycle point. -/
def stateTemperatureInDegreesCelsius
    {amountScale : AmountOfSubstanceScale}
    {gasConstantScale : MolarGasConstantScale}
    (setup : HeliumRefrigeratorSetup amountScale gasConstantScale)
    (point : CyclePoint) : ℝ :=
  temperatureInDegreesCelsius setup.temperatureStorageUnit
    (setup.stateAt point).temperature

/-! ## Assumptions: scenario, figure/data readouts, and governing laws -/

/-- Prose-level helium refrigerator and reversed-cycle description. -/
structure MatchesHeliumRefrigeratorScenario
    {amountScale : AmountOfSubstanceScale}
    {gasConstantScale : MolarGasConstantScale}
    (setup : HeliumRefrigeratorSetup amountScale gasConstantScale) : Prop where
  gasIsHelium : setup.gasSpecies = .helium
  heliumIsModeledAsMonatomicIdealGas :
    setup.molecularModel = .monatomicIdealGas
  operatesAsReversedRefrigerator :
    setup.cycleOperation = .reversedRefrigerator
  reversibleEquilibriumIdealization :
    setup.cycleIdealization = .reversibleEquilibrium

/-!
Primary-image evidence. The upper-right label is -23 °C, following the visible
minus sign rather than the auxiliary caption. Left pressures and temperatures
are deliberately not supplied; the governing laws must determine what is
needed from the right-hand state data.
-/
structure MatchesSuppliedReversedCycleFigure
    {amountScale : AmountOfSubstanceScale}
    {gasConstantScale : MolarGasConstantScale}
    (setup : HeliumRefrigeratorSetup amountScale gasConstantScale) : Prop where
  horizontalAxisIsVolume : setup.figure.horizontalAxis = .volume
  verticalAxisIsPressure : setup.figure.verticalAxis = .pressure
  volumeAxisUsesCubicCentimeters :
    setup.figure.axisUnit .volume = .cubicCentimeters
  pressureAxisUsesKilopascals :
    setup.figure.axisUnit .pressure = .kilopascals
  pointCoordinatesRepresentStates : ∀ point,
    setup.figure.pointVolumeInCubicCentimeters point =
        volumeInCubicCentimeters (setup.stateAt point).volume ∧
      setup.figure.pointPressureInKilopascals point =
        pressureInKilopascals (setup.stateAt point).pressure
  leftVolumesReadForty :
    setup.figure.pointVolumeInCubicCentimeters .leftHot = 40 ∧
      setup.figure.pointVolumeInCubicCentimeters .leftCool = 40
  rightVolumesReadOneHundred :
    setup.figure.pointVolumeInCubicCentimeters .rightWarm = 100 ∧
      setup.figure.pointVolumeInCubicCentimeters .rightCold = 100
  upperRightPressureReadsOneHundredFifty :
    setup.figure.pointPressureInKilopascals .rightWarm = 150
  upperRightTemperatureLabel :
    setup.figure.temperatureLabelInDegreesCelsius .rightWarm = some (-23)
  lowerRightTemperatureLabel :
    setup.figure.temperatureLabelInDegreesCelsius .rightCold = some (-73)
  noLeftTemperatureLabels :
    setup.figure.temperatureLabelInDegreesCelsius .leftHot = none ∧
      setup.figure.temperatureLabelInDegreesCelsius .leftCool = none
  displayedTemperatureLabelsRepresentStates :
    stateTemperatureInDegreesCelsius setup .rightWarm = -23 ∧
      stateTemperatureInDegreesCelsius setup .rightCold = -73
  rightLegIsIsochoric :
    setup.figure.legKind .rightIsochoricHeating = .isochoric
  upperCurveIsAdiabatic :
    setup.figure.legKind .upperAdiabaticCompression = .adiabatic
  leftLegIsIsochoric :
    setup.figure.legKind .leftIsochoricCooling = .isochoric
  lowerCurveIsAdiabatic :
    setup.figure.legKind .lowerAdiabaticExpansion = .adiabatic
  arrowsFollowReversedCycle : ∀ leg,
    setup.figure.arrowStart leg = legStart leg ∧
      setup.figure.arrowFinish leg = legFinish leg ∧
      setup.figure.directionArrowShown leg = true
  bothAdiabaticAnnotationsShown :
    setup.figure.adiabaticAnnotationPointsTo .upperAdiabaticCompression = true ∧
      setup.figure.adiabaticAnnotationPointsTo .lowerAdiabaticExpansion = true

/-- Operating rate stated in the question, separate from image evidence. -/
structure MatchesOperatingData
    {amountScale : AmountOfSubstanceScale}
    {gasConstantScale : MolarGasConstantScale}
    (setup : HeliumRefrigeratorSetup amountScale gasConstantScale) : Prop where
  sixtyCyclesPerSecond : frequencyInHertz setup.operatingFrequency = 60

/-- Positivity conditions required by the ideal-gas and adiabatic laws. -/
structure HasPhysicalRefrigeratorParameters
    {amountScale : AmountOfSubstanceScale}
    {gasConstantScale : MolarGasConstantScale}
    (setup : HeliumRefrigeratorSetup amountScale gasConstantScale) : Prop where
  positiveGasAmount : 0 < amountScale.inMoles setup.gasAmount
  positiveGasConstant :
    0 < gasConstantScale.inJoulesPerMoleKelvin setup.universalGasConstant
  everyPressurePositive : ∀ point,
    0 < pressureInPascals (setup.stateAt point).pressure
  everyVolumePositive : ∀ point,
    0 < volumeInCubicMeters (setup.stateAt point).volume
  everyAbsoluteTemperaturePositive : ∀ point,
    0 < stateTemperatureInKelvin setup point
  positiveOperatingFrequency : 0 < frequencyInHertz setup.operatingFrequency
  adiabaticExponentGreaterThanOne : 1 < setup.adiabaticExponent

/-!
Governing laws for a reversible monatomic ideal-gas cycle: pV = nRT;
U = (3/2)nRT; gamma = 5/3; the reversible adiabatic temperature-volume law;
zero heat on adiabats; zero boundary work on isochores; the first law; the
cyclic work-input sign convention; and power equal to work per cycle times
cycle frequency. No field fixes the requested numerical power or an answer.
-/
structure SatisfiesReversibleMonatomicIdealGasCycleLaws
    {amountScale : AmountOfSubstanceScale}
    {gasConstantScale : MolarGasConstantScale}
    (setup : HeliumRefrigeratorSetup amountScale gasConstantScale) : Prop where
  idealGasEquation : ∀ point,
    pressureInPascals (setup.stateAt point).pressure *
        volumeInCubicMeters (setup.stateAt point).volume =
      amountScale.inMoles setup.gasAmount *
        gasConstantScale.inJoulesPerMoleKelvin setup.universalGasConstant *
          stateTemperatureInKelvin setup point
  monatomicInternalEnergy : ∀ point,
    energyInJoules (setup.stateAt point).internalEnergy =
      (3 / 2 : ℝ) * amountScale.inMoles setup.gasAmount *
        gasConstantScale.inJoulesPerMoleKelvin setup.universalGasConstant *
          stateTemperatureInKelvin setup point
  monatomicAdiabaticExponent : setup.adiabaticExponent = 5 / 3
  reversibleAdiabaticTemperatureVolumeLaw : ∀ leg,
    setup.figure.legKind leg = .adiabatic →
      stateTemperatureInKelvin setup (legFinish leg) =
        stateTemperatureInKelvin setup (legStart leg) *
          Real.rpow
            (volumeInCubicMeters (setup.stateAt (legStart leg)).volume /
              volumeInCubicMeters (setup.stateAt (legFinish leg)).volume)
            (setup.adiabaticExponent - 1)
  adiabaticLegsExchangeNoHeat : ∀ leg,
    setup.figure.legKind leg = .adiabatic →
      energyInJoules (setup.heatAbsorbedByGas leg) = 0
  isochoricLegsDoNoBoundaryWork : ∀ leg,
    setup.figure.legKind leg = .isochoric →
      energyInJoules (setup.workDoneByGas leg) = 0
  firstLawOnEachLeg : ∀ leg,
    energyInJoules (setup.stateAt (legFinish leg)).internalEnergy -
        energyInJoules (setup.stateAt (legStart leg)).internalEnergy =
      energyInJoules (setup.heatAbsorbedByGas leg) -
        energyInJoules (setup.workDoneByGas leg)
  workInputIsNegativeNetWorkByGas :
    energyInJoules setup.netWorkInputPerCycle =
      -(energyInJoules (setup.workDoneByGas .rightIsochoricHeating) +
        energyInJoules (setup.workDoneByGas .upperAdiabaticCompression) +
        energyInJoules (setup.workDoneByGas .leftIsochoricCooling) +
        energyInJoules (setup.workDoneByGas .lowerAdiabaticExpansion))
  powerIsWorkPerCycleTimesFrequency :
    powerInWatts setup.inputPower =
      energyInJoules setup.netWorkInputPerCycle *
        frequencyInHertz setup.operatingFrequency

/-! ## Derived exact value and displayed answer choices -/

/-!
The exact SI expression before rounding. Here 5003/20 K is -23 °C, 50 K is
the right-side temperature difference, and (5/2)^(2/3) is the adiabatic
temperature multiplier from 100 cm³ to 40 cm³ for monatomic helium.
-/
def exactModeledInputPowerWatts : ℝ :=
  60 * (3 / 2 : ℝ) *
    ((150000 * (1 / 10000 : ℝ)) / (5003 / 20 : ℝ)) * 50 *
      (Real.rpow (5 / 2 : ℝ) (2 / 3 : ℝ) - 1)

/-- Labels of the four printed power choices. -/
inductive AnswerChoice where
  | A
  | B
  | C
  | D
  deriving DecidableEq, Repr

/-- Whole-watt value printed beside each answer label. -/
def displayedPowerInWatts : AnswerChoice → ℝ
  | .A => 265
  | .B => 190
  | .C => 151
  | .D => 227

/-- Recorded dataset answer, retained only as answer-list metadata. -/
def recordedDatasetAnswer : AnswerChoice := .D

/-- The modeled input power rounds to the displayed whole-watt value. -/
def RoundsToDisplayedWholeWatt
    {amountScale : AmountOfSubstanceScale}
    {gasConstantScale : MolarGasConstantScale}
    (setup : HeliumRefrigeratorSetup amountScale gasConstantScale)
    (choice : AnswerChoice) : Prop :=
  |powerInWatts setup.inputPower - displayedPowerInWatts choice| <
    (1 / 2 : ℝ)

/-- A choice is strictly closer to the modeled power than every alternative. -/
def IsUniqueClosestDisplayedPower
    {amountScale : AmountOfSubstanceScale}
    {gasConstantScale : MolarGasConstantScale}
    (setup : HeliumRefrigeratorSetup amountScale gasConstantScale)
    (choice : AnswerChoice) : Prop :=
  ∀ other : AnswerChoice, other ≠ choice →
    |powerInWatts setup.inputPower - displayedPowerInWatts choice| <
      |powerInWatts setup.inputPower - displayedPowerInWatts other|

/-!
The figure readouts and monatomic ideal-gas laws determine the exact unrounded
power expression. This is a current target conclusion, not an assumption.
-/
lemma inputPower_eq_exactModeledValue
    {amountScale : AmountOfSubstanceScale}
    {gasConstantScale : MolarGasConstantScale}
    (setup : HeliumRefrigeratorSetup amountScale gasConstantScale)
    (_scenario : MatchesHeliumRefrigeratorScenario setup)
    (_figure : MatchesSuppliedReversedCycleFigure setup)
    (_data : MatchesOperatingData setup)
    (_physical : HasPhysicalRefrigeratorParameters setup)
    (_laws : SatisfiesReversibleMonatomicIdealGasCycleLaws setup) :
    powerInWatts setup.inputPower = exactModeledInputPowerWatts := by
  have hTemperatureWarm :
      stateTemperatureInKelvin setup .rightWarm = 5003 / 20 := by
    have h :=
      _figure.displayedTemperatureLabelsRepresentStates.1
    change stateTemperatureInKelvin setup .rightWarm - 5463 / 20 = -23 at h
    linarith
  have hTemperatureCold :
      stateTemperatureInKelvin setup .rightCold = 4003 / 20 := by
    have h :=
      _figure.displayedTemperatureLabelsRepresentStates.2
    change stateTemperatureInKelvin setup .rightCold - 5463 / 20 = -73 at h
    linarith
  have hVolumeRightWarm :
      volumeInCubicMeters (setup.stateAt .rightWarm).volume = 1 / 10000 := by
    have hCoordinates :=
      (_figure.pointCoordinatesRepresentStates .rightWarm).1
    rw [_figure.rightVolumesReadOneHundred.1] at hCoordinates
    unfold volumeInCubicCentimeters at hCoordinates
    linarith
  have hVolumeRightCold :
      volumeInCubicMeters (setup.stateAt .rightCold).volume = 1 / 10000 := by
    have hCoordinates :=
      (_figure.pointCoordinatesRepresentStates .rightCold).1
    rw [_figure.rightVolumesReadOneHundred.2] at hCoordinates
    unfold volumeInCubicCentimeters at hCoordinates
    linarith
  have hVolumeLeftHot :
      volumeInCubicMeters (setup.stateAt .leftHot).volume = 1 / 25000 := by
    have hCoordinates :=
      (_figure.pointCoordinatesRepresentStates .leftHot).1
    rw [_figure.leftVolumesReadForty.1] at hCoordinates
    unfold volumeInCubicCentimeters at hCoordinates
    linarith
  have hVolumeLeftCool :
      volumeInCubicMeters (setup.stateAt .leftCool).volume = 1 / 25000 := by
    have hCoordinates :=
      (_figure.pointCoordinatesRepresentStates .leftCool).1
    rw [_figure.leftVolumesReadForty.2] at hCoordinates
    unfold volumeInCubicCentimeters at hCoordinates
    linarith
  have hPressureWarm :
      pressureInPascals (setup.stateAt .rightWarm).pressure = 150000 := by
    have hCoordinates :=
      (_figure.pointCoordinatesRepresentStates .rightWarm).2
    rw [_figure.upperRightPressureReadsOneHundredFifty] at hCoordinates
    unfold pressureInKilopascals at hCoordinates
    linarith
  have hAmountGasConstant :
      amountScale.inMoles setup.gasAmount *
          gasConstantScale.inJoulesPerMoleKelvin setup.universalGasConstant =
        (150000 * (1 / 10000 : ℝ)) / (5003 / 20 : ℝ) := by
    have h := _laws.idealGasEquation .rightWarm
    rw [hPressureWarm, hVolumeRightWarm, hTemperatureWarm] at h
    norm_num at h ⊢
    linarith
  have hTemperatureLeftHot :
      stateTemperatureInKelvin setup .leftHot =
        (5003 / 20 : ℝ) * Real.rpow (5 / 2 : ℝ) (2 / 3 : ℝ) := by
    have h := _laws.reversibleAdiabaticTemperatureVolumeLaw
      .upperAdiabaticCompression _figure.upperCurveIsAdiabatic
    simp only [legStart, legFinish] at h
    rw [hTemperatureWarm, hVolumeRightWarm, hVolumeLeftHot,
      _laws.monatomicAdiabaticExponent] at h
    norm_num at h ⊢
    exact h
  have hAdiabaticFactorPositive :
      0 < Real.rpow (5 / 2 : ℝ) (2 / 3 : ℝ) := by
    exact Real.rpow_pos_of_pos (by norm_num) _
  have hReciprocalAdiabaticFactor :
      Real.rpow (2 / 5 : ℝ) (2 / 3 : ℝ) =
        (Real.rpow (5 / 2 : ℝ) (2 / 3 : ℝ))⁻¹ := by
    calc
      Real.rpow (2 / 5 : ℝ) (2 / 3 : ℝ) =
          Real.rpow ((5 / 2 : ℝ)⁻¹) (2 / 3 : ℝ) := by norm_num
      _ = (Real.rpow (5 / 2 : ℝ) (2 / 3 : ℝ))⁻¹ :=
        Real.inv_rpow (by norm_num) _
  have hTemperatureLeftCool :
      stateTemperatureInKelvin setup .leftCool =
        (4003 / 20 : ℝ) * Real.rpow (5 / 2 : ℝ) (2 / 3 : ℝ) := by
    have h := _laws.reversibleAdiabaticTemperatureVolumeLaw
      .lowerAdiabaticExpansion _figure.lowerCurveIsAdiabatic
    simp only [legStart, legFinish] at h
    rw [hTemperatureCold, hVolumeLeftCool, hVolumeRightCold,
      _laws.monatomicAdiabaticExponent] at h
    norm_num at h
    change (4003 / 20 : ℝ) =
      stateTemperatureInKelvin setup .leftCool *
        Real.rpow (2 / 5 : ℝ) (2 / 3 : ℝ) at h
    rw [hReciprocalAdiabaticFactor] at h
    calc
      stateTemperatureInKelvin setup .leftCool =
          stateTemperatureInKelvin setup .leftCool *
            ((Real.rpow (5 / 2 : ℝ) (2 / 3 : ℝ))⁻¹ *
              Real.rpow (5 / 2 : ℝ) (2 / 3 : ℝ)) := by
                rw [inv_mul_cancel₀ hAdiabaticFactorPositive.ne', mul_one]
      _ = (stateTemperatureInKelvin setup .leftCool *
            (Real.rpow (5 / 2 : ℝ) (2 / 3 : ℝ))⁻¹) *
              Real.rpow (5 / 2 : ℝ) (2 / 3 : ℝ) := by ring
      _ = (4003 / 20 : ℝ) *
              Real.rpow (5 / 2 : ℝ) (2 / 3 : ℝ) := by rw [← h]
  have hInternalWarm := _laws.monatomicInternalEnergy .rightWarm
  have hInternalCold := _laws.monatomicInternalEnergy .rightCold
  have hInternalHot := _laws.monatomicInternalEnergy .leftHot
  have hInternalCool := _laws.monatomicInternalEnergy .leftCool
  rw [hTemperatureWarm] at hInternalWarm
  rw [hTemperatureCold] at hInternalCold
  rw [hTemperatureLeftHot] at hInternalHot
  rw [hTemperatureLeftCool] at hInternalCool
  have hUpperHeat := _laws.adiabaticLegsExchangeNoHeat
    .upperAdiabaticCompression _figure.upperCurveIsAdiabatic
  have hLowerHeat := _laws.adiabaticLegsExchangeNoHeat
    .lowerAdiabaticExpansion _figure.lowerCurveIsAdiabatic
  have hRightWork := _laws.isochoricLegsDoNoBoundaryWork
    .rightIsochoricHeating _figure.rightLegIsIsochoric
  have hLeftWork := _laws.isochoricLegsDoNoBoundaryWork
    .leftIsochoricCooling _figure.leftLegIsIsochoric
  have hFirstUpper := _laws.firstLawOnEachLeg .upperAdiabaticCompression
  have hFirstLower := _laws.firstLawOnEachLeg .lowerAdiabaticExpansion
  simp only [legStart, legFinish] at hFirstUpper hFirstLower
  rw [hInternalHot, hInternalWarm, hUpperHeat] at hFirstUpper
  rw [hInternalCold, hInternalCool, hLowerHeat] at hFirstLower
  have hUpperWork :
      energyInJoules
          (setup.workDoneByGas .upperAdiabaticCompression) =
        (3 / 2 : ℝ) * amountScale.inMoles setup.gasAmount *
            gasConstantScale.inJoulesPerMoleKelvin setup.universalGasConstant *
              (5003 / 20 : ℝ) -
          (3 / 2 : ℝ) * amountScale.inMoles setup.gasAmount *
            gasConstantScale.inJoulesPerMoleKelvin setup.universalGasConstant *
              ((5003 / 20 : ℝ) *
                Real.rpow (5 / 2 : ℝ) (2 / 3 : ℝ)) := by
    linarith
  have hLowerWork :
      energyInJoules
          (setup.workDoneByGas .lowerAdiabaticExpansion) =
        (3 / 2 : ℝ) * amountScale.inMoles setup.gasAmount *
            gasConstantScale.inJoulesPerMoleKelvin setup.universalGasConstant *
              ((4003 / 20 : ℝ) *
                Real.rpow (5 / 2 : ℝ) (2 / 3 : ℝ)) -
          (3 / 2 : ℝ) * amountScale.inMoles setup.gasAmount *
            gasConstantScale.inJoulesPerMoleKelvin setup.universalGasConstant *
              (4003 / 20 : ℝ) := by
    linarith
  have hWorkInput := _laws.workInputIsNegativeNetWorkByGas
  rw [hRightWork, hUpperWork, hLeftWork, hLowerWork] at hWorkInput
  have hPower := _laws.powerIsWorkPerCycleTimesFrequency
  rw [hWorkInput, _data.sixtyCyclesPerSecond] at hPower
  have hPowerExpression :
      powerInWatts setup.inputPower =
        60 * (3 / 2 : ℝ) *
          (amountScale.inMoles setup.gasAmount *
            gasConstantScale.inJoulesPerMoleKelvin setup.universalGasConstant) *
          50 * (Real.rpow (5 / 2 : ℝ) (2 / 3 : ℝ) - 1) := by
    rw [hPower]
    ring
  rw [hPowerExpression, hAmountGasConstant]
  unfold exactModeledInputPowerWatts
  ring

/-!
The exact value is approximately 227.2 W and therefore rounds uniquely to D.
This is also a current target conclusion, not a premise.
-/
lemma inputPower_rounds_uniquely_to_D
    {amountScale : AmountOfSubstanceScale}
    {gasConstantScale : MolarGasConstantScale}
    (setup : HeliumRefrigeratorSetup amountScale gasConstantScale)
    (_scenario : MatchesHeliumRefrigeratorScenario setup)
    (_figure : MatchesSuppliedReversedCycleFigure setup)
    (_data : MatchesOperatingData setup)
    (_physical : HasPhysicalRefrigeratorParameters setup)
    (_laws : SatisfiesReversibleMonatomicIdealGasCycleLaws setup) :
    RoundsToDisplayedWholeWatt setup .D ∧
      IsUniqueClosestDisplayedPower setup .D := by
  have hPower := inputPower_eq_exactModeledValue setup
    _scenario _figure _data _physical _laws
  have hAdiabaticFactorPositive :
      0 < Real.rpow (5 / 2 : ℝ) (2 / 3 : ℝ) := by
    exact Real.rpow_pos_of_pos (by norm_num) _
  have hAdiabaticFactorCube :
      (Real.rpow (5 / 2 : ℝ) (2 / 3 : ℝ)) ^ 3 = 25 / 4 := by
    change (((5 / 2 : ℝ) ^ (2 / 3 : ℝ)) ^ (3 : ℕ)) = 25 / 4
    rw [← Real.rpow_mul_natCast (by norm_num : (0 : ℝ) ≤ 5 / 2)
      (2 / 3 : ℝ) 3]
    norm_num [Real.rpow_two]
  have hAdiabaticFactorLower :
      (46 / 25 : ℝ) < Real.rpow (5 / 2 : ℝ) (2 / 3 : ℝ) := by
    apply lt_of_pow_lt_pow_left₀ 3 hAdiabaticFactorPositive.le
    rw [hAdiabaticFactorCube]
    norm_num
  have hAdiabaticFactorUpper :
      Real.rpow (5 / 2 : ℝ) (2 / 3 : ℝ) < (1843 / 1000 : ℝ) := by
    apply lt_of_pow_lt_pow_left₀ 3 (by norm_num : (0 : ℝ) ≤ 1843 / 1000)
    rw [hAdiabaticFactorCube]
    norm_num
  have hExactPowerLower :
      (453 / 2 : ℝ) < exactModeledInputPowerWatts := by
    unfold exactModeledInputPowerWatts
    norm_num at hAdiabaticFactorLower ⊢
    nlinarith
  have hExactPowerUpper :
      exactModeledInputPowerWatts < (455 / 2 : ℝ) := by
    unfold exactModeledInputPowerWatts
    norm_num at hAdiabaticFactorUpper ⊢
    nlinarith
  have hRounds :
      |exactModeledInputPowerWatts - 227| < (1 / 2 : ℝ) := by
    rw [abs_lt]
    constructor <;> linarith
  constructor
  · unfold RoundsToDisplayedWholeWatt
    rw [hPower]
    simpa [displayedPowerInWatts] using hRounds
  · unfold IsUniqueClosestDisplayedPower
    intro other hOther
    rw [hPower]
    cases other with
    | A =>
        change |exactModeledInputPowerWatts - 227| <
          |exactModeledInputPowerWatts - 265|
        rw [abs_of_neg
          (show exactModeledInputPowerWatts - 265 < 0 by linarith)]
        linarith
    | B =>
        change |exactModeledInputPowerWatts - 227| <
          |exactModeledInputPowerWatts - 190|
        rw [abs_of_pos
          (show 0 < exactModeledInputPowerWatts - 190 by linarith)]
        linarith
    | C =>
        change |exactModeledInputPowerWatts - 227| <
          |exactModeledInputPowerWatts - 151|
        rw [abs_of_pos
          (show 0 < exactModeledInputPowerWatts - 151 by linarith)]
        linarith
    | D =>
        exact (hOther rfl).elim

/-!
At 60 cycles/s the reversed helium cycle has the exact modeled input power
above and selects answer D, 227 W to the displayed precision.

Blueprint label: thm:physics:phyx_mini_0431:target.
-/
theorem problem_phyx_mini_0431
    {amountScale : AmountOfSubstanceScale}
    {gasConstantScale : MolarGasConstantScale}
    (setup : HeliumRefrigeratorSetup amountScale gasConstantScale)
    (_scenario : MatchesHeliumRefrigeratorScenario setup)
    (_figure : MatchesSuppliedReversedCycleFigure setup)
    (_data : MatchesOperatingData setup)
    (_physical : HasPhysicalRefrigeratorParameters setup)
    (_laws : SatisfiesReversibleMonatomicIdealGasCycleLaws setup) :
    powerInWatts setup.inputPower = exactModeledInputPowerWatts ∧
      RoundsToDisplayedWholeWatt setup .D ∧
      IsUniqueClosestDisplayedPower setup .D := by
  refine ⟨inputPower_eq_exactModeledValue setup
    _scenario _figure _data _physical _laws, ?_⟩
  exact inputPower_rounds_uniquely_to_D setup
    _scenario _figure _data _physical _laws

end PhyXMiniProblems.ProblemPhyXMini0431
