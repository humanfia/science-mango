import Mathlib
import Physlib.SpaceAndTime.Space.LengthUnit
import Physlib.Thermodynamics.Temperature.Basic
import Physlib.Thermodynamics.Temperature.TemperatureUnits
import Physlib.Units.WithDim.Energy
import Physlib.Units.WithDim.Pressure

/- USER: The assigned source file did not exist when this autoformalization task began. -/

noncomputable section

namespace PhyXMiniProblems.ProblemPhyXMini0406

open Dimension

/-!
# Final pressure after insulated gas--water thermal contact

A rigid `4000 cm³` container holds `0.40 mol` of a monatomic ideal gas at
`10 atm`. A beaker containing `20 g` of water at `20 °C` has a thin metal
bottom in good thermal contact with the gas. Exterior insulation makes the
combined gas--water system energetically isolated, and the containers have
negligible thermal mass. After a long time the water and gas have a common
temperature.

Mass, volume, pressure, energy, and absolute temperature are represented by
physical quantity types. Real numbers occur only as calibrated readouts in
named units. Amount of substance and specific heat capacity use small abstract
scale interfaces because Physlib does not provide the molar macroscopic model
needed by this problem.
-/

/-! ## Physical quantities and calibrated readouts -/

/-- The physical dimension of volume, `L³`. -/
def volumeDimension : Dimension := L𝓭 * L𝓭 * L𝓭

/-- A nonnegative, unit-independent physical mass. -/
abbrev MassQuantity : Type := Dimensionful (WithDim M𝓭 NNReal)

/-- A nonnegative, unit-independent physical volume. -/
abbrev VolumeQuantity : Type :=
  Dimensionful (WithDim volumeDimension NNReal)

/--
An abstract physical amount-of-substance scale with a calibrated mole
readout. The carrier is not identified with a bare real number.
-/
structure AmountOfSubstanceScale where
  Quantity : Type
  inMoles : Quantity → ℝ

/--
An abstract scale for mass-specific heat capacity, calibrated in joules per
kilogram-kelvin.
-/
structure SpecificHeatCapacityScale where
  Quantity : Type
  inJoulesPerKilogramKelvin : Quantity → ℝ

/-- Read a physical mass in a selected mass unit. -/
def massReadout (unit : MassUnit) (mass : MassQuantity) : ℝ :=
  ((mass {UnitChoices.SI with mass := unit}).val : ℝ)

/-- Read a physical volume in the cube of a selected length unit. -/
def volumeReadout (unit : LengthUnit) (volume : VolumeQuantity) : ℝ :=
  ((volume {UnitChoices.SI with length := unit}).val : ℝ)

/-- Read a dimensionful pressure in coherent SI pascals. -/
def pressureInPascals (pressure : DimPressure) : ℝ :=
  (pressure UnitChoices.SI).val

/-- Read a dimensionful energy in coherent SI joules. -/
def energyInJoules (energy : DimEnergy) : ℝ :=
  (energy UnitChoices.SI).val

/-- Gram readout used for the water mass in the problem statement. -/
def massInGrams (mass : MassQuantity) : ℝ :=
  massReadout MassUnit.grams mass

/-- Kilogram readout used by the calorimetry law. -/
def massInKilograms (mass : MassQuantity) : ℝ :=
  massReadout MassUnit.kilograms mass

/-- Cubic-centimetre readout used for the gas-container volume. -/
def volumeInCubicCentimeters (volume : VolumeQuantity) : ℝ :=
  volumeReadout LengthUnit.centimeters volume

/-- Cubic-metre readout used by the SI ideal-gas law. -/
def volumeInCubicMeters (volume : VolumeQuantity) : ℝ :=
  volumeReadout LengthUnit.meters volume

/-- Kelvin readout of Physlib's absolute temperature. -/
def temperatureInKelvin (temperature : Temperature) : ℝ :=
  Temperature.toReal temperature

/-- Celsius readout obtained from the absolute kelvin readout. -/
def temperatureInDegreesCelsius (temperature : Temperature) : ℝ :=
  temperatureInKelvin temperature - (27315 / 100 : ℝ)

/-- Pressure as a multiple of Physlib's standard atmosphere. -/
def pressureInStandardAtmospheres (pressure : DimPressure) : ℝ :=
  pressureInPascals pressure /
    pressureInPascals DimPressure.standardAtmosphere

/-- Universal molar gas constant, read in joules per mole-kelvin. -/
def universalMolarGasConstant_J_per_mol_K : ℝ :=
  8314 / 1000

/-! ## Time stages, apparatus roles, and primary-figure data -/

/-- The given initial state and the equilibrium state reached after a long time. -/
inductive ThermalStage where
  | initial
  | equilibratedAfterLongTime
  deriving DecidableEq, Fintype, Repr

/-- The constitution of the gas named in the prose. -/
inductive GasConstitution where
  | monatomic
  | other
  deriving DecidableEq, Repr

/-- Material forming the thermally conducting interface. -/
inductive InterfaceMaterial where
  | metal
  | other
  deriving DecidableEq, Repr

/-- Quality of thermal contact across the beaker bottom. -/
inductive ThermalContactQuality where
  | good
  | poor
  deriving DecidableEq, Repr

/-- Thermal condition of the apparatus boundary. -/
inductive ExteriorBoundaryCondition where
  | insulated
  | exchangesHeatWithSurroundings
  deriving DecidableEq, Repr

/-- Thermal-mass idealization for the beaker and gas container. -/
inductive ContainerThermalMassModel where
  | negligible
  | nonnegligible
  deriving DecidableEq, Repr

/-- Literal labels visible in the supplied raster. -/
inductive FigureLabel where
  | water
  | gas
  | thinMetal
  | insulation
  deriving DecidableEq, Fintype, Repr

/-- The two material regions vertically separated by the thin metal line. -/
inductive FigureRegion where
  | upper
  | lower
  deriving DecidableEq, Fintype, Repr

/-- Material shown in a region of the figure. -/
inductive FigureRegionContent where
  | water
  | gas
  deriving DecidableEq, Repr

/-- Qualitative information retained from the supplied figure. -/
structure SuppliedThermalContactFigure where
  labelShown : FigureLabel → Bool
  regionContent : FigureRegion → FigureRegionContent
  upperRegionAboveLowerRegion : Bool
  thinMetalSeparatesRegions : Bool
  waterTouchesThinMetal : Bool
  gasTouchesThinMetal : Bool
  insulationSurroundsWaterAndGas : Bool

/-- A thermodynamic state of the monatomic gas. -/
structure GasState where
  pressure : DimPressure
  volume : VolumeQuantity
  absoluteTemperature : Temperature
  internalEnergy : DimEnergy

/-- A thermal state of the water. -/
structure WaterState where
  absoluteTemperature : Temperature
  internalEnergy : DimEnergy

/-!
All independent physical quantities of the experiment. The final gas pressure
is an unknown observable inside the final `GasState`; it is not defined from
an answer choice or requested value.
-/
structure InsulatedGasWaterSetup
    (amountScale : AmountOfSubstanceScale)
    (heatCapacityScale : SpecificHeatCapacityScale) where
  gasConstitution : GasConstitution
  interfaceMaterial : InterfaceMaterial
  contactQuality : ThermalContactQuality
  exteriorBoundary : ExteriorBoundaryCondition
  containerThermalMassModel : ContainerThermalMassModel
  gasContainerRigid : Bool
  temperatureUnit : TemperatureUnit
  gasAmount : amountScale.Quantity
  waterMass : MassQuantity
  waterSpecificHeatCapacity : heatCapacityScale.Quantity
  gasState : ThermalStage → GasState
  waterState : ThermalStage → WaterState
  figure : SuppliedThermalContactFigure

/-! ## Scenario, figure/data readouts, and governing laws -/

/-- Qualitative apparatus and material assumptions stated in the prose. -/
structure MatchesInsulatedGasWaterScenario
    {amountScale : AmountOfSubstanceScale}
    {heatCapacityScale : SpecificHeatCapacityScale}
    (setup : InsulatedGasWaterSetup amountScale heatCapacityScale) : Prop where
  gasIsMonatomic : setup.gasConstitution = .monatomic
  interfaceIsMetal : setup.interfaceMaterial = .metal
  waterAndGasHaveGoodThermalContact : setup.contactQuality = .good
  surroundingsAreThermallyInsulated :
    setup.exteriorBoundary = .insulated
  containersHaveNegligibleThermalMass :
    setup.containerThermalMassModel = .negligible
  gasContainerVolumeIsRigid : setup.gasContainerRigid = true
  absoluteTemperatureScaleIsKelvin :
    setup.temperatureUnit = TemperatureUnit.kelvin

/-- Qualitative labels and geometry read directly from the primary image. -/
structure MatchesSuppliedThermalContactFigure
    (figure : SuppliedThermalContactFigure) : Prop where
  everyLiteralLabelShown : ∀ label, figure.labelShown label = true
  upperRegionContainsWater : figure.regionContent .upper = .water
  lowerRegionContainsGas : figure.regionContent .lower = .gas
  waterIsAboveGas : figure.upperRegionAboveLowerRegion = true
  thinMetalBetweenWaterAndGas : figure.thinMetalSeparatesRegions = true
  waterContactsMetal : figure.waterTouchesThinMetal = true
  gasContactsMetal : figure.gasTouchesThinMetal = true
  insulationEnclosesBothRegions :
    figure.insulationSurroundsWaterAndGas = true

/-! Numerical data stated in the problem; no final pressure occurs here. -/
structure MatchesProblemReadouts
    {amountScale : AmountOfSubstanceScale}
    {heatCapacityScale : SpecificHeatCapacityScale}
    (setup : InsulatedGasWaterSetup amountScale heatCapacityScale) : Prop where
  waterMassGrams : massInGrams setup.waterMass = 20
  initialWaterTemperatureCelsius :
    temperatureInDegreesCelsius
      (setup.waterState .initial).absoluteTemperature = 20
  gasContainerVolumeCubicCentimeters :
    volumeInCubicCentimeters (setup.gasState .initial).volume = 4000
  gasAmountMoles : amountScale.inMoles setup.gasAmount = 2 / 5
  initialGasPressureAtmospheres :
    pressureInStandardAtmospheres (setup.gasState .initial).pressure = 10

/-!
Supplemental textbook thermal data needed for the numerical calculation. The
problem expects this material property rather than printing it.
-/
structure UsesReferenceWaterThermalData
    {amountScale : AmountOfSubstanceScale}
    {heatCapacityScale : SpecificHeatCapacityScale}
    (setup : InsulatedGasWaterSetup amountScale heatCapacityScale) : Prop where
  liquidWaterSpecificHeat_J_per_kg_K :
    heatCapacityScale.inJoulesPerKilogramKelvin
      setup.waterSpecificHeatCapacity = 4186

/-- Positivity and nondegeneracy conditions for physical observables. -/
structure HasPhysicalThermodynamicParameters
    {amountScale : AmountOfSubstanceScale}
    {heatCapacityScale : SpecificHeatCapacityScale}
    (setup : InsulatedGasWaterSetup amountScale heatCapacityScale) : Prop where
  waterMassPositive : 0 < massInKilograms setup.waterMass
  gasAmountPositive : 0 < amountScale.inMoles setup.gasAmount
  waterSpecificHeatPositive :
    0 < heatCapacityScale.inJoulesPerKilogramKelvin
      setup.waterSpecificHeatCapacity
  gasPressuresPositive :
    ∀ stage, 0 < pressureInPascals (setup.gasState stage).pressure
  gasVolumesPositive :
    ∀ stage, 0 < volumeInCubicMeters (setup.gasState stage).volume
  gasTemperaturesPositive :
    ∀ stage, 0 < temperatureInKelvin
      (setup.gasState stage).absoluteTemperature
  waterTemperaturesPositive :
    ∀ stage, 0 < temperatureInKelvin
      (setup.waterState stage).absoluteTemperature

/-!
Governing thermodynamic relations in coherent SI readouts: rigid volume,
`PV = nRT`, monatomic-gas internal energy, water calorimetry, conservation of
the isolated gas--water energy, and common long-time temperature. None contains
a numerical final pressure or answer choice.
-/
structure SatisfiesInsulatedGasWaterLaws
    {amountScale : AmountOfSubstanceScale}
    {heatCapacityScale : SpecificHeatCapacityScale}
    (setup : InsulatedGasWaterSetup amountScale heatCapacityScale) : Prop where
  rigidGasVolume :
    (setup.gasState .equilibratedAfterLongTime).volume =
      (setup.gasState .initial).volume
  molarIdealGasLaw : ∀ stage,
    pressureInPascals (setup.gasState stage).pressure *
        volumeInCubicMeters (setup.gasState stage).volume =
      amountScale.inMoles setup.gasAmount *
        universalMolarGasConstant_J_per_mol_K *
        temperatureInKelvin (setup.gasState stage).absoluteTemperature
  monatomicGasInternalEnergy : ∀ stage,
    energyInJoules (setup.gasState stage).internalEnergy =
      (3 / 2 : ℝ) * amountScale.inMoles setup.gasAmount *
        universalMolarGasConstant_J_per_mol_K *
        temperatureInKelvin (setup.gasState stage).absoluteTemperature
  waterSensibleEnergyChange :
    energyInJoules
          (setup.waterState .equilibratedAfterLongTime).internalEnergy -
        energyInJoules (setup.waterState .initial).internalEnergy =
      massInKilograms setup.waterMass *
        heatCapacityScale.inJoulesPerKilogramKelvin
          setup.waterSpecificHeatCapacity *
        (temperatureInKelvin
            (setup.waterState .equilibratedAfterLongTime).absoluteTemperature -
          temperatureInKelvin
            (setup.waterState .initial).absoluteTemperature)
  isolatedTotalEnergyConservation :
    energyInJoules
          (setup.gasState .equilibratedAfterLongTime).internalEnergy +
        energyInJoules
          (setup.waterState .equilibratedAfterLongTime).internalEnergy =
      energyInJoules (setup.gasState .initial).internalEnergy +
        energyInJoules (setup.waterState .initial).internalEnergy
  longTimeThermalEquilibrium :
    temperatureInKelvin
        (setup.gasState .equilibratedAfterLongTime).absoluteTemperature =
      temperatureInKelvin
        (setup.waterState .equilibratedAfterLongTime).absoluteTemperature

/-! ## Displayed choices and formal conclusions -/

/-- Labels of the four gas-pressure choices printed in the problem. -/
inductive AnswerChoice where
  | A
  | B
  | C
  | D
  deriving DecidableEq, Fintype, Repr

/-- Pressure in standard atmospheres printed beside each answer label. -/
def displayedPressureInAtmospheres : AnswerChoice → ℝ
  | .A => 5
  | .B => 10
  | .C => 14 / 5
  | .D => 1

/-- The dataset's recorded answer, retained only as metadata. -/
def recordedDatasetAnswer : AnswerChoice := .C

/-- A displayed pressure agrees after rounding to one decimal place. -/
def RoundsToDisplayedPressure
    {amountScale : AmountOfSubstanceScale}
    {heatCapacityScale : SpecificHeatCapacityScale}
    (setup : InsulatedGasWaterSetup amountScale heatCapacityScale)
    (choice : AnswerChoice) : Prop :=
  |pressureInStandardAtmospheres
      (setup.gasState .equilibratedAfterLongTime).pressure -
        displayedPressureInAtmospheres choice| < 1 / 20

/-- A choice is at least as close as every displayed pressure. -/
def IsClosestDisplayedPressure
    {amountScale : AmountOfSubstanceScale}
    {heatCapacityScale : SpecificHeatCapacityScale}
    (setup : InsulatedGasWaterSetup amountScale heatCapacityScale)
    (choice : AnswerChoice) : Prop :=
  ∀ other : AnswerChoice,
    |pressureInStandardAtmospheres
        (setup.gasState .equilibratedAfterLongTime).pressure -
          displayedPressureInAtmospheres choice| ≤
      |pressureInStandardAtmospheres
        (setup.gasState .equilibratedAfterLongTime).pressure -
          displayedPressureInAtmospheres other|

/-- The selected answer is the unique closest displayed pressure. -/
def IsUniqueClosestDisplayedPressure
    {amountScale : AmountOfSubstanceScale}
    {heatCapacityScale : SpecificHeatCapacityScale}
    (setup : InsulatedGasWaterSetup amountScale heatCapacityScale)
    (choice : AnswerChoice) : Prop :=
  IsClosestDisplayedPressure setup choice ∧
    ∀ other : AnswerChoice,
      IsClosestDisplayedPressure setup other → other = choice

/-! Unit-conversion consequences of the dimensional quantity types. -/

lemma massInKilograms_eq_massInGrams_div_thousand
    (mass : MassQuantity) :
    massInKilograms mass = massInGrams mass / 1000 := by
  unfold massInKilograms massInGrams massReadout
  have h := congrArg (fun x : WithDim M𝓭 NNReal => (x.val : ℝ))
    (mass.2 UnitChoices.SI
      ({UnitChoices.SI with mass := MassUnit.grams} : UnitChoices))
  norm_num [UnitChoices.dimScale, UnitChoices.SI, MassUnit.grams,
    MassUnit.kilograms, M𝓭, NNReal.smul_def] at h ⊢
  simp only [NNReal.toReal] at h ⊢
  linarith

lemma volumeInCubicMeters_eq_volumeInCubicCentimeters_div_million
    (volume : VolumeQuantity) :
    volumeInCubicMeters volume =
      volumeInCubicCentimeters volume / 1000000 := by
  unfold volumeInCubicMeters volumeInCubicCentimeters volumeReadout
  have h := congrArg (fun x : WithDim volumeDimension NNReal => (x.val : ℝ))
    (volume.2 UnitChoices.SI
      ({UnitChoices.SI with length := LengthUnit.centimeters} : UnitChoices))
  norm_num [UnitChoices.dimScale, UnitChoices.SI, LengthUnit.centimeters,
    LengthUnit.meters, volumeDimension, L𝓭, NNReal.smul_def] at h ⊢
  simp only [NNReal.toReal] at h ⊢
  linarith

lemma pressureInPascals_eq_atmospheres_mul_standardAtmosphere
    (pressure : DimPressure) :
    pressureInPascals pressure =
      pressureInStandardAtmospheres pressure * 101325 := by
  unfold pressureInStandardAtmospheres
  have hstd :
      pressureInPascals DimPressure.standardAtmosphere = 101325 := by
    norm_num [pressureInPascals, DimPressure.standardAtmosphere,
      CarriesDimension.toDimensionful_apply_apply]
  rw [hstd]
  ring

/-!
The energy balance determines a common equilibrium temperature of about
`345.20 K`; the exact rational SI readout is retained here.
-/
lemma finalEquilibriumTemperatureInKelvin_eq
    {amountScale : AmountOfSubstanceScale}
    {heatCapacityScale : SpecificHeatCapacityScale}
    (setup : InsulatedGasWaterSetup amountScale heatCapacityScale)
    (_readouts : MatchesProblemReadouts setup)
    (_thermalData : UsesReferenceWaterThermalData setup)
    (_laws : SatisfiesInsulatedGasWaterLaws setup) :
    temperatureInKelvin
        (setup.gasState .equilibratedAfterLongTime).absoluteTemperature =
      76555045 / 221771 := by
  have h_mass :=
    massInKilograms_eq_massInGrams_div_thousand setup.waterMass
  rw [_readouts.waterMassGrams] at h_mass
  norm_num at h_mass
  have h_volume :=
    volumeInCubicMeters_eq_volumeInCubicCentimeters_div_million
      (setup.gasState .initial).volume
  rw [_readouts.gasContainerVolumeCubicCentimeters] at h_volume
  norm_num at h_volume
  have h_pressure :=
    pressureInPascals_eq_atmospheres_mul_standardAtmosphere
      (setup.gasState .initial).pressure
  rw [_readouts.initialGasPressureAtmospheres] at h_pressure
  norm_num at h_pressure
  have h_waterInitial := _readouts.initialWaterTemperatureCelsius
  norm_num [temperatureInDegreesCelsius] at h_waterInitial
  have h_amount := _readouts.gasAmountMoles
  norm_num at h_amount
  have h_heat := _thermalData.liquidWaterSpecificHeat_J_per_kg_K
  have h_ideal := _laws.molarIdealGasLaw .initial
  rw [h_pressure, h_volume, h_amount] at h_ideal
  norm_num [universalMolarGasConstant_J_per_mol_K] at h_ideal
  have h_gasInitial := _laws.monatomicGasInternalEnergy .initial
  rw [h_amount] at h_gasInitial
  norm_num [universalMolarGasConstant_J_per_mol_K] at h_gasInitial
  have h_gasFinal :=
    _laws.monatomicGasInternalEnergy .equilibratedAfterLongTime
  rw [h_amount] at h_gasFinal
  norm_num [universalMolarGasConstant_J_per_mol_K] at h_gasFinal
  have h_water := _laws.waterSensibleEnergyChange
  rw [h_mass, h_heat] at h_water
  norm_num at h_water
  have h_conservation := _laws.isolatedTotalEnergyConservation
  have h_equilibrium := _laws.longTimeThermalEquilibrium
  linarith

/-!
The final ideal-gas equation then gives approximately `2.83245 atm`.
-/
lemma finalGasPressureInStandardAtmospheres_eq
    {amountScale : AmountOfSubstanceScale}
    {heatCapacityScale : SpecificHeatCapacityScale}
    (setup : InsulatedGasWaterSetup amountScale heatCapacityScale)
    (_readouts : MatchesProblemReadouts setup)
    (_thermalData : UsesReferenceWaterThermalData setup)
    (_laws : SatisfiesInsulatedGasWaterLaws setup) :
    pressureInStandardAtmospheres
        (setup.gasState .equilibratedAfterLongTime).pressure =
      9092552059 / 3210135225 := by
  have h_temperature :=
    finalEquilibriumTemperatureInKelvin_eq
      setup _readouts _thermalData _laws
  have h_initialVolume :=
    volumeInCubicMeters_eq_volumeInCubicCentimeters_div_million
      (setup.gasState .initial).volume
  rw [_readouts.gasContainerVolumeCubicCentimeters] at h_initialVolume
  norm_num at h_initialVolume
  have h_rigid :=
    congrArg volumeInCubicMeters _laws.rigidGasVolume
  rw [h_initialVolume] at h_rigid
  have h_amount := _readouts.gasAmountMoles
  norm_num at h_amount
  have h_ideal := _laws.molarIdealGasLaw .equilibratedAfterLongTime
  rw [h_rigid, h_amount, h_temperature] at h_ideal
  norm_num [universalMolarGasConstant_J_per_mol_K] at h_ideal
  have h_pressure :=
    pressureInPascals_eq_atmospheres_mul_standardAtmosphere
      (setup.gasState .equilibratedAfterLongTime).pressure
  linarith

/-!
The modeled final pressure rounds to `2.8 atm` and uniquely selects choice C.

This formalizes blueprint label `thm:physics:phyx_mini_0406:target`.
-/
theorem problem_phyx_mini_0406
    {amountScale : AmountOfSubstanceScale}
    {heatCapacityScale : SpecificHeatCapacityScale}
    (setup : InsulatedGasWaterSetup amountScale heatCapacityScale)
    (_scenario : MatchesInsulatedGasWaterScenario setup)
    (_figure : MatchesSuppliedThermalContactFigure setup.figure)
    (_readouts : MatchesProblemReadouts setup)
    (_thermalData : UsesReferenceWaterThermalData setup)
    (_physical : HasPhysicalThermodynamicParameters setup)
    (_laws : SatisfiesInsulatedGasWaterLaws setup) :
    pressureInStandardAtmospheres
          (setup.gasState .equilibratedAfterLongTime).pressure =
        9092552059 / 3210135225 ∧
      RoundsToDisplayedPressure setup .C ∧
      IsUniqueClosestDisplayedPressure setup .C ∧
      recordedDatasetAnswer = .C := by
  have h_pressure :=
    finalGasPressureInStandardAtmospheres_eq
      setup _readouts _thermalData _laws
  refine ⟨h_pressure, ?_, ?_, rfl⟩
  · norm_num [RoundsToDisplayedPressure, h_pressure,
      displayedPressureInAtmospheres, abs_of_nonneg, abs_of_neg]
  · constructor
    · intro other
      rw [h_pressure]
      cases other <;>
        norm_num [displayedPressureInAtmospheres, abs_of_nonneg, abs_of_neg]
    · intro other h_other
      unfold IsClosestDisplayedPressure at h_other
      cases other with
      | A =>
          have h := h_other .C
          rw [h_pressure] at h
          norm_num [displayedPressureInAtmospheres, abs_of_nonneg,
            abs_of_neg] at h
      | B =>
          have h := h_other .C
          rw [h_pressure] at h
          norm_num [displayedPressureInAtmospheres, abs_of_nonneg,
            abs_of_neg] at h
      | C => rfl
      | D =>
          have h := h_other .C
          rw [h_pressure] at h
          norm_num [displayedPressureInAtmospheres, abs_of_nonneg,
            abs_of_neg] at h

end PhyXMiniProblems.ProblemPhyXMini0406
