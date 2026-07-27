import Mathlib.Analysis.SpecialFunctions.Exp
import Physlib.Thermodynamics.Temperature.Basic
import Physlib.Units.WithDim.Area
import Physlib.Units.WithDim.Pressure

namespace IPhO2026Problems.IPhO2026_4_B_4

noncomputable section

/-- A physical length, independent of the chosen system of units. -/
abbrev DimLength : Type :=
  Dimensionful (WithDim Dimension.L𝓭 NNReal)

/-- A physical volume, independent of the chosen system of units. -/
abbrev DimVolume : Type :=
  Dimensionful
    (WithDim (Dimension.L𝓭 * Dimension.L𝓭 * Dimension.L𝓭) NNReal)

/-- The numerical value of a pressure in pascals. -/
def pressureInPascals (pressure : DimPressure) : ℝ :=
  (pressure.1 UnitChoices.SI).val

/-- The numerical value of a length in metres. -/
def lengthInMeters (length : DimLength) : ℝ :=
  (length.1 UnitChoices.SI).val

/-- The numerical value of an area in square metres. -/
def areaInSquareMeters (area : DimArea) : ℝ :=
  (area.1 UnitChoices.SI).val

/-- The numerical value of a volume in cubic metres. -/
def volumeInCubicMeters (volume : DimVolume) : ℝ :=
  (volume.1 UnitChoices.SI).val

/-- The numerical value of an absolute temperature in kelvin for this experiment. -/
def temperatureInKelvin (temperature : Temperature) : ℝ :=
  temperature.toReal

/-- Physical dimensions and recorded levels from the Figure 19 inner-cylinder setup. -/
structure Figure19CylinderGeometry where
  innerCylinderCrossSection : DimArea
  initialWaterLevelHeight : DimLength
  referenceGasColumnHeight : DimLength
  measuredGasColumnHeight : DimLength
  referenceGasVolume : DimVolume
  measuredGasVolume : DimVolume

/-- The sample values obtained by extrapolating the B.2 graph in previous part B.3. -/
structure PreviousPartB3Readout (geometry : Figure19CylinderGeometry) : Prop where
  referenceHeight_eq :
    lengthInMeters geometry.referenceGasColumnHeight = (5.9 : ℝ) / 100
  referenceVolume_eq :
    volumeInCubicMeters geometry.referenceGasVolume = (53.4 : ℝ) / 1000000

/-- The dimensional and thermodynamic laws used for the B.4 idealized experiment. -/
structure DryAirWaterVaporExperiment
    (geometry : Figure19CylinderGeometry)
    (referenceTemperature measuredTemperature : Temperature)
    (atmosphericPressure referenceDryAirPressure referenceVaporPressure
      measuredDryAirPressure measuredVaporPressure : DimPressure) : Prop where
  initialWaterLevel_eq :
    lengthInMeters geometry.initialWaterLevelHeight = (5.0 : ℝ) / 100
  referenceTemperature_eq :
    temperatureInKelvin referenceTemperature = 273.15
  crossSection_pos :
    0 < areaInSquareMeters geometry.innerCylinderCrossSection
  referenceHeight_pos :
    0 < lengthInMeters geometry.referenceGasColumnHeight
  measuredHeight_pos :
    0 < lengthInMeters geometry.measuredGasColumnHeight
  referenceVolume_pos :
    0 < volumeInCubicMeters geometry.referenceGasVolume
  measuredVolume_pos :
    0 < volumeInCubicMeters geometry.measuredGasVolume
  referenceTemperature_pos :
    0 < temperatureInKelvin referenceTemperature
  measuredTemperature_pos :
    0 < temperatureInKelvin measuredTemperature
  atmosphericPressure_pos :
    0 < pressureInPascals atmosphericPressure
  referenceDryAirPressure_nonneg :
    0 ≤ pressureInPascals referenceDryAirPressure
  referenceVaporPressure_nonneg :
    0 ≤ pressureInPascals referenceVaporPressure
  measuredDryAirPressure_nonneg :
    0 ≤ pressureInPascals measuredDryAirPressure
  measuredVaporPressure_nonneg :
    0 ≤ pressureInPascals measuredVaporPressure
  referenceVolume_geometry :
    volumeInCubicMeters geometry.referenceGasVolume =
      areaInSquareMeters geometry.innerCylinderCrossSection *
        lengthInMeters geometry.referenceGasColumnHeight
  measuredVolume_geometry :
    volumeInCubicMeters geometry.measuredGasVolume =
      areaInSquareMeters geometry.innerCylinderCrossSection *
        lengthInMeters geometry.measuredGasColumnHeight
  referenceTotalPressure :
    pressureInPascals atmosphericPressure =
      pressureInPascals referenceDryAirPressure +
        pressureInPascals referenceVaporPressure
  referenceVaporPressure_zero :
    pressureInPascals referenceVaporPressure = 0
  measuredTotalPressure :
    pressureInPascals atmosphericPressure =
      pressureInPascals measuredDryAirPressure +
        pressureInPascals measuredVaporPressure
  dryAirIdealGasInvariant :
    pressureInPascals referenceDryAirPressure *
          volumeInCubicMeters geometry.referenceGasVolume /
        temperatureInKelvin referenceTemperature =
      pressureInPascals measuredDryAirPressure *
          volumeInCubicMeters geometry.measuredGasVolume /
        temperatureInKelvin measuredTemperature

/-- Parameters for the equilibrium vapor-pressure law quoted before part B. -/
structure ClausiusClapeyronData where
  referenceVaporPressure : DimPressure
  molarLatentHeatJPerMol : ℝ
  molarGasConstantJPerMolKelvin : ℝ
  molarLatentHeat_pos : 0 < molarLatentHeatJPerMol
  molarGasConstant_eq : molarGasConstantJPerMolKelvin = 8.31

/-- The Clausius--Clapeyron law from equation (3), kept separate from the B.4
zero-reference-vapor approximation. -/
def SatisfiesClausiusClapeyron
    (data : ClausiusClapeyronData)
    (referenceTemperature measuredTemperature : Temperature)
    (measuredVaporPressure : DimPressure) : Prop :=
  pressureInPascals measuredVaporPressure =
    pressureInPascals data.referenceVaporPressure *
      Real.exp
        (-(data.molarLatentHeatJPerMol / data.molarGasConstantJPerMolKelvin) *
          (1 / temperatureInKelvin measuredTemperature -
            1 / temperatureInKelvin referenceTemperature))

/-- In the Figure 19 atmospheric-pressure experiment, the measured water-vapor
partial pressure is determined by the two gas-column heights and absolute temperatures. -/
theorem vaporPressure_formula
    (geometry : Figure19CylinderGeometry)
    (referenceTemperature measuredTemperature : Temperature)
    (atmosphericPressure referenceDryAirPressure referenceVaporPressure
      measuredDryAirPressure measuredVaporPressure : DimPressure)
    (_previousPart : PreviousPartB3Readout geometry)
    (_model : DryAirWaterVaporExperiment geometry referenceTemperature measuredTemperature
      atmosphericPressure referenceDryAirPressure referenceVaporPressure
      measuredDryAirPressure measuredVaporPressure) :
    pressureInPascals measuredVaporPressure =
      pressureInPascals atmosphericPressure *
        (1 -
          lengthInMeters geometry.referenceGasColumnHeight *
              temperatureInKelvin measuredTemperature /
            (lengthInMeters geometry.measuredGasColumnHeight *
              temperatureInKelvin referenceTemperature)) := by
  have hRefDry :
      pressureInPascals referenceDryAirPressure =
        pressureInPascals atmosphericPressure := by
    linarith [_model.referenceTotalPressure, _model.referenceVaporPressure_zero]
  have hInv := _model.dryAirIdealGasInvariant
  rw [_model.referenceVolume_geometry, _model.measuredVolume_geometry, hRefDry] at hInv
  field_simp [ne_of_gt _model.referenceTemperature_pos,
    ne_of_gt _model.measuredTemperature_pos] at hInv
  have hInv' :
      pressureInPascals atmosphericPressure *
            lengthInMeters geometry.referenceGasColumnHeight *
          temperatureInKelvin measuredTemperature =
        temperatureInKelvin referenceTemperature *
            pressureInPascals measuredDryAirPressure *
          lengthInMeters geometry.measuredGasColumnHeight := by
    apply mul_left_cancel₀ (ne_of_gt _model.crossSection_pos)
    nlinarith [hInv]
  have hVapor :
      pressureInPascals measuredVaporPressure =
        pressureInPascals atmosphericPressure -
          pressureInPascals measuredDryAirPressure := by
    linarith [_model.measuredTotalPressure]
  rw [hVapor]
  field_simp [ne_of_gt _model.measuredHeight_pos,
    ne_of_gt _model.referenceTemperature_pos]
  nlinarith [hInv']

end

end IPhO2026Problems.IPhO2026_4_B_4
