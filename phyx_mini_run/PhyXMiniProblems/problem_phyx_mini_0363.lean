import Mathlib.Data.Real.Basic
import Physlib.Thermodynamics.Temperature.Basic
import Physlib.Thermodynamics.Temperature.TemperatureUnits
import Physlib.Units.WithDim.Pressure

noncomputable section

namespace PhyXMiniProblems.ProblemPhyXMini0363

open Dimension

/-- A physical volume, tagged with dimension length cubed and a nonnegative value. -/
abbrev VolumeQuantity : Type :=
  Dimensionful (WithDim (L𝓭 * L𝓭 * L𝓭) NNReal)

/-- Physical pressure, using Physlib's dimensionful pressure type. -/
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

/-- Convert the stored absolute-temperature scale to a kelvin readout. -/
def temperatureInKelvins
    (storageUnit : TemperatureUnit)
    (temperature : TemperatureQuantity) : ℝ :=
  let unitRatio : NNReal := storageUnit / TemperatureUnit.kelvin
  temperature.toReal * (unitRatio : ℝ)

/-- A thermodynamic state with physical pressure, volume, and absolute temperature. -/
structure GasState where
  pressure : PressureQuantity
  volume : VolumeQuantity
  absoluteTemperature : TemperatureQuantity

/-- The directed process arrow in the figure, from point 1 to point 2. -/
structure DirectedGasProcess where
  stateOne : GasState
  stateTwo : GasState
  temperatureStorageUnit : TemperatureUnit

/-- Positivity of the pressure, volume, and kelvin readouts of a state. -/
def HasPositiveReadouts
    (storageUnit : TemperatureUnit) (state : GasState) : Prop :=
  0 < pressureInAtmospheres state.pressure ∧
  0 < volumeInCubicCentimeters state.volume ∧
  0 < temperatureInKelvins storageUnit state.absoluteTemperature

/-- The ideal-gas law written in the chart units atm, cm³, mol, and K. -/
def SatisfiesIdealGasLaw
    (storageUnit : TemperatureUnit)
    (amountMol gasConstantAtmCm3PerMolKelvin : ℝ)
    (state : GasState) : Prop :=
  pressureInAtmospheres state.pressure *
      volumeInCubicCentimeters state.volume =
    amountMol * gasConstantAtmCm3PerMolKelvin *
      temperatureInKelvins storageUnit state.absoluteTemperature

/-- Model the pictured inverse p-V curve by a constant pressure-volume product
between its labeled endpoints. -/
def FollowsInversePVcurve
    (process : DirectedGasProcess) : Prop :=
  pressureInAtmospheres process.stateOne.pressure *
      volumeInCubicCentimeters process.stateOne.volume =
    pressureInAtmospheres process.stateTwo.pressure *
      volumeInCubicCentimeters process.stateTwo.volume

/-- Convert an absolute-temperature readout in kelvin to degrees Celsius. -/
def kelvinToCelsius (temperatureKelvin : ℝ) : ℝ :=
  temperatureKelvin - (27315 : ℝ) / 100

/-- A Celsius value rounds to the displayed whole-degree answer. -/
def RoundsToNearestDegreeCelsius
    (temperatureKelvin displayedCelsius : ℝ) : Prop :=
  |kelvinToCelsius temperatureKelvin - displayedCelsius| < (1 : ℝ) / 2

/--
For the directed process shown, the final temperature at point 2 rounds to
458 degrees Celsius (answer A).
-/
theorem finalTemperatureRoundsTo458C
    (process : DirectedGasProcess)
    (amountMol gasConstantAtmCm3PerMolKelvin : ℝ)
    (hStateOnePositive :
      HasPositiveReadouts process.temperatureStorageUnit process.stateOne)
    (hStateTwoPositive :
      HasPositiveReadouts process.temperatureStorageUnit process.stateTwo)
    (hAmount : amountMol = (20 : ℝ) / 1000)
    (hGasConstant :
      gasConstantAtmCm3PerMolKelvin = (82057 : ℝ) / 1000)
    (hPointOnePressure :
      pressureInAtmospheres process.stateOne.pressure = 3)
    (hPointOneVolume :
      volumeInCubicCentimeters process.stateOne.volume = 400)
    (hPointTwoPressure :
      pressureInAtmospheres process.stateTwo.pressure = 1)
    (hInverseCurve : FollowsInversePVcurve process)
    (hIdealGasAtOne :
      SatisfiesIdealGasLaw process.temperatureStorageUnit amountMol
        gasConstantAtmCm3PerMolKelvin process.stateOne)
    (hIdealGasAtTwo :
      SatisfiesIdealGasLaw process.temperatureStorageUnit amountMol
        gasConstantAtmCm3PerMolKelvin process.stateTwo) :
    RoundsToNearestDegreeCelsius
      (temperatureInKelvins process.temperatureStorageUnit
        process.stateTwo.absoluteTemperature) 458 := by
  unfold RoundsToNearestDegreeCelsius kelvinToCelsius
  unfold FollowsInversePVcurve at hInverseCurve
  unfold SatisfiesIdealGasLaw at hIdealGasAtTwo
  norm_num [hPointOnePressure, hPointOneVolume, hPointTwoPressure, hAmount,
    hGasConstant] at hInverseCurve hIdealGasAtTwo ⊢
  rw [abs_lt]
  constructor <;> nlinarith

end PhyXMiniProblems.ProblemPhyXMini0363
