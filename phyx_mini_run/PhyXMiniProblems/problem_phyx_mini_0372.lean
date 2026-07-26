import Mathlib
import Physlib.Thermodynamics.Temperature.Basic

/-!
# PhyX mini problem 0372

An ideal-gas sample follows the directed process `1 → 2 → 3` in a pressure-volume
diagram.  Pressure and volume are represented by their measured scalar components in
atmospheres and cubic centimetres, respectively; absolute temperature uses PhysLean's
`Temperature` type.

The source calls the gas helium and records choice A, `-29 °C`.  The recorded choice is
inconsistent with the helium mass and the state-1 coordinates in the primary image, so
it is retained below only as source metadata.  The theorem states the exact temperature
supported by the source data and the ideal-gas law.  Its conclusion is not included in
any physical-law or figure hypothesis.
-/

namespace PhyXMini0372

/-- The gas species named in the problem statement. -/
inductive GasSpecies where
  | helium
  deriving DecidableEq

/-- A fixed gas sample, with mass measured in grams and amount in moles. -/
structure GasSample where
  species : GasSpecies
  massGrams : ℝ
  amountMoles : ℝ

/-- One labelled point of the pressure-volume diagram.

The scalar fields are readouts in the units printed on the axes.  Temperature remains
an absolute physical temperature rather than an unrestricted real number. -/
structure PVState where
  pressureAtm : ℝ
  volumeCm3 : ℝ
  temperature : Temperature

/-- The three labelled states and the two directed process segments shown in the figure. -/
structure ThreeStateProcess where
  sample : GasSample
  state1 : PVState
  state2 : PVState
  state3 : PVState
  transition : PVState → PVState → Prop
  firstToSecond : transition state1 state2
  secondToThird : transition state2 state3

/-- Mixed-unit material and ideal-gas constants used by the textbook calculation. -/
structure IdealGasParameters where
  molarMassGramsPerMole : GasSpecies → ℝ
  gasConstantAtmCm3PerMoleKelvin : ℝ

/-- The governing conversion from sample mass to amount of substance. -/
def SatisfiesMassMoleRelation (parameters : IdealGasParameters)
    (sample : GasSample) : Prop :=
  sample.massGrams =
    sample.amountMoles * parameters.molarMassGramsPerMole sample.species

/-- The ideal-gas equation `p V = n R T`, expressed in the units printed in the problem. -/
def SatisfiesIdealGasEquation (parameters : IdealGasParameters)
    (sample : GasSample) (state : PVState) : Prop :=
  state.pressureAtm * state.volumeCm3 =
    sample.amountMoles * parameters.gasConstantAtmCm3PerMoleKelvin *
      state.temperature.toReal

/-- Celsius readout of an absolute temperature whose underlying readout is in kelvin. -/
noncomputable def temperatureInDegreesCelsius (temperature : Temperature) : ℝ :=
  temperature.toReal - 27315 / 100

/--
For the source-stated helium sample and the primary image's directed diagram
`1 → 2 → 3`, the ideal-gas law gives
`T₁ = 200000 / 4103 K`, hence `T₁ = 200000 / 4103 - 273.15 °C`.

The dataset records choice A, `-29 °C`, but that value is source metadata rather than a
premise or conclusion because it contradicts the stated helium data.

Blueprint label: `thm:physics:phyx_mini_0372:target`.
-/
theorem stateOneTemperature_from_heliumData
    (process : ThreeStateProcess)
    (parameters : IdealGasParameters)
    (h_species : process.sample.species = GasSpecies.helium)
    (h_mass_readout : process.sample.massGrams = 1 / 10)
    (h_molar_mass_helium :
      parameters.molarMassGramsPerMole GasSpecies.helium = 4)
    (h_gas_constant :
      parameters.gasConstantAtmCm3PerMoleKelvin = 4103 / 50)
    (h_amount_positive : 0 < process.sample.amountMoles)
    (h_mass_mole : SatisfiesMassMoleRelation parameters process.sample)
    (h_state1_ideal :
      SatisfiesIdealGasEquation parameters process.sample process.state1)
    (h_state2_ideal :
      SatisfiesIdealGasEquation parameters process.sample process.state2)
    (h_state3_ideal :
      SatisfiesIdealGasEquation parameters process.sample process.state3)
    (h_state1_pressure_readout : process.state1.pressureAtm = 1)
    (h_state1_volume_readout : process.state1.volumeCm3 = 100)
    (h_state2_volume_readout : process.state2.volumeCm3 = 300)
    (h_state2_temperature_readout : process.state2.temperature.toReal = 2926)
    (h_state3_pressure_readout : process.state3.pressureAtm = 2)
    (h_state3_temperature_readout : process.state3.temperature.toReal = 2438)
    (h_state2_pressure_positive : 0 < process.state2.pressureAtm)
    (h_state3_volume_positive : 0 < process.state3.volumeCm3) :
    temperatureInDegreesCelsius process.state1.temperature =
      200000 / 4103 - 27315 / 100 := by
  unfold SatisfiesMassMoleRelation at h_mass_mole
  unfold SatisfiesIdealGasEquation at h_state1_ideal
  unfold temperatureInDegreesCelsius
  rw [h_mass_readout, h_species, h_molar_mass_helium] at h_mass_mole
  rw [h_state1_pressure_readout, h_state1_volume_readout, h_gas_constant] at h_state1_ideal
  norm_num at h_mass_mole h_state1_ideal ⊢
  nlinarith

end PhyXMini0372
