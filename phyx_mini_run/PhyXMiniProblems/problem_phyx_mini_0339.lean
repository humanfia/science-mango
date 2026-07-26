import Mathlib
import Physlib.Thermodynamics.Temperature.Basic
import Physlib.Units.WithDim.Energy
import Physlib.Units.WithDim.Pressure

/-!
# Internal-energy change in an isothermal ideal-gas process

The primary figure is a pressure-volume diagram.  Its blue curve is directed
from the point `a`, at `0.600 atm`, to the point `b`, at `0.200 atm` and
`0.100 m³`.  The gas remains at `85 °C` throughout the process.

Pressure, volume, and internal energy are represented by unit-independent
dimensionful Physlib quantities.  Real numbers are used only for readouts in
the units printed in the problem and for the process parameter.
-/

noncomputable section

namespace PhyXMiniProblems.ProblemPhyXMini0339

open Dimension

/-! ## Physical quantities and readouts -/

/-- A physical volume, carrying the dimension `L³`. -/
abbrev GasVolume : Type :=
  Dimensionful (WithDim (L𝓭 * L𝓭 * L𝓭) ℝ)

/-- The pressure readout in standard atmospheres. -/
def pressureInAtmospheres (pressure : DimPressure) : ℝ :=
  (pressure UnitChoices.SI).val /
    (DimPressure.standardAtmosphere UnitChoices.SI).val

/-- The volume readout in cubic metres. -/
def volumeInCubicMeters (volume : GasVolume) : ℝ :=
  (volume UnitChoices.SI).val

/--
The Celsius readout obtained from an absolute-temperature value interpreted
in kelvin.  The offset is `273.15 K`.
-/
def temperatureInDegreesCelsius (temperature : Temperature) : ℝ :=
  temperature.toReal - 27315 / 100

/-- The SI readout of an energy; for `DimEnergy` this is measured in joules. -/
def energyInJoules (energy : DimEnergy) : ℝ :=
  (energy UnitChoices.SI).val

/-! ## Gas states and labels from the figure -/

/-- The two endpoint labels printed beside the blue process curve. -/
inductive PVDiagramPoint where
  | a
  | b
  deriving DecidableEq, Repr

/-- A thermodynamic state of the ideal gas. -/
structure IdealGasState where
  pressure : DimPressure
  volume : GasVolume
  temperature : Temperature
  internalEnergy : DimEnergy

/--
Constitutive data for a fixed sample of ideal gas.  In particular,
`internalEnergyAtTemperature` expresses the ideal-gas fact that internal
energy has temperature, rather than pressure or volume, as its state
variable.
-/
structure IdealGasSample where
  amountOfGasInMoles : ℝ
  internalEnergyAtTemperature : Temperature → DimEnergy

/--
The blue curve, parameterized from `0` to `1`.  The endpoint labels are stored
explicitly so that its arrow direction is part of the model rather than only
documentation.
-/
structure IdealGasPVProcess where
  gas : IdealGasSample
  stateAlong : ℝ → IdealGasState
  startLabel : PVDiagramPoint
  endLabel : PVDiagramPoint

/-- State at the endpoint marked `a` in the diagram. -/
def stateAtA (process : IdealGasPVProcess) : IdealGasState :=
  process.stateAlong 0

/-- State at the endpoint marked `b` in the diagram. -/
def stateAtB (process : IdealGasPVProcess) : IdealGasState :=
  process.stateAlong 1

/-! ## Scenario data and governing physics -/

/--
The direction and numerical readouts supplied by the problem and primary
image.  The blue curve, not either dashed coordinate guide, is the process.
No value for the requested internal-energy change occurs in this structure.
-/
structure MatchesScenarioAndFigureData
    (process : IdealGasPVProcess) : Prop where
  arrow_starts_at_a : process.startLabel = .a
  arrow_ends_at_b : process.endLabel = .b
  pressure_at_a_atm :
    pressureInAtmospheres (stateAtA process).pressure = 3 / 5
  pressure_at_b_atm :
    pressureInAtmospheres (stateAtB process).pressure = 1 / 5
  volume_at_b_cubic_meters :
    volumeInCubicMeters (stateAtB process).volume = 1 / 10
  isothermal_at_85_celsius :
    ∀ parameter : ℝ,
      parameter ∈ Set.Icc (0 : ℝ) 1 →
        temperatureInDegreesCelsius
            (process.stateAlong parameter).temperature = 85

/-- Positivity conditions selecting physically meaningful gas states. -/
structure HasPhysicalIdealGasParameters
    (process : IdealGasPVProcess) : Prop where
  gas_amount_positive : 0 < process.gas.amountOfGasInMoles
  pressure_positive :
    ∀ parameter : ℝ,
      parameter ∈ Set.Icc (0 : ℝ) 1 →
        0 < ((process.stateAlong parameter).pressure UnitChoices.SI).val
  volume_positive :
    ∀ parameter : ℝ,
      parameter ∈ Set.Icc (0 : ℝ) 1 →
        0 < volumeInCubicMeters (process.stateAlong parameter).volume
  absolute_temperature_positive :
    ∀ parameter : ℝ,
      parameter ∈ Set.Icc (0 : ℝ) 1 →
        0 < (process.stateAlong parameter).temperature.toReal

/--
The caloric equation of state for an ideal gas: at every state on the
process, internal energy is the sample's fixed function of absolute
temperature alone.  This is a general governing law along the whole path; it
does not assert that the endpoint energy change is zero.
-/
structure SatisfiesIdealGasCaloricLaw
    (process : IdealGasPVProcess) : Prop where
  internal_energy_is_temperature_state_function :
    ∀ parameter : ℝ,
      parameter ∈ Set.Icc (0 : ℝ) 1 →
        (process.stateAlong parameter).internalEnergy =
          process.gas.internalEnergyAtTemperature
            (process.stateAlong parameter).temperature

/-- The endpoint change `U_b - U_a`, read in joules. -/
def internalEnergyChangeInJoules (process : IdealGasPVProcess) : ℝ :=
  energyInJoules (stateAtB process).internalEnergy -
    energyInJoules (stateAtA process).internalEnergy

/--
An isothermal process of an ideal gas changes its internal energy by `0 J`
(answer choice B).

Blueprint label: `thm:physics:phyx_mini_0339:target`.
-/
theorem internalEnergyChange_eq_zero_joules
    (process : IdealGasPVProcess)
    (_physical : HasPhysicalIdealGasParameters process)
    (_data : MatchesScenarioAndFigureData process)
    (_caloricLaw : SatisfiesIdealGasCaloricLaw process) :
    internalEnergyChangeInJoules process = 0 := by
  have temperature_at_a :=
    _data.isothermal_at_85_celsius 0 (by norm_num)
  have temperature_at_b :=
    _data.isothermal_at_85_celsius 1 (by norm_num)
  have endpoint_temperatures_equal :
      (stateAtB process).temperature = (stateAtA process).temperature := by
    apply Temperature.ext
    apply NNReal.coe_injective
    unfold temperatureInDegreesCelsius at temperature_at_a temperature_at_b
    change
      ((stateAtB process).temperature.val : ℝ) - 27315 / 100 = 85
        at temperature_at_b
    change
      ((stateAtA process).temperature.val : ℝ) - 27315 / 100 = 85
        at temperature_at_a
    linarith
  have energy_at_a :=
    _caloricLaw.internal_energy_is_temperature_state_function 0 (by norm_num)
  have energy_at_b :=
    _caloricLaw.internal_energy_is_temperature_state_function 1 (by norm_num)
  have endpoint_internal_energies_equal :
      (stateAtB process).internalEnergy = (stateAtA process).internalEnergy := by
    calc
      (stateAtB process).internalEnergy =
          process.gas.internalEnergyAtTemperature
            (stateAtB process).temperature := by
              simpa [stateAtB] using energy_at_b
      _ = process.gas.internalEnergyAtTemperature
            (stateAtA process).temperature := by
              rw [endpoint_temperatures_equal]
      _ = (stateAtA process).internalEnergy := by
              simpa [stateAtA] using energy_at_a.symm
  unfold internalEnergyChangeInJoules
  rw [endpoint_internal_energies_equal]
  exact sub_self _

end PhyXMiniProblems.ProblemPhyXMini0339
