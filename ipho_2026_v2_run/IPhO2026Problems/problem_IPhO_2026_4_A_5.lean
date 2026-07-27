import Mathlib
import Physlib.Thermodynamics.Temperature.Basic
import Physlib.Units.WithDim.Pressure

noncomputable section

namespace IPhO2026Problems.Problem4A5

/-- Labels used for the apparatus in Figure 17 and on the official source page. -/
inductive ApparatusLabel
  | sealedAirColumnCA
  | innerCylinderIC
  | outerCylinderOC
  | propyleneGlycolPG
  | valveD
  | valveE
  deriving DecidableEq

/-- The cylinder dimensions read from Figure 17, expressed as SI scalar readouts. -/
structure Figure17Geometry where
  innerCylinderDiameter_m : ℝ
  innerCylinderInternalHeight_m : ℝ

/--
The part of the experimental apparatus relevant to the sealed air column.
Scalar fields are explicitly SI readouts; pressure itself is represented below by
Physlib's dimensionful `DimPressure`.
-/
structure IsochoricApparatus where
  geometry : Figure17Geometry
  propyleneGlycolHeight_m : ℝ
  ambientAirDensity_kg_per_m3 : ℝ
  sealedAirVolume_m3 : ℝ
  valveDClosed : Bool
  valveEClosed : Bool

/--
The Figure 17 geometry and the instructions `h = 4.5 cm`, `ρₐ = 1.12 kg/m³`,
with both valves closed.  The final equality is the cylindrical volume of CA
remaining above the propylene glycol.
-/
def IsPreparedIsochoricApparatus (a : IsochoricApparatus) : Prop :=
  0 < a.geometry.innerCylinderDiameter_m ∧
  0 < a.geometry.innerCylinderInternalHeight_m ∧
  a.propyleneGlycolHeight_m = 0.045 ∧
  a.propyleneGlycolHeight_m < a.geometry.innerCylinderInternalHeight_m ∧
  a.ambientAirDensity_kg_per_m3 = 1.12 ∧
  a.valveDClosed = true ∧
  a.valveEClosed = true ∧
  a.sealedAirVolume_m3 =
    Real.pi * (a.geometry.innerCylinderDiameter_m / 2) ^ 2 *
      (a.geometry.innerCylinderInternalHeight_m - a.propyleneGlycolHeight_m) ∧
  0 < a.sealedAirVolume_m3

/-- The numerical value, in pascals, of a dimensionful pressure in SI units. -/
def pressureInPascals (p : DimPressure) : ℝ :=
  (p.1 UnitChoices.SI).val

/--
The real readout of an absolute temperature.  Throughout this experiment the
arbitrary temperature unit carried by `Temperature` is fixed to kelvin.
-/
def temperatureInKelvin (T : Temperature) : ℝ :=
  T.toReal

/--
One constant-volume heating run.  `pressureAt` is a physical, dimensionful
pressure, while the amount of substance and gas constant are SI scalar
readouts in mol and J mol⁻¹ K⁻¹.
-/
structure IsochoricHeatingRun where
  apparatus : IsochoricApparatus
  pressureAt : Temperature → DimPressure
  referenceTemperature : Temperature
  heatedTemperature : Temperature
  amountOfAir_mol : ℝ
  universalGasConstant_J_per_mol_K : ℝ

/-- The system reference temperature is `273.15 K` and its pressure is positive. -/
def UsesStandardReferenceState (run : IsochoricHeatingRun) : Prop :=
  temperatureInKelvin run.referenceTemperature = (27315 : ℝ) / 100 ∧
  0 < pressureInPascals (run.pressureAt run.referenceTemperature)

/--
Orientation information for the recorded branch: the second state is reached
by heating, and the measured pressure increases along that branch.
-/
def IsHeatingBranch (run : IsochoricHeatingRun) : Prop :=
  temperatureInKelvin run.referenceTemperature <
      temperatureInKelvin run.heatedTemperature ∧
  pressureInPascals (run.pressureAt run.referenceTemperature) <
      pressureInPascals (run.pressureAt run.heatedTemperature)

/--
The governing ideal-gas law `P V = n R T` for the sealed air column.  The one
apparatus volume is used at every temperature, encoding the isochoric process.
-/
def ObeysIsochoricIdealGasLaw (run : IsochoricHeatingRun) : Prop :=
  ∀ T : Temperature, 0 < temperatureInKelvin T →
    pressureInPascals (run.pressureAt T) * run.apparatus.sealedAirVolume_m3 =
      run.amountOfAir_mol * run.universalGasConstant_J_per_mol_K *
        temperatureInKelvin T

/--
Reusable content of part A.3: the pressure plot is proportional to absolute
temperature.  The quantified equation makes this a constraining interface.
-/
def HasIsochoricPressureLinearity (run : IsochoricHeatingRun) : Prop :=
  ∃ pressureSlope_Pa_per_K : ℝ,
    0 < pressureSlope_Pa_per_K ∧
    ∀ T : Temperature, 0 < temperatureInKelvin T →
      pressureInPascals (run.pressureAt T) =
        pressureSlope_Pa_per_K * temperatureInKelvin T

/--
The source definition
`β₀ = (1 / P₀) (ΔP / ΔT)`, with the reference-to-heated orientation fixed by
`IsHeatingBranch`.  Its dimensional role is inverse kelvin.
-/
def thermalPressureCoefficientPerKelvin (run : IsochoricHeatingRun) : ℝ :=
  let referencePressure_Pa :=
    pressureInPascals (run.pressureAt run.referenceTemperature)
  let pressureChange_Pa :=
    pressureInPascals (run.pressureAt run.heatedTemperature) -
      referencePressure_Pa
  let temperatureChange_K :=
    temperatureInKelvin run.heatedTemperature -
      temperatureInKelvin run.referenceTemperature
  (1 / referencePressure_Pa) * (pressureChange_Pa / temperatureChange_K)

/-- A scalar estimate together with its symmetric reported uncertainty. -/
structure Estimate where
  centralValue : ℝ
  uncertainty : ℝ

/-- Membership in the closed symmetric uncertainty band of an estimate. -/
def Estimate.Contains (estimate : Estimate) (value : ℝ) : Prop :=
  0 ≤ estimate.uncertainty ∧
  |value - estimate.centralValue| ≤ estimate.uncertainty

/-- The official experimental answer `0.0034 ± 0.0007 K⁻¹`. -/
def officialCoefficientEstimatePerKelvin : Estimate where
  centralValue := 0.0034
  uncertainty := 0.0007

/--
The ideal-gas law at fixed positive volume supplies the proportionality used
in the pressure-versus-temperature plot of part A.3.
-/
theorem idealGasLaw_implies_isochoricPressureLinearity
    (run : IsochoricHeatingRun)
    (hPrepared : IsPreparedIsochoricApparatus run.apparatus)
    (hAmount : 0 < run.amountOfAir_mol)
    (hGasConstant : 0 < run.universalGasConstant_J_per_mol_K)
    (hIdealGas : ObeysIsochoricIdealGasLaw run) :
    HasIsochoricPressureLinearity run := by
  sorry

/--
For a positive reference state and a genuinely heated second state, the
normalized secant slope of an isochoric proportionality is `1 / T₀`.
-/
theorem thermalPressureCoefficient_eq_inverse_referenceTemperature
    (run : IsochoricHeatingRun)
    (hReference : UsesStandardReferenceState run)
    (hHeating : IsHeatingBranch run)
    (hLinearity : HasIsochoricPressureLinearity run) :
    thermalPressureCoefficientPerKelvin run =
      1 / temperatureInKelvin run.referenceTemperature := by
  sorry

/--
IPhO 2026 experimental problem 4, part A.5.

The ideal-gas coefficient at the stated reference temperature is `1 / 273.15
K`, lies in the official `0.0034 ± 0.0007 K⁻¹` interval, and rounds to
`0.0037 K⁻¹` at four decimal places.
-/
theorem IPhO2026_4_A_5_thermalPressureCoefficient
    (run : IsochoricHeatingRun)
    (hPrepared : IsPreparedIsochoricApparatus run.apparatus)
    (hReference : UsesStandardReferenceState run)
    (hHeating : IsHeatingBranch run)
    (hAmount : 0 < run.amountOfAir_mol)
    (hGasConstant : 0 < run.universalGasConstant_J_per_mol_K)
    (hIdealGas : ObeysIsochoricIdealGasLaw run) :
    thermalPressureCoefficientPerKelvin run =
        1 / temperatureInKelvin run.referenceTemperature ∧
      thermalPressureCoefficientPerKelvin run = 1 / ((27315 : ℝ) / 100) ∧
      officialCoefficientEstimatePerKelvin.Contains
        (thermalPressureCoefficientPerKelvin run) ∧
      |thermalPressureCoefficientPerKelvin run - 0.0037| ≤ 0.00005 := by
  sorry

end IPhO2026Problems.Problem4A5
