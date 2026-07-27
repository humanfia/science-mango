import Mathlib
import Physlib.Units.WithDim.Energy
import Physlib.Units.WithDim.Pressure

/-!
# IPhO 2026 experimental problem 4, part B.6

The inner cylinder contains dry air and water vapor while its water height is
recorded as a function of temperature.  Part B.5 supplies a molar latent-heat
estimate from a Clausius--Clapeyron graph.  Part B.6 converts that estimate into
latent heat per unit mass using the molar mass of water.

Physlib's `Dimension` does not include an amount-of-substance component.
Consequently, ordinary physical quantities below use `Dimensionful` and
`WithDim`, while experimental molar readouts are explicitly named real values
in `J/mol` or `kg/mol`.
-/

noncomputable section

open Dimension

namespace IPhO2026Problems.IPhO2026_4_B_6

/-! ## Dimension-carrying quantities and SI readouts -/

/-- The mechanical dimension of energy. -/
def energyDimension : Dimension :=
  M𝓭 * L𝓭 * L𝓭 * T𝓭⁻¹ * T𝓭⁻¹

/-- The dimension of energy per unit mass. -/
def specificEnergyDimension : Dimension :=
  energyDimension * M𝓭⁻¹

abbrev Temperature : Type :=
  Dimensionful (WithDim Θ𝓭 ℝ)

abbrev Length : Type :=
  Dimensionful (WithDim L𝓭 ℝ)

abbrev Pressure : Type :=
  Dimensionful (WithDim (M𝓭 * L𝓭⁻¹ * T𝓭⁻¹ * T𝓭⁻¹) ℝ)

abbrev Mass : Type :=
  Dimensionful (WithDim M𝓭 ℝ)

abbrev Energy : Type :=
  Dimensionful (WithDim energyDimension ℝ)

abbrev SpecificEnergy : Type :=
  Dimensionful (WithDim specificEnergyDimension ℝ)

/-- The scalar readout of a dimensionful quantity in the SI unit system. -/
def siReadout {d : Dimension}
    (quantity : Dimensionful (WithDim d ℝ)) : ℝ :=
  (quantity.1 UnitChoices.SI).val

/-! ## Experimental setup and reported molar estimate -/

/--
The part B.5 estimate of molar latent heat.  Both fields are scalar
experimental readouts in joules per mole.
-/
structure MolarLatentHeatEstimate where
  centralJoulesPerMole : ℝ
  uncertaintyJoulesPerMole : ℝ
  uncertainty_nonnegative : 0 ≤ uncertaintyJoulesPerMole

/--
Quantities and labelled functions appearing in the B.1--B.6 inner-cylinder
experiment.  The names retain the source labels `P_atm`, `H`, `T`, `H₀`,
`T₀`, `P_v`, `P_v0`, `Q_v`, `M₀`, and `L_v`.
-/
structure VaporizationExperiment where
  atmosphericPressurePatm : Pressure
  innerCylinderTotalPressureAt : Temperature → Pressure
  dryAirPartialPressureAt : Temperature → Pressure
  vaporPressurePvAt : Temperature → Pressure
  vaporPressureScalePv0 : Pressure
  waterHeightHAt : Temperature → Length
  referenceTemperatureT0 : Temperature
  extrapolatedHeightH0 : Length
  pressureControlTolerancePa : ℝ
  gasConstantJoulesPerMoleKelvin : ℝ
  molarLatentHeatQv : MolarLatentHeatEstimate
  waterMolarMassM0KilogramsPerMole : ℝ
  latentHeatPerUnitMassLv : SpecificEnergy
  latentEnergyForAmountMol : ℝ → Energy
  vaporizedWaterMassForAmountMol : ℝ → Mass
  fittedClausiusSlopeKelvin : ℝ
  fittedSlopeUncertaintyKelvin : ℝ

/-! ## Figure/data readouts, governing laws, and previous-part result -/

/--
Reference values and procedure readouts from pages 11--12, together with the
standard molar mass of water needed for B.6.
-/
structure HasReferenceAndProcedureData
    (experiment : VaporizationExperiment) : Prop where
  referenceTemperatureKelvin :
    siReadout experiment.referenceTemperatureT0 = 273.15
  extrapolatedReferenceHeight :
    experiment.waterHeightHAt experiment.referenceTemperatureT0 =
      experiment.extrapolatedHeightH0
  vaporPressureNegligibleAtReference :
    siReadout
      (experiment.vaporPressurePvAt experiment.referenceTemperatureT0) = 0
  gasConstant :
    experiment.gasConstantJoulesPerMoleKelvin = 8.31
  waterMolarMass :
    experiment.waterMolarMassM0KilogramsPerMole = (18 : ℝ) / 1000
  pressureControlTolerance_nonnegative :
    0 ≤ experiment.pressureControlTolerancePa
  totalPressureApproximatelyAtmospheric :
    ∀ temperature : Temperature,
      |siReadout (experiment.innerCylinderTotalPressureAt temperature) -
          siReadout experiment.atmosphericPressurePatm| ≤
        experiment.pressureControlTolerancePa

/--
The physical laws used by the experimental model.  The final B.6 quotient is
not a field here:

* total pressure is the sum of dry-air and vapor partial pressures;
* vapor pressure obeys the integrated Clausius--Clapeyron relation;
* an amount `n` of water has mass `M₀ n`;
* the same vaporization energy can be described molarly as `Q_v n` or by
  specific latent heat as `L_v` times the vaporized mass.
-/
structure GoverningLaws (experiment : VaporizationExperiment) : Prop where
  partialPressureBalance :
    ∀ temperature : Temperature,
      siReadout (experiment.innerCylinderTotalPressureAt temperature) =
        siReadout (experiment.dryAirPartialPressureAt temperature) +
          siReadout (experiment.vaporPressurePvAt temperature)
  clausiusClapeyron :
    ∀ temperature : Temperature,
      0 < siReadout temperature →
      0 < siReadout (experiment.vaporPressurePvAt temperature) →
      0 < siReadout experiment.vaporPressureScalePv0 →
      Real.log
          (siReadout (experiment.vaporPressurePvAt temperature) /
            siReadout experiment.vaporPressureScalePv0) =
        -(experiment.molarLatentHeatQv.centralJoulesPerMole /
            experiment.gasConstantJoulesPerMoleKelvin) *
          (1 / siReadout temperature -
            1 / siReadout experiment.referenceTemperatureT0)
  vaporizedMassFromMoles :
    ∀ amountMol : ℝ, 0 < amountMol →
      siReadout (experiment.vaporizedWaterMassForAmountMol amountMol) =
        experiment.waterMolarMassM0KilogramsPerMole * amountMol
  latentEnergyFromMoles :
    ∀ amountMol : ℝ, 0 < amountMol →
      siReadout (experiment.latentEnergyForAmountMol amountMol) =
        experiment.molarLatentHeatQv.centralJoulesPerMole * amountMol
  latentEnergyFromMass :
    ∀ amountMol : ℝ, 0 < amountMol →
      siReadout (experiment.latentEnergyForAmountMol amountMol) =
        siReadout experiment.latentHeatPerUnitMassLv *
          siReadout (experiment.vaporizedWaterMassForAmountMol amountMol)
  molarMass_positive :
    0 < experiment.waterMolarMassM0KilogramsPerMole

/--
The only imported previous-part conclusion: the B.5 graph has reported slope
`-4700 ± 200 K` and gives `Q_v = 39 ± 2 kJ/mol`.
-/
structure PreviousPartB5Result
    (experiment : VaporizationExperiment) : Prop where
  fittedSlope :
    experiment.fittedClausiusSlopeKelvin = -4700
  fittedSlopeUncertainty :
    experiment.fittedSlopeUncertaintyKelvin = 200
  molarLatentHeatCentral :
    experiment.molarLatentHeatQv.centralJoulesPerMole = 39 * 1000
  molarLatentHeatUncertainty :
    experiment.molarLatentHeatQv.uncertaintyJoulesPerMole = 2 * 1000

/-! ## Part B.6 target -/

/--
Converting the B.5 molar result by the water molar mass gives

`L_v = Q_v / M₀`.

The second conjunct formalizes the official rounded report
`L_v = 2190 ± 110 kJ/kg`: the SI value, divided by `1000` to obtain
`kJ/kg`, lies in the stated uncertainty band.
-/
theorem latentHeatPerUnitMass_from_molarEstimate
    (experiment : VaporizationExperiment)
    (_data : HasReferenceAndProcedureData experiment)
    (_laws : GoverningLaws experiment)
    (_previous : PreviousPartB5Result experiment) :
    siReadout experiment.latentHeatPerUnitMassLv =
        experiment.molarLatentHeatQv.centralJoulesPerMole /
          experiment.waterMolarMassM0KilogramsPerMole ∧
      |siReadout experiment.latentHeatPerUnitMassLv / 1000 - 2190| ≤ 110 := by
  have hmass := _laws.vaporizedMassFromMoles 1 (by norm_num)
  have hmolar := _laws.latentEnergyFromMoles 1 (by norm_num)
  have hspecific := _laws.latentEnergyFromMass 1 (by norm_num)
  norm_num at hmass hmolar hspecific
  rw [hmolar, hmass] at hspecific
  have hconversion :
      siReadout experiment.latentHeatPerUnitMassLv =
        experiment.molarLatentHeatQv.centralJoulesPerMole /
          experiment.waterMolarMassM0KilogramsPerMole :=
    (eq_div_iff (ne_of_gt _laws.molarMass_positive)).2 hspecific.symm
  constructor
  · exact hconversion
  · rw [hconversion, _previous.molarLatentHeatCentral, _data.waterMolarMass]
    norm_num [abs_le]

end IPhO2026Problems.IPhO2026_4_B_6
