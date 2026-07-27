import Mathlib

namespace IPhO2026Problems.IPhO2026_4_B_6

/-- Display units used for the scalar readouts in the water-vapor experiment.

The index prevents, for example, a pressure readout from being used as a
temperature.  Molar quantities are retained as distinct physical roles because
the available `Physlib.Units` dimensional system does not include amount of
substance as a base dimension. -/
inductive DisplayUnit
  | kelvin
  | metre
  | pascal
  | joulePerMoleKelvin
  | kilojoulePerMole
  | kilogramPerMole
  | kilojoulePerKilogram
  | mole
  | kilogram
  | kilojoule
  | inverseKelvin
  | dimensionless
  deriving DecidableEq

/-- A measured scalar component in a fixed display unit, together with its
absolute uncertainty in that same unit. -/
structure Measurement (unit : DisplayUnit) where
  central : ℝ
  uncertainty : ℝ
  uncertainty_nonnegative : 0 ≤ uncertainty

/-- The two cylinders named in the experimental apparatus. -/
inductive CylinderLabel
  | innerCylinder
  | outerCylinder
  deriving DecidableEq

/-- Axis quantities used in the Clausius--Clapeyron graph of part B.5. -/
inductive GraphAxisQuantity
  | inverseTemperature
  | logVaporToAtmosphericPressure
  deriving DecidableEq

/-- The graph constructed in B.5.  Its slope has units of kelvin because the
vertical coordinate is dimensionless and the horizontal coordinate has units
of inverse kelvin. -/
structure ClausiusClapeyronPlot where
  horizontalAxis : GraphAxisQuantity
  verticalAxis : GraphAxisQuantity
  slope : Measurement .kelvin

/-- Scalar readouts and named apparatus quantities from pages 11--12.

`waterHeight` and `referenceWaterHeight` are the quantities denoted by `H` and
`H₀`; `temperature` and `referenceTemperature` are `T` and `T₀`.
`clausiusReferencePressure` is the positive normalization pressure `Pᵥ₀` in
the logarithm.  It is deliberately distinct from
`vaporPressureAtFreezing`, which the experimental approximation sets to zero. -/
structure WaterVaporExperiment where
  gasRegion : CylinderLabel
  waterHeight : Measurement .metre
  referenceWaterHeight : Measurement .metre
  temperature : Measurement .kelvin
  referenceTemperature : Measurement .kelvin
  atmosphericPressure : Measurement .pascal
  totalGasPressure : Measurement .pascal
  dryAirPressure : Measurement .pascal
  vaporPressure : Measurement .pascal
  vaporPressureAtFreezing : Measurement .pascal
  clausiusReferencePressure : Measurement .pascal
  gasConstant : Measurement .joulePerMoleKelvin

/-- Governing thermodynamic and apparatus relations used in parts B.4--B.5.

The central value of `molarLatentHeat` is expressed in kJ/mol, hence the factor
`1000` in the Clausius--Clapeyron equation with `R` in J/(mol·K). -/
structure VaporPressureLaws
    (experiment : WaterVaporExperiment)
    (molarLatentHeat : Measurement .kilojoulePerMole) : Prop where
  gas_is_in_inner_cylinder :
    experiment.gasRegion = .innerCylinder
  current_temperature_positive :
    0 < experiment.temperature.central
  reference_temperature_value :
    experiment.referenceTemperature.central = 273.15
  reference_pressure_positive :
    0 < experiment.clausiusReferencePressure.central
  current_vapor_pressure_positive :
    0 < experiment.vaporPressure.central
  gas_constant_value :
    experiment.gasConstant.central = 8.31
  gas_constant_positive :
    0 < experiment.gasConstant.central
  vapor_pressure_at_freezing_is_zero :
    experiment.vaporPressureAtFreezing.central = 0
  partial_pressure_balance :
    experiment.totalGasPressure.central =
      experiment.dryAirPressure.central + experiment.vaporPressure.central
  total_pressure_approximately_atmospheric :
    |experiment.totalGasPressure.central -
        experiment.atmosphericPressure.central| ≤
      experiment.totalGasPressure.uncertainty +
        experiment.atmosphericPressure.uncertainty
  clausius_clapeyron :
    Real.log
        (experiment.vaporPressure.central /
          experiment.clausiusReferencePressure.central) =
      -((1000 * molarLatentHeat.central) /
          experiment.gasConstant.central) *
        (1 / experiment.temperature.central -
          1 / experiment.referenceTemperature.central)

/-- The reusable experimental conclusion of B.5.  This is input data for B.6,
not the requested conversion to latent heat per unit mass. -/
structure PreviousPartB5Result
    (plot : ClausiusClapeyronPlot)
    (molarLatentHeat : Measurement .kilojoulePerMole) : Prop where
  horizontal_axis :
    plot.horizontalAxis = .inverseTemperature
  vertical_axis :
    plot.verticalAxis = .logVaporToAtmosphericPressure
  slope_central_kelvin :
    plot.slope.central = -4700
  slope_uncertainty_kelvin :
    plot.slope.uncertainty = 200
  molar_latent_heat_central_kilojoule_per_mole :
    molarLatentHeat.central = 39
  molar_latent_heat_uncertainty_kilojoule_per_mole :
    molarLatentHeat.uncertainty = 2

/-- The molar mass datum for water, expressed in kg/mol. -/
structure WaterMolarMassData
    (waterMolarMass : Measurement .kilogramPerMole) : Prop where
  central_kilogram_per_mole :
    waterMolarMass.central = 18 / 1000
  treated_as_exact :
    waterMolarMass.uncertainty = 0
  positive :
    0 < waterMolarMass.central

/-- One nonzero batch of vaporized water.  These are extensive physical
quantities rather than alternate names for `Qᵥ`, `M₀`, or `Lᵥ`. -/
structure VaporizationBatch where
  amount : Measurement .mole
  mass : Measurement .kilogram
  energy : Measurement .kilojoule

/-- Extensivity laws for a vaporized batch.

The energy can be computed from amount times molar latent heat or from mass
times specific latent heat.  The two uncertainty equations express propagation
under multiplication by the exact batch amount/mass; they do not assume the
requested quotient formula. -/
structure VaporizationExtensivity
    (batch : VaporizationBatch)
    (molarLatentHeat : Measurement .kilojoulePerMole)
    (waterMolarMass : Measurement .kilogramPerMole)
    (specificLatentHeat : Measurement .kilojoulePerKilogram) : Prop where
  amount_positive :
    0 < batch.amount.central
  amount_treated_as_exact :
    batch.amount.uncertainty = 0
  mass_from_amount_and_molar_mass :
    batch.mass.central =
      batch.amount.central * waterMolarMass.central
  mass_uncertainty_zero :
    batch.mass.uncertainty = 0
  energy_from_molar_latent_heat :
    batch.energy.central =
      batch.amount.central * molarLatentHeat.central
  energy_from_specific_latent_heat :
    batch.energy.central =
      batch.mass.central * specificLatentHeat.central
  energy_uncertainty_from_molar_latent_heat :
    batch.energy.uncertainty =
      batch.amount.central * molarLatentHeat.uncertainty
  energy_uncertainty_from_specific_latent_heat :
    batch.energy.uncertainty =
      batch.mass.central * specificLatentHeat.uncertainty

/-- A printed `central ± uncertainty` result is compatible with an unrounded
measurement when the printed central value lies inside the propagated
uncertainty interval and the two uncertainty magnitudes differ by at most the
stated reporting tolerance. -/
def CompatibleReportedMeasurement {unit : DisplayUnit}
    (measurement : Measurement unit)
    (reportedCentral reportedUncertainty uncertaintyReportingTolerance : ℝ) :
    Prop :=
  0 ≤ reportedUncertainty ∧
    |measurement.central - reportedCentral| ≤ measurement.uncertainty ∧
    |measurement.uncertainty - reportedUncertainty| ≤
      uncertaintyReportingTolerance

/-- Extensivity of energy, amount, and mass implies the requested central-value
conversion `Lᵥ = Qᵥ / M₀`. -/
lemma specific_latent_heat_formula_of_extensivity
    (batch : VaporizationBatch)
    (molarLatentHeat : Measurement .kilojoulePerMole)
    (waterMolarMass : Measurement .kilogramPerMole)
    (specificLatentHeat : Measurement .kilojoulePerKilogram)
    (hMass : 0 < waterMolarMass.central)
    (hExtensive :
      VaporizationExtensivity batch molarLatentHeat waterMolarMass
        specificLatentHeat) :
    specificLatentHeat.central =
      molarLatentHeat.central / waterMolarMass.central := by
  sorry

/-- The extensive uncertainty equations give the corresponding uncertainty
propagation through division by the exact molar mass. -/
lemma specific_latent_heat_uncertainty_of_extensivity
    (batch : VaporizationBatch)
    (molarLatentHeat : Measurement .kilojoulePerMole)
    (waterMolarMass : Measurement .kilogramPerMole)
    (specificLatentHeat : Measurement .kilojoulePerKilogram)
    (hMass : 0 < waterMolarMass.central)
    (hExtensive :
      VaporizationExtensivity batch molarLatentHeat waterMolarMass
        specificLatentHeat) :
    specificLatentHeat.uncertainty =
      molarLatentHeat.uncertainty / waterMolarMass.central := by
  sorry

/-- The rounded B.5 input `39 ± 2 kJ/mol`, divided by `0.018 kg/mol`, is
compatible with the official B.6 report `2190 ± 110 kJ/kg`.

The tolerance `2 kJ/kg` applies only to rounding the propagated uncertainty;
the central-value comparison uses the propagated uncertainty interval itself. -/
lemma official_specific_latent_heat_report
    (plot : ClausiusClapeyronPlot)
    (molarLatentHeat : Measurement .kilojoulePerMole)
    (waterMolarMass : Measurement .kilogramPerMole)
    (specificLatentHeat : Measurement .kilojoulePerKilogram)
    (hB5 : PreviousPartB5Result plot molarLatentHeat)
    (hMolarMass : WaterMolarMassData waterMolarMass)
    (hCentral :
      specificLatentHeat.central =
        molarLatentHeat.central / waterMolarMass.central)
    (hUncertainty :
      specificLatentHeat.uncertainty =
        molarLatentHeat.uncertainty / waterMolarMass.central) :
    CompatibleReportedMeasurement specificLatentHeat 2190 110 2 := by
  sorry

/-- IPhO 2026 Problem 4 B.6: converting the B.5 molar latent heat by the
water molar mass gives the latent heat of vaporization per unit mass, propagates
its uncertainty, and supports the official `2190 ± 110 kJ/kg` report. -/
theorem latent_heat_of_vaporization_per_unit_mass
    (experiment : WaterVaporExperiment)
    (plot : ClausiusClapeyronPlot)
    (batch : VaporizationBatch)
    (molarLatentHeat : Measurement .kilojoulePerMole)
    (waterMolarMass : Measurement .kilogramPerMole)
    (specificLatentHeat : Measurement .kilojoulePerKilogram)
    (hThermodynamics : VaporPressureLaws experiment molarLatentHeat)
    (hB5 : PreviousPartB5Result plot molarLatentHeat)
    (hMolarMass : WaterMolarMassData waterMolarMass)
    (hExtensive :
      VaporizationExtensivity batch molarLatentHeat waterMolarMass
        specificLatentHeat) :
    specificLatentHeat.central =
        molarLatentHeat.central / waterMolarMass.central ∧
      specificLatentHeat.uncertainty =
        molarLatentHeat.uncertainty / waterMolarMass.central ∧
      CompatibleReportedMeasurement specificLatentHeat 2190 110 2 := by
  sorry

end IPhO2026Problems.IPhO2026_4_B_6
