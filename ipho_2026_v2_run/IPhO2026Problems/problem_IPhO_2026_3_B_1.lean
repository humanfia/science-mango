import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Physlib.Thermodynamics.Temperature.Basic
import Physlib.Units.WithDim.Energy

/-!
# IPhO 2026 Problem 3 B.1

An isothermal change of the magnetic-field-strength magnitude in a paramagnetic
torus.  All real-valued fields below are explicitly SI-coordinate readouts;
energy itself is kept as PhysLean's dimensionful `DimEnergy`.
-/

namespace IPhO2026Problems
namespace ProblemIPhO2026_3_B_1

noncomputable section

/-- The SI (joule) coordinate of a dimensionful energy. -/
def energyInJoules (energy : DimEnergy) : ℝ :=
  (energy UnitChoices.SI).val

/-- Fixed material and geometric data for the paramagnetic torus.

`materialK_SI` has the dimensional role forced by
`T * M * V = n * K * H`, while `materialLambda_SI` has the role forced by
`C_M = n * lambda / T^2`. -/
structure ParamagneticTorus where
  /-- Fixed torus volume, in cubic metres. -/
  volumeCubicMetres : ℝ
  /-- Amount of paramagnetic material, in moles. -/
  amountMoles : ℝ
  /-- SI readout of the material constant `K`. -/
  materialK_SI : ℝ
  /-- SI readout of the material constant `lambda`. -/
  materialLambda_SI : ℝ
  volume_pos : 0 < volumeCubicMetres
  amount_pos : 0 < amountMoles
  materialK_pos : 0 < materialK_SI
  materialLambda_nonneg : 0 ≤ materialLambda_SI

/-- Data of a field sweep, parametrized by a dimensionless real parameter.

The physical process runs from parameter `0` to parameter `1`.  The derivative
readouts are retained explicitly so that the differential thermodynamic laws
constrain the corresponding finite changes.  Work and heat curves record
energy entering the torus.
-/
structure IsothermalFieldSweep where
  /-- Absolute temperature along the sweep. -/
  temperature : ℝ → Temperature
  /-- Magnetic-field-strength magnitude `H`, in amperes per metre. -/
  fieldStrengthAmperePerMetre : ℝ → ℝ
  /-- Magnetization magnitude `M`, in amperes per metre. -/
  magnetizationAmperePerMetre : ℝ → ℝ
  /-- Heat capacity at constant magnetization, in joules per kelvin. -/
  heatCapacityAtConstantMagnetization : ℝ → ℝ
  /-- Internal energy of the torus. -/
  internalEnergy : ℝ → DimEnergy
  /-- Accumulated magnetic work entering the torus. -/
  workEntering : ℝ → DimEnergy
  /-- Accumulated heat entering the torus. -/
  heatEntering : ℝ → DimEnergy
  /-- Temperature derivative with respect to the sweep parameter. -/
  temperatureRateKelvin : ℝ → ℝ
  /-- Field-strength derivative with respect to the sweep parameter. -/
  fieldStrengthRateAmperePerMetre : ℝ → ℝ
  /-- Magnetization derivative with respect to the sweep parameter. -/
  magnetizationRateAmperePerMetre : ℝ → ℝ
  /-- Internal-energy derivative, in joules per sweep parameter. -/
  internalEnergyRateJoules : ℝ → ℝ
  /-- Magnetic-work derivative, in joules per sweep parameter. -/
  workRateJoules : ℝ → ℝ
  /-- Heat derivative, in joules per sweep parameter. -/
  heatRateJoules : ℝ → ℝ

/-- The signed heat transferred into the torus during the physical sweep. -/
def netHeatEnteringInJoules (process : IsothermalFieldSweep) : ℝ :=
  energyInJoules (process.heatEntering 1) -
    energyInJoules (process.heatEntering 0)

/-- Governing laws and calibrated readouts for the isothermal field sweep.

The `magneticWorkLaw` field is the reusable result of part A.3.  The
`firstLawSignConvention` equation expresses that both work and heat entering
the torus are positive.  No field states the requested finite heat formula.
-/
structure SatisfiesIsothermalParamagneticTorusLaws
    (torus : ParamagneticTorus)
    (vacuumPermeability_SI : ℝ)
    (fixedTemperature : Temperature)
    (initialFieldStrength finalFieldStrength : ℝ)
    (process : IsothermalFieldSweep) : Prop where
  isothermal :
    ∀ s, process.temperature s = fixedTemperature
  prescribedFieldSweep :
    ∀ s,
      process.fieldStrengthAmperePerMetre s =
        initialFieldStrength + s * (finalFieldStrength - initialFieldStrength)
  temperatureHasDerivative :
    ∀ s,
      HasDerivAt
        (fun r => (process.temperature r : ℝ))
        (process.temperatureRateKelvin s) s
  fieldStrengthHasDerivative :
    ∀ s,
      HasDerivAt process.fieldStrengthAmperePerMetre
        (process.fieldStrengthRateAmperePerMetre s) s
  magnetizationHasDerivative :
    ∀ s,
      HasDerivAt process.magnetizationAmperePerMetre
        (process.magnetizationRateAmperePerMetre s) s
  internalEnergyHasDerivative :
    ∀ s,
      HasDerivAt (fun r => energyInJoules (process.internalEnergy r))
        (process.internalEnergyRateJoules s) s
  workHasDerivative :
    ∀ s,
      HasDerivAt (fun r => energyInJoules (process.workEntering r))
        (process.workRateJoules s) s
  heatHasDerivative :
    ∀ s,
      HasDerivAt (fun r => energyInJoules (process.heatEntering r))
        (process.heatRateJoules s) s
  equationOfState :
    ∀ s,
      (process.temperature s : ℝ) *
          process.magnetizationAmperePerMetre s *
          torus.volumeCubicMetres =
        torus.amountMoles * torus.materialK_SI *
          process.fieldStrengthAmperePerMetre s
  heatCapacityLaw :
    ∀ s,
      process.heatCapacityAtConstantMagnetization s =
        torus.amountMoles * torus.materialLambda_SI /
          (process.temperature s : ℝ) ^ 2
  internalEnergyDifferentialLaw :
    ∀ s,
      process.internalEnergyRateJoules s =
        process.heatCapacityAtConstantMagnetization s *
          process.temperatureRateKelvin s
  magneticWorkLaw :
    ∀ s,
      process.workRateJoules s =
        vacuumPermeability_SI * torus.volumeCubicMetres *
          process.fieldStrengthAmperePerMetre s *
          process.magnetizationRateAmperePerMetre s
  firstLawSignConvention :
    ∀ s,
      process.internalEnergyRateJoules s =
        process.heatRateJoules s + process.workRateJoules s

/-- Along an isothermal sweep, `dU = C_M dT` forces the internal-energy
rate to vanish. -/
theorem internalEnergyRate_eq_zero
    (torus : ParamagneticTorus)
    (vacuumPermeability_SI : ℝ)
    (fixedTemperature : Temperature)
    (initialFieldStrength finalFieldStrength : ℝ)
    (process : IsothermalFieldSweep)
    (laws : SatisfiesIsothermalParamagneticTorusLaws torus
      vacuumPermeability_SI fixedTemperature initialFieldStrength
      finalFieldStrength process) :
    ∀ s, process.internalEnergyRateJoules s = 0 := by
  intro s
  have htemperatureRate : process.temperatureRateKelvin s = 0 := by
    have hconstantTemperature :
        HasDerivAt (fun r => (process.temperature r : ℝ)) 0 s := by
      simpa only [laws.isothermal] using
        (hasDerivAt_const s (fixedTemperature : ℝ))
    exact (laws.temperatureHasDerivative s).unique hconstantTemperature
  rw [laws.internalEnergyDifferentialLaw s, htemperatureRate, mul_zero]

/-- The equation of state and the oriented linear field sweep determine the
magnetization rate. -/
theorem magnetizationRate_eq
    (torus : ParamagneticTorus)
    (vacuumPermeability_SI : ℝ)
    (fixedTemperature : Temperature)
    (initialFieldStrength finalFieldStrength : ℝ)
    (process : IsothermalFieldSweep)
    (temperature_pos : 0 < (fixedTemperature : ℝ))
    (laws : SatisfiesIsothermalParamagneticTorusLaws torus
      vacuumPermeability_SI fixedTemperature initialFieldStrength
      finalFieldStrength process) :
    ∀ s,
      process.magnetizationRateAmperePerMetre s =
        torus.amountMoles * torus.materialK_SI *
            (finalFieldStrength - initialFieldStrength) /
          ((fixedTemperature : ℝ) * torus.volumeCubicMetres) := by
  intro s
  have hdenominator :
      (fixedTemperature : ℝ) * torus.volumeCubicMetres ≠ 0 :=
    mul_ne_zero (ne_of_gt temperature_pos) (ne_of_gt torus.volume_pos)
  have hmagnetization :
      process.magnetizationAmperePerMetre =
        fun r =>
          torus.amountMoles * torus.materialK_SI *
              (initialFieldStrength +
                r * (finalFieldStrength - initialFieldStrength)) /
            ((fixedTemperature : ℝ) * torus.volumeCubicMetres) := by
    funext r
    have hequationOfState := laws.equationOfState r
    rw [laws.isothermal r, laws.prescribedFieldSweep r] at hequationOfState
    apply (eq_div_iff hdenominator).2
    calc
      process.magnetizationAmperePerMetre r *
            ((fixedTemperature : ℝ) * torus.volumeCubicMetres) =
          (fixedTemperature : ℝ) *
            process.magnetizationAmperePerMetre r *
              torus.volumeCubicMetres := by ring
      _ = torus.amountMoles * torus.materialK_SI *
            (initialFieldStrength +
              r * (finalFieldStrength - initialFieldStrength)) :=
        hequationOfState
  have hmodelDerivative :
      HasDerivAt
        (fun r =>
          torus.amountMoles * torus.materialK_SI *
              (initialFieldStrength +
                r * (finalFieldStrength - initialFieldStrength)) /
            ((fixedTemperature : ℝ) * torus.volumeCubicMetres))
        (torus.amountMoles * torus.materialK_SI *
            (finalFieldStrength - initialFieldStrength) /
          ((fixedTemperature : ℝ) * torus.volumeCubicMetres)) s := by
    have hlinear :
        HasDerivAt
          (fun r : ℝ =>
            initialFieldStrength +
              r * (finalFieldStrength - initialFieldStrength))
          (finalFieldStrength - initialFieldStrength) s :=
      (hasDerivAt_mul_const
        (finalFieldStrength - initialFieldStrength)).const_add
          initialFieldStrength
    exact
      (hlinear.const_mul
        (torus.amountMoles * torus.materialK_SI)).div_const
          ((fixedTemperature : ℝ) * torus.volumeCubicMetres)
  have hgivenDerivative := laws.magnetizationHasDerivative s
  rw [hmagnetization] at hgivenDerivative
  exact hgivenDerivative.unique hmodelDerivative

/-- Combining the first law, isothermal internal-energy law, equation of
state, and magnetic work law determines the instantaneous heat rate. -/
theorem heatRate_eq
    (torus : ParamagneticTorus)
    (vacuumPermeability_SI : ℝ)
    (fixedTemperature : Temperature)
    (initialFieldStrength finalFieldStrength : ℝ)
    (process : IsothermalFieldSweep)
    (temperature_pos : 0 < (fixedTemperature : ℝ))
    (laws : SatisfiesIsothermalParamagneticTorusLaws torus
      vacuumPermeability_SI fixedTemperature initialFieldStrength
      finalFieldStrength process) :
    ∀ s,
      process.heatRateJoules s =
        -(vacuumPermeability_SI * torus.amountMoles *
            torus.materialK_SI / (fixedTemperature : ℝ)) *
          process.fieldStrengthAmperePerMetre s *
          (finalFieldStrength - initialFieldStrength) := by
  intro s
  have hinternalEnergy := internalEnergyRate_eq_zero torus
    vacuumPermeability_SI fixedTemperature initialFieldStrength
    finalFieldStrength process laws s
  have hmagnetization := magnetizationRate_eq torus
    vacuumPermeability_SI fixedTemperature initialFieldStrength
    finalFieldStrength process temperature_pos laws s
  have hwork :
      process.workRateJoules s =
        (vacuumPermeability_SI * torus.amountMoles *
            torus.materialK_SI / (fixedTemperature : ℝ)) *
          process.fieldStrengthAmperePerMetre s *
          (finalFieldStrength - initialFieldStrength) := by
    rw [laws.magneticWorkLaw s, hmagnetization]
    field_simp [ne_of_gt temperature_pos, ne_of_gt torus.volume_pos]
  rw [laws.firstLawSignConvention s, hwork] at hinternalEnergy
  linarith

/-- The heat transferred into the paramagnetic torus when the magnitude of
`H` changes isothermally from `H_i` to `H_f`.

The sweep parametrization records the orientation, so the same signed formula
also covers a decreasing field magnitude.
-/
theorem heat_transferred_into_torus
    (torus : ParamagneticTorus)
    (vacuumPermeability_SI : ℝ)
    (fixedTemperature : Temperature)
    (initialFieldStrength finalFieldStrength : ℝ)
    (process : IsothermalFieldSweep)
    (vacuumPermeability_pos : 0 < vacuumPermeability_SI)
    (temperature_pos : 0 < (fixedTemperature : ℝ))
    (initialFieldStrength_nonneg : 0 ≤ initialFieldStrength)
    (finalFieldStrength_nonneg : 0 ≤ finalFieldStrength)
    (laws : SatisfiesIsothermalParamagneticTorusLaws torus
      vacuumPermeability_SI fixedTemperature initialFieldStrength
      finalFieldStrength process) :
    netHeatEnteringInJoules process =
      -(vacuumPermeability_SI * torus.amountMoles *
          torus.materialK_SI / (2 * (fixedTemperature : ℝ))) *
        (finalFieldStrength ^ 2 - initialFieldStrength ^ 2) := by
  let coefficient :=
    vacuumPermeability_SI * torus.amountMoles *
      torus.materialK_SI / (fixedTemperature : ℝ)
  have hheatDerivative :
      ∀ s,
        HasDerivAt
          (fun r => energyInJoules (process.heatEntering r))
          (-coefficient *
            (initialFieldStrength +
              s * (finalFieldStrength - initialFieldStrength)) *
            (finalFieldStrength - initialFieldStrength)) s := by
    intro s
    have hderivative := laws.heatHasDerivative s
    rw [heatRate_eq torus vacuumPermeability_SI fixedTemperature
      initialFieldStrength finalFieldStrength process temperature_pos laws s,
      laws.prescribedFieldSweep s] at hderivative
    simpa only [coefficient] using hderivative
  have hintegrable :
      IntervalIntegrable
        (fun s : ℝ =>
          -coefficient *
            (initialFieldStrength +
              s * (finalFieldStrength - initialFieldStrength)) *
            (finalFieldStrength - initialFieldStrength))
        MeasureTheory.volume 0 1 := by
    exact
      (by
        fun_prop :
        Continuous
          (fun s : ℝ =>
            -coefficient *
              (initialFieldStrength +
                s * (finalFieldStrength - initialFieldStrength)) *
              (finalFieldStrength - initialFieldStrength))).intervalIntegrable 0 1
  have hintegral :=
    intervalIntegral.integral_eq_sub_of_hasDerivAt
      (fun s _ => hheatDerivative s) hintegrable
  unfold netHeatEnteringInJoules
  rw [← hintegral]
  norm_num [intervalIntegral.integral_mul_const,
    intervalIntegral.integral_const_mul]
  dsimp only [coefficient]
  field_simp [ne_of_gt temperature_pos]
  ring

end

end ProblemIPhO2026_3_B_1
end IPhO2026Problems
