import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Physlib.Units.WithDim.Basic

namespace IPhO2026Problems
namespace IPhO2026_3_C_4

open Dimension

/-!
The types below use `WithDim` to keep the dimensional role of every physical
quantity visible. Their real-valued projections are readouts in one fixed
coherent unit convention.
-/

/-- The mechanical-energy dimension `M L² T⁻²`. -/
abbrev EnergyDimension : Dimension :=
  M𝓭 * L𝓭 * L𝓭 * T𝓭⁻¹ * T𝓭⁻¹

/-- An absolute-temperature quantity. -/
abbrev TemperatureQuantity : Type := WithDim Θ𝓭 ℝ

/-- An elapsed-time quantity. -/
abbrev TimeQuantity : Type := WithDim T𝓭 ℝ

/-- A volume quantity. -/
abbrev VolumeQuantity : Type := WithDim (L𝓭 * L𝓭 * L𝓭) ℝ

/-- An `A/m` magnetic-field-strength or magnetization quantity. -/
abbrev MagneticFieldStrengthQuantity : Type :=
  WithDim (C𝓭 * T𝓭⁻¹ * L𝓭⁻¹) ℝ

/-- A constant-volume heat capacity, with dimension energy/temperature. -/
abbrev HeatCapacityQuantity : Type :=
  WithDim (EnergyDimension * Θ𝓭⁻¹) ℝ

/-- A power or heat-transfer-rate quantity, with dimension energy/time. -/
abbrev PowerQuantity : Type :=
  WithDim (EnergyDimension * T𝓭⁻¹) ℝ

/-- The four labelled states in the `H`-versus-`T` Carnot-cycle figure. -/
inductive CarnotCycleState
  | state1
  | state2
  | state3
  | state4
  deriving DecidableEq

namespace CarnotCycleState

/-- The oriented cycle read from Figure 3b: `1 → 2 → 3 → 4 → 1`. -/
def next : CarnotCycleState → CarnotCycleState
  | state1 => state2
  | state2 => state3
  | state3 => state4
  | state4 => state1

end CarnotCycleState

/--
The paramagnetic-torus context inherited by part C. The amount of substance
and Curie constant are explicitly SI scalar readouts because Physlib's
foundational `Dimension` currently has no amount-of-substance component.
-/
structure ParamagneticTorusContext where
  volume : VolumeQuantity
  amountOfSubstanceMoles : ℝ
  curieConstantSI : ℝ
  temperature : CarnotCycleState → TemperatureQuantity
  magnetization : CarnotCycleState → MagneticFieldStrengthQuantity
  magneticField : CarnotCycleState → MagneticFieldStrengthQuantity
  volume_pos : 0 < volume.val
  amountOfSubstanceMoles_pos : 0 < amountOfSubstanceMoles
  curieConstantSI_pos : 0 < curieConstantSI
  temperature_pos : ∀ state, 0 < (temperature state).val
  equationOfState : ∀ state,
    (temperature state).val * (magnetization state).val * volume.val =
      amountOfSubstanceMoles * curieConstantSI * (magneticField state).val

/--
The fixed data of the cooling experiment. Constancy of `heatCapacity`,
`inputPower`, and `hotReservoirTemperature` is represented by their being
single experiment parameters rather than time-dependent functions.
-/
structure CarnotCoolingExperiment where
  torus : ParamagneticTorusContext
  heatCapacity : HeatCapacityQuantity
  inputPower : PowerQuantity
  hotReservoirTemperature : TemperatureQuantity
  initialTemperature : TemperatureQuantity
  finalTemperature : TemperatureQuantity
  elapsedTime : TimeQuantity
  heatCapacity_pos : 0 < heatCapacity.val
  inputPower_pos : 0 < inputPower.val
  finalTemperature_pos : 0 < finalTemperature.val
  finalTemperature_lt_initial : finalTemperature.val < initialTemperature.val
  initialTemperature_lt_hot :
    initialTemperature.val < hotReservoirTemperature.val
  elapsedTime_nonneg : 0 ≤ elapsedTime.val

/--
Time-dependent readouts for the body temperature and the magnitudes of the
cold- and hot-side heat-transfer rates.
-/
structure CarnotCoolingProcess where
  temperatureTrajectory : ℝ → TemperatureQuantity
  coldHeatAbsorptionRate : ℝ → PowerQuantity
  hotHeatDeliveryRate : ℝ → PowerQuantity

/--
The governing laws for the continuously repeated Carnot cycles. The three
last fields encode, respectively, `dQ_c / dQ_h = T_c / T_h`,
`dQ_c = -C_c dT_c`, and `P = dQ_h/dt - dQ_c/dt`.
-/
structure SatisfiesCarnotCoolingLaw
    (experiment : CarnotCoolingExperiment)
    (process : CarnotCoolingProcess) : Prop where
  temperatureReadout_differentiable :
    Differentiable ℝ (fun τ => (process.temperatureTrajectory τ).val)
  initial_condition :
    (process.temperatureTrajectory 0).val =
      experiment.initialTemperature.val
  final_condition :
    (process.temperatureTrajectory experiment.elapsedTime.val).val =
      experiment.finalTemperature.val
  temperature_pos_on_run : ∀ τ ∈ Set.Icc 0 experiment.elapsedTime.val,
    0 < (process.temperatureTrajectory τ).val
  temperature_lt_hot_on_run : ∀ τ ∈ Set.Icc 0 experiment.elapsedTime.val,
    (process.temperatureTrajectory τ).val <
      experiment.hotReservoirTemperature.val
  coldHeatAbsorptionRate_pos : ∀ τ ∈ Set.Icc 0 experiment.elapsedTime.val,
    0 < (process.coldHeatAbsorptionRate τ).val
  hotHeatDeliveryRate_pos : ∀ τ ∈ Set.Icc 0 experiment.elapsedTime.val,
    0 < (process.hotHeatDeliveryRate τ).val
  carnot_heat_ratio : ∀ τ ∈ Set.Icc 0 experiment.elapsedTime.val,
    (process.coldHeatAbsorptionRate τ).val /
        (process.hotHeatDeliveryRate τ).val =
      (process.temperatureTrajectory τ).val /
        experiment.hotReservoirTemperature.val
  body_heat_balance : ∀ τ ∈ Set.Icc 0 experiment.elapsedTime.val,
    (process.coldHeatAbsorptionRate τ).val =
      -experiment.heatCapacity.val *
        deriv (fun s => (process.temperatureTrajectory s).val) τ
  refrigerator_power_balance : ∀ τ ∈ Set.Icc 0 experiment.elapsedTime.val,
    (process.hotHeatDeliveryRate τ).val -
        (process.coldHeatAbsorptionRate τ).val =
      experiment.inputPower.val

/--
Eliminating the cold- and hot-side heat rates gives the instantaneous cooling
equation that will be integrated in `elapsed_time_formula`.
-/
theorem instantaneous_cooling_power_equation
    (experiment : CarnotCoolingExperiment)
    (process : CarnotCoolingProcess)
    (law : SatisfiesCarnotCoolingLaw experiment process)
    (τ : ℝ) (hτ : τ ∈ Set.Icc 0 experiment.elapsedTime.val) :
    experiment.inputPower.val =
      experiment.heatCapacity.val *
        (experiment.hotReservoirTemperature.val /
          (process.temperatureTrajectory τ).val - 1) *
        (-deriv (fun s => (process.temperatureTrajectory s).val) τ) := by
  have htemperature_pos :
      0 < (process.temperatureTrajectory τ).val :=
    law.temperature_pos_on_run τ hτ
  have hhot_pos : 0 < experiment.hotReservoirTemperature.val :=
    lt_trans experiment.finalTemperature_pos
      (lt_trans experiment.finalTemperature_lt_initial
        experiment.initialTemperature_lt_hot)
  have hhot_rate_pos :
      0 < (process.hotHeatDeliveryRate τ).val :=
    law.hotHeatDeliveryRate_pos τ hτ
  have hratio := law.carnot_heat_ratio τ hτ
  have hbody := law.body_heat_balance τ hτ
  have hpower := law.refrigerator_power_balance τ hτ
  field_simp [ne_of_gt htemperature_pos, ne_of_gt hhot_pos,
    ne_of_gt hhot_rate_pos] at hratio ⊢
  nlinarith

/--
The required running time for cooling the body from `T₀` to `T` with constant
heat capacity, constant refrigerator input power, and constant hot-reservoir
temperature.
-/
theorem elapsed_time_formula
    (experiment : CarnotCoolingExperiment)
    (process : CarnotCoolingProcess)
    (law : SatisfiesCarnotCoolingLaw experiment process) :
    experiment.elapsedTime.val =
      (experiment.heatCapacity.val *
          experiment.hotReservoirTemperature.val /
        experiment.inputPower.val) *
      (Real.log (experiment.initialTemperature.val /
          experiment.finalTemperature.val) -
        (experiment.initialTemperature.val -
            experiment.finalTemperature.val) /
          experiment.hotReservoirTemperature.val) := by
  have htime_pos : 0 < experiment.elapsedTime.val := by
    refine lt_of_le_of_ne experiment.elapsedTime_nonneg ?_
    intro hzero
    have hinitial_eq_final :
        experiment.initialTemperature.val =
          experiment.finalTemperature.val := by
      calc
        experiment.initialTemperature.val =
            (process.temperatureTrajectory 0).val :=
          law.initial_condition.symm
        _ = (process.temperatureTrajectory experiment.elapsedTime.val).val := by
          rw [← hzero]
        _ = experiment.finalTemperature.val := law.final_condition
    linarith [experiment.finalTemperature_lt_initial]
  have hhot_pos : 0 < experiment.hotReservoirTemperature.val :=
    lt_trans experiment.finalTemperature_pos
      (lt_trans experiment.finalTemperature_lt_initial
        experiment.initialTemperature_lt_hot)
  let θ : ℝ → ℝ :=
    fun τ => (process.temperatureTrajectory τ).val
  let F : ℝ → ℝ :=
    fun τ =>
      (experiment.heatCapacity.val *
          experiment.hotReservoirTemperature.val /
        experiment.inputPower.val) *
      (Real.log (θ τ) -
        θ τ / experiment.hotReservoirTemperature.val)
  have hF_differentiableAt :
      ∀ τ ∈ Set.Icc 0 experiment.elapsedTime.val,
        DifferentiableAt ℝ F τ := by
    intro τ hτ
    have hθ_pos : 0 < θ τ := by
      simpa [θ] using law.temperature_pos_on_run τ hτ
    have hθ_differentiable : DifferentiableAt ℝ θ τ := by
      simpa [θ] using law.temperatureReadout_differentiable τ
    dsimp [F]
    exact
      (((Real.differentiableAt_log (ne_of_gt hθ_pos)).comp τ
          hθ_differentiable).sub
        (hθ_differentiable.div_const
          experiment.hotReservoirTemperature.val)).const_mul
        (experiment.heatCapacity.val *
          experiment.hotReservoirTemperature.val /
            experiment.inputPower.val)
  have hF_continuous :
      ContinuousOn F (Set.Icc 0 experiment.elapsedTime.val) := by
    intro τ hτ
    exact (hF_differentiableAt τ hτ).continuousAt.continuousWithinAt
  have hF_differentiable :
      DifferentiableOn ℝ F (Set.Ioo 0 experiment.elapsedTime.val) := by
    intro τ hτ
    exact
      (hF_differentiableAt τ (Set.Ioo_subset_Icc_self hτ)).differentiableWithinAt
  obtain ⟨c, hc, hmean⟩ :=
    exists_deriv_eq_slope F htime_pos hF_continuous hF_differentiable
  have hc_closed : c ∈ Set.Icc 0 experiment.elapsedTime.val :=
    Set.Ioo_subset_Icc_self hc
  have hθ_pos : 0 < θ c := by
    simpa [θ] using law.temperature_pos_on_run c hc_closed
  have hθ_differentiable : DifferentiableAt ℝ θ c := by
    simpa [θ] using law.temperatureReadout_differentiable c
  have hF_deriv :
      deriv F c =
        (experiment.heatCapacity.val *
            experiment.hotReservoirTemperature.val /
          experiment.inputPower.val) *
        (deriv θ c / θ c -
          deriv θ c / experiment.hotReservoirTemperature.val) := by
    have hθ_hasDeriv :
        HasDerivAt θ (deriv θ c) c :=
      hθ_differentiable.hasDerivAt
    have hcalculus :=
      ((hθ_hasDeriv.log (ne_of_gt hθ_pos)).sub
        (hθ_hasDeriv.div_const
          experiment.hotReservoirTemperature.val)).const_mul
        (experiment.heatCapacity.val *
          experiment.hotReservoirTemperature.val /
            experiment.inputPower.val)
    simpa [F] using hcalculus.deriv
  have hinstant :
      experiment.inputPower.val =
        experiment.heatCapacity.val *
          (experiment.hotReservoirTemperature.val / θ c - 1) *
          (-deriv θ c) := by
    simpa [θ] using
      instantaneous_cooling_power_equation experiment process law c hc_closed
  have hF_deriv_eq : deriv F c = -1 := by
    rw [hF_deriv]
    field_simp [ne_of_gt hθ_pos, ne_of_gt hhot_pos,
      ne_of_gt experiment.inputPower_pos] at hinstant ⊢
    nlinarith
  rw [hF_deriv_eq] at hmean
  have hF_difference :
      F 0 - F experiment.elapsedTime.val =
        experiment.elapsedTime.val := by
    field_simp [ne_of_gt htime_pos] at hmean
    linarith
  have hinitial_pos : 0 < experiment.initialTemperature.val :=
    lt_trans experiment.finalTemperature_pos
      experiment.finalTemperature_lt_initial
  rw [Real.log_div (ne_of_gt hinitial_pos)
    (ne_of_gt experiment.finalTemperature_pos)]
  dsimp [F, θ] at hF_difference
  rw [← WithDim.val_div_val, ← WithDim.val_div_val] at hF_difference
  rw [law.initial_condition, law.final_condition] at hF_difference
  convert hF_difference.symm using 1
  all_goals ring

end IPhO2026_3_C_4
end IPhO2026Problems
