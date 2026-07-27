import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.Calculus.Deriv.Inv
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.Real.Sqrt
import Physlib.Units.WithDim.Energy

/-!
# IPhO 2026, problem 3, part B.2

This file models the adiabatic change of the applied magnetic-field magnitude
for the fixed-volume paramagnetic torus (Pm-T).  Physical quantities supported
by Physlib are dimension-tagged and independent of a choice of units.  The
thermodynamic laws are stated using their SI readouts along a dimensionless
process parameter `τ ∈ [0, 1]`.

The amount of substance is recorded by its numerical value in moles because
Physlib's foundational `Dimension` currently has no amount-of-substance
component.
-/

namespace IPhO2026Problems.IPhO2026_3_B_2

open Dimension UnitChoices
open NNReal

/-- Absolute thermodynamic temperature, with physical dimension temperature. -/
abbrev ThermodynamicTemperature :=
  Dimensionful (WithDim Θ𝓭 ℝ≥0)

/-- The fixed physical volume of the paramagnetic torus. -/
abbrev PhysicalVolume :=
  Dimensionful (WithDim (L𝓭 * L𝓭 * L𝓭) ℝ≥0)

/--
Magnitude of the applied magnetic-field strength `H`.

In SI its unit is ampere per metre, represented dimensionally as
charge per time per length.
-/
abbrev AppliedFieldStrengthMagnitude :=
  Dimensionful (WithDim (C𝓭 * T𝓭⁻¹ * L𝓭⁻¹) ℝ≥0)

/-- Magnitude of the torus magnetization `M`, also measured in ampere per metre. -/
abbrev MagnetizationMagnitude :=
  Dimensionful (WithDim (C𝓭 * T𝓭⁻¹ * L𝓭⁻¹) ℝ≥0)

/--
Vacuum permeability `μ₀`.

Its SI dimension is mass times length divided by charge squared.
-/
abbrev VacuumPermeability :=
  Dimensionful (WithDim (M𝓭 * L𝓭 * C𝓭⁻¹ * C𝓭⁻¹) ℝ)

/--
The equation-of-state constant `K`, per mole.

Since amount of substance is represented by its scalar molar readout, the
dimension recorded here is temperature times volume.
-/
abbrev CurieConstantPerMole :=
  Dimensionful (WithDim (Θ𝓭 * L𝓭 * L𝓭 * L𝓭) ℝ)

/--
The material constant `λ`, per mole, with the dimension energy times
temperature.
-/
abbrev LambdaPerMole :=
  Dimensionful
    (WithDim
      (M𝓭 * L𝓭 * L𝓭 * T𝓭⁻¹ * T𝓭⁻¹ * Θ𝓭)
      ℝ)

/-- Heat capacity at constant magnetization, with dimension energy/temperature. -/
abbrev HeatCapacityAtConstantMagnetization :=
  Dimensionful
    (WithDim
      (M𝓭 * L𝓭 * L𝓭 * T𝓭⁻¹ * T𝓭⁻¹ * Θ𝓭⁻¹)
      ℝ)

/-- Numerical readout of a temperature in kelvin. -/
noncomputable def temperatureInKelvin
    (temperature : ThermodynamicTemperature) : ℝ :=
  (temperature SI).val

/-- Numerical readout of a volume in cubic metres. -/
noncomputable def volumeInCubicMeters (volume : PhysicalVolume) : ℝ :=
  (volume SI).val

/-- Numerical SI readout of an applied field-strength magnitude. -/
noncomputable def fieldStrengthInSI
    (field : AppliedFieldStrengthMagnitude) : ℝ :=
  (field SI).val

/-- Numerical SI readout of a magnetization magnitude. -/
noncomputable def magnetizationInSI
    (magnetization : MagnetizationMagnitude) : ℝ :=
  (magnetization SI).val

/-- Numerical SI readout of vacuum permeability. -/
noncomputable def vacuumPermeabilityInSI
    (permeability : VacuumPermeability) : ℝ :=
  (permeability SI).val

/-- Numerical SI readout of the equation-of-state constant per mole. -/
noncomputable def curieConstantInSI
    (constant : CurieConstantPerMole) : ℝ :=
  (constant SI).val

/-- Numerical SI readout of `λ` per mole. -/
noncomputable def lambdaInSI (lambda : LambdaPerMole) : ℝ :=
  (lambda SI).val

/-- Numerical SI readout of heat capacity at constant magnetization. -/
noncomputable def heatCapacityInSI
    (heatCapacity : HeatCapacityAtConstantMagnetization) : ℝ :=
  (heatCapacity SI).val

/-- Numerical readout of an energy in joules. -/
noncomputable def energyInJoules (energy : DimEnergy) : ℝ :=
  (energy SI).val

/--
The fixed material and geometric parameters of the paramagnetic torus.

`amountInMoles` is the scalar molar readout `n`; all other fields are physical
dimensionful quantities.
-/
structure ParamagneticTorus where
  volume : PhysicalVolume
  amountInMoles : ℝ
  curieConstant : CurieConstantPerMole
  lambda : LambdaPerMole
  vacuumPermeability : VacuumPermeability

/-- A quasistatic state of the paramagnetic torus. -/
structure ParamagneticTorusState where
  temperature : ThermodynamicTemperature
  appliedFieldStrength : AppliedFieldStrengthMagnitude
  magnetization : MagnetizationMagnitude

/--
A process of the torus, parameterized by dimensionless `τ`.

Heat and work are signed energies.  Their sign convention is fixed below by
the first-law hypothesis: transfer into the material is positive.
-/
structure ParamagneticTorusProcess where
  state : ℝ → ParamagneticTorusState
  heatCapacityAtConstantMagnetization :
    ℝ → HeatCapacityAtConstantMagnetization
  internalEnergy : ℝ → DimEnergy
  workIntoMaterial : ℝ → DimEnergy
  heatIntoMaterial : ℝ → DimEnergy

/-- Temperature readout along a torus process. -/
noncomputable def temperatureAlongProcessInKelvin
    (process : ParamagneticTorusProcess) (τ : ℝ) : ℝ :=
  temperatureInKelvin (process.state τ).temperature

/-- Applied-field-strength readout along a torus process. -/
noncomputable def fieldStrengthAlongProcessInSI
    (process : ParamagneticTorusProcess) (τ : ℝ) : ℝ :=
  fieldStrengthInSI (process.state τ).appliedFieldStrength

/-- Magnetization readout along a torus process. -/
noncomputable def magnetizationAlongProcessInSI
    (process : ParamagneticTorusProcess) (τ : ℝ) : ℝ :=
  magnetizationInSI (process.state τ).magnetization

/--
The equation of state, constitutive heat-capacity relation, energy law,
magnetic-work law from part A.3, first law, and adiabatic condition.

No endpoint temperature relation is included here.
-/
structure SatisfiesParamagneticTorusLaws
    (torus : ParamagneticTorus)
    (process : ParamagneticTorusProcess) : Prop where
  amount_positive :
    0 < torus.amountInMoles
  volume_positive :
    0 < volumeInCubicMeters torus.volume
  curieConstant_positive :
    0 < curieConstantInSI torus.curieConstant
  lambda_positive :
    0 < lambdaInSI torus.lambda
  vacuumPermeability_positive :
    0 < vacuumPermeabilityInSI torus.vacuumPermeability
  temperature_positive :
    ∀ τ ∈ Set.Icc (0 : ℝ) 1,
      0 < temperatureAlongProcessInKelvin process τ
  fieldStrength_isMagnitude :
    ∀ τ ∈ Set.Icc (0 : ℝ) 1,
      0 ≤ fieldStrengthAlongProcessInSI process τ
  magnetization_isMagnitude :
    ∀ τ ∈ Set.Icc (0 : ℝ) 1,
      0 ≤ magnetizationAlongProcessInSI process τ
  temperature_differentiable :
    DifferentiableOn ℝ
      (temperatureAlongProcessInKelvin process)
      (Set.Icc (0 : ℝ) 1)
  fieldStrength_differentiable :
    DifferentiableOn ℝ
      (fieldStrengthAlongProcessInSI process)
      (Set.Icc (0 : ℝ) 1)
  magnetization_differentiable :
    DifferentiableOn ℝ
      (magnetizationAlongProcessInSI process)
      (Set.Icc (0 : ℝ) 1)
  internalEnergy_differentiable :
    DifferentiableOn ℝ
      (fun τ => energyInJoules (process.internalEnergy τ))
      (Set.Icc (0 : ℝ) 1)
  work_differentiable :
    DifferentiableOn ℝ
      (fun τ => energyInJoules (process.workIntoMaterial τ))
      (Set.Icc (0 : ℝ) 1)
  heat_differentiable :
    DifferentiableOn ℝ
      (fun τ => energyInJoules (process.heatIntoMaterial τ))
      (Set.Icc (0 : ℝ) 1)
  equationOfState :
    ∀ τ ∈ Set.Icc (0 : ℝ) 1,
      temperatureAlongProcessInKelvin process τ *
            magnetizationAlongProcessInSI process τ *
          volumeInCubicMeters torus.volume =
        torus.amountInMoles *
            curieConstantInSI torus.curieConstant *
          fieldStrengthAlongProcessInSI process τ
  heatCapacityEquation :
    ∀ τ ∈ Set.Icc (0 : ℝ) 1,
      heatCapacityInSI
          (process.heatCapacityAtConstantMagnetization τ) =
        torus.amountInMoles * lambdaInSI torus.lambda /
          (temperatureAlongProcessInKelvin process τ) ^ 2
  internalEnergyDifferential :
    ∀ τ ∈ Set.Ioo (0 : ℝ) 1,
      deriv (fun s => energyInJoules (process.internalEnergy s)) τ =
        heatCapacityInSI
            (process.heatCapacityAtConstantMagnetization τ) *
          deriv (temperatureAlongProcessInKelvin process) τ
  magneticWorkDifferential_previousA3 :
    ∀ τ ∈ Set.Ioo (0 : ℝ) 1,
      deriv (fun s => energyInJoules (process.workIntoMaterial s)) τ =
        vacuumPermeabilityInSI torus.vacuumPermeability *
              volumeInCubicMeters torus.volume *
            fieldStrengthAlongProcessInSI process τ *
          deriv (magnetizationAlongProcessInSI process) τ
  firstLaw_enteringPositive :
    ∀ τ ∈ Set.Ioo (0 : ℝ) 1,
      deriv (fun s => energyInJoules (process.internalEnergy s)) τ =
        deriv (fun s => energyInJoules (process.heatIntoMaterial s)) τ +
          deriv (fun s => energyInJoules (process.workIntoMaterial s)) τ
  adiabatic_noHeat :
    ∀ τ ∈ Set.Ioo (0 : ℝ) 1,
      deriv (fun s => energyInJoules (process.heatIntoMaterial s)) τ = 0

/--
For an adiabatic change of applied-field magnitude from `H_initial_SI` to
`H_final_SI`, beginning at `T_initial_K`, the final-minus-initial temperature
has the value stated in IPhO 2026 problem 3, part B.2.
-/
theorem adiabatic_temperature_change
    (torus : ParamagneticTorus)
    (process : ParamagneticTorusProcess)
    (laws : SatisfiesParamagneticTorusLaws torus process)
    (H_initial_SI H_final_SI T_initial_K : ℝ)
    (h_initial_field :
      fieldStrengthAlongProcessInSI process 0 = H_initial_SI)
    (h_final_field :
      fieldStrengthAlongProcessInSI process 1 = H_final_SI)
    (h_initial_temperature :
      temperatureAlongProcessInKelvin process 0 = T_initial_K) :
    temperatureAlongProcessInKelvin process 1 - T_initial_K =
      T_initial_K *
        (Real.sqrt
            ((lambdaInSI torus.lambda +
                vacuumPermeabilityInSI torus.vacuumPermeability *
                  curieConstantInSI torus.curieConstant *
                  H_final_SI ^ 2) /
              (lambdaInSI torus.lambda +
                vacuumPermeabilityInSI torus.vacuumPermeability *
                  curieConstantInSI torus.curieConstant *
                  H_initial_SI ^ 2)) -
          1) := by
  have h_zero_mem : (0 : ℝ) ∈ Set.Icc (0 : ℝ) 1 := by
    norm_num
  have h_one_mem : (1 : ℝ) ∈ Set.Icc (0 : ℝ) 1 := by
    norm_num
  have h_initial_temperature_positive :
      0 < temperatureAlongProcessInKelvin process 0 :=
    laws.temperature_positive 0 h_zero_mem
  have h_final_temperature_positive :
      0 < temperatureAlongProcessInKelvin process 1 :=
    laws.temperature_positive 1 h_one_mem
  have h_initial_denominator_positive :
      0 <
        lambdaInSI torus.lambda +
          vacuumPermeabilityInSI torus.vacuumPermeability *
            curieConstantInSI torus.curieConstant *
            fieldStrengthAlongProcessInSI process 0 ^ 2 := by
    have h_coefficient_nonnegative :
        0 ≤
          vacuumPermeabilityInSI torus.vacuumPermeability *
            curieConstantInSI torus.curieConstant :=
      mul_nonneg
        (le_of_lt laws.vacuumPermeability_positive)
        (le_of_lt laws.curieConstant_positive)
    have h_field_term_nonnegative :
        0 ≤
          (vacuumPermeabilityInSI torus.vacuumPermeability *
              curieConstantInSI torus.curieConstant) *
            fieldStrengthAlongProcessInSI process 0 ^ 2 :=
      mul_nonneg h_coefficient_nonnegative
        (sq_nonneg (fieldStrengthAlongProcessInSI process 0))
    linarith [laws.lambda_positive]
  have h_final_denominator_positive :
      0 <
        lambdaInSI torus.lambda +
          vacuumPermeabilityInSI torus.vacuumPermeability *
            curieConstantInSI torus.curieConstant *
            fieldStrengthAlongProcessInSI process 1 ^ 2 := by
    have h_coefficient_nonnegative :
        0 ≤
          vacuumPermeabilityInSI torus.vacuumPermeability *
            curieConstantInSI torus.curieConstant :=
      mul_nonneg
        (le_of_lt laws.vacuumPermeability_positive)
        (le_of_lt laws.curieConstant_positive)
    have h_field_term_nonnegative :
        0 ≤
          (vacuumPermeabilityInSI torus.vacuumPermeability *
              curieConstantInSI torus.curieConstant) *
            fieldStrengthAlongProcessInSI process 1 ^ 2 :=
      mul_nonneg h_coefficient_nonnegative
        (sq_nonneg (fieldStrengthAlongProcessInSI process 1))
    linarith [laws.lambda_positive]
  have h_adiabatic_energy_balance :
      ∀ τ ∈ Set.Ioo (0 : ℝ) 1,
        (torus.amountInMoles * lambdaInSI torus.lambda /
              temperatureAlongProcessInKelvin process τ ^ 2) *
            deriv (temperatureAlongProcessInKelvin process) τ =
          vacuumPermeabilityInSI torus.vacuumPermeability *
                volumeInCubicMeters torus.volume *
              fieldStrengthAlongProcessInSI process τ *
            deriv (magnetizationAlongProcessInSI process) τ := by
    intro τ hτ
    rw [← laws.heatCapacityEquation τ (Set.Ioo_subset_Icc_self hτ)]
    rw [← laws.internalEnergyDifferential τ hτ]
    rw [laws.firstLaw_enteringPositive τ hτ]
    rw [laws.adiabatic_noHeat τ hτ, zero_add]
    exact laws.magneticWorkDifferential_previousA3 τ hτ
  have h_initial_temperature_value_positive : 0 < T_initial_K := by
    rw [← h_initial_temperature]
    exact h_initial_temperature_positive
  have h_initial_denominator_value_positive :
      0 <
        lambdaInSI torus.lambda +
          vacuumPermeabilityInSI torus.vacuumPermeability *
            curieConstantInSI torus.curieConstant *
            H_initial_SI ^ 2 := by
    rw [← h_initial_field]
    exact h_initial_denominator_positive
  have h_final_denominator_value_positive :
      0 <
        lambdaInSI torus.lambda +
          vacuumPermeabilityInSI torus.vacuumPermeability *
            curieConstantInSI torus.curieConstant *
            H_final_SI ^ 2 := by
    rw [← h_final_field]
    exact h_final_denominator_positive
  let T : ℝ → ℝ := temperatureAlongProcessInKelvin process
  let H : ℝ → ℝ := fieldStrengthAlongProcessInSI process
  let M : ℝ → ℝ := magnetizationAlongProcessInSI process
  let n : ℝ := torus.amountInMoles
  let lam : ℝ := lambdaInSI torus.lambda
  let mu : ℝ :=
    vacuumPermeabilityInSI torus.vacuumPermeability
  let K : ℝ := curieConstantInSI torus.curieConstant
  let V : ℝ := volumeInCubicMeters torus.volume
  let D : ℝ → ℝ := fun τ => lam + mu * K * (H τ * H τ)
  let F : ℝ → ℝ := fun τ => (T τ * T τ) / D τ
  have hn_pos : 0 < n := by
    simpa only [n] using laws.amount_positive
  have hlam_pos : 0 < lam := by
    simpa only [lam] using laws.lambda_positive
  have hmu_pos : 0 < mu := by
    simpa only [mu] using laws.vacuumPermeability_positive
  have hK_pos : 0 < K := by
    simpa only [K] using laws.curieConstant_positive
  have hV_pos : 0 < V := by
    simpa only [V] using laws.volume_positive
  have hT_pos : ∀ τ ∈ Set.Icc (0 : ℝ) 1, 0 < T τ := by
    intro τ hτ
    simpa only [T] using laws.temperature_positive τ hτ
  have hD_pos : ∀ τ ∈ Set.Icc (0 : ℝ) 1, 0 < D τ := by
    intro τ hτ
    dsimp only [D]
    have hmuK_nonnegative : 0 ≤ mu * K :=
      mul_nonneg hmu_pos.le hK_pos.le
    have hHsq_nonnegative : 0 ≤ H τ * H τ :=
      mul_self_nonneg (H τ)
    nlinarith [mul_nonneg hmuK_nonnegative hHsq_nonnegative]
  have hT_diff : DifferentiableOn ℝ T (Set.Icc (0 : ℝ) 1) := by
    simpa only [T] using laws.temperature_differentiable
  have hH_diff : DifferentiableOn ℝ H (Set.Icc (0 : ℝ) 1) := by
    simpa only [H] using laws.fieldStrength_differentiable
  have hM_diff : DifferentiableOn ℝ M (Set.Icc (0 : ℝ) 1) := by
    simpa only [M] using laws.magnetization_differentiable
  have h_ode :
      ∀ τ ∈ Set.Ioo (0 : ℝ) 1,
        D τ * deriv T τ =
          mu * K * H τ * T τ * deriv H τ := by
    intro τ hτ
    have hT_at : DifferentiableAt ℝ T τ :=
      hT_diff.differentiableAt (Icc_mem_nhds hτ.1 hτ.2)
    have hH_at : DifferentiableAt ℝ H τ :=
      hH_diff.differentiableAt (Icc_mem_nhds hτ.1 hτ.2)
    have hM_at : DifferentiableAt ℝ M τ :=
      hM_diff.differentiableAt (Icc_mem_nhds hτ.1 hτ.2)
    have h_eos : T τ * M τ * V = n * K * H τ := by
      simpa only [T, M, V, n, K, H] using
        laws.equationOfState τ (Set.Ioo_subset_Icc_self hτ)
    have h_eos_eventually :
        (fun s => T s * M s * V) =ᶠ[nhds τ]
          (fun s => n * K * H s) := by
      filter_upwards [Icc_mem_nhds hτ.1 hτ.2] with s hs
      simpa only [T, M, V, n, K, H] using
        laws.equationOfState s hs
    have h_left_deriv :
        HasDerivAt (fun s => T s * M s * V)
          ((deriv T τ * M τ + T τ * deriv M τ) * V) τ :=
      (hT_at.hasDerivAt.mul hM_at.hasDerivAt).mul_const V
    have h_right_deriv :
        HasDerivAt (fun s => n * K * H s)
          (n * K * deriv H τ) τ := by
      exact hH_at.hasDerivAt.const_mul (n * K)
    have h_eos_deriv := h_eos_eventually.deriv_eq
    rw [h_left_deriv.deriv, h_right_deriv.deriv] at h_eos_deriv
    have h_balance :
        (n * lam / T τ ^ 2) * deriv T τ =
          mu * V * H τ * deriv M τ := by
      simpa only [n, lam, T, mu, V, H, M] using
        h_adiabatic_energy_balance τ hτ
    have hT_ne : T τ ≠ 0 :=
      ne_of_gt (hT_pos τ (Set.Ioo_subset_Icc_self hτ))
    have h_balance_cleared :
        n * lam * deriv T τ =
          mu * V * H τ * deriv M τ * T τ ^ 2 := by
      field_simp [hT_ne] at h_balance
      nlinarith [h_balance]
    have h_times_n :
        n * (D τ * deriv T τ -
          mu * K * H τ * T τ * deriv H τ) = 0 := by
      dsimp only [D]
      linear_combination
        mu * H τ * T τ * h_eos_deriv -
        mu * H τ * deriv T τ * h_eos +
        h_balance_cleared
    have h_zero :
        D τ * deriv T τ -
          mu * K * H τ * T τ * deriv H τ = 0 :=
      (mul_eq_zero.mp h_times_n).resolve_left (ne_of_gt hn_pos)
    exact sub_eq_zero.mp h_zero
  have hF_diff :
      DifferentiableOn ℝ F (Set.Icc (0 : ℝ) 1) := by
    dsimp only [F, D]
    change
      DifferentiableOn ℝ
        ((T * T) /
          ((fun _ : ℝ => lam) +
            fun τ => mu * K * (H * H) τ))
        (Set.Icc (0 : ℝ) 1)
    exact
      (hT_diff.mul hT_diff).div
        ((differentiableOn_const (c := lam)).add
          ((hH_diff.mul hH_diff).const_mul (mu * K)))
        (fun τ hτ => ne_of_gt (hD_pos τ hτ))
  have hF_deriv_zero :
      ∀ τ ∈ Set.Ioo (0 : ℝ) 1, deriv F τ = 0 := by
    intro τ hτ
    have hT_at : DifferentiableAt ℝ T τ :=
      hT_diff.differentiableAt (Icc_mem_nhds hτ.1 hτ.2)
    have hH_at : DifferentiableAt ℝ H τ :=
      hH_diff.differentiableAt (Icc_mem_nhds hτ.1 hτ.2)
    have h_num :
        HasDerivAt (fun s => T s * T s)
          (deriv T τ * T τ + T τ * deriv T τ) τ :=
      hT_at.hasDerivAt.mul hT_at.hasDerivAt
    have h_den :
        HasDerivAt D
          (mu * K *
            (deriv H τ * H τ + H τ * deriv H τ)) τ := by
      dsimp only [D]
      change
        HasDerivAt
          ((fun _ : ℝ => lam) +
            fun s => mu * K * (H * H) s)
          (mu * K *
            (deriv H τ * H τ + H τ * deriv H τ)) τ
      simpa only [zero_add] using
        (hasDerivAt_const τ lam).add
          ((hH_at.hasDerivAt.mul hH_at.hasDerivAt).const_mul
            (mu * K))
    have hD_ne : D τ ≠ 0 :=
      ne_of_gt (hD_pos τ (Set.Ioo_subset_Icc_self hτ))
    have h_quot := h_num.div h_den hD_ne
    have h_numerator_zero :
        (deriv T τ * T τ + T τ * deriv T τ) * D τ -
          (T τ * T τ) *
            (mu * K *
              (deriv H τ * H τ + H τ * deriv H τ)) = 0 := by
      linear_combination 2 * T τ * h_ode τ hτ
    have h_quotient_zero :
        ((deriv T τ * T τ + T τ * deriv T τ) * D τ -
          (T τ * T τ) *
            (mu * K *
              (deriv H τ * H τ + H τ * deriv H τ))) /
            D τ ^ 2 = 0 := by
      rw [div_eq_zero_iff]
      exact Or.inl h_numerator_zero
    have hF_has : HasDerivAt F 0 τ := by
      change HasDerivAt ((fun s => T s * T s) / D) 0 τ
      rw [← h_quotient_zero]
      exact h_quot
    exact hF_has.deriv
  obtain ⟨c, hc, hc_slope⟩ :=
    exists_deriv_eq_slope F (by norm_num) hF_diff.continuousOn
      (hF_diff.mono Set.Ioo_subset_Icc_self)
  have hc_zero := hF_deriv_zero c hc
  rw [hc_zero] at hc_slope
  have hF_endpoints : F 1 = F 0 := by
    norm_num at hc_slope
    linarith
  have hT0 : T 0 = T_initial_K := by
    simpa only [T] using h_initial_temperature
  have hH0 : H 0 = H_initial_SI := by
    simpa only [H] using h_initial_field
  have hH1 : H 1 = H_final_SI := by
    simpa only [H] using h_final_field
  have hD0 :
      D 0 = lam + mu * K * H_initial_SI ^ 2 := by
    simp only [D, hH0]
    ring
  have hD1 :
      D 1 = lam + mu * K * H_final_SI ^ 2 := by
    simp only [D, hH1]
    ring
  have hD0_pos : 0 < D 0 := hD_pos 0 h_zero_mem
  have hD1_pos : 0 < D 1 := hD_pos 1 h_one_mem
  have h_square_cross :
      T 1 ^ 2 * D 0 = T 0 ^ 2 * D 1 := by
    apply
      (div_eq_div_iff (ne_of_gt hD1_pos) (ne_of_gt hD0_pos)).mp
    simpa only [F, pow_two] using hF_endpoints
  have h_ratio_pos : 0 < D 1 / D 0 :=
    div_pos hD1_pos hD0_pos
  have h_square_ratio :
      T 1 ^ 2 = T 0 ^ 2 * (D 1 / D 0) := by
    field_simp [ne_of_gt hD0_pos]
    exact h_square_cross
  have h_candidate_square :
      (T 0 * Real.sqrt (D 1 / D 0)) ^ 2 = T 1 ^ 2 := by
    calc
      (T 0 * Real.sqrt (D 1 / D 0)) ^ 2 =
          T 0 ^ 2 * Real.sqrt (D 1 / D 0) ^ 2 := by
            ring
      _ = T 0 ^ 2 * (D 1 / D 0) := by
        rw [Real.sq_sqrt h_ratio_pos.le]
      _ = T 1 ^ 2 := h_square_ratio.symm
  have h_candidate_pos :
      0 < T 0 * Real.sqrt (D 1 / D 0) :=
    mul_pos (hT_pos 0 h_zero_mem) (Real.sqrt_pos.2 h_ratio_pos)
  have hT1_formula :
      T 1 = T 0 * Real.sqrt (D 1 / D 0) := by
    nlinarith [h_candidate_square, hT_pos 1 h_one_mem]
  change
    T 1 - T_initial_K =
      T_initial_K *
        (Real.sqrt
            ((lam + mu * K * H_final_SI ^ 2) /
              (lam + mu * K * H_initial_SI ^ 2)) -
          1)
  rw [hT1_formula, hT0, hD1, hD0]
  ring

end IPhO2026Problems.IPhO2026_3_B_2
