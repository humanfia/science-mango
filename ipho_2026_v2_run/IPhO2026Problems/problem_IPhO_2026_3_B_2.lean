import Mathlib
import Physlib.Units.WithDim.Basic

/-!
# IPhO 2026 Problem 3, part B.2

An adiabatic change of the magnetic-field-strength magnitude of a paramagnetic
torus changes its temperature.  The physical quantities below are tagged with
their dimensions using `Physlib.WithDim`.  Calculus is performed on their
coherent-SI scalar readouts, exposed by `WithDim.val`.
-/

namespace IPhO2026Problems.IPhO2026_3_B_2

open Dimension
open Set

/-! ## Dimensions and physical quantities -/

/-- The dimension of volume. -/
def volumeDimension : Dimension := L𝓭 ^ 3

/-- The dimension of energy. -/
def energyDimension : Dimension := M𝓭 * L𝓭 ^ 2 * T𝓭⁻¹ ^ 2

/-- The dimension of both magnetic field strength `H` and magnetization `M`. -/
def magneticFieldStrengthDimension : Dimension := C𝓭 * T𝓭⁻¹ * L𝓭⁻¹

/-- The dimension of heat capacity. -/
def heatCapacityDimension : Dimension := energyDimension * Θ𝓭⁻¹

/--
The dimension assigned to the Curie-law constant `K`.

`Physlib.Dimension` does not include amount of substance among its base
dimensions, so the mole readout `n` is kept separately and `K` carries the
remaining temperature-times-volume dimension.
-/
def curieConstantDimension : Dimension := Θ𝓭 * volumeDimension

/-- The dimension of the heat-capacity parameter `λ`. -/
def heatCapacityParameterDimension : Dimension := energyDimension * Θ𝓭

/-- The SI dimension of vacuum permeability `μ₀`. -/
def vacuumPermeabilityDimension : Dimension := M𝓭 * L𝓭 * C𝓭⁻¹ ^ 2

abbrev TemperatureQuantity := WithDim Θ𝓭 ℝ
abbrev VolumeQuantity := WithDim volumeDimension ℝ
abbrev EnergyQuantity := WithDim energyDimension ℝ
abbrev MagneticFieldStrengthQuantity := WithDim magneticFieldStrengthDimension ℝ
abbrev MagnetizationQuantity := WithDim magneticFieldStrengthDimension ℝ
abbrev HeatCapacityQuantity := WithDim heatCapacityDimension ℝ
abbrev CurieConstantQuantity := WithDim curieConstantDimension ℝ
abbrev HeatCapacityParameterQuantity := WithDim heatCapacityParameterDimension ℝ
abbrev VacuumPermeabilityQuantity := WithDim vacuumPermeabilityDimension ℝ

/-! ## Torus data and process readouts -/

/--
Fixed data of the paramagnetic torus.  The real components are coherent-SI
readouts.  Positivity records physical admissibility, not the requested
temperature-change formula.
-/
structure ParamagneticTorusModel where
  /-- Amount of paramagnetic material, measured in moles. -/
  amountInMoles : ℝ
  /-- The fixed volume `V` of the torus. -/
  volumeSI : VolumeQuantity
  /-- The constant `K` in `T M V = n K H`. -/
  curieConstantSI : CurieConstantQuantity
  /-- The constant `λ` in `C_M = n λ / T²`. -/
  heatCapacityParameterSI : HeatCapacityParameterQuantity
  /-- Vacuum permeability `μ₀`. -/
  vacuumPermeabilitySI : VacuumPermeabilityQuantity
  amountInMoles_pos : 0 < amountInMoles
  volume_pos : 0 < volumeSI.val
  curieConstant_pos : 0 < curieConstantSI.val
  heatCapacityParameter_pos : 0 < heatCapacityParameterSI.val
  vacuumPermeability_pos : 0 < vacuumPermeabilitySI.val

/--
Measured quantities along a dimensionless process parameter `s`.

The interval endpoints `s = 0` and `s = 1` represent the incoming and outgoing
states.  Since `s` is dimensionless, the heat and work input rates below have
the dimension of energy.
-/
structure AdiabaticPathReadout where
  temperatureSI : ℝ → TemperatureQuantity
  fieldStrengthMagnitudeSI : ℝ → MagneticFieldStrengthQuantity
  magnetizationMagnitudeSI : ℝ → MagnetizationQuantity
  internalEnergySI : ℝ → EnergyQuantity
  heatCapacityAtConstantMagnetizationSI : ℝ → HeatCapacityQuantity
  heatInputRateSI : ℝ → EnergyQuantity
  workInputRateSI : ℝ → EnergyQuantity

/-- The closed parameter interval occupied by the change. -/
def processDomain : Set ℝ := Set.Icc 0 1

/--
The governing laws and endpoint readouts for a quasistatic adiabatic change.

The sign convention is exposed by `first_law`: positive `heatInputRateSI` and
positive `workInputRateSI` both increase the internal energy.  The field
`magnetic_work` is the reusable conclusion of part A.3.
-/
structure IsAdiabaticQuasistaticChange
    (model : ParamagneticTorusModel)
    (path : AdiabaticPathReadout)
    (initialTemperature finalTemperature : TemperatureQuantity)
    (initialFieldStrength finalFieldStrength : MagneticFieldStrengthQuantity) : Prop where
  temperature_differentiable :
    DifferentiableOn ℝ (fun s => (path.temperatureSI s).val) processDomain
  fieldStrength_differentiable :
    DifferentiableOn ℝ (fun s => (path.fieldStrengthMagnitudeSI s).val) processDomain
  magnetization_differentiable :
    DifferentiableOn ℝ (fun s => (path.magnetizationMagnitudeSI s).val) processDomain
  internalEnergy_differentiable :
    DifferentiableOn ℝ (fun s => (path.internalEnergySI s).val) processDomain
  initial_temperature : path.temperatureSI 0 = initialTemperature
  final_temperature : path.temperatureSI 1 = finalTemperature
  initial_field_strength : path.fieldStrengthMagnitudeSI 0 = initialFieldStrength
  final_field_strength : path.fieldStrengthMagnitudeSI 1 = finalFieldStrength
  temperature_positive :
    ∀ s ∈ processDomain, 0 < (path.temperatureSI s).val
  fieldStrengthMagnitude_nonnegative :
    ∀ s ∈ processDomain, 0 ≤ (path.fieldStrengthMagnitudeSI s).val
  magnetizationMagnitude_nonnegative :
    ∀ s ∈ processDomain, 0 ≤ (path.magnetizationMagnitudeSI s).val
  equation_of_state :
    ∀ s ∈ processDomain,
      (path.temperatureSI s).val
          * (path.magnetizationMagnitudeSI s).val
          * model.volumeSI.val =
        model.amountInMoles * model.curieConstantSI.val
          * (path.fieldStrengthMagnitudeSI s).val
  heat_capacity :
    ∀ s ∈ processDomain,
      (path.heatCapacityAtConstantMagnetizationSI s).val =
        model.amountInMoles * model.heatCapacityParameterSI.val
          / (path.temperatureSI s).val ^ 2
  internal_energy_change :
    ∀ s ∈ processDomain,
      derivWithin (fun u => (path.internalEnergySI u).val) processDomain s =
        (path.heatCapacityAtConstantMagnetizationSI s).val
          * derivWithin (fun u => (path.temperatureSI u).val) processDomain s
  adiabatic :
    ∀ s ∈ processDomain, (path.heatInputRateSI s).val = 0
  first_law :
    ∀ s ∈ processDomain,
      derivWithin (fun u => (path.internalEnergySI u).val) processDomain s =
        (path.heatInputRateSI s).val + (path.workInputRateSI s).val
  magnetic_work :
    ∀ s ∈ processDomain,
      (path.workInputRateSI s).val =
        model.vacuumPermeabilitySI.val * model.volumeSI.val
          * (path.fieldStrengthMagnitudeSI s).val
          * derivWithin (fun u => (path.magnetizationMagnitudeSI u).val)
              processDomain s

/-! ## Derivability bridges -/

/--
The differential laws reduce to the separable magnetocaloric ODE.  This is the
algebra-and-product-rule bridge from the physical assumptions to the invariant
used in the endpoint calculation.
-/
theorem reduced_adiabatic_temperature_ode
    (model : ParamagneticTorusModel)
    (path : AdiabaticPathReadout)
    (initialTemperature finalTemperature : TemperatureQuantity)
    (initialFieldStrength finalFieldStrength : MagneticFieldStrengthQuantity)
    (hphysics : IsAdiabaticQuasistaticChange model path
      initialTemperature finalTemperature initialFieldStrength finalFieldStrength)
    (s : ℝ) (hs : s ∈ processDomain) :
    (model.heatCapacityParameterSI.val
          + model.vacuumPermeabilitySI.val * model.curieConstantSI.val
            * (path.fieldStrengthMagnitudeSI s).val ^ 2)
        * derivWithin (fun u => (path.temperatureSI u).val) processDomain s =
      model.vacuumPermeabilitySI.val * model.curieConstantSI.val
        * (path.fieldStrengthMagnitudeSI s).val
        * (path.temperatureSI s).val
        * derivWithin (fun u => (path.fieldStrengthMagnitudeSI u).val)
            processDomain s := by
  let T : ℝ → ℝ := fun u => (path.temperatureSI u).val
  let H : ℝ → ℝ := fun u => (path.fieldStrengthMagnitudeSI u).val
  let M : ℝ → ℝ := fun u => (path.magnetizationMagnitudeSI u).val
  let n : ℝ := model.amountInMoles
  let V : ℝ := model.volumeSI.val
  let K : ℝ := model.curieConstantSI.val
  let lam : ℝ := model.heatCapacityParameterSI.val
  let mu : ℝ := model.vacuumPermeabilitySI.val
  have hT : DifferentiableWithinAt ℝ T processDomain s := by
    simpa [T] using hphysics.temperature_differentiable s hs
  have hH : DifferentiableWithinAt ℝ H processDomain s := by
    simpa [H] using hphysics.fieldStrength_differentiable s hs
  have hM : DifferentiableWithinAt ℝ M processDomain s := by
    simpa [M] using hphysics.magnetization_differentiable s hs
  have hunique : UniqueDiffWithinAt ℝ processDomain s := by
    simpa [processDomain] using
      (uniqueDiffOn_Icc (by norm_num : (0 : ℝ) < 1) s hs)
  have heosOn :
      Set.EqOn (fun u => T u * M u * V) (fun u => n * K * H u)
        processDomain := by
    intro u hu
    simpa [T, H, M, n, V, K] using hphysics.equation_of_state u hu
  have heos : T s * M s * V = n * K * H s := heosOn hs
  have hleft :
      derivWithin (fun u => T u * M u * V) processDomain s =
        (derivWithin T processDomain s * M s
            + T s * derivWithin M processDomain s) * V := by
    simpa only [Pi.mul_apply] using
      ((hT.hasDerivWithinAt.mul hM.hasDerivWithinAt).mul_const V).derivWithin
        hunique
  have hright :
      derivWithin (fun u => n * K * H u) processDomain s =
        n * K * derivWithin H processDomain s := by
    simpa only [mul_assoc] using
      (hH.hasDerivWithinAt.const_mul (n * K)).derivWithin hunique
  have hde :
      (derivWithin T processDomain s * M s
          + T s * derivWithin M processDomain s) * V =
        n * K * derivWithin H processDomain s := by
    calc
      _ = derivWithin (fun u => T u * M u * V) processDomain s := hleft.symm
      _ = derivWithin (fun u => n * K * H u) processDomain s :=
        derivWithin_congr heosOn (heosOn hs)
      _ = _ := hright
  have henergyRaw :
      (path.heatCapacityAtConstantMagnetizationSI s).val
            * derivWithin T processDomain s =
        mu * V * H s * derivWithin M processDomain s := by
    rw [← hphysics.internal_energy_change s hs, hphysics.first_law s hs,
      hphysics.adiabatic s hs, zero_add, hphysics.magnetic_work s hs]
  rw [hphysics.heat_capacity s hs] at henergyRaw
  have henergy :
      (n * lam / T s ^ 2) * derivWithin T processDomain s =
        mu * V * H s * derivWithin M processDomain s := by
    simpa [T, H, M, n, V, lam, mu] using henergyRaw
  have hTpos : 0 < T s := by
    simpa [T] using hphysics.temperature_positive s hs
  field_simp [ne_of_gt hTpos] at henergy
  have hscaled :
      n * ((lam + mu * K * H s ^ 2) * derivWithin T processDomain s
        - mu * K * H s * T s * derivWithin H processDomain s) = 0 := by
    linear_combination
      mu * H s * T s * hde
        - mu * H s * derivWithin T processDomain s * heos
        + henergy
  have hz := (mul_eq_zero.mp hscaled).resolve_left (ne_of_gt model.amountInMoles_pos)
  simpa [T, H, n, K, lam, mu] using (sub_eq_zero.mp hz)

/-- The positive energy-times-temperature scale occurring in the ODE. -/
def magnetothermalScaleSI
    (model : ParamagneticTorusModel) (path : AdiabaticPathReadout) (s : ℝ) : ℝ :=
  model.heatCapacityParameterSI.val
    + model.vacuumPermeabilitySI.val * model.curieConstantSI.val
      * (path.fieldStrengthMagnitudeSI s).val ^ 2

/-- The path invariant obtained by separating the reduced ODE. -/
noncomputable def magnetothermalInvariantSI
    (model : ParamagneticTorusModel) (path : AdiabaticPathReadout) (s : ℝ) : ℝ :=
  (path.temperatureSI s).val ^ 2 / magnetothermalScaleSI model path s

/--
Along any admissible adiabatic path, `T² / (λ + μ₀ K H²)` is constant.
Mathlib's derivative-zero-on-an-interval theorem can carry the final
calculus step once the reduced ODE has been established.
-/
theorem magnetothermal_invariant_constant
    (model : ParamagneticTorusModel)
    (path : AdiabaticPathReadout)
    (initialTemperature finalTemperature : TemperatureQuantity)
    (initialFieldStrength finalFieldStrength : MagneticFieldStrengthQuantity)
    (hphysics : IsAdiabaticQuasistaticChange model path
      initialTemperature finalTemperature initialFieldStrength finalFieldStrength) :
    ∀ s ∈ processDomain,
      magnetothermalInvariantSI model path s =
        magnetothermalInvariantSI model path 0 := by
  let T : ℝ → ℝ := fun u => (path.temperatureSI u).val
  let H : ℝ → ℝ := fun u => (path.fieldStrengthMagnitudeSI u).val
  let lam : ℝ := model.heatCapacityParameterSI.val
  let mu : ℝ := model.vacuumPermeabilitySI.val
  let K : ℝ := model.curieConstantSI.val
  let S : ℝ → ℝ := fun u => lam + mu * K * H u ^ 2
  let F : ℝ → ℝ := T ^ 2 / S
  have hTOn : DifferentiableOn ℝ T processDomain := by
    simpa [T] using hphysics.temperature_differentiable
  have hHOn : DifferentiableOn ℝ H processDomain := by
    simpa [H] using hphysics.fieldStrength_differentiable
  have hSOn : DifferentiableOn ℝ S processDomain := by
    simpa [S, mul_assoc] using
      (differentiableOn_const lam).add ((hHOn.pow 2).const_mul (mu * K))
  have hSpos : ∀ u ∈ processDomain, 0 < S u := by
    intro u hu
    have hcoeff : 0 < mu * K := by
      exact mul_pos model.vacuumPermeability_pos model.curieConstant_pos
    exact add_pos_of_pos_of_nonneg model.heatCapacityParameter_pos
      (mul_nonneg hcoeff.le (sq_nonneg (H u)))
  have hFOn : DifferentiableOn ℝ F processDomain := by
    change DifferentiableOn ℝ (T ^ 2 / S) processDomain
    exact (hTOn.pow 2).div hSOn (fun u hu => ne_of_gt (hSpos u hu))
  have hFderiv :
      ∀ u ∈ Set.Ico (0 : ℝ) 1, derivWithin F processDomain u = 0 := by
    intro u hu
    have hu' : u ∈ processDomain := by
      exact ⟨hu.1, hu.2.le⟩
    have hT := hTOn u hu'
    have hH := hHOn u hu'
    have hS := hSOn u hu'
    have hunique : UniqueDiffWithinAt ℝ processDomain u := by
      simpa [processDomain] using
        (uniqueDiffOn_Icc (by norm_num : (0 : ℝ) < 1) u hu')
    have hTderiv :
        derivWithin (T ^ 2) processDomain u =
          2 * T u * derivWithin T processDomain u := by
      simpa using (hT.hasDerivWithinAt.pow 2).derivWithin hunique
    have hSderiv :
        derivWithin S processDomain u =
          2 * mu * K * H u * derivWithin H processDomain u := by
      convert
        (((hH.hasDerivWithinAt.pow 2).const_mul (mu * K)).const_add lam).derivWithin
          hunique using 1
      all_goals simp [S]
      all_goals ring
    have hode :
        S u * derivWithin T processDomain u =
          mu * K * H u * T u * derivWithin H processDomain u := by
      simpa [S, T, H, lam, mu, K] using
        reduced_adiabatic_temperature_ode model path initialTemperature
          finalTemperature initialFieldStrength finalFieldStrength hphysics u hu'
    rw [show F = T ^ 2 / S by rfl,
      derivWithin_div (hT.pow 2) hS (ne_of_gt (hSpos u hu')),
      hTderiv, hSderiv]
    have hnum :
        2 * T u * derivWithin T processDomain u * S u
            - T u ^ 2 * (2 * mu * K * H u * derivWithin H processDomain u) = 0 := by
      linear_combination 2 * T u * hode
    simp only [Pi.pow_apply]
    rw [hnum, zero_div]
  intro s hs
  have hconstant :=
    constant_of_derivWithin_zero
      (a := (0 : ℝ)) (b := 1)
      (by simpa [processDomain] using hFOn)
      (by simpa [processDomain] using hFderiv) s
      (by simpa [processDomain] using hs)
  simpa [F, S, T, H, lam, mu, K, magnetothermalInvariantSI,
    magnetothermalScaleSI] using hconstant

/-! ## Current subquestion -/

/--
For an adiabatic change from `Hᵢ` to `H_f`, the requested temperature change
`ΔT = T_f - Tᵢ`.

The positivity assumptions in the physical model and along the path select the
positive square-root branch.
-/
theorem adiabatic_temperature_change
    (model : ParamagneticTorusModel)
    (path : AdiabaticPathReadout)
    (initialTemperature finalTemperature : TemperatureQuantity)
    (initialFieldStrength finalFieldStrength : MagneticFieldStrengthQuantity)
    (hphysics : IsAdiabaticQuasistaticChange model path
      initialTemperature finalTemperature initialFieldStrength finalFieldStrength) :
    finalTemperature.val - initialTemperature.val =
      initialTemperature.val *
        (Real.sqrt
            ((model.heatCapacityParameterSI.val
                + model.vacuumPermeabilitySI.val * model.curieConstantSI.val
                  * finalFieldStrength.val ^ 2) /
              (model.heatCapacityParameterSI.val
                + model.vacuumPermeabilitySI.val * model.curieConstantSI.val
                  * initialFieldStrength.val ^ 2)) - 1) := by
  let Ai : ℝ :=
    model.heatCapacityParameterSI.val
      + model.vacuumPermeabilitySI.val * model.curieConstantSI.val
        * initialFieldStrength.val ^ 2
  let Af : ℝ :=
    model.heatCapacityParameterSI.val
      + model.vacuumPermeabilitySI.val * model.curieConstantSI.val
        * finalFieldStrength.val ^ 2
  have hcoeff :
      0 < model.vacuumPermeabilitySI.val * model.curieConstantSI.val :=
    mul_pos model.vacuumPermeability_pos model.curieConstant_pos
  have hAi : 0 < Ai := by
    exact add_pos_of_pos_of_nonneg model.heatCapacityParameter_pos
      (mul_nonneg hcoeff.le (sq_nonneg initialFieldStrength.val))
  have hAf : 0 < Af := by
    exact add_pos_of_pos_of_nonneg model.heatCapacityParameter_pos
      (mul_nonneg hcoeff.le (sq_nonneg finalFieldStrength.val))
  have hzero : (0 : ℝ) ∈ processDomain := by
    simp [processDomain]
  have hone : (1 : ℝ) ∈ processDomain := by
    simp [processDomain]
  have hTi : 0 < initialTemperature.val := by
    simpa [hphysics.initial_temperature] using
      hphysics.temperature_positive 0 hzero
  have hTf : 0 < finalTemperature.val := by
    simpa [hphysics.final_temperature] using
      hphysics.temperature_positive 1 hone
  have hinvPath :=
    magnetothermal_invariant_constant model path initialTemperature
      finalTemperature initialFieldStrength finalFieldStrength hphysics 1 hone
  have hinv :
      finalTemperature.val ^ 2 / Af = initialTemperature.val ^ 2 / Ai := by
    simpa [magnetothermalInvariantSI, magnetothermalScaleSI, Ai, Af,
      hphysics.initial_temperature, hphysics.final_temperature,
      hphysics.initial_field_strength, hphysics.final_field_strength] using hinvPath
  change finalTemperature.val - initialTemperature.val =
    initialTemperature.val * (Real.sqrt (Af / Ai) - 1)
  have hratio : 0 ≤ Af / Ai := div_nonneg hAf.le hAi.le
  have hrel := hinv
  field_simp [ne_of_gt hAf, ne_of_gt hAi] at hrel
  have hsquare :
      (initialTemperature.val * Real.sqrt (Af / Ai)) ^ 2 =
        finalTemperature.val ^ 2 := by
    rw [mul_pow, Real.sq_sqrt hratio]
    field_simp [ne_of_gt hAi]
    nlinarith
  have hrhs : 0 ≤ initialTemperature.val * Real.sqrt (Af / Ai) :=
    mul_nonneg hTi.le (Real.sqrt_nonneg _)
  have hroot :
      finalTemperature.val = initialTemperature.val * Real.sqrt (Af / Ai) := by
    nlinarith
  rw [hroot]
  ring

end IPhO2026Problems.IPhO2026_3_B_2
