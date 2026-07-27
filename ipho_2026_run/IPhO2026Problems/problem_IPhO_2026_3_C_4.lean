import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Physlib.Thermodynamics.Temperature.Basic
import Physlib.Units.WithDim.Basic

/-!
# IPhO 2026, problem 3, part C.4

The physical quantities below are scalar readouts in one coherent choice of
units.  `Temperature` supplies Physlib's nonnegative absolute-temperature type,
while `WithDim` records the dimensions of the remaining readouts.

For the continuously repeated Carnot cycles, `hotHeatRate` and `coldHeatRate`
represent the continuous-limit versions of `dQₕ/dt` and `dQ꜀/dt`.  The
governing-law predicate records:

* constant input-power balance `dQₕ/dt - dQ꜀/dt = P`;
* the figure/source relation `dQ꜀/dQₕ = T꜀/Tₕ`;
* heat balance of the cooled body, `dT꜀/dt = -(dQ꜀/dt)/C꜀`.

The integrated expression requested in C.4 occurs only in the conclusion of
`IPhO_2026_3_C_4_elapsedTime`.
-/

namespace IPhO2026Problems.IPhO2026_3_C_4

noncomputable section

open Dimension

/-! ## Dimensioned scalar readouts -/

/-- The dimension of mechanical or thermal energy, `M L² T⁻²`. -/
def energyDimension : Dimension :=
  M𝓭 * L𝓭 * L𝓭 * T𝓭⁻¹ * T𝓭⁻¹

/-- The dimension of volume, `L³`. -/
def volumeDimension : Dimension :=
  L𝓭 * L𝓭 * L𝓭

/-- The SI dimension of both magnetic field strength `H` and magnetization `M`,
`A/L = C T⁻¹ L⁻¹`. -/
def magneticIntensityDimension : Dimension :=
  C𝓭 * T𝓭⁻¹ * L𝓭⁻¹

/-- The dimension of a heat capacity, energy per absolute temperature. -/
def heatCapacityDimension : Dimension :=
  energyDimension * Θ𝓭⁻¹

/-- The dimension of power or heat-flow rate, energy per time. -/
def powerDimension : Dimension :=
  energyDimension * T𝓭⁻¹

/-- The dimension of the Curie constant `K` in `T M V = n K H`, with amount of
substance tracked separately in moles. -/
def molarCurieConstantDimension : Dimension :=
  Θ𝓭 * volumeDimension

/-- A scalar energy readout, such as the magnitudes `Qₕ` and `Q꜀`. -/
abbrev EnergyReadout : Type :=
  WithDim energyDimension ℝ

/-- A scalar volume readout for the paramagnetic torus. -/
abbrev VolumeReadout : Type :=
  WithDim volumeDimension ℝ

/-- A scalar readout of either magnetic field strength or magnetization. -/
abbrev MagneticIntensityReadout : Type :=
  WithDim magneticIntensityDimension ℝ

/-- A scalar readout of the body's constant heat capacity `C꜀`. -/
abbrev HeatCapacityReadout : Type :=
  WithDim heatCapacityDimension ℝ

/-- A scalar readout of power or a heat-flow rate. -/
abbrev PowerReadout : Type :=
  WithDim powerDimension ℝ

/-- A scalar elapsed-time readout. -/
abbrev TimeReadout : Type :=
  WithDim T𝓭 ℝ

/-- Physlib's dimension basis has no amount-of-substance coordinate, so the
molar readout is kept as a separately named physical quantity. -/
structure AmountOfSubstanceReadout where
  /-- Numerical amount in moles. -/
  moles : ℝ

/-! ## Figure 3b and the paramagnetic Carnot cycle -/

/-- The four labels in the `H`-versus-`T` cycle shown in Figure 3b. -/
inductive CyclePoint
  | one
  | two
  | three
  | four
  deriving DecidableEq, Repr

/-- The direction of the refrigeration cycle read from Figure 3b. -/
def refrigerationCycleOrder : List CyclePoint :=
  [.one, .two, .three, .four, .one]

/-- Readouts describing the paramagnetic torus and the labelled points of its
Carnot refrigeration cycle.  At each point, the plotted coordinates are
`(temperatureAt point, magneticFieldAt point)`. -/
structure ParamagneticCarnotCycle where
  /-- Coherent units used for all scalar readouts. -/
  unitChoice : UnitChoices
  /-- Volume `V` of the torus. -/
  torusVolume : VolumeReadout
  /-- Amount `n` of paramagnetic substance. -/
  amountOfSubstance : AmountOfSubstanceReadout
  /-- Material constant `K` in the equation of state. -/
  curieConstant : WithDim molarCurieConstantDimension ℝ
  /-- Absolute temperature coordinate at each figure label. -/
  temperatureAt : CyclePoint → Temperature
  /-- Magnetic-field-strength coordinate `H` at each figure label. -/
  magneticFieldAt : CyclePoint → MagneticIntensityReadout
  /-- Magnetization `M` at each figure label. -/
  magnetizationAt : CyclePoint → MagneticIntensityReadout
  /-- Constant hot-reservoir temperature `Tₕ`. -/
  hotReservoirTemperature : Temperature
  /-- Cold-reservoir temperature `T꜀` for the represented operating cycle. -/
  coldReservoirTemperature : Temperature
  /-- Magnitude `Qₕ` delivered to the hot reservoir in one cycle. -/
  hotHeatMagnitude : EnergyReadout
  /-- Magnitude `Q꜀` absorbed from the cold reservoir in one cycle. -/
  coldHeatMagnitude : EnergyReadout

/-- The paramagnetic equation of state `T M V = n K H` at every labelled
cycle point. -/
def ObeysParamagneticEquationOfState (cycle : ParamagneticCarnotCycle) : Prop :=
  ∀ point : CyclePoint,
    (cycle.temperatureAt point : ℝ) * (cycle.magnetizationAt point).val *
          cycle.torusVolume.val =
      cycle.amountOfSubstance.moles * cycle.curieConstant.val *
        (cycle.magneticFieldAt point).val

/-- Temperature levels read from Figure 3b: states 1 and 4 lie on the hot
isotherm, while states 2 and 3 lie on the cold isotherm. -/
def FollowsFigureThreeB (cycle : ParamagneticCarnotCycle) : Prop :=
  cycle.temperatureAt .one = cycle.hotReservoirTemperature ∧
    cycle.temperatureAt .four = cycle.hotReservoirTemperature ∧
    cycle.temperatureAt .two = cycle.coldReservoirTemperature ∧
    cycle.temperatureAt .three = cycle.coldReservoirTemperature

/-! ## Continuous cooling experiment -/

/-- Data for cooling a finite-capacity body by continuously repeated Carnot
cycles.  A single field for `C꜀`, `P`, and `Tₕ` expresses that each is constant
during the run.  The real argument of the time-dependent readouts is time
measured in `unitChoice`. -/
structure ContinuousCoolingRun where
  /-- Coherent units used for the run's scalar readouts. -/
  unitChoice : UnitChoices
  /-- Constant heat capacity `C꜀` of the cooled body. -/
  bodyHeatCapacity : HeatCapacityReadout
  /-- Constant power `P` transferred to the refrigerator. -/
  inputPower : PowerReadout
  /-- Constant hot-reservoir temperature `Tₕ`. -/
  hotReservoirTemperature : Temperature
  /-- Body temperature `T₀` at time zero. -/
  initialTemperature : Temperature
  /-- Requested final body temperature `T`. -/
  finalTemperature : Temperature
  /-- Operating time `t` needed to reach the final temperature. -/
  elapsedTime : TimeReadout
  /-- Instantaneous temperature `T꜀(t)` of the cooled body. -/
  bodyTemperature : ℝ → Temperature
  /-- Continuous-limit hot heat-flow magnitude `dQₕ/dt`. -/
  hotHeatRate : ℝ → PowerReadout
  /-- Continuous-limit cold heat-flow magnitude `dQ꜀/dt`. -/
  coldHeatRate : ℝ → PowerReadout

/-- Endpoint, positivity, and operating-temperature conditions for an actual
cooling run from `T₀` down to `T`, entirely below `Tₕ`. -/
def HasPhysicalOperatingRange (run : ContinuousCoolingRun) : Prop :=
  0 < run.bodyHeatCapacity.val ∧
    0 < run.inputPower.val ∧
    0 < (run.finalTemperature : ℝ) ∧
    (run.finalTemperature : ℝ) < (run.initialTemperature : ℝ) ∧
    (run.initialTemperature : ℝ) < (run.hotReservoirTemperature : ℝ) ∧
    0 < run.elapsedTime.val ∧
    run.bodyTemperature 0 = run.initialTemperature ∧
    run.bodyTemperature run.elapsedTime.val = run.finalTemperature ∧
    ContinuousOn (fun s : ℝ => (run.bodyTemperature s : ℝ))
      (Set.Icc (0 : ℝ) run.elapsedTime.val) ∧
    ∀ s ∈ Set.Icc (0 : ℝ) run.elapsedTime.val,
      0 < (run.bodyTemperature s : ℝ) ∧
        (run.bodyTemperature s : ℝ) < (run.hotReservoirTemperature : ℝ)

/-- Governing laws for the continuous limit of the repeated Carnot cycles.

The middle equality is exactly the source relation
`dQ꜀/dQₕ = T꜀/Tₕ`, expressed using heat-flow rates.  The final derivative is
the constant-heat-capacity law for the cooled body. -/
def ObeysContinuousCarnotCoolingLaws (run : ContinuousCoolingRun) : Prop :=
  ∀ s ∈ Set.Ioo (0 : ℝ) run.elapsedTime.val,
    0 < (run.coldHeatRate s).val ∧
      0 < (run.hotHeatRate s).val ∧
      (run.hotHeatRate s).val - (run.coldHeatRate s).val =
        run.inputPower.val ∧
      (run.coldHeatRate s).val / (run.hotHeatRate s).val =
        (run.bodyTemperature s : ℝ) /
          (run.hotReservoirTemperature : ℝ) ∧
      HasDerivAt (fun u : ℝ => (run.bodyTemperature u : ℝ))
        (-((run.coldHeatRate s).val / run.bodyHeatCapacity.val)) s

/-- Elapsed time for cooling the body from `T₀` to `T` with constant heat
capacity, constant refrigerator input power, and constant hot-reservoir
temperature. -/
theorem IPhO_2026_3_C_4_elapsedTime
    (cycle : ParamagneticCarnotCycle)
    (run : ContinuousCoolingRun)
    (h_sameUnits : run.unitChoice = cycle.unitChoice)
    (h_sameHotReservoir :
      run.hotReservoirTemperature = cycle.hotReservoirTemperature)
    (h_figure : FollowsFigureThreeB cycle)
    (h_equationOfState : ObeysParamagneticEquationOfState cycle)
    (h_operatingRange : HasPhysicalOperatingRange run)
    (h_carnotCooling : ObeysContinuousCarnotCoolingLaws run) :
    run.elapsedTime.val =
      (run.bodyHeatCapacity.val * (run.hotReservoirTemperature : ℝ) /
          run.inputPower.val) *
        (Real.log
            ((run.initialTemperature : ℝ) / (run.finalTemperature : ℝ)) -
          ((run.initialTemperature : ℝ) - (run.finalTemperature : ℝ)) /
            (run.hotReservoirTemperature : ℝ)) := by
  rcases h_operatingRange with
    ⟨h_heatCapacity_pos, h_power_pos, h_final_pos, h_final_lt_initial,
      h_initial_lt_hot, h_elapsed_pos, h_temperature_zero,
      h_temperature_elapsed, h_temperature_continuous, h_temperature_range⟩
  have h_hot_pos : 0 < (run.hotReservoirTemperature : ℝ) :=
    h_final_pos.trans (h_final_lt_initial.trans h_initial_lt_hot)
  let temperature : ℝ → ℝ := fun s => (run.bodyTemperature s : ℝ)
  let potential : ℝ → ℝ := fun s =>
    (run.bodyHeatCapacity.val / run.inputPower.val) *
      ((run.hotReservoirTemperature : ℝ) * Real.log (temperature s) -
        temperature s)
  have h_temperature_continuous :
      ContinuousOn temperature (Set.Icc (0 : ℝ) run.elapsedTime.val) := by
    simpa only [temperature] using h_temperature_continuous
  have h_temperature_ne :
      ∀ s ∈ Set.Icc (0 : ℝ) run.elapsedTime.val, temperature s ≠ 0 := by
    intro s hs
    exact ne_of_gt (h_temperature_range s hs).1
  have h_potential_continuous :
      ContinuousOn potential (Set.Icc (0 : ℝ) run.elapsedTime.val) := by
    simpa only [potential] using
      (((h_temperature_continuous.log h_temperature_ne).const_mul
          (run.hotReservoirTemperature : ℝ)).sub h_temperature_continuous).const_mul
        (run.bodyHeatCapacity.val / run.inputPower.val)
  have h_potential_derivative :
      ∀ s ∈ Set.Ioo (0 : ℝ) run.elapsedTime.val,
        HasDerivAt potential (-1) s := by
    intro s hs
    have hs_closed : s ∈ Set.Icc (0 : ℝ) run.elapsedTime.val :=
      ⟨hs.1.le, hs.2.le⟩
    obtain ⟨h_cold_pos, h_hot_rate_pos, h_power_balance, h_carnot_ratio,
        h_temperature_derivative⟩ := h_carnotCooling s hs
    have h_ratio_cross :
        (run.coldHeatRate s).val * (run.hotReservoirTemperature : ℝ) =
          temperature s * (run.hotHeatRate s).val := by
      exact (div_eq_div_iff h_hot_rate_pos.ne' h_hot_pos.ne').mp h_carnot_ratio
    have h_hot_sub_temperature :
        (run.hotReservoirTemperature : ℝ) - temperature s ≠ 0 :=
      ne_of_gt (sub_pos.mpr (h_temperature_range s hs_closed).2)
    have h_cold_formula :
        (run.coldHeatRate s).val =
          run.inputPower.val * temperature s /
            ((run.hotReservoirTemperature : ℝ) - temperature s) := by
      apply (eq_div_iff h_hot_sub_temperature).2
      calc
        (run.coldHeatRate s).val *
              ((run.hotReservoirTemperature : ℝ) - temperature s) =
            (run.coldHeatRate s).val *
                (run.hotReservoirTemperature : ℝ) -
              temperature s * (run.coldHeatRate s).val := by ring
        _ = temperature s * (run.hotHeatRate s).val -
              temperature s * (run.coldHeatRate s).val := by
            rw [h_ratio_cross]
        _ = temperature s *
              ((run.hotHeatRate s).val - (run.coldHeatRate s).val) := by ring
        _ = temperature s * run.inputPower.val := by rw [h_power_balance]
        _ = run.inputPower.val * temperature s := by ring
    have h_temperature_ne_s : temperature s ≠ 0 :=
      ne_of_gt (h_temperature_range s hs_closed).1
    have h_raw_derivative :=
      ((((h_temperature_derivative.log h_temperature_ne_s).const_mul
          (run.hotReservoirTemperature : ℝ)).sub h_temperature_derivative).const_mul
        (run.bodyHeatCapacity.val / run.inputPower.val))
    have h_derivative_value :
        (run.bodyHeatCapacity.val / run.inputPower.val) *
              ((run.hotReservoirTemperature : ℝ) *
                  (-((run.coldHeatRate s).val / run.bodyHeatCapacity.val) /
                    temperature s) -
                (-((run.coldHeatRate s).val / run.bodyHeatCapacity.val))) =
            -1 := by
      rw [h_cold_formula]
      field_simp [h_heatCapacity_pos.ne', h_power_pos.ne',
        h_temperature_ne_s, h_hot_sub_temperature]
      ring
    simpa only [potential, temperature, Pi.sub_apply, h_derivative_value] using
      h_raw_derivative
  obtain ⟨s, hs, h_slope⟩ :=
    exists_hasDerivAt_eq_slope potential (fun _ => -1) h_elapsed_pos
      h_potential_continuous h_potential_derivative
  have h_potential_difference :
      potential run.elapsedTime.val - potential 0 = -run.elapsedTime.val := by
    rw [sub_zero] at h_slope
    field_simp [h_elapsed_pos.ne'] at h_slope
    linarith
  have h_temperature_zero_real :
      temperature 0 = (run.initialTemperature : ℝ) := by
    simp only [temperature, h_temperature_zero]
  have h_temperature_elapsed_real :
      temperature run.elapsedTime.val = (run.finalTemperature : ℝ) := by
    simp only [temperature, h_temperature_elapsed]
  dsimp only [potential] at h_potential_difference
  rw [h_temperature_zero_real, h_temperature_elapsed_real] at h_potential_difference
  rw [Real.log_div (ne_of_gt (h_final_pos.trans h_final_lt_initial))
    (ne_of_gt h_final_pos)]
  field_simp [h_power_pos.ne', h_hot_pos.ne'] at h_potential_difference ⊢
  nlinarith [h_potential_difference]

end

end IPhO2026Problems.IPhO2026_3_C_4
