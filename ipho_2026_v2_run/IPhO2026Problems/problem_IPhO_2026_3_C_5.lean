import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Physlib.Thermodynamics.Temperature.Basic
import Physlib.Units.WithDim.Energy

/-!
# IPhO 2026 Problem 3, part C.5

This file models the overall coefficient of performance of the paramagnetic
Carnot refrigerator.  Dimensionful quantities are evaluated in SI units only
when the scalar equations from the problem are stated.
-/

namespace IPhO2026_3_C_5

open Dimension

/-! ## Dimensionful quantities used by the problem -/

/-- The physical dimension of an energy. -/
def energyDimension : Dimension :=
  M𝓭 * L𝓭 * L𝓭 * T𝓭⁻¹ * T𝓭⁻¹

/-- A duration, represented by Physlib's unit-independent dimensionful API. -/
abbrev DimDuration : Type :=
  Dimensionful (WithDim T𝓭 ℝ)

/-- Power, with physical dimension energy per unit time. -/
abbrev DimPower : Type :=
  Dimensionful (WithDim (energyDimension * T𝓭⁻¹) ℝ)

/-- Heat capacity, with physical dimension energy per unit temperature. -/
abbrev DimHeatCapacity : Type :=
  Dimensionful (WithDim (energyDimension * Θ𝓭⁻¹) ℝ)

/-- Volume, with physical dimension length cubed. -/
abbrev DimVolume : Type :=
  Dimensionful (WithDim (L𝓭 * L𝓭 * L𝓭) ℝ)

/-- Magnetic field strength and magnetization, both measured in ampere/metre. -/
abbrev DimAmperePerMeter : Type :=
  Dimensionful (WithDim (C𝓭 * T𝓭⁻¹ * L𝓭⁻¹) ℝ)

/-- The scalar value of a dimensionful quantity in Physlib's SI unit choice. -/
noncomputable def siValue {d : Dimension}
    (q : Dimensionful (WithDim d ℝ)) : ℝ :=
  (q UnitChoices.SI).val

/-- The common absolute-temperature readout used throughout the problem. -/
noncomputable def temperatureValue (temperature : Temperature) : ℝ :=
  Temperature.toReal temperature

/-! ## Figure 3b and the paramagnetic torus -/

/-- The four labels appearing on the Carnot cycle in Figure 3b. -/
inductive CyclePoint
  | one
  | two
  | three
  | four
  deriving DecidableEq, Repr

/-- The directed cycle order shown in Figure 3b. -/
def figure3bCycleOrder : List CyclePoint :=
  [.one, .two, .three, .four, .one]

/-- The branch on which heat is absorbed from the cold reservoir. -/
def coldHeatBranch : CyclePoint × CyclePoint :=
  (.two, .three)

/-- The branch on which heat is delivered to the hot reservoir. -/
def hotHeatBranch : CyclePoint × CyclePoint :=
  (.four, .one)

/-- Material data for the paramagnetic torus.

Physlib has no amount-of-substance dimension.  Consequently `amountInMoles`
and the Curie constant are explicitly named SI scalar readouts rather than
being presented as dimensionless physical quantities.
-/
structure ParamagneticTorus where
  fixedVolume : DimVolume
  amountInMoles : ℝ
  curieConstantKelvinCubicMetersPerMole : ℝ

/-- The state data and heat magnitudes attached to Figure 3b. -/
structure Figure3bCarnotCycle where
  torus : ParamagneticTorus
  hotReservoirTemperature : Temperature
  coldReservoirTemperature : Temperature
  temperature : CyclePoint → Temperature
  magneticFieldStrength : CyclePoint → DimAmperePerMeter
  magnetization : CyclePoint → DimAmperePerMeter
  heatAbsorbedFromCold : DimEnergy
  heatDeliveredToHot : DimEnergy

/-- Data needed to apply the reusable isothermal heat relation from part B. -/
structure IsothermalHeatModel where
  vacuumPermeabilitySI : ℝ
  heatTransferredIntoTorus :
    CyclePoint → CyclePoint → DimEnergy

/-- The part-B isothermal heat law, with heat entering the torus taken positive. -/
structure IsothermalHeatRelation
    (cycle : Figure3bCarnotCycle) (model : IsothermalHeatModel) : Prop where
  vacuumPermeability_positive : 0 < model.vacuumPermeabilitySI
  equation :
    ∀ (initial final : CyclePoint),
      cycle.temperature initial = cycle.temperature final →
      siValue (model.heatTransferredIntoTorus initial final) =
        - (model.vacuumPermeabilitySI * cycle.torus.amountInMoles *
            cycle.torus.curieConstantKelvinCubicMetersPerMole /
            (2 * temperatureValue (cycle.temperature initial))) *
          (siValue (cycle.magneticFieldStrength final) ^ 2 -
            siValue (cycle.magneticFieldStrength initial) ^ 2)

/-- Governing laws and figure readouts for the directed Carnot cycle. -/
structure Figure3bCarnotLaws
    (cycle : Figure3bCarnotCycle) (model : IsothermalHeatModel) : Prop where
  state_one_is_hot :
    cycle.temperature .one = cycle.hotReservoirTemperature
  state_four_is_hot :
    cycle.temperature .four = cycle.hotReservoirTemperature
  state_two_is_cold :
    cycle.temperature .two = cycle.coldReservoirTemperature
  state_three_is_cold :
    cycle.temperature .three = cycle.coldReservoirTemperature
  positive_amount : 0 < cycle.torus.amountInMoles
  positive_curie_constant :
    0 < cycle.torus.curieConstantKelvinCubicMetersPerMole
  positive_volume : 0 < siValue cycle.torus.fixedVolume
  positive_hot_temperature :
    0 < temperatureValue cycle.hotReservoirTemperature
  positive_cold_temperature :
    0 < temperatureValue cycle.coldReservoirTemperature
  cold_below_hot :
    temperatureValue cycle.coldReservoirTemperature <
      temperatureValue cycle.hotReservoirTemperature
  equation_of_state :
    ∀ point : CyclePoint,
      temperatureValue (cycle.temperature point) *
          siValue (cycle.magnetization point) *
          siValue cycle.torus.fixedVolume =
        cycle.torus.amountInMoles *
          cycle.torus.curieConstantKelvinCubicMetersPerMole *
          siValue (cycle.magneticFieldStrength point)
  cold_heat_on_two_to_three :
    siValue cycle.heatAbsorbedFromCold =
      siValue (model.heatTransferredIntoTorus .two .three)
  hot_heat_on_four_to_one :
    siValue cycle.heatDeliveredToHot =
      -siValue (model.heatTransferredIntoTorus .four .one)
  cold_heat_is_magnitude : 0 ≤ siValue cycle.heatAbsorbedFromCold
  hot_heat_is_magnitude : 0 ≤ siValue cycle.heatDeliveredToHot

/-! ## Constant-power cooling run from C.4 and C.5 -/

/-- All dimensionful data accumulated over the cycles performed up to time `t`. -/
structure CoolingRun where
  finalCycle : Figure3bCarnotCycle
  bodyHeatCapacity : DimHeatCapacity
  inputPower : DimPower
  elapsedTime : DimDuration
  initialBodyTemperature : Temperature
  finalBodyTemperature : Temperature
  totalHeatAbsorbedFromCold : DimEnergy
  totalWorkInput : DimEnergy

/-- Governing constant-heat-capacity and constant-power relations for the run. -/
structure ConstantPowerCoolingLaws (run : CoolingRun) : Prop where
  positive_heat_capacity : 0 < siValue run.bodyHeatCapacity
  positive_input_power : 0 < siValue run.inputPower
  positive_elapsed_time : 0 < siValue run.elapsedTime
  positive_final_temperature :
    0 < temperatureValue run.finalBodyTemperature
  final_below_initial :
    temperatureValue run.finalBodyTemperature <
      temperatureValue run.initialBodyTemperature
  initial_below_hot :
    temperatureValue run.initialBodyTemperature <
      temperatureValue run.finalCycle.hotReservoirTemperature
  final_cycle_at_body_temperature :
    run.finalCycle.coldReservoirTemperature = run.finalBodyTemperature
  heat_removed_from_constant_heat_capacity :
    siValue run.totalHeatAbsorbedFromCold =
      siValue run.bodyHeatCapacity *
        (temperatureValue run.initialBodyTemperature -
          temperatureValue run.finalBodyTemperature)
  work_from_constant_power :
    siValue run.totalWorkInput =
      siValue run.inputPower * siValue run.elapsedTime

/-- The reusable elapsed-time conclusion of part C.4. -/
structure C4ElapsedTimeResult (run : CoolingRun) : Prop where
  elapsed_time :
    siValue run.elapsedTime =
      (siValue run.bodyHeatCapacity *
          temperatureValue run.finalCycle.hotReservoirTemperature /
          siValue run.inputPower) *
        (Real.log
            (temperatureValue run.initialBodyTemperature /
              temperatureValue run.finalBodyTemperature) -
          (temperatureValue run.initialBodyTemperature -
              temperatureValue run.finalBodyTemperature) /
            temperatureValue run.finalCycle.hotReservoirTemperature)

/-- The overall coefficient of performance, `Q_c / W`, for the whole run. -/
noncomputable def overallCoefficientOfPerformance (run : CoolingRun) : ℝ :=
  siValue run.totalHeatAbsorbedFromCold / siValue run.totalWorkInput

/-- Blueprint label: `thm:physics:IPhO_2026_3_C_5:target`.

The overall COP for every cycle performed while the body cools from `T₀` to
`T`, using the elapsed time obtained in C.4.
-/
theorem overall_coefficient_of_performance
    (run : CoolingRun)
    (isothermalModel : IsothermalHeatModel)
    (_isothermalLaw :
      IsothermalHeatRelation run.finalCycle isothermalModel)
    (_figureLaws : Figure3bCarnotLaws run.finalCycle isothermalModel)
    (coolingLaws : ConstantPowerCoolingLaws run)
    (c4Result : C4ElapsedTimeResult run) :
    overallCoefficientOfPerformance run =
      (temperatureValue run.finalCycle.hotReservoirTemperature /
          (temperatureValue run.initialBodyTemperature -
            temperatureValue run.finalBodyTemperature) *
          Real.log
            (temperatureValue run.initialBodyTemperature /
              temperatureValue run.finalBodyTemperature) -
        1)⁻¹ := by
  rcases coolingLaws with
    ⟨hC, hP, ht, hTf, hTfTi, hTiH, hFinal, hQ, hW⟩
  rcases c4Result with ⟨htime⟩
  unfold overallCoefficientOfPerformance
  rw [hQ, hW, htime]
  have hΔ :
      0 <
        temperatureValue run.initialBodyTemperature -
          temperatureValue run.finalBodyTemperature :=
    sub_pos.mpr hTfTi
  have hHot :
      0 < temperatureValue run.finalCycle.hotReservoirTemperature :=
    lt_trans hTf (lt_trans hTfTi hTiH)
  have hScale :
      0 <
        siValue run.bodyHeatCapacity *
            temperatureValue run.finalCycle.hotReservoirTemperature /
          siValue run.inputPower :=
    div_pos (mul_pos hC hHot) hP
  have hProduct :
      0 <
        (siValue run.bodyHeatCapacity *
              temperatureValue run.finalCycle.hotReservoirTemperature /
            siValue run.inputPower) *
          (Real.log
              (temperatureValue run.initialBodyTemperature /
                temperatureValue run.finalBodyTemperature) -
            (temperatureValue run.initialBodyTemperature -
                temperatureValue run.finalBodyTemperature) /
              temperatureValue run.finalCycle.hotReservoirTemperature) := by
    rw [← htime]
    exact ht
  have hBracket :
      0 <
        Real.log
            (temperatureValue run.initialBodyTemperature /
              temperatureValue run.finalBodyTemperature) -
          (temperatureValue run.initialBodyTemperature -
              temperatureValue run.finalBodyTemperature) /
            temperatureValue run.finalCycle.hotReservoirTemperature :=
    pos_of_mul_pos_right hProduct hScale.le
  have hFactor :
      0 <
        temperatureValue run.finalCycle.hotReservoirTemperature /
              (temperatureValue run.initialBodyTemperature -
                temperatureValue run.finalBodyTemperature) *
            Real.log
              (temperatureValue run.initialBodyTemperature /
                temperatureValue run.finalBodyTemperature) -
          1 := by
    rw [show
      temperatureValue run.finalCycle.hotReservoirTemperature /
              (temperatureValue run.initialBodyTemperature -
                temperatureValue run.finalBodyTemperature) *
            Real.log
              (temperatureValue run.initialBodyTemperature /
                temperatureValue run.finalBodyTemperature) -
          1 =
        (temperatureValue run.finalCycle.hotReservoirTemperature /
            (temperatureValue run.initialBodyTemperature -
              temperatureValue run.finalBodyTemperature)) *
          (Real.log
              (temperatureValue run.initialBodyTemperature /
                temperatureValue run.finalBodyTemperature) -
              (temperatureValue run.initialBodyTemperature -
                temperatureValue run.finalBodyTemperature) /
              temperatureValue run.finalCycle.hotReservoirTemperature) by
      field_simp [hΔ.ne', hHot.ne']]
    exact mul_pos (div_pos hHot hΔ) hBracket
  field_simp [hΔ.ne', hHot.ne', hC.ne', hP.ne', hBracket.ne',
    hFactor.ne']

end IPhO2026_3_C_5
