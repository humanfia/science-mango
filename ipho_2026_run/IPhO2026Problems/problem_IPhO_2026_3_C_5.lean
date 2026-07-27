import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Physlib.Thermodynamics.Temperature.Basic

namespace IPhO2026Problems.IPhO2026_3_C_5

/-- The four labelled states of the magnetic Carnot cycle in Figure 3b. -/
inductive CycleState
  | one
  | two
  | three
  | four
  deriving DecidableEq, Fintype

/-- The directed legs of the cycle `1 → 2 → 3 → 4 → 1`. -/
inductive CycleLeg
  | oneToTwo
  | twoToThree
  | threeToFour
  | fourToOne
  deriving DecidableEq, Fintype

/-- Initial state of each directed cycle leg. -/
def CycleLeg.startState : CycleLeg → CycleState
  | .oneToTwo => .one
  | .twoToThree => .two
  | .threeToFour => .three
  | .fourToOne => .four

/-- Final state of each directed cycle leg. -/
def CycleLeg.endState : CycleLeg → CycleState
  | .oneToTwo => .two
  | .twoToThree => .three
  | .threeToFour => .four
  | .fourToOne => .one

/--
Scalar SI readouts for one instantaneous paramagnetic-torus Carnot cycle.

Temperatures use PhysLean's absolute `Temperature` type. The remaining fields
are explicitly measured components in the units stated by their names, rather
than aliases for the underlying physical quantities. Heat entering the torus
is positive; `coldHeatMagnitudeJoule` and `hotHeatMagnitudeJoule` are
nonnegative magnitudes.
-/
structure MagneticCarnotCycle where
  stateTemperature : CycleState → Temperature
  magneticFieldAmperePerMeter : CycleState → ℝ
  magnetizationAmperePerMeter : CycleState → ℝ
  heatIntoTorusJoule : CycleLeg → ℝ
  coldHeatMagnitudeJoule : ℝ
  hotHeatMagnitudeJoule : ℝ
  hotReservoirTemperature : Temperature
  coldReservoirTemperature : Temperature
  torusVolumeCubicMeter : ℝ
  amountMole : ℝ
  curieConstantKelvinCubicMeterPerMole : ℝ
  vacuumPermeabilityHenryPerMeter : ℝ

/--
The temperature labels and heat-transfer legs read from Figure 3b.

States 1 and 4 are on the hot isotherm, states 2 and 3 are on the cold
isotherm, heat is absorbed from the cold reservoir on `2 → 3`, and heat is
delivered to the hot reservoir on `4 → 1`. The other two legs are adiabatic.
-/
def FollowsFigureThreeB (cycle : MagneticCarnotCycle) : Prop :=
  cycle.stateTemperature .one = cycle.hotReservoirTemperature ∧
  cycle.stateTemperature .four = cycle.hotReservoirTemperature ∧
  cycle.stateTemperature .two = cycle.coldReservoirTemperature ∧
  cycle.stateTemperature .three = cycle.coldReservoirTemperature ∧
  cycle.heatIntoTorusJoule .oneToTwo = 0 ∧
  cycle.heatIntoTorusJoule .twoToThree = cycle.coldHeatMagnitudeJoule ∧
  cycle.heatIntoTorusJoule .threeToFour = 0 ∧
  cycle.heatIntoTorusJoule .fourToOne = -cycle.hotHeatMagnitudeJoule ∧
  0 ≤ cycle.coldHeatMagnitudeJoule ∧
  0 ≤ cycle.hotHeatMagnitudeJoule

/-- The paramagnetic equation of state `T M V = n K H` at all four states. -/
def SatisfiesParamagneticEquationOfState (cycle : MagneticCarnotCycle) : Prop :=
  ∀ state,
    (cycle.stateTemperature state).val * cycle.magnetizationAmperePerMeter state *
        cycle.torusVolumeCubicMeter =
      cycle.amountMole * cycle.curieConstantKelvinCubicMeterPerMole *
        cycle.magneticFieldAmperePerMeter state

/--
The isothermal heat relation from part B.1 on the cold and hot isotherms.
Its sign convention is heat entering the paramagnetic torus positive.
-/
def SatisfiesIsothermalHeatRelation (cycle : MagneticCarnotCycle) : Prop :=
  cycle.heatIntoTorusJoule .twoToThree =
      -(cycle.vacuumPermeabilityHenryPerMeter * cycle.amountMole *
          cycle.curieConstantKelvinCubicMeterPerMole /
          (2 * cycle.coldReservoirTemperature.val)) *
        (cycle.magneticFieldAmperePerMeter .three ^ 2 -
          cycle.magneticFieldAmperePerMeter .two ^ 2) ∧
    cycle.heatIntoTorusJoule .fourToOne =
      -(cycle.vacuumPermeabilityHenryPerMeter * cycle.amountMole *
          cycle.curieConstantKelvinCubicMeterPerMole /
          (2 * cycle.hotReservoirTemperature.val)) *
        (cycle.magneticFieldAmperePerMeter .one ^ 2 -
          cycle.magneticFieldAmperePerMeter .four ^ 2)

/-- Positivity conditions for the physical torus and its two reservoirs. -/
def HasPhysicalCycleParameters (cycle : MagneticCarnotCycle) : Prop :=
  0 < cycle.torusVolumeCubicMeter ∧
  0 < cycle.amountMole ∧
  0 < cycle.curieConstantKelvinCubicMeterPerMole ∧
  0 < cycle.vacuumPermeabilityHenryPerMeter ∧
  0 < cycle.hotReservoirTemperature.val ∧
  0 < cycle.coldReservoirTemperature.val

/--
Measured scalar data for all refrigerator cycles performed while a
constant-heat-capacity body cools from `initialTemperature` to
`finalTemperature`.
-/
structure CoolingRun where
  initialTemperature : Temperature
  finalTemperature : Temperature
  hotReservoirTemperature : Temperature
  cooledBodyHeatCapacityJoulePerKelvin : ℝ
  inputPowerWatt : ℝ
  elapsedTimeSecond : ℝ
  totalColdHeatJoule : ℝ
  totalInputWorkJoule : ℝ

/-- Overall refrigerator coefficient of performance, `COP = Q_c / W`. -/
noncomputable def coefficientOfPerformance (run : CoolingRun) : ℝ :=
  run.totalColdHeatJoule / run.totalInputWorkJoule

/--
The overall coefficient of performance of all cycles up to the elapsed time
computed in part C.4.

The C.4 elapsed-time relation is an explicit previous-part hypothesis. The
other two run relations are the constant-heat-capacity energy balance
`Q_c = C_c (T₀ - T)` and the constant-input-power work balance `W = P t`.
-/
theorem overallCoefficientOfPerformance
    (cycle : MagneticCarnotCycle)
    (run : CoolingRun)
    (hFigure : FollowsFigureThreeB cycle)
    (hEquationOfState : SatisfiesParamagneticEquationOfState cycle)
    (hIsothermalHeat : SatisfiesIsothermalHeatRelation cycle)
    (hCyclePhysical : HasPhysicalCycleParameters cycle)
    (hHotReservoir :
      cycle.hotReservoirTemperature = run.hotReservoirTemperature)
    (hFinalColdReservoir :
      cycle.coldReservoirTemperature = run.finalTemperature)
    (hInitialTemperaturePositive : 0 < run.initialTemperature.val)
    (hFinalTemperaturePositive : 0 < run.finalTemperature.val)
    (hCooling : run.finalTemperature.val < run.initialTemperature.val)
    (hHeatCapacityPositive : 0 < run.cooledBodyHeatCapacityJoulePerKelvin)
    (hPowerPositive : 0 < run.inputPowerWatt)
    (hElapsedTimeFromC4 :
      run.elapsedTimeSecond =
        (run.cooledBodyHeatCapacityJoulePerKelvin *
            run.hotReservoirTemperature.val / run.inputPowerWatt) *
          (Real.log
              (run.initialTemperature.val / run.finalTemperature.val) -
            (run.initialTemperature.val - run.finalTemperature.val) /
              run.hotReservoirTemperature.val))
    (hTotalColdHeat :
      run.totalColdHeatJoule =
        run.cooledBodyHeatCapacityJoulePerKelvin *
          (run.initialTemperature.val - run.finalTemperature.val))
    (hTotalInputWork :
      run.totalInputWorkJoule = run.inputPowerWatt * run.elapsedTimeSecond) :
    coefficientOfPerformance run =
      (run.hotReservoirTemperature.val /
            (run.initialTemperature.val - run.finalTemperature.val) *
          Real.log (run.initialTemperature.val / run.finalTemperature.val) -
        1)⁻¹ := by
  have hHotNN : 0 < run.hotReservoirTemperature.val := by
    rw [← hHotReservoir]
    exact hCyclePhysical.2.2.2.2.1
  have hHotReal : 0 < (run.hotReservoirTemperature.val : ℝ) := by
    exact_mod_cast hHotNN
  have hCoolingReal : (run.finalTemperature.val : ℝ) <
      (run.initialTemperature.val : ℝ) := by
    exact_mod_cast hCooling
  rw [coefficientOfPerformance, hTotalColdHeat, hTotalInputWork,
    hElapsedTimeFromC4]
  have hC : run.cooledBodyHeatCapacityJoulePerKelvin ≠ 0 :=
    ne_of_gt hHeatCapacityPositive
  have hP : run.inputPowerWatt ≠ 0 := ne_of_gt hPowerPositive
  have hHot : (run.hotReservoirTemperature.val : ℝ) ≠ 0 := ne_of_gt hHotReal
  have hDelta : (run.initialTemperature.val : ℝ) -
      (run.finalTemperature.val : ℝ) ≠ 0 :=
    sub_ne_zero.mpr (ne_of_gt hCoolingReal)
  rw [show run.inputPowerWatt *
          (run.cooledBodyHeatCapacityJoulePerKelvin *
              (run.hotReservoirTemperature.val : ℝ) / run.inputPowerWatt *
            (Real.log ((run.initialTemperature.val : ℝ) /
                (run.finalTemperature.val : ℝ)) -
              ((run.initialTemperature.val : ℝ) -
                  (run.finalTemperature.val : ℝ)) /
                (run.hotReservoirTemperature.val : ℝ))) =
        run.cooledBodyHeatCapacityJoulePerKelvin *
          ((run.hotReservoirTemperature.val : ℝ) *
              Real.log ((run.initialTemperature.val : ℝ) /
                (run.finalTemperature.val : ℝ)) -
            ((run.initialTemperature.val : ℝ) -
              (run.finalTemperature.val : ℝ))) by
      field_simp [hP, hHot]]
  rw [mul_div_mul_left _ _ hC]
  rw [show (run.hotReservoirTemperature.val : ℝ) /
            ((run.initialTemperature.val : ℝ) -
              (run.finalTemperature.val : ℝ)) *
          Real.log ((run.initialTemperature.val : ℝ) /
            (run.finalTemperature.val : ℝ)) - 1 =
        ((run.hotReservoirTemperature.val : ℝ) *
              Real.log ((run.initialTemperature.val : ℝ) /
                (run.finalTemperature.val : ℝ)) -
            ((run.initialTemperature.val : ℝ) -
              (run.finalTemperature.val : ℝ))) /
          ((run.initialTemperature.val : ℝ) -
            (run.finalTemperature.val : ℝ)) by
      field_simp [hDelta]]
  rw [inv_div]

end IPhO2026Problems.IPhO2026_3_C_5
