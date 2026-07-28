/-
  Autoformalization of IPhO 2026, Theoretical Problem 3 (T3), Part C.5.

  Blueprint chapter: blueprint/src/chapters/IPhO2026Problems_problem_IPhO_2026_3_C_5.tex
  Source report:     reports/ipho_2026_k3/problem_IPhO_2026_3_C_5.source.json
  Official page:     T3_page-4.png (IPhO 2026 Theoretical Exam, page 14/14)

  Physical situation (parts C.4/C.5):
  A paramagnetic torus (potassium chromate) performs a sequence of infinitesimal
  Carnot refrigeration cycles 1 -> 2 -> 3 -> 4 -> 1 drawn in the H-versus-T
  plane (Figure 3b) in order to cool a body of constant heat capacity C_c.
  The hot reservoir stays at constant temperature T_h and the refrigerator
  draws constant input power P; the cold-reservoir temperature T_c tracks the
  cooled body's temperature, decreasing from T_0 at t = 0 to T < T_0.

  Current subquestion (C.5, 1.5 pts):
    Determine the overall coefficient of performance COP = Q_c / W of the
    refrigerator of question T3-C4, with all the cycles performed until time t
    (the time found in C.4).  Answer in terms of T_0, T_h and T.

  Recorded official answer:
    COP = [(T_h/(T_0 - T)) * ln(T_0/T) - 1]^{-1}.

  All theorem statements below are faithful contracts; proof bodies are `sorry`
  by design (autoformalize stage).
-/

import Mathlib

namespace IPhO2026.Problem3.C5

section Quantities

/-!
Physical quantities appearing in the statement.  They are deterministically
measurable real scalars (SI units): temperatures (K), heats (J), work (J),
time (s), heat capacity (J/K).  Abstract parameters rather than transparent
aliases are used so that the contracts cannot be closed by unfolding.
-/

/-- Cold end of the cooling process: body's final temperature `T < T_0` (K). -/
opaque tempFinal : ℝ

/-- Hot-reservoir temperature `T_h`, constant throughout (K). -/
opaque tempHot : ℝ

/-- Body's initial temperature `T_0` (K), equal to the cold-reservoir
    temperature at `t = 0`. -/
opaque tempInitial : ℝ

/-- Total heat `Q_c` absorbed from the cooled body over all cycles up to the
    time found in C.4 (J). -/
opaque totalHeatCold : ℝ

/-- Total work input `W` to the refrigerator over the same interval (J). -/
opaque totalWork : ℝ

/-- Time `t` found in part C.4 for the body to cool from `T_0` to `T` (s). -/
opaque elapsedTime : ℝ

/-- Constant heat capacity `C_c` of the cooled body (J/K). -/
opaque heatCapacityBody : ℝ

/-- Constant mechanical input power `P` supplied to the refrigerator (W). -/
opaque inputPower : ℝ

/-- Body mass of the paramagnetic working material (context parameter, kg). -/
opaque workingMass : ℝ

/-- Volume `V` of the paramagnetic torus (figure parameter, m³). -/
opaque torusVolume : ℝ

/-- Amount of working substance `n` (mol). -/
opaque amountOfSubstance : ℝ

/-- Material constant `K = 1.87e-6 K·m³/mol` of potassium chromate,
    entering the equation of state `T * M * V = n * K * H`. -/
opaque materialConstantK : ℝ

/-- The four field values `H₁, H₂, H₃, H₄` (A/m) labelling the corners of the
    Carnot cycle 1 → 2 → 3 → 4 → 1 of Figure 3b in the H-versus-T plane. -/
structure CycleFields where
  H1 : ℝ
  H2 : ℝ
  H3 : ℝ
  H4 : ℝ

/-- Positivity/zero-< assumptions used throughout C.4–C.5.  These record the
    physical regime of the problem: positive absolute temperatures with
    `T < T_0 < T_h`, a body of positive heat capacity, and a refrigerator
    driven at constant positive input power over a positive elapsed time. -/
structure RegimeAssumptions : Prop where
  tempFinal_pos    : 0 < tempFinal
  tempInitial_pos  : 0 < tempInitial
  tempHot_pos      : 0 < tempHot
  final_lt_initial : tempFinal < tempInitial
  initial_lt_hot   : tempInitial < tempHot
  heatCapacity_pos : 0 < heatCapacityBody
  inputPower_pos   : 0 < inputPower
  elapsedTime_pos  : 0 < elapsedTime

end Quantities

section GoverningLaws

/-!
Governing laws entering C.5.  The conclusion of C.5 does **not** appear here:
the equation `COP = [(T_h/(T_0 - T)) * ln(T_0/T) - 1]⁻¹` is only ever a
target below.  The previous-part results (C.4 elapsed time, and the
per-cycle relation `dQ_c/dQ_h = T_c/T_h` quoted by T3-C4) are encoded as
derived-bridge equations on the accumulated totals, not as bare definitions
of the answer.
-/

/-- Coefficient of performance of a refrigerator: the dimensionless ratio
    `Q_c / W`.  This is the *definition of the quantity* asked for in T3-C.5
    ("COP = Q_c/W"), not its value; the value is the theorem's target. -/
noncomputable def coefficientOfPerformance : ℝ :=
  totalHeatCold / totalWork

/-- Constant-power assumption (part C.4 hypothesis): the total work input over
    elapsed time `t` is `W = P * t`.  Carrier for the `W = P t` bridge. -/
def ConstantPowerWork (W P t : ℝ) : Prop :=
  W = P * t

/-- Constant-heat-capacity body: the heat the body releases while cooling from
    `T_0` to `T` is `Q_c = C_c * (T_0 - T)`.  Carrier for the calorimetric
    bridge `Q_c = C_c (T_0 - T)`. -/
def CooledBodyHeatBalance (Qc Cc T0 T : ℝ) : Prop :=
  Qc = Cc * (T0 - T)

/-- Accumulated Carnot/Carnot-quota relation (previous-part law, reused):
    in each infinitesimal cycle `dQ_c/dQ_h = T_c/T_h` with `T_h` constant, so
    the total heat dumped to the hot reservoir and the total heat extracted
    from the cooling body obey `Q_h = Q_c * T_h * ln(T_0/T) / (T_0 - T)`.

    This predicate *constrains* the totals via an equation linking them to the
    temperature data; it does not mention the COP formula of the target. -/
def AccumulatedCarnotHeatRelation (Qh Qc Th T0 T : ℝ) : Prop :=
  Qh = Qc * Th * Real.log (T0 / T) / (T0 - T)

/-- First law for the accumulated refrigerator operation (energy balance):
    the heat delivered to the hot reservoir equals the extracted heat plus the
    supplied work, `Q_h = Q_c + W`. -/
def RefrigeratorEnergyBalance (Qh Qc W : ℝ) : Prop :=
  Qh = Qc + W

/-- Part C.4 result (natural-language prerequisite, reused as licensed):
    the elapsed time to cool from `T_0` to `T` at constant power `P` is
    `t = (C_c * T_h / P) * (ln(T_0/T) - (T_0 - T)/T_h)`. -/
def C4ElapsedTimeLaw (t Cc Th P T0 T : ℝ) : Prop :=
  t = (Cc * Th / P) * (Real.log (T0 / T) - (T0 - T) / Th)

/-- Equation of state of the paramagnetic torus (context from part C):
    `T * M * V = n * K * H` relating temperature, magnetization `M`,
    volume `V`, amount `n`, material constant `K` and field `H`. -/
def ParamagneticEquationOfState (Tgas M V n K H : ℝ) : Prop :=
  Tgas * M * V = n * K * H

end GoverningLaws

section PhysicsContracts

/-- Data read out from the operating history and the C.4 analysis:
    the accumulated totals `Q_c`, `Q_h`, `W`, `t` satisfy the governing laws
    above under the regime assumptions. -/
structure OperatingHistory (Qh : ℝ) : Prop where
  work_law    : ConstantPowerWork totalWork inputPower elapsedTime
  body_heat   : CooledBodyHeatBalance totalHeatCold heatCapacityBody tempInitial tempFinal
  carnot_heat : AccumulatedCarnotHeatRelation Qh totalHeatCold tempHot tempInitial tempFinal
  energy      : RefrigeratorEnergyBalance Qh totalHeatCold totalWork
  c4_time     : C4ElapsedTimeLaw elapsedTime heatCapacityBody tempHot inputPower tempInitial tempFinal

/-- T3-C.5 — overall coefficient of performance up to the time found in C.4:

    `COP = Q_c/W = [(T_h/(T_0 - T)) * ln(T_0/T) - 1]⁻¹`.

    The right-hand side is the *target conclusion*; nothing in the hypotheses
    below is or implies this equation definitionally — the laws above only
    relate the totals `Q_c`, `Q_h`, `W`, `t` to the parameters.  The full
    bridge uses the C.4 elapsed time (so that the answer is a function of
    `T_0, T_h, T` alone).  The `1.5`-point marking is recorded in the
    blueprint chapter. -/
theorem overall_coefficient_of_performance
    (regime : RegimeAssumptions)
    (Qh : ℝ) (hist : OperatingHistory Qh) :
    coefficientOfPerformance
      = ((tempHot / (tempInitial - tempFinal))
          * Real.log (tempInitial / tempFinal) - 1)⁻¹ := by
  have hd_pos : 0 < tempInitial - tempFinal := sub_pos.mpr regime.final_lt_initial
  have hQc : totalHeatCold = heatCapacityBody * (tempInitial - tempFinal) := hist.body_heat
  have hQc_ne : totalHeatCold ≠ 0 := by
    rw [hQc]
    exact ne_of_gt (mul_pos regime.heatCapacity_pos hd_pos)
  have hsum : totalHeatCold * tempHot * Real.log (tempInitial / tempFinal)
        / (tempInitial - tempFinal) = totalHeatCold + totalWork :=
    hist.carnot_heat.symm.trans hist.energy
  have hW1 : totalWork = totalHeatCold * tempHot * Real.log (tempInitial / tempFinal)
        / (tempInitial - tempFinal) - totalHeatCold := by linarith
  have hW : totalWork = totalHeatCold * (tempHot * Real.log (tempInitial / tempFinal)
        / (tempInitial - tempFinal) - 1) := by
    rw [hW1]
    ring
  unfold coefficientOfPerformance
  rw [hW,
    show tempHot * Real.log (tempInitial / tempFinal) / (tempInitial - tempFinal) - 1
      = tempHot / (tempInitial - tempFinal) * Real.log (tempInitial / tempFinal) - 1 by ring,
    div_mul_eq_div_div, div_self hQc_ne, one_div]

/-- Intermediate target — direct route form of the same conclusion, obtained
    purely from the accumulated totals and the first law *without* invoking
    the explicit C.4 time:  with `Q_c = C_c (T_0 - T)`,
    `Q_h = Q_c T_h ln(T_0/T)/(T_0 - T)` and `W = Q_h - Q_c`,
    one gets `Q_c/W = [(T_h/(T_0 - T)) ln(T_0/T) - 1]⁻¹` directly.  This
    isolates the energy-balance bridge as an independent contract. -/
theorem coefficient_of_performance_via_energy_balance
    (regime : RegimeAssumptions)
    (Qh : ℝ)
    (body_heat   : CooledBodyHeatBalance totalHeatCold heatCapacityBody tempInitial tempFinal)
    (carnot_heat : AccumulatedCarnotHeatRelation Qh totalHeatCold tempHot tempInitial tempFinal)
    (energy      : RefrigeratorEnergyBalance Qh totalHeatCold totalWork) :
    coefficientOfPerformance
      = ((tempHot / (tempInitial - tempFinal))
          * Real.log (tempInitial / tempFinal) - 1)⁻¹ := by
  have hd_pos : 0 < tempInitial - tempFinal := sub_pos.mpr regime.final_lt_initial
  have hQc : totalHeatCold = heatCapacityBody * (tempInitial - tempFinal) := body_heat
  have hQc_ne : totalHeatCold ≠ 0 := by
    rw [hQc]
    exact ne_of_gt (mul_pos regime.heatCapacity_pos hd_pos)
  have hsum : totalHeatCold * tempHot * Real.log (tempInitial / tempFinal)
        / (tempInitial - tempFinal) = totalHeatCold + totalWork :=
    carnot_heat.symm.trans energy
  have hW1 : totalWork = totalHeatCold * tempHot * Real.log (tempInitial / tempFinal)
        / (tempInitial - tempFinal) - totalHeatCold := by linarith
  have hW : totalWork = totalHeatCold * (tempHot * Real.log (tempInitial / tempFinal)
        / (tempInitial - tempFinal) - 1) := by
    rw [hW1]
    ring
  unfold coefficientOfPerformance
  rw [hW,
    show tempHot * Real.log (tempInitial / tempFinal) / (tempInitial - tempFinal) - 1
      = tempHot / (tempInitial - tempFinal) * Real.log (tempInitial / tempFinal) - 1 by ring,
    div_mul_eq_div_div, div_self hQc_ne, one_div]

end PhysicsContracts

end IPhO2026.Problem3.C5
