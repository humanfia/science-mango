import Mathlib

/-!
# IPhO 2026 · Theory problem T3-C5 — "Carnot refrigerator of the Pm-T":
the overall coefficient of performance over the whole cooling process

Autoformalization of IPhO 2026 T3-C5 (source:
`reports/ipho_2026/problem_ipho_2026_t3_c5.source.json`; problem page
`ipho_2026_source/image/T3_page-4.png` — the T3-C4 and T3-C5 statements,
inspected — with the cycle diagram Fig. 3b on `T3_page-3.png` and the T3-B
model table on `T3_page-2.png`).

## Subquestion T3-C5 (page 14, 1.5 pts)

"The efficiency of a refrigerator is quantified by its *coefficient of
performance* `COP = Q_c/W`.  Determine the overall COP of the refrigerator of
question T3-C4 with all the cycles performed until time `t`.  Write your
answer in terms of `T_0` and `T_h` and `T`."

## The T3-C4 setup it refers to (page 14, inspected)

"In order to continuously lower the temperature of a body with constant heat
capacity `C_c`, Carnot cycles are allowed to occur over time in such a way
that the power `P` transferred to the refrigerator remains constant.  It is
then assumed that the temperature `T_h` of the hot reservoir remains constant
and that in each operating cycle the temperature `T_c` of the cooled body
decreases by `dT_c`, satisfying the relation `dQ_c/dQ_h = T_c/T_h`.  If at
`t = 0` we have `T_c = T_0`, determine the time `t` that the Carnot
refrigerator must operate for the cooled body to reach a temperature
`T < T_0`.  Express your answer in terms of `C_c`, `T_h`, `P`, `T_0` and `T`."

## Physical model

The Pm-T keeps executing the Carnot refrigeration cycle `1 → 2 → 3 → 4 → 1`
of Fig. 3b, but now *quasi-statically and continuously*: each cycle is
infinitesimal, the cold reservoir is the cooled body itself at its current
temperature `T_c`, and `T_c` drifts down from `T_0` (at `t = 0`) to the final
`T < T_0` (at time `t`).  Per infinitesimal cycle at body temperature `T_c`:

* constant heat capacity of the cooled body: the heat extracted from the body
  when its temperature changes by `dT_c` is `dQ_c = −C_c·dT_c`
  (`ConstantHeatCapacityHeatExtracted`);
* the stipulated per-cycle Carnot relation `dQ_c/dQ_h = T_c/T_h`, the
  differential form of the shared Clausius equality
  `CarnotReservoirHeatRelation` (`carnot_differential_ratio`);
* energy conservation for the refrigerator, `dQ_h = dQ_c + dW`
  (`RefrigeratorFirstLaw`).

Together these give the per-cycle work
`dW = C_c·(T_h − T_c)/T_c·(−dT_c)` (`differential_work_per_cycle`), positive
on the cooling branch (`differential_work_pos`).  The total work input over
all cycles performed while the body cools from `T_0` to `T` is the continuum
accumulation of the per-cycle works along the cooling path
(`TotalWorkOfQuasiStaticCycles`),
`W_tot = ∫_{T_c = T}^{T_0} C_c·(T_h − T_c)/T_c dT_c`, and the constant-power
stipulation ties it to the elapsed time, `W_tot = P·t`
(`ConstantPowerWork`).

## Previous-part dependencies (policy: derive_inline_from_problem_only_material)

* **T3-C4** (the elapsed time): derived inline as `elapsed_time_c4`,
  `t = (C_c/P)·(T_h·ln(T_0/T) − (T_0 − T))`, from the constant-power law and
  the accumulated work (`total_work_eval`, resting on the FTC evaluation
  `work_integral_eq`).  No sibling file is imported.
* **T3-C shared context**: the Clausius equality `CarnotReservoirHeatRelation`
  (`Q_h/T_h = Q_c/T_c`, verbatim-compatible with `IPhO2026.T3C2`/`T3C3`) is
  reused here at the per-cycle level — it *is* the C4-stipulated relation
  `dQ_c/dQ_h = T_c/T_h`.  The into-system heat sign convention
  `HeatFlowsIntoSystem` is also shared.  The equation of state
  `T·M·V = n·K·H` and the T3-B1 isothermal heat relation underlie the
  per-cycle Carnot relation but cancel out of the C4/C5 energy bookkeeping
  (cf. the volume cancellation in `IPhO2026.T3C3.heat_cold_leg_magnetization_form`),
  so they are not re-declared here.

## Governing laws (assumption side)

1. `ConstantHeatCapacityHeatExtracted`, 2. `CarnotReservoirHeatRelation`
   (per-cycle), 3. `RefrigeratorFirstLaw` — the three stipulated per-cycle
   laws above;
4. `ConstantPowerWork` — cumulative work at constant input power, `W = P·t`;
5. `ConstantHeatCapacityCooling` — integrated calorimetry at constant heat
   capacity: the total heat extracted from the body while it cools from `T_0`
   to `T` is `Q_c_tot = C_c·(T_0 − T)`;
6. `TotalWorkOfQuasiStaticCycles` — additivity of the work over the
   infinitesimal cycles in the continuum (quasi-static) limit;
7. physical ranges and branch readouts: `C_c, P, T_h, T_0, T > 0`,
   `T < T_0` (cooling), `T_0 ≤ T_h` (the hot reservoir is at least as warm as
   the body's initial temperature — consistent with the T3-C3 data,
   `T_h ≈ 1.424 K > T_0 = 1.00 K`); the initial condition `T_c = T_0` at
   `t = 0` is encoded in the integration limits.

## Derivation (answer-blind, from the laws above only)

* `work_integral_eq` (fundamental theorem of calculus,
  `integral_one_div_of_pos`):
  `∫_{T}^{T_0} C_c·(T_h−T_c)/T_c dT_c = C_c·(T_h·ln(T_0/T) − (T_0 − T))`;
* `elapsed_time_c4` (the T3-C4 result, inline): from `W_tot = P·t`,
  `t = (C_c/P)·(T_h·ln(T_0/T) − (T_0 − T))` — an expression in `C_c`, `T_h`,
  `P`, `T_0`, `T`, as T3-C4 requests;
* `overall_cop` (the T3-C5 target): with `Q_c_tot = C_c·(T_0 − T)` and
  `W_tot = C_c·(T_h·ln(T_0/T) − (T_0 − T))` the factor `C_c` cancels,

      COP = Q_c_tot/W_tot = (T_0 − T)/(T_h·ln(T_0/T) − (T_0 − T)),

  an expression in `T_0`, `T_h`, `T` only, as T3-C5 requests.  (Equivalently,
  on the C4 route: `COP = C_c·(T_0 − T)/(P·t)` with `t` from
  `elapsed_time_c4`, in which `C_c` and `P` cancel.)

## Current target (conclusion side only)

`overall_cop` (symbolic closed form; blueprint
`thm:physics:ipho_2026_t3_c5:target`) and its packaged form
`overall_cop_eq_expr` with the raw requested combination `overallCOPExpr`.
No hypothesis, premise structure or local definition mentions the value of
the COP.  `coefficientOfPerformance Q_c W = Q_c/W` is the *problem-given*
definition of the coefficient of performance, not the answer.

*Branch/orientation record*: on the cooling branch `T < T_0` with
`T_0 ≤ T_h`, the extracted heat is positive (`overall_heat_extracted_pos`),
the total work input is positive (`total_work_pos`, via
`work_denominator_pos`: `T_h·ln(T_0/T) > T_0 − T`, from
`Real.self_sub_one_lt_mul_log` at `T_0/T > 1`), and the overall COP is
positive (`overall_cop_pos`).

## Units

All quantities are real numbers carrying SI units, recorded per declaration:
`T_h, T_c, T_0, T` in K; `C_c` in J/K; `P` in W = J/s; `t` in s; `dT_c` in K;
`dQ_c, dQ_h, dW, Q_c_tot, W_tot` in J; the COP is dimensionless.
Consistency: `C_c·(T_h − T_c)/T_c·dT_c` is (J/K)·K = J ✓;
`C_c·T_h·ln(T_0/T)` is (J/K)·K = J ✓; `C_c/P·[…]` is (J/K)/(J/s)·K = s ✓;
`(T_0 − T)/(T_h·ln(T_0/T) − (T_0 − T))` is K/K ✓ dimensionless.

## Uncertainty

The source reports no `±` uncertainties and T3-C4/T3-C5 carry no numerical
data (the answer is symbolic), so uncertainty propagation and rounding are
*not applicable*; no rounding rule is attached.

## Grounding (LeanExplore, packages Mathlib + Physlib)

LeanExplore finds no refrigerator/COP/Carnot-cycle API (near misses: Physlib's
`CanonicalEnsemble.heatCapacity` and the ideal-gas adiabatic relations
`adiabatic_relation_UaUbVaVb`, `adiabatic_relation_log` — statistical-ensemble
and ideal-gas machinery, not this problem's scalar state-function model), so
the laws are kept as faithful local governing predicates, verbatim-compatible
with the sibling files where shared.  The continuum evaluation is grounded in
Mathlib's interval integrals: `integral_one_div_of_pos`
(`∫ x in a..b, 1/x = Real.log (b/a)`), `intervalIntegral.integral_congr`,
`intervalIntegral.integral_sub`, `intervalIntegral.integral_const_mul`,
`intervalIntegral.integral_const`, `intervalIntegral.intervalIntegrable_inv`,
`intervalIntegral.intervalIntegrable_const`, `IntervalIntegrable.const_mul`;
the logarithm bounds in `Real.self_sub_one_lt_mul_log` and `Real.log_pos`.
-/

namespace IPhO2026.T3C5

/-! ## Governing laws I — shared T3-C cycle laws (verbatim-compatible) -/

/-- Sign convention for heat (shared context of T3): a signed heat value `Q`
represents energy flowing *into* the paramagnetic torus exactly when it is
positive.  The `Q_h`, `Q_c` of T3-C are *magnitudes* of the heats exchanged
with the reservoirs; in T3-C4/C5 the cooled body plays the role of the cold
reservoir, so the per-cycle `dQ_c` and the accumulated `Q_c_tot` are
non-negative magnitudes.  Units: J. -/
def HeatFlowsIntoSystem (Q : ℝ) : Prop := 0 < Q

/-- **Carnot (Clausius) heat relation** (governing law carried by the name of
the cycle): for a reversible cycle whose only heat exchanges are with the hot
reservoir at `T_h` and the cold reservoir at `T_c`, the heat magnitudes
satisfy `Q_h/T_h = Q_c/T_c`.  In T3-C4/C5 it is applied per infinitesimal
cycle, `dQ_h/T_h = dQ_c/T_c`, which is exactly the stipulated relation
`dQ_c/dQ_h = T_c/T_h` (`carnot_differential_ratio`).  Units: J/K on both
sides. -/
def CarnotReservoirHeatRelation (Q_h T_h Q_c T_c : ℝ) : Prop :=
  Q_h / T_h = Q_c / T_c

/-! ## Governing laws II — the continuous cooling process of T3-C4/T3-C5 -/

/-- **Constant-heat-capacity heat extraction, differential form** (T3-C4
stipulation: the cooled body has *constant heat capacity* `C_c`): when the
body's temperature changes by `dT_c`, the heat extracted from the body (the
magnitude absorbed from the cold reservoir by one infinitesimal cycle) is
`dQ_c = −C_c·dT_c` — positive on the cooling branch `dT_c < 0`.  This is the
differential form of `đQ = C_c·dT` at constant `C_c`.  Units: (J/K)·K = J. -/
def ConstantHeatCapacityHeatExtracted (dQ_c C_c dT_c : ℝ) : Prop :=
  dQ_c = -C_c * dT_c

/-- **First law for one refrigerator cycle** (energy conservation, in
magnitudes): the heat `Q_h` delivered to the hot reservoir equals the heat
`Q_c` absorbed from the cold reservoir plus the work `W` supplied to the
refrigerator, `Q_h = Q_c + W`.  Applied per infinitesimal cycle as
`dQ_h = dQ_c + dW`.  Units: J. -/
def RefrigeratorFirstLaw (W Q_c Q_h : ℝ) : Prop := Q_h = Q_c + W

/-- **Constant-power work accumulation** (T3-C4 stipulation: "the power `P`
transferred to the refrigerator remains constant"): the cumulative work input
over the elapsed time `t` is `W = P·t`.  Units: (J/s)·s = J. -/
def ConstantPowerWork (W P t : ℝ) : Prop := W = P * t

/-- **Constant-heat-capacity calorimetry, integrated form**: the total heat
extracted from a body of constant heat capacity `C_c` while it cools from
`T_i` to `T_f` is `Q_removed = C_c·(T_i − T_f)` — the exact integral of
`ConstantHeatCapacityHeatExtracted` over the cooling path.  Units:
(J/K)·K = J. -/
def ConstantHeatCapacityCooling (Q_removed C_c T_i T_f : ℝ) : Prop :=
  Q_removed = C_c * (T_i - T_f)

/-- **Total work of the quasi-static sequence of cycles** (continuum
accumulation law): the total work input over all infinitesimal Carnot cycles
performed while the body cools from `T_0` down to `T` is the sum — in the
quasi-static limit, the interval integral — of the per-cycle works
`dW = C_c·(T_h − T_c)/T_c·(−dT_c)` (see `differential_work_per_cycle`) along
the cooling path, with `T_c` running from `T_0` to `T`:

    `W_tot = ∫_{T_c = T}^{T_0} C_c·(T_h − T_c)/T_c dT_c`.

The initial condition `T_c = T_0` at `t = 0` and the final condition
`T_c = T` at time `t` are encoded in the integration limits.  Units:
(J/K)·K integrated over K gives J ✓. -/
def TotalWorkOfQuasiStaticCycles (W C_c T_h T_0 T : ℝ) : Prop :=
  W = ∫ T_c in T..T_0, C_c * (T_h - T_c) / T_c

/-- **Coefficient of performance of a refrigerator** (the problem-given
definition in T3-C5): `COP = Q_c/W`, the ratio of the heat `Q_c` absorbed
from the cold reservoir (the cooled body) to the work `W` supplied to the
refrigerator.  Dimensionless.  This records only the *definition* of the COP;
what its overall value equals is the content of `overall_cop`. -/
noncomputable def coefficientOfPerformance (Q_c W : ℝ) : ℝ := Q_c / W

/-! ## Bridge lemmas I — the per-cycle (differential) laws -/

/-- **The C4-stipulated ratio form of the per-cycle Carnot relation**
(bridge 1): the Clausius equality `dQ_h/T_h = dQ_c/T_c`
(`CarnotReservoirHeatRelation`, shared T3-C law applied to one infinitesimal
cycle) is, on the operating branch where `T_h`, `T_c` and `dQ_h` are
positive, exactly the relation stipulated in the T3-C4 statement,
`dQ_c/dQ_h = T_c/T_h`.
Proof route: unfold the predicate; `field_simp` with the nonvanishing of
`T_h`, `T_c`, `dQ_h`; `linear_combination`. -/
theorem carnot_differential_ratio {dQ_h T_h dQ_c T_c : ℝ}
    (hTh : 0 < T_h) (hTc : 0 < T_c) (hdQh : 0 < dQ_h)
    (hC : CarnotReservoirHeatRelation dQ_h T_h dQ_c T_c) :
    dQ_c / dQ_h = T_c / T_h := by
  unfold CarnotReservoirHeatRelation at hC
  have hTh' := hTh.ne'
  have hTc' := hTc.ne'
  have hdQh' := hdQh.ne'
  field_simp at *
  linear_combination -hC

/-- **Per-cycle work input** (bridge 2, assembly of the three stipulated
per-cycle laws): at body temperature `T_c`, an infinitesimal cycle that
changes the body temperature by `dT_c` requires the work input
`dW = C_c·(T_h − T_c)/T_c·(−dT_c)`.
Derivation: `dQ_h = dQ_c·T_h/T_c` from `hC`; the first law `hfirst` gives
`dW = dQ_h − dQ_c = dQ_c·(T_h − T_c)/T_c`; the calorimetry law `hheat`
substitutes `dQ_c = −C_c·dT_c`.  Units: J.
Proof route: unfold the three predicates; `field_simp`; `linear_combination`. -/
theorem differential_work_per_cycle {C_c dT_c dQ_c dQ_h dW T_c T_h : ℝ}
    (hTc : 0 < T_c) (hTh : 0 < T_h)
    (hheat : ConstantHeatCapacityHeatExtracted dQ_c C_c dT_c)
    (hC : CarnotReservoirHeatRelation dQ_h T_h dQ_c T_c)
    (hfirst : RefrigeratorFirstLaw dW dQ_c dQ_h) :
    dW = C_c * (T_h - T_c) / T_c * (-dT_c) := by
  unfold ConstantHeatCapacityHeatExtracted at hheat
  unfold CarnotReservoirHeatRelation at hC
  unfold RefrigeratorFirstLaw at hfirst
  have hTc' := hTc.ne'
  have hTh' := hTh.ne'
  field_simp at *
  linear_combination -T_c * hfirst + (T_h - T_c) * hheat + hC

/-- **Per-cycle work is positive on the cooling branch** (bridge 3, branch
record): with `C_c > 0`, `0 < T_c < T_h` (the refrigerator's hot reservoir is
warmer than the cooled body) and `dT_c < 0` (the body cools), the per-cycle
work input `C_c·(T_h − T_c)/T_c·(−dT_c)` is positive. -/
theorem differential_work_pos {C_c dT_c T_c T_h : ℝ}
    (hCc : 0 < C_c) (hTc : 0 < T_c) (hTcTh : T_c < T_h) (hdT : dT_c < 0) :
    0 < C_c * (T_h - T_c) / T_c * (-dT_c) := by
  have h1 : 0 < T_h - T_c := sub_pos.mpr hTcTh
  have h2 : 0 < -dT_c := neg_pos.mpr hdT
  positivity

/-! ## Bridge lemmas II — continuum accumulation and its evaluation -/

/-- **Evaluation of the accumulated-work integral** (bridge 4, the
fundamental theorem of calculus): for `0 < T ≤ T_0`,

    `∫_{T_c = T}^{T_0} C_c·(T_h − T_c)/T_c dT_c
      = C_c·(T_h·ln(T_0/T) − (T_0 − T))`.

The integrand is regular on the integration interval (`T > 0`), where
`C_c·(T_h − T_c)/T_c = C_c·T_h·(1/T_c) − C_c`; the `1/T_c` part integrates to
`ln(T_0/T)` by `integral_one_div_of_pos` and the constant part to
`C_c·(T_0 − T)`.  Units: J. -/
theorem work_integral_eq {C_c T_h T_0 T : ℝ}
    (hT : 0 < T) (hT0 : 0 < T_0) (hTT0 : T ≤ T_0) :
    (∫ T_c in T..T_0, C_c * (T_h - T_c) / T_c) =
      C_c * (T_h * Real.log (T_0 / T) - (T_0 - T)) := by
  have hne : ∀ T_c ∈ Set.uIcc T T_0, T_c ≠ 0 := by
    intro T_c hTc
    rw [Set.uIcc_of_le hTT0] at hTc
    exact ne_of_gt (lt_of_lt_of_le hT hTc.1)
  have hInt1 : IntervalIntegrable (fun T_c : ℝ => 1 / T_c)
      MeasureTheory.MeasureSpace.volume T T_0 := by
    simpa [one_div] using
      intervalIntegral.intervalIntegrable_inv (μ := MeasureTheory.MeasureSpace.volume)
        (f := fun x : ℝ => x) (a := T) (b := T_0) hne continuousOn_id
  have hrewrite : (∫ T_c in T..T_0, C_c * (T_h - T_c) / T_c)
      = ∫ T_c in T..T_0, (C_c * T_h * (1 / T_c) - C_c) := by
    apply intervalIntegral.integral_congr
    intro T_c hTc
    have h := hne T_c hTc
    field_simp
  rw [hrewrite,
    intervalIntegral.integral_sub (hInt1.const_mul _) intervalIntegral.intervalIntegrable_const,
    intervalIntegral.integral_const_mul, integral_one_div_of_pos hT hT0,
    intervalIntegral.integral_const, smul_eq_mul]
  ring

/-- **Total work input in closed form** (bridge 5): the accumulated work of
`TotalWorkOfQuasiStaticCycles` evaluates, by `work_integral_eq`, to
`W_tot = C_c·(T_h·ln(T_0/T) − (T_0 − T))`.  Units: J. -/
theorem total_work_eval {C_c T_h T_0 T W_tot : ℝ}
    (hT : 0 < T) (hT0 : 0 < T_0) (hTT0 : T ≤ T_0)
    (hW : TotalWorkOfQuasiStaticCycles W_tot C_c T_h T_0 T) :
    W_tot = C_c * (T_h * Real.log (T_0 / T) - (T_0 - T)) := by
  unfold TotalWorkOfQuasiStaticCycles at hW
  rw [hW]
  exact work_integral_eq hT hT0 hTT0

/-- **T3-C4 result, derived inline** (previous-part dependency, policy
`derive_inline_from_problem_only_material`): cooling the body of constant
heat capacity `C_c` from `T_0` to `T` with constant refrigerator input power
`P` and constant hot-reservoir temperature `T_h` takes the time

    `t = (C_c/P)·(T_h·ln(T_0/T) − (T_0 − T))`,

an expression in `C_c`, `T_h`, `P`, `T_0`, `T`, as T3-C4 requests.
Derivation: the constant-power law `W_tot = P·t` with the closed-form work
`total_work_eval`; solve for `t` (`P ≠ 0`).  Units: J/(J/s) = s. -/
theorem elapsed_time_c4 {C_c P T_h T_0 T W_tot t : ℝ}
    (hP : 0 < P) (hT : 0 < T) (hT0 : 0 < T_0) (hTT0 : T ≤ T_0)
    (hW : TotalWorkOfQuasiStaticCycles W_tot C_c T_h T_0 T)
    (hPW : ConstantPowerWork W_tot P t) :
    t = C_c / P * (T_h * Real.log (T_0 / T) - (T_0 - T)) := by
  have hWeval := total_work_eval hT hT0 hTT0 hW
  unfold ConstantPowerWork at hPW
  field_simp
  linear_combination hWeval - hPW

/-! ## Bridge lemmas III — branch/orientation records -/

/-- **Work denominator positivity** (bridge 6, branch record): on the cooling
branch `0 < T < T_0` with `T_0 ≤ T_h`, the accumulated-work bracket is
strictly positive, `T_h·ln(T_0/T) − (T_0 − T) > 0`.  With `x = T_0/T > 1`,
`Real.self_sub_one_lt_mul_log` gives `x − 1 < x·ln x`, i.e.
`(T_0 − T)/T < (T_0/T)·ln(T_0/T)`; multiplying by `T > 0` and using
`T_0 ≤ T_h` with `ln(T_0/T) > 0` (`Real.log_pos`) yields the claim. -/
theorem work_denominator_pos {T_h T_0 T : ℝ}
    (hT : 0 < T) (hT0 : 0 < T_0) (hTT0 : T < T_0) (hT0Th : T_0 ≤ T_h) :
    0 < T_h * Real.log (T_0 / T) - (T_0 - T) := by
  have hx1 : 1 < T_0 / T := (one_lt_div hT).mpr hTT0
  have hx0 : 0 ≤ T_0 / T := le_of_lt (div_pos hT0 hT)
  have hlog : 0 < Real.log (T_0 / T) := Real.log_pos hx1
  have h2 := Real.self_sub_one_lt_mul_log hx0 (ne_of_gt hx1)
  have h4 : T_0 / T - 1 = (T_0 - T) / T := by field_simp
  rw [h4] at h2
  have h6 := (div_lt_iff₀ hT).mp h2
  have h7 : (T_0 / T) * Real.log (T_0 / T) * T = T_0 * Real.log (T_0 / T) := by
    field_simp
  rw [h7] at h6
  have h5 : T_0 * Real.log (T_0 / T) ≤ T_h * Real.log (T_0 / T) :=
    mul_le_mul_of_nonneg_right hT0Th hlog.le
  linarith

/-- **Total work input is positive** (branch record): cooling the body
requires positive net work, `0 < W_tot` — the closed form of
`total_work_eval` is a product of the positive `C_c` and the positive bracket
of `work_denominator_pos`. -/
theorem total_work_pos {C_c T_h T_0 T W_tot : ℝ}
    (hCc : 0 < C_c) (hT : 0 < T) (hT0 : 0 < T_0)
    (hTT0 : T < T_0) (hT0Th : T_0 ≤ T_h)
    (hW : TotalWorkOfQuasiStaticCycles W_tot C_c T_h T_0 T) :
    0 < W_tot := by
  rw [total_work_eval hT hT0 hTT0.le hW]
  exact mul_pos hCc (work_denominator_pos hT hT0 hTT0 hT0Th)

/-- **Total extracted heat is positive** (branch record): the heat absorbed
from the cooled body over all cycles, `Q_c_tot = C_c·(T_0 − T)`, flows *into*
the refrigerator working substance, `HeatFlowsIntoSystem Q_c_tot`, since
`C_c > 0` and the body cools, `T < T_0`. -/
theorem overall_heat_extracted_pos {Q_c_tot C_c T_0 T : ℝ}
    (hCc : 0 < C_c) (hTT0 : T < T_0)
    (hQc : ConstantHeatCapacityCooling Q_c_tot C_c T_0 T) :
    HeatFlowsIntoSystem Q_c_tot := by
  unfold ConstantHeatCapacityCooling at hQc
  unfold HeatFlowsIntoSystem
  rw [hQc]
  exact mul_pos hCc (sub_pos.mpr hTT0)

/-! ## Main target (T3-C5): the overall coefficient of performance -/

/-- Raw end-to-end expression requested by T3-C5 (derived candidate): the
overall COP as a combination of `T_0`, `T_h`, `T`,
`(T_0 − T)/(T_h·ln(T_0/T) − (T_0 − T))`.  The definition merely records the
derived combination; that the actual overall COP equals it is the content of
`overall_cop` — no hypothesis or premise mentions this expression.
Dimensionless (K/K). -/
noncomputable def overallCOPExpr (T_0 T_h T : ℝ) : ℝ :=
  (T_0 - T) / (T_h * Real.log (T_0 / T) - (T_0 - T))

/-- **T3-C5 main target** (blueprint `thm:physics:ipho_2026_t3_c5:target`).
For the refrigerator of T3-C4 — the Pm-T executing infinitesimal Carnot
cycles with constant input power `P` and constant hot-reservoir temperature
`T_h` while the body of constant heat capacity `C_c` cools from `T_0` to
`T < T_0` (so `Q_c_tot = C_c·(T_0 − T)` is the total heat extracted from the
body and `W_tot` the total work input over all cycles performed until the
elapsed time `t`, with `W_tot = P·t`) — the overall coefficient of
performance `COP = Q_c_tot/W_tot` of all the cycles is

    `COP = (T_0 − T)/(T_h·ln(T_0/T) − (T_0 − T))`,

an expression in `T_0`, `T_h`, `T` only, as requested.
Derivation chain: `total_work_eval` (resting on the FTC bridge
`work_integral_eq`) gives `W_tot = C_c·(T_h·ln(T_0/T) − (T_0 − T))`; the
calorimetry hypothesis `hQc` gives `Q_c_tot = C_c·(T_0 − T)`; the common
factor `C_c ≠ 0` cancels (`mul_div_mul_left`).  The constant-power hypothesis
`hPW` (with `t`) frames "all the cycles performed until time `t`": combined
with `elapsed_time_c4` it yields the same expression via
`COP = C_c·(T_0 − T)/(P·t)` — `C_c` and `P` both cancel, which is why they do
not appear in the answer. -/
theorem overall_cop {C_c P T_h T_0 T t : ℝ}
    (hCc : 0 < C_c) (_hP : 0 < P) (_hTh : 0 < T_h) (hT0 : 0 < T_0)
    (hT : 0 < T) (hTT0 : T < T_0) (_hT0Th : T_0 ≤ T_h)
    {Q_c_tot W_tot : ℝ}
    (hQc : ConstantHeatCapacityCooling Q_c_tot C_c T_0 T)
    (hW : TotalWorkOfQuasiStaticCycles W_tot C_c T_h T_0 T)
    (_hPW : ConstantPowerWork W_tot P t) :
    coefficientOfPerformance Q_c_tot W_tot =
      (T_0 - T) / (T_h * Real.log (T_0 / T) - (T_0 - T)) := by
  have hWeval := total_work_eval hT hT0 hTT0.le hW
  unfold coefficientOfPerformance
  unfold ConstantHeatCapacityCooling at hQc
  rw [hQc, hWeval, mul_div_mul_left _ _ hCc.ne']

/-- Packaged form of the main target (naming expansion): the overall COP
equals the raw requested expression `overallCOPExpr`.
Proof route: `overall_cop`; `overallCOPExpr` unfolds definitionally to the
closed form. -/
theorem overall_cop_eq_expr {C_c P T_h T_0 T t : ℝ}
    (hCc : 0 < C_c) (hP : 0 < P) (hTh : 0 < T_h) (hT0 : 0 < T_0)
    (hT : 0 < T) (hTT0 : T < T_0) (hT0Th : T_0 ≤ T_h)
    {Q_c_tot W_tot : ℝ}
    (hQc : ConstantHeatCapacityCooling Q_c_tot C_c T_0 T)
    (hW : TotalWorkOfQuasiStaticCycles W_tot C_c T_h T_0 T)
    (hPW : ConstantPowerWork W_tot P t) :
    coefficientOfPerformance Q_c_tot W_tot = overallCOPExpr T_0 T_h T := by
  unfold overallCOPExpr
  exact overall_cop hCc hP hTh hT0 hT hTT0 hT0Th hQc hW hPW

/-- **The overall COP is positive** (branch record): the refrigerator indeed
moves a positive heat `Q_c_tot` out of the cooled body at the cost of a
positive total work `W_tot`, so `0 < COP`.
Proof route: `overall_heat_extracted_pos`, `total_work_pos`, `div_pos`. -/
theorem overall_cop_pos {C_c T_h T_0 T : ℝ}
    (hCc : 0 < C_c) (hT : 0 < T) (hT0 : 0 < T_0)
    (hTT0 : T < T_0) (hT0Th : T_0 ≤ T_h)
    {Q_c_tot W_tot : ℝ}
    (hQc : ConstantHeatCapacityCooling Q_c_tot C_c T_0 T)
    (hW : TotalWorkOfQuasiStaticCycles W_tot C_c T_h T_0 T) :
    0 < coefficientOfPerformance Q_c_tot W_tot := by
  have hQ := overall_heat_extracted_pos hCc hTT0 hQc
  have hWtot := total_work_pos hCc hT hT0 hTT0 hT0Th hW
  unfold coefficientOfPerformance
  exact div_pos hQ hWtot

end IPhO2026.T3C5
