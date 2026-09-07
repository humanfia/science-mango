import Mathlib

/-!
# IPhO 2026 · Theory problem T3-C4 — "Chasing the absolute zero":
operating time of the constant-power Carnot refrigerator

Autoformalization of IPhO 2026 T3-C4 (source:
`reports/ipho_2026/problem_ipho_2026_t3_c4.source.json`; problem page
`ipho_2026_source/image/T3_page-4.png` (the T3-C4 statement, page 14), with the
cycle diagram Fig. 3b on `ipho_2026_source/image/T3_page-3.png` and the T3-B
model table on `ipho_2026_source/image/T3_page-2.png`).

## Subquestion T3-C4 (page 14, 2.0 pts)

"In order to continuously lower the temperature of a body with constant heat
capacity `C_c`, Carnot cycles are allowed to occur over time in such a way that
the power `P` transferred to the refrigerator remains constant.  It is then
assumed that the temperature `T_h` of the hot reservoir remains constant and
that in each operating cycle the temperature `T_c` of the cooled body decreases
by `dT_c`, satisfying the relation `dQ_c/dQ_h = T_c/T_h`.  If at `t = 0` we
have `T_c = T_0`, determine the time `t` that the Carnot refrigerator must
operate for the cooled body to reach a temperature `T < T_0`.  Express your
answer in terms of `C_c`, `T_h`, `P`, `T_0` and `T`."

## Physical model

The body is the cold reservoir of the Carnot refrigeration cycle
`1 → 2 → 3 → 4 → 1` of Fig. 3b (T3-C shared context), now run *continuously*:
each infinitesimal cycle extracts the heat `dQ_c` from the body at its current
temperature `T_c`, delivers `dQ_h` to the hot reservoir at the constant `T_h`,
and consumes the work `dW`.  T3-C4 is cycle-realization-agnostic: the statement
itself supplies the per-cycle Carnot relation `dQ_c/dQ_h = T_c/T_h` (the
Clausius equality for the reversible cycle of the shared context), so the Pm-T
specifics — the equation of state `T·M·V = n·K·H`, the T3-B1 isothermal heat
and the vertex fields `H₁..H₄` that fix *how* the cycle of Fig. 3b is realized —
do not enter the elapsed-time relation and are not re-assumed here (they live
in the sibling files `IPhO2026.T3B1`, `IPhO2026.T3C2`, `IPhO2026.T3C3`).

The continuum of cycles is modeled as a *cooling schedule*
(`CoolingSchedule`): the body temperature `Tbody` decreases monotonically from
`T_0` at `t = 0` to `T < T_0` at the sought time `t`.  The infinitesimal
per-cycle laws accumulate along this schedule to interval integrals over the
temperature path (the same step/accumulated pairing as `IPhO2026.T3B1`'s
`MaterialWorkStep`/`WorkAlongPath`): the total work input is
`W = ∫ τ in T..T_0, C_c·(T_h/τ − 1) dτ` (`WorkToCoolBody`), and constant input
power accumulates to `W = P·t` (`ConstantPowerWork`, the accumulated form of
the step law `dW = P·dt`).

## Governing laws (assumption side)

1. `CarnotHeatRatioStep` — stated verbatim in T3-C4: per cycle,
   `dQ_c/dQ_h = T_c/T_h` (Clausius equality of the reversible cycle; the
   adiabatic legs of Fig. 3b exchange no heat).
2. `RefrigeratorFirstLawStep` — energy conservation per cycle: the heat
   delivered to the hot reservoir equals the heat extracted from the body plus
   the work input, `dQ_h = dQ_c + dW`.  (Heat magnitudes are positive;
   `dT_c < 0` on the cooling branch.)
3. `ConstantHeatCapacityCoolingStep` — the body's heat capacity `C_c` is
   constant ("a body with constant heat capacity `C_c`"): extracting `dQ_c`
   lowers the body temperature by `dT_c` with `dQ_c = −C_c·dT_c`.
4. `ConstantPowerWorkStep` / `ConstantPowerWork` — "the power `P` transferred
   to the refrigerator remains constant": step form `dW = P·dt`, accumulated
   form `W = P·t`.
5. Process hypotheses: the cooling schedule (`Tbody 0 = T_0`, `Tbody t = T`,
   antitone — "continuously lower", "at `t = 0` we have `T_c = T_0`",
   "reach a temperature `T < T_0`") and the accumulated-work law
   `WorkToCoolBody`.
6. Physical ranges and refrigerator-regime branch: `C_c, P, T_h, T_0, T > 0`,
   `T < T_0` (given verbatim) and `T_0 < T_h` (the body is the cold side
   throughout: the refrigerator dumps heat to a hotter reservoir, and the
   largest body temperature visited is `T_0`).

## Derivation (answer-blind, from the laws above only)

* Per cycle (`work_step_of_cooling_step`): the Carnot ratio gives
  `dQ_h = dQ_c·T_h/T_c`; the first law then gives
  `dW = dQ_h − dQ_c = dQ_c·(T_h/T_c − 1)`; with the calorimetry law
  `dQ_c = −C_c·dT_c` this is `dW = C_c·(T_h/T_c − 1)·(−dT_c)` — positive on
  the cooling branch `dT_c < 0` since `T_c ≤ T_0 < T_h`.
* Accumulated along the cooling schedule (`work_to_cool_body_closed_form`,
  the path parameter is the body temperature):
  `W = C_c·∫_T^{T_0} (T_h/τ − 1) dτ = C_c·(T_h·ln(T_0/T) − (T_0 − T))`
  (via Mathlib's `integral_inv`, `∫ τ in T..T_0, τ⁻¹ = Real.log (T_0/T)`).
* Constant power: `P·t = W`, so with `P > 0`,

    `t = (C_c/P)·(T_h·ln(T_0/T) − (T_0 − T))`,

  in terms of `C_c`, `T_h`, `P`, `T_0` and `T` exactly as requested.

## Current target (conclusion side only)

`carnot_refrigerator_cooling_time` (symbolic closed form; blueprint
`thm:physics:ipho_2026_t3_c4:target`) and its packaged form
`carnot_refrigerator_cooling_time_eq_expr` with the raw requested combination
`coolingTimeExpr`.  No hypothesis, premise structure or local definition
mentions the value of `t` or the expression `(C_c/P)·(T_h·ln(T_0/T) − (T_0−T))`;
the laws pin `t` (through `W` and `P`), not the other way round.

*Branch/orientation record*: the cooling direction is the source-stated
`T < T_0` with the antitone schedule; the refrigerator regime is
`T_0 < T_h`.  `cooling_time_pos` records that the elapsed time is genuinely
positive — the strict content is `T_h·ln(T_0/T) > T_0 − T`, proved from the
logarithmic lower bound `1 − (T_0/T)⁻¹ ≤ Real.log (T_0/T)`
(`Real.one_sub_inv_le_log_of_pos`) and the regime inequality `T_h > T_0`.

## Units

All quantities are real numbers carrying SI units, recorded per declaration:
`T_h, T_c, T_0, T` in K; `C_c` in J/K; `dQ_c, dQ_h, dW, W` in J; `P` in
J/s (W); `t, dt` in s.  Consistency of the target: `C_c/P` carries
(J/K)/(J/s) = s/K and the bracket `T_h·ln(T_0/T) − (T_0 − T)` carries K
(the logarithm's argument is dimensionless), so `t` carries s ✓; the per-cycle
work step `C_c·(T_h/T_c − 1)·(−dT_c)` carries (J/K)·1·K = J ✓.

## Uncertainty

The source reports no `±` uncertainties; the answer is symbolic, so uncertainty
propagation is *not applicable* (no rounding rule is needed either: the
question asks for an expression, not a number).

## Grounding (LeanExplore, packages Mathlib + Physlib)

LeanExplore finds no Carnot-cycle/refrigerator or calorimetry API: Physlib's
`adiabatic_relation_log` and `adiabatic_relation_UaUbVaVb` are ideal-gas
relations and `CanonicalEnsemble.thermodynamicEntropy` is statistical-ensemble
machinery — near misses for this scalar heat-engine model, as recorded in the
sibling files `IPhO2026.T3B1`, `IPhO2026.T3C2`, `IPhO2026.T3C3`.  The laws are
therefore kept as faithful local governing predicates.  The analytic layer is
grounded in Mathlib: `intervalIntegral` notation `∫ τ in T..T_0, …`,
`integral_inv` (`∫ τ in a..b, τ⁻¹ = Real.log (b/a)` away from 0),
`intervalIntegral.integral_sub`, `intervalIntegral.integral_const_mul`,
`intervalIntegral.integral_const`, and `Real.one_sub_inv_le_log_of_pos` for the
positivity record.  The two bridge lemmas `work_step_of_cooling_step` and
`work_to_cool_body_closed_form` are fully proved; the main assembly
`carnot_refrigerator_cooling_time` (combine the closed form with `W = P·t` and
divide by `P ≠ 0` via `eq_div_iff`, then `field_simp`) was machine-checked
end-to-end in a scratch validation before its body was deferred to the prover
stage, following the sibling files' autoformalize discipline.
-/

namespace IPhO2026.T3C4

/-! ## Governing laws I — per-cycle step laws -/

/-- **Carnot (Clausius) heat ratio, per cycle** (stated verbatim in T3-C4:
"in each operating cycle the temperature `T_c` of the cooled body decreases by
`dT_c`, satisfying the relation `dQ_c/dQ_h = T_c/T_h`"): for one infinitesimal
operating cycle of the refrigerator at cold-side temperature `T_c`, the heat
`dQ_c` extracted from the cooled body and the heat `dQ_h` delivered to the hot
reservoir at `T_h` satisfy `dQ_c/dQ_h = T_c/T_h`.  This is the Clausius
equality for the reversible cycle of Fig. 3b (the adiabatic legs `1 → 2`,
`3 → 4` exchange no heat); `dQ_c, dQ_h` are positive magnitudes.
Units: dimensionless on both sides. -/
def CarnotHeatRatioStep (dQ_c dQ_h T_c T_h : ℝ) : Prop := dQ_c / dQ_h = T_c / T_h

/-- **First law for one refrigerator cycle** (energy conservation; the heat
magnitude sign convention of the T3-C context): the heat delivered to the hot
reservoir equals the heat extracted from the cooled body plus the work input
to the refrigerator, `dQ_h = dQ_c + dW`.  Units: J. -/
def RefrigeratorFirstLawStep (dW dQ_c dQ_h : ℝ) : Prop := dQ_h = dQ_c + dW

/-- **Constant-heat-capacity calorimetry, per cycle** (T3-C4 stipulation:
"a body with constant heat capacity `C_c`"): when the refrigerator extracts
the heat `dQ_c` from the body, the body temperature decreases by `dT_c`
(negative on the cooling branch) with `dQ_c = −C_c·dT_c`.  This is the
infinitesimal form of `Q = C_c·ΔT` at constant `C_c`.  Units: J = (J/K)·K. -/
def ConstantHeatCapacityCoolingStep (dQ_c C_c dT_c : ℝ) : Prop :=
  dQ_c = -(C_c * dT_c)

/-- **Constant input power, step form** (T3-C4 stipulation: "the power `P`
transferred to the refrigerator remains constant"): over the elapsed time `dt`
the work input to the refrigerator is `dW = P·dt`.  Units: J = (J/s)·s. -/
def ConstantPowerWorkStep (dW P dt : ℝ) : Prop := dW = P * dt

/-! ## Governing laws II — the continuous cooling process (accumulated forms) -/

/-- **Cooling schedule** (process reading of "Carnot cycles are allowed to
occur over time … If at `t = 0` we have `T_c = T_0` … reach a temperature
`T < T_0`"): the body temperature `Tbody` is a monotone-*decreasing* function
of time on the operating interval `[0, t]`, starting at the initial
temperature `T_0` and ending at the target temperature `T`.  This records the
initial condition and the continuous-cooling branch of the setup.
Units: `Tbody s` in K, `s, t` in s. -/
def CoolingSchedule (Tbody : ℝ → ℝ) (t T_0 T : ℝ) : Prop :=
  Tbody 0 = T_0 ∧ Tbody t = T ∧ AntitoneOn Tbody (Set.Icc 0 t)

/-- **Work accumulated along the cooling schedule** (accumulated form of the
per-cycle work step of `work_step_of_cooling_step`,
`dW = C_c·(T_h/T_c − 1)·(−dT_c)`): as the body temperature decreases
monotonically from `T_0` to `T`, the infinitesimal works sum to the interval
integral over the temperature path,
`W = ∫ τ in T..T_0, C_c·(T_h/τ − 1) dτ`.  (The change of parameter from time
to temperature uses the antitone cooling schedule; the integrand is the
per-cycle work per unit temperature *drop*, positive since `τ ≤ T_0 < T_h`.)
Units: J — (J/K)·K over the K-valued path. -/
def WorkToCoolBody (W C_c T_h T_0 T : ℝ) : Prop :=
  W = ∫ τ in T..T_0, C_c * (T_h / τ - 1)

/-- **Constant input power, accumulated form** (the step law
`dW = P·dt` of `ConstantPowerWorkStep` integrated over the operating time at
constant `P`): running the refrigerator for the elapsed time `t` at the
constant input power `P` consumes the total work `W = P·t`.
Units: J = (J/s)·s. -/
def ConstantPowerWork (W P t : ℝ) : Prop := W = P * t

/-! ## Bridge lemmas -/

/-- **Per-cycle work step** (bridge 1, assembly of the three step laws): one
infinitesimal operating cycle at cold-side temperature `T_c` that lowers the
body temperature by `dT_c` consumes the work
`dW = C_c·(T_h/T_c − 1)·(−dT_c)`.
Derivation: the Carnot ratio `dQ_c/dQ_h = T_c/T_h` (with `dQ_h, T_h ≠ 0`) gives
`dQ_h = dQ_c·T_h/T_c`; the first law gives `dW = dQ_h − dQ_c`; the calorimetry
law substitutes `dQ_c = −C_c·dT_c`.  The factor `(T_h/T_c − 1)` is the
reciprocal of the per-cycle Carnot coefficient of performance
`T_c/(T_h − T_c)`.
This is the integrand density of `WorkToCoolBody`: `dW/(−dT_c) = C_c·(T_h/T_c − 1)`. -/
theorem work_step_of_cooling_step {dW dQ_c dQ_h C_c T_c T_h dT_c : ℝ}
    (hTc : 0 < T_c) (hTh : 0 < T_h) (hdQh : 0 < dQ_h)
    (hCarnot : CarnotHeatRatioStep dQ_c dQ_h T_c T_h)
    (hFirst : RefrigeratorFirstLawStep dW dQ_c dQ_h)
    (hCap : ConstantHeatCapacityCoolingStep dQ_c C_c dT_c) :
    dW = C_c * (T_h / T_c - 1) * (-dT_c) := by
  unfold CarnotHeatRatioStep at hCarnot
  unfold RefrigeratorFirstLawStep at hFirst
  unfold ConstantHeatCapacityCoolingStep at hCap
  have hdQh' : dQ_h ≠ 0 := ne_of_gt hdQh
  have hTh' : T_h ≠ 0 := ne_of_gt hTh
  have hTc' : T_c ≠ 0 := ne_of_gt hTc
  have hratio : dQ_c * T_h = T_c * dQ_h := by
    rw [div_eq_div_iff hdQh' hTh'] at hCarnot
    exact hCarnot
  have hdQh_eq : dQ_h = dQ_c * T_h / T_c := by
    rw [eq_div_iff hTc']
    linear_combination -hratio
  have hdW : dW = dQ_h - dQ_c := by linear_combination -hFirst
  rw [hdW, hdQh_eq, hCap]
  field_simp [hTc']
  ring

/-- **Closed form of the accumulated work** (bridge 2, the analytic core):
the work accumulated while the body cools from `T_0` to `T` is
`W = C_c·(T_h·ln(T_0/T) − (T_0 − T))`.
Proof route: split the integrand as `C_c·T_h·τ⁻¹ − C_c`
(`intervalIntegral.integral_sub`; the reciprocal is integrable on
`[T, T_0]` since `0 < T ≤ T_0`, via `continuousOn_inv₀` and
`ContinuousOn.intervalIntegrable`), then `intervalIntegral.integral_const_mul`,
Mathlib's `integral_inv` (`∫ τ in T..T_0, τ⁻¹ = Real.log (T_0/T)`),
`intervalIntegral.integral_const` and `ring`. -/
theorem work_to_cool_body_closed_form {W C_c T_h T_0 T : ℝ}
    (hT : 0 < T) (hTT0 : T ≤ T_0)
    (hW : WorkToCoolBody W C_c T_h T_0 T) :
    W = C_c * (T_h * Real.log (T_0 / T) - (T_0 - T)) := by
  have h0 : (0 : ℝ) ∉ Set.uIcc T T_0 := by
    rw [Set.uIcc_of_le hTT0]
    exact fun hmem => absurd hmem.1 (not_le_of_gt hT)
  have hcont : ContinuousOn (fun τ : ℝ => τ⁻¹) (Set.uIcc T T_0) :=
    continuousOn_inv₀.mono (Set.subset_compl_singleton_iff.mpr h0)
  have hsplit : (fun τ : ℝ => C_c * (T_h / τ - 1)) = fun τ => C_c * T_h * τ⁻¹ - C_c := by
    funext τ
    rw [div_eq_mul_inv]
    ring
  have hI : IntervalIntegrable (fun τ : ℝ => τ⁻¹) MeasureTheory.volume T T_0 :=
    hcont.intervalIntegrable
  rw [hW, hsplit,
    intervalIntegral.integral_sub (hI.const_mul _) intervalIntegrable_const,
    intervalIntegral.integral_const_mul, intervalIntegral.integral_const,
    integral_inv h0, smul_eq_mul]
  ring

/-! ## Main target (T3-C4): the elapsed operating time, symbolic form -/

/-- Raw end-to-end expression requested by T3-C4 (derived candidate): the
elapsed operating time as a combination of the five permitted variables,
`(C_c/P)·(T_h·ln(T_0/T) − (T_0 − T))`.  The definition merely records the
derived combination; that the actual elapsed time equals it is the content of
`carnot_refrigerator_cooling_time` — no hypothesis or premise mentions this
expression.  Units: (J/K)/(J/s)·K = s. -/
noncomputable def coolingTimeExpr (C_c T_h P T_0 T : ℝ) : ℝ :=
  C_c / P * (T_h * Real.log (T_0 / T) - (T_0 - T))

/-- **T3-C4 main target.**  For the body of constant heat capacity `C_c`
cooled by the Carnot refrigerator of the T3-C context — per-cycle Clausius
relation `dQ_c/dQ_h = T_c/T_h`, first law `dQ_h = dQ_c + dW`, calorimetry
`dQ_c = −C_c·dT_c` per cycle, accumulated to `WorkToCoolBody` along a cooling
schedule from `T_0` at `t = 0` to `T < T_0` — running at the constant input
power `P` against the constant hot-reservoir temperature `T_h`: the elapsed
operating time is

    `t = (C_c/P)·(T_h·ln(T_0/T) − (T_0 − T))`,

in terms of `C_c`, `T_h`, `P`, `T_0` and `T` exactly as requested.

Derivation chain: `work_step_of_cooling_step` gives the per-cycle work
`dW = C_c·(T_h/T_c − 1)·(−dT_c)`; `work_to_cool_body_closed_form` accumulates
it to `W = C_c·(T_h·ln(T_0/T) − (T_0 − T))`; the constant-power law
`W = P·t` (`ConstantPowerWork`) with `P ≠ 0` then gives `t`
(`eq_div_iff`, `field_simp`).  The machine-checked proof (validated in a
scratch file at the autoformalize stage) is deferred to the prover stage,
following the sibling files' discipline. -/
theorem carnot_refrigerator_cooling_time {C_c T_h P T_0 T W t : ℝ} {Tbody : ℝ → ℝ}
    (hC : 0 < C_c) (hTh : 0 < T_h) (hP : 0 < P)
    (hT0 : 0 < T_0) (hT : 0 < T)
    (hTT0 : T < T_0) (hT0h : T_0 < T_h)
    (hsched : CoolingSchedule Tbody t T_0 T)
    (hW : WorkToCoolBody W C_c T_h T_0 T)
    (hPow : ConstantPowerWork W P t) :
    t = C_c / P * (T_h * Real.log (T_0 / T) - (T_0 - T)) := by
  have hP' : P ≠ 0 := ne_of_gt hP
  have hWclosed : W = C_c * (T_h * Real.log (T_0 / T) - (T_0 - T)) :=
    work_to_cool_body_closed_form hT hTT0.le hW
  have hPt : P * t = C_c * (T_h * Real.log (T_0 / T) - (T_0 - T)) := by
    have h1 : W = P * t := hPow
    rw [hWclosed] at h1
    exact h1.symm
  have ht : t = C_c * (T_h * Real.log (T_0 / T) - (T_0 - T)) / P := by
    rw [eq_div_iff hP']
    linear_combination hPt
  rw [ht]
  field_simp [hP']

/-- Packaged form of the main target (naming expansion): the elapsed operating
time equals the raw requested expression `coolingTimeExpr`.
Proof route: `carnot_refrigerator_cooling_time`; `coolingTimeExpr` unfolds
definitionally to the closed form. -/
theorem carnot_refrigerator_cooling_time_eq_expr {C_c T_h P T_0 T W t : ℝ} {Tbody : ℝ → ℝ}
    (hC : 0 < C_c) (hTh : 0 < T_h) (hP : 0 < P)
    (hT0 : 0 < T_0) (hT : 0 < T)
    (hTT0 : T < T_0) (hT0h : T_0 < T_h)
    (hsched : CoolingSchedule Tbody t T_0 T)
    (hW : WorkToCoolBody W C_c T_h T_0 T)
    (hPow : ConstantPowerWork W P t) :
    t = coolingTimeExpr C_c T_h P T_0 T := by
  unfold coolingTimeExpr
  exact carnot_refrigerator_cooling_time hC hTh hP hT0 hT hTT0 hT0h hsched hW hPow

/-- **Positive operating time** (branch/direction record): cooling the body
from `T_0` to `T < T_0` against the hotter reservoir (`T_0 < T_h`) takes a
strictly positive time at constant positive power — the work
`C_c·(T_h·ln(T_0/T) − (T_0 − T))` is positive.
Proof route: rewrite `t` by `carnot_refrigerator_cooling_time`; the
logarithmic lower bound `Real.one_sub_inv_le_log_of_pos` at `T_0/T > 0` gives
`(T_0 − T)/T_0 ≤ Real.log (T_0/T)`; multiplying by `T_h` and using
`T_h > T_0` with `(T_0 − T)/T_0 > 0` yields
`T_h·ln(T_0/T) > T_0·(T_0 − T)/T_0 = T_0 − T`; then `mul_pos` with
`C_c/P > 0`. -/
theorem cooling_time_pos {C_c T_h P T_0 T W t : ℝ} {Tbody : ℝ → ℝ}
    (hC : 0 < C_c) (hTh : 0 < T_h) (hP : 0 < P)
    (hT0 : 0 < T_0) (hT : 0 < T)
    (hTT0 : T < T_0) (hT0h : T_0 < T_h)
    (hsched : CoolingSchedule Tbody t T_0 T)
    (hW : WorkToCoolBody W C_c T_h T_0 T)
    (hPow : ConstantPowerWork W P t) :
    0 < t := by
  have hteq := carnot_refrigerator_cooling_time hC hTh hP hT0 hT hTT0 hT0h hsched hW hPow
  rw [hteq]
  have hlog : 1 - (T_0 / T)⁻¹ ≤ Real.log (T_0 / T) :=
    Real.one_sub_inv_le_log_of_pos (div_pos hT0 hT)
  rw [inv_div] at hlog
  have hkey : (T_0 - T) / T_0 ≤ Real.log (T_0 / T) := by
    rw [sub_div, div_self (ne_of_gt hT0)]
    exact hlog
  have hdrop : 0 < (T_0 - T) / T_0 := div_pos (sub_pos.mpr hTT0) hT0
  have h1 : T_h * ((T_0 - T) / T_0) ≤ T_h * Real.log (T_0 / T) :=
    mul_le_mul_of_nonneg_left hkey hTh.le
  have h2 : T_0 * ((T_0 - T) / T_0) < T_h * ((T_0 - T) / T_0) :=
    mul_lt_mul_of_pos_right hT0h hdrop
  have h3 : T_0 * ((T_0 - T) / T_0) = T_0 - T := by field_simp
  have hbracket : 0 < T_h * Real.log (T_0 / T) - (T_0 - T) := by linarith
  exact mul_pos (div_pos hC hP) hbracket

end IPhO2026.T3C4
