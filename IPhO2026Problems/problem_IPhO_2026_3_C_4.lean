import Mathlib

/-!
# IPhO 2026, Problem 3 (paramagnetic-torus Carnot refrigerator), Subquestion C.4

Blueprint chapter: `blueprint/src/chapters/IPhO2026Problems_problem_IPhO_2026_3_C_4.tex`
Source report:     `reports/ipho_2026_k3/problem_IPhO_2026_3_C_4.source.json`
Official page:     `T3_page-4.png` (Figure 3b, cycle `1 → 2 → 3 → 4 → 1` in the
                   `H`-versus-`T` plane)

## Physical situation

The paramagnetic torus (potassium chromate) executes the Carnot refrigeration
cycle `1 → 2 → 3 → 4 → 1` of Figure 3b.  `T_h`, `T_c` are the hot- and
cold-reservoir temperatures; `Q_h`, `Q_c` are the *magnitudes* of the heat
delivered to the hot reservoir and absorbed from the cold reservoir.
Governing laws available from the previous parts:

* equation of state of the paramagnet: `T * M * V = n * K * H`;
* isothermal heat relation (part B.1 result):
  `Q = -(μ₀ * n * K / (2 * T)) * (H_f^2 - H_i^2)` (heat *into* the torus);
* Carnot heat ratio for the reversible cycle: `Q_h / Q_c = T_h / T_c`.

## Current subquestion (C.4, 2 pts)

A body of constant heat capacity `C_c` is cooled from `T_0` to `T` while the
refrigerator input power `P` and the hot-reservoir temperature `T_h` remain
constant.  Determine the elapsed time.

Recorded official answer (appears only on the conclusion side below):

    t = (C_c * T_h / P) * (ln (T_0 / T) - (T_0 - T) / T_h).

## Physical model of the cooling run

The cold end of the refrigerator is the body being cooled, so the
cold-reservoir temperature tracks the body's instantaneous temperature `T'`,
decreasing from `T_0` at `s = 0` to `T` at `s = t`.  Per infinitesimal
Carnot cycle executed at cold temperature `T'` (all "densities" below are
per unit temperature drop of the body, since the infinitesimal cycles are
indexed by the control temperature):

* calorimetry (meaning of the heat capacity `C_c`): the heat drawn from the
  body per unit temperature drop is `C_c`;
* Carnot heat ratio at cold temperature `T'`: `δQ_h = δQ_c * T_h / T'`;
* first law (work–heat balance over one cycle): `δW = δQ_h - δQ_c`;
* constant input power: `δW = P * δs`, i.e. the residence-time density is
  the work density divided by `P`.

Hence `δs / ΔT' = (C_c / P) * (T_h / T' - 1)` with `ΔT' > 0` the width of the
infinitesimal temperature window crossed at `T'` (the run cools, so `dT' < 0`
along the run; densities per unit *drop* record the cooling branch
explicitly), and

    t = ∫_{T}^{T_0} (C_c / P) * (T_h / T' - 1) dT'
      = (C_c * T_h / P) * (ln (T_0 / T) - (T_0 - T) / T_h).

This file is an autoformalization: every proof body is `sorry` by design, and
the recorded answer appears only as the conclusion of the target theorems.
-/

namespace IPhO2026.Problem3.C4

open MeasureTheory

section Quantities

/-!
### Named quantities

Physical scalars (SI units): temperatures in kelvin, heats and work in
joules, power in watts, times in seconds, heat capacity in joules per kelvin,
magnetization and applied field in ampere per metre, amount of substance in
moles, volume in cubic metres.  Result/recorded quantities are `opaque`
parameters rather than transparent aliases so the contracts cannot be closed
by unfolding; the varying control temperature `T'` of the run stays a bound
variable, so the instantaneous laws below range over it quantificationally.
-/

/-- Hot-reservoir temperature `T_h`, constant throughout the run (K). -/
opaque tempHot : ℝ

/-- Body's initial temperature `T_0` (K): the cold-reservoir temperature at
    `s = 0`. -/
opaque tempInitial : ℝ

/-- Body's final temperature `T` (K): the cold end of the cooling process,
    with `T < T_0`. -/
opaque tempFinal : ℝ

/-- Constant heat capacity `C_c` of the cooled body (J/K). -/
opaque heatCapacityBody : ℝ

/-- Constant mechanical input power `P` drawn by the refrigerator (W). -/
opaque inputPower : ℝ

/-- Elapsed time `t` of the cooling run from `T_0` to `T` (s); the quantity
    the subquestion asks to determine.  Its *value* (the recorded answer) is
    only ever a conclusion below. -/
opaque elapsedTime : ℝ

/-- Constant parameters of the paramagnetic torus (Pm-T) working substance.
    `K` is the material constant of potassium chromate entering the equation
    of state `T * M * V = n * K * H`; all fields are positive physical
    scalars.  The values `μ₀`, `n * K` and `V` drop out of the C.4 elapsed
    time, but they are part of the setup and of the per-cycle proof route
    (the material constant `K` of potassium chromate is read from the
    statement), so they are captured here. -/
structure TorusParams where
  /-- Vacuum permeability `μ₀` (H/m). -/
  μ₀ : ℝ
  /-- Amount of paramagnetic substance `n` (mol). -/
  n : ℝ
  /-- Material constant `K` of the equation of state. -/
  K : ℝ
  /-- Fixed volume `V` of the torus (m³). -/
  V : ℝ
  μ₀_pos : 0 < μ₀
  n_pos  : 0 < n
  K_pos  : 0 < K
  V_pos  : 0 < V

/-- Thermodynamic state of the working substance at one corner of the cycle:
    scalar readouts of temperature `T` (K), applied-field magnitude `H` and
    magnetization magnitude `M` (both A/m). -/
structure WorkingState where
  T : ℝ
  H : ℝ
  M : ℝ

/-- The four corner states `1, 2, 3, 4` of the Carnot cycle of Figure 3b in
    the `H`-versus-`T` plane (processes `1 → 2 → 3 → 4 → 1`): a figure label
    preserved for the per-cycle route, even though the C.4 elapsed time is
    independent of the corner values. -/
structure CycleCorners where
  state1 : WorkingState
  state2 : WorkingState
  state3 : WorkingState
  state4 : WorkingState

/-- Operating history of the cooling run, as temperature-window densities.
    For every instantaneous cold (control) temperature `T'` visited between
    `T_0` and `T`, the fields give, per unit temperature drop of the body at
    `T'`, the heat drawn from the body, the heat dumped to the hot reservoir,
    the work supplied, and the residence time of the refrigerator:

    * `heatDrawnDensity T'`  — `δQ_c / ΔT'` (J/K);
    * `heatDumpedDensity T'` — `δQ_h / ΔT'` (J/K);
    * `workDensity T'`       — `δW / ΔT'`   (J/K);
    * `residenceDensity T'`  — `δs / ΔT'`    (s/K);

    where `ΔT' > 0` is the width of the infinitesimal temperature window
    crossed at `T'` (positive because the run cools: `dT' < 0` along the run,
    and the densities per unit *drop* record the cooling branch explicitly). -/
structure CoolingRun where
  heatDrawnDensity  : ℝ → ℝ
  heatDumpedDensity : ℝ → ℝ
  workDensity       : ℝ → ℝ
  residenceDensity  : ℝ → ℝ

/-- Regime assumptions of the cooling run: positive absolute temperatures
    with the ordering `T < T_0 < T_h`, a body of positive heat capacity,
    constant positive input power, and a positive elapsed time.  These
    encode the physical branch of the problem (a *cooling* run whose
    reservoirs straddle the visited temperatures). -/
structure RegimeAssumptions : Prop where
  tempHot_pos      : 0 < tempHot
  tempInitial_pos  : 0 < tempInitial
  tempFinal_pos    : 0 < tempFinal
  final_lt_initial : tempFinal < tempInitial
  initial_lt_hot   : tempInitial < tempHot
  heatCapacity_pos : 0 < heatCapacityBody
  inputPower_pos   : 0 < inputPower
  elapsedTime_pos  : 0 < elapsedTime

end Quantities

section GoverningLaws

/-!
### Governing laws (assumptions — never the C.4 answer)

Each `Prop`-valued definition below is an equation (or a conjunction of
equations and sign conditions) usable by rewriting, so the interfaces
constrain the model rather than merely asserting that witnesses exist.
The C.4 elapsed-time formula appears nowhere in this section.
-/

/-- Equation of state of the ideal paramagnet: `T * M * V = n * K * H`.
    Its consequence used downstream (`M = n * K * H / (V * T)` off
    `T, V ≠ 0`) is contracted in `magnetization_of_eos` below. -/
def ParamagnetEOS (p : TorusParams) (s : WorkingState) : Prop :=
  s.T * s.M * p.V = p.n * p.K * s.H

/-- Isothermal heat relation (previous-part result from part B): at constant
    temperature `T`, when the applied field changes from `Hi` to `Hf`, the
    heat transferred *into* the torus is

        `Q = -(μ₀ * n * K / (2 * T)) * (Hf^2 - Hi^2)`.

    The sign of `Q` carries the transfer direction (into the torus positive);
    the sign relation is packaged in `heat_leaves_torus_on_field_increase`. -/
def IsothermalHeatIntoTorus (p : TorusParams) (T Hi Hf Q : ℝ) : Prop :=
  Q = -(p.μ₀ * p.n * p.K / (2 * T)) * (Hf ^ 2 - Hi ^ 2)

/-- Carnot heat ratio for the reversible refrigeration cycle executed between
    reservoir temperatures `Th` (hot) and `Tc` (cold), with `Qh`, `Qc` the
    *magnitudes* of the heats exchanged with the reservoirs:
    `Qh * Tc = Qc * Th` (product form, so `Qh / Qc = Th / Tc` is available
    off `Tc, Qc ≠ 0`), together with sign conditions recording the
    refrigerator branch (heat actually extracted from the cold end). -/
def CarnotHeatRatio (Th Tc Qh Qc : ℝ) : Prop :=
  Qh * Tc = Qc * Th ∧ 0 < Qc ∧ 0 ≤ Qh

/-- First law of thermodynamics over one infinitesimal refrigeration cycle
    (work–heat balance; the working substance returns to its initial state,
    so its internal-energy change vanishes): `W = Qh - Qc` with all three as
    positive magnitudes per cycle (here: per unit temperature drop). -/
def CycleWorkHeatBalance (W Qh Qc : ℝ) : Prop :=
  W = Qh - Qc

/-- Constant-power law of the run in density form: per unit temperature drop,
    the supplied work density equals the constant input power times the
    residence-time density, `δW/ΔT' = P * δs/ΔT'`.  (Its whole-run
    accumulation is `W_total = P * t`.) -/
def ConstantPowerDensityLaw (workDensity residenceDensity : ℝ) : Prop :=
  workDensity = inputPower * residenceDensity

/-- Calorimetric law of the cooled body in density form: per unit temperature
    drop, the heat drawn from the body is its (constant) heat capacity —
    this *is* the meaning of "a body of heat capacity `C_c`" on the cooling
    branch (`dQ_c = -C_c dT'` with `dT' < 0`). -/
def BodyCalorimeterDensityLaw (heatDrawnDensity : ℝ) : Prop :=
  heatDrawnDensity = heatCapacityBody

/-- The infinitesimal Carnot refrigeration cycle at control temperature `T'`,
    for `T < T' < T_0`: the run data at `T'` obey the Carnot heat ratio at
    cold temperature `T'`, the first law, the constant-power law, the
    calorimetric law, and the residence time is positive (refrigerator
    branch: the cooling actually takes time).  This predicate quantifies
    over `T'`; it does not sum the run — the accumulation is contracted in
    `elapsedTime_eq_integral`. -/
def InfinitesimalCycleLaw (run : CoolingRun) (T' : ℝ) : Prop :=
  CarnotHeatRatio tempHot T'
    (run.heatDumpedDensity T') (run.heatDrawnDensity T') ∧
  CycleWorkHeatBalance
    (run.workDensity T') (run.heatDumpedDensity T') (run.heatDrawnDensity T') ∧
  ConstantPowerDensityLaw (run.workDensity T') (run.residenceDensity T') ∧
  BodyCalorimeterDensityLaw (run.heatDrawnDensity T') ∧
  0 < run.residenceDensity T'

/-- The cooling run: at every control temperature `T'` strictly between
    `T` and `T_0` the refrigerator executes the infinitesimal Carnot cycle of
    `InfinitesimalCycleLaw`.  The endpoint densities are left unconstrained
    (windows of zero width carry no accumulated time). -/
def IsCoolingRun (run : CoolingRun) : Prop :=
  ∀ T' ∈ Set.Ioo tempFinal tempInitial, InfinitesimalCycleLaw run T'

end GoverningLaws

section ContextLemmas

/-!
### Elimination consequences of the context laws (EOS, isothermal heat)

These lemmas make the `Prop`-valued physical interfaces constraining: each
packages a reusable equation or inequality consequence that later proofs can
rewrite with.
-/

/-- The equation of state determines the magnetization from the field:
    `M = (n * K * H) / (V * T)` — the transport form of the EOS used when the
    isothermal heat relation is moved between `H`-data and `M`-data. -/
lemma magnetization_of_eos (p : TorusParams) (s : WorkingState)
    (hT : s.T ≠ 0) (h : ParamagnetEOS p s) :
    s.M = p.n * p.K * s.H / (p.V * s.T) := by
  have hVne : p.V ≠ 0 := ne_of_gt p.V_pos
  have h' : s.T * s.M * p.V = p.n * p.K * s.H := h
  field_simp
  linear_combination h'

/-- Sign content of the isothermal heat relation: when the field is increased
    at fixed positive temperature, heat leaves the torus (`Q < 0`) — the
    orientation of the `3 → 4` leg of Figure 3b, and the reason `Q_h` is a
    heat *delivered to* the hot reservoir. -/
lemma heat_leaves_torus_on_field_increase (p : TorusParams) {T Hi Hf Q : ℝ}
    (hT : 0 < T) (hHi : 0 ≤ Hi) (hlt : Hi < Hf)
    (h : IsothermalHeatIntoTorus p T Hi Hf Q) :
    Q < 0 := by
  have hfactor : 0 < p.μ₀ * p.n * p.K / (2 * T) :=
    div_pos (mul_pos (mul_pos p.μ₀_pos p.n_pos) p.K_pos) (by linarith)
  have hΔ : 0 < Hf ^ 2 - Hi ^ 2 := by nlinarith
  have hm : 0 < (p.μ₀ * p.n * p.K / (2 * T)) * (Hf ^ 2 - Hi ^ 2) :=
    mul_pos hfactor hΔ
  have hQ : Q = -(p.μ₀ * p.n * p.K / (2 * T)) * (Hf ^ 2 - Hi ^ 2) := h
  rw [hQ]
  linarith

/-- Cycle corners of Figure 3b at cold temperature `T'`: states `1, 4` sit at
    `T_h`, states `2, 3` sit at `T'`, and the equation of state holds at
    every corner.  (Figure data; the C.4 result does not depend on the corner
    values, but the per-cycle justifications of the Carnot ratio do.) -/
def Figure3bCorners (p : TorusParams) (c : CycleCorners) (T' : ℝ) : Prop :=
  c.state1.T = tempHot ∧ c.state4.T = tempHot ∧
  c.state2.T = T' ∧ c.state3.T = T' ∧
  (∀ s ∈ ([c.state1, c.state2, c.state3, c.state4] : List WorkingState),
    ParamagnetEOS p s)

end ContextLemmas

section BridgeLemmas

/-!
### Bridge obligations: per-cycle laws → elapsed time

Each lemma contracts one nontrivial step of the derivation
`P ds = C_c (T_h / T' - 1) (-dT')` ⇒
`t = (C_c * T_h / P) * (ln (T_0 / T) - (T_0 - T) / T_h)`.
All are stated as equations usable by rewriting; all proofs are `sorry`.
-/

/-- Per-cycle heat dumped to the hot reservoir (density form): the Carnot
    heat ratio at cold temperature `T'` and the calorimetric law give
    `δQ_h/ΔT' = C_c * T_h / T'`.
    Carrier: `CarnotHeatRatio` (product form, divided by `T' ≠ 0`) together
    with `BodyCalorimeterDensityLaw`. -/
lemma heatDumpedDensity_eq (run : CoolingRun) {T' : ℝ}
    (hT' : T' ∈ Set.Ioo tempFinal tempInitial)
    (hrun : IsCoolingRun run) :
    run.heatDumpedDensity T' = heatCapacityBody * tempHot / T' := by
  obtain ⟨⟨hprod, _hQcpos, _hQhnn⟩, _, _, hcal, _⟩ := hrun T' hT'
  have hsub : run.heatDrawnDensity T' = heatCapacityBody := hcal
  by_cases hTz : T' = 0
  · -- Window degeneracy: the per-cycle law bundle is consistent with an
    -- arbitrary `heatDumpedDensity 0` when the visited window contains
    -- `T' = 0` (at `T' = 0` the product-form ratio carries no quotient,
    -- and `T_h = 0` is not excluded by the bundle alone).  The physical
    -- regime `0 < tempFinal < tempInitial < tempHot`
    -- (`RegimeAssumptions`, carried by every downstream theorem) rules this
    -- branch out via `tempFinal < T' < tempInitial`; this lemma's frozen
    -- signature, however, does not take the regime as an argument.  This
    -- is the single remaining gap of the file (recorded in
    -- `.archon/task_results/`).
    sorry
  · have hT'ne : T' ≠ 0 := hTz
    field_simp
    linear_combination hprod + tempHot * hsub

/-- Per-cycle work density: the first law with `heatDumpedDensity_eq` and the
    calorimetric law gives `δW/ΔT' = C_c * (T_h / T' - 1)`. -/
lemma workDensity_eq (run : CoolingRun) {T' : ℝ}
    (hT' : T' ∈ Set.Ioo tempFinal tempInitial)
    (hrun : IsCoolingRun run) :
    run.workDensity T' = heatCapacityBody * (tempHot / T' - 1) := by
  have hdumped := heatDumpedDensity_eq run hT' hrun
  obtain ⟨_, hbal, _, hcal, _⟩ := hrun T' hT'
  rw [hdumped] at hbal
  rw [hbal, hcal]
  ring

/-- Residence-time density: the constant-power law `δW = P * δs` divides
    (`P > 0` from the regime) to `ds/ΔT' = (C_c / P) * (T_h / T' - 1)`.
    This is the differential relation `P ds = C_c (T_h/T' - 1)(-dT')` of the
    informal solution, with the cooling branch (`ΔT' > 0` per drop) built in. -/
lemma residenceDensity_eq (run : CoolingRun) {T' : ℝ}
    (hT' : T' ∈ Set.Ioo tempFinal tempInitial)
    (hrun : IsCoolingRun run) :
    run.residenceDensity T' =
      (heatCapacityBody / inputPower) * (tempHot / T' - 1) := by
  have hwork := workDensity_eq run hT' hrun
  obtain ⟨_, _, hpow, _, _⟩ := hrun T' hT'
  by_cases hP : inputPower = 0
  · -- `inputPower = 0` is the second face of the gap recorded at
    -- `heatDumpedDensity_eq` (the frozen signature carries no regime
    -- hypothesis, so `P > 0` is unavailable; with `P = 0` the power law is
    -- consistent with the unconstrained `residenceDensity T' = W/0`,
    -- i.e. `0·s = W` with any `s` when `T_h = T'`).  See the
    -- `task_results` note.
    sorry
  · have hres : run.residenceDensity T' = run.workDensity T' / inputPower := by
      rw [hpow]
      field_simp
    rw [hres, hwork]
    field_simp

end BridgeLemmas

section PhysicsContracts

/-- **Accumulation bridge.**  The elapsed time of the cooling run, defined
    operationally as the integral of the residence-time density over the
    visited temperatures (`haccum`: additivity of time over the run), equals
    the integral of the explicit residence density:

        t = ∫_{T'} in [T, T_0], (C_c / P) * (T_h / T' - 1).

    Carrier: `residenceDensity_eq` on `Set.Ioo`, upgraded to set-integral
    congruence (the endpoints form a measure-zero set). -/
theorem elapsedTime_eq_integral
    (regime : RegimeAssumptions)
    (run : CoolingRun) (hrun : IsCoolingRun run)
    (haccum : elapsedTime
      = ∫ T' in Set.Icc tempFinal tempInitial, run.residenceDensity T') :
    elapsedTime
      = ∫ T' in Set.Icc tempFinal tempInitial,
          (heatCapacityBody / inputPower) * (tempHot / T' - 1) := by
  rw [haccum]
  -- The physical regime positions the visited window strictly above `0`
  -- (`0 < tempFinal`, so `T' ≠ 0` throughout); it is referenced here since
  -- the pointwise identity it feeds (`residenceDensity_eq`) is stated, per
  -- the frozen contract, without the regime and closes its `T' = 0`
  -- branch only in the redraft of that lemma.
  have := regime.tempFinal_pos
  apply setIntegral_congr_ae measurableSet_Icc
  rw [ae_iff]
  apply measure_mono_null (t := {tempFinal, tempInitial})
  · intro x hx
    simp only [Set.mem_setOf_eq, not_forall] at hx
    obtain ⟨hmem, hne⟩ := hx
    by_contra hnotin
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff, not_or] at hnotin
    apply hne
    rcases Set.mem_Icc.mp hmem with ⟨h1, h2⟩
    exact residenceDensity_eq run
      ⟨lt_of_le_of_ne h1 (Ne.symm hnotin.1), lt_of_le_of_ne h2 hnotin.2⟩ hrun
  · exact (Set.countable_singleton tempInitial).insert tempFinal
      |>.measure_zero volume

/-- **Evaluation bridge (real analysis).**  The residence-time integral
    evaluates by the fundamental theorem of calculus
    (`∫ T_h/T' = T_h * ln (T_0/T)` off `0 < T ≤ T' ≤ T_0`, `∫ 1 = T_0 - T`):

        ∫_{[T, T_0]} (C_c / P) * (T_h / T' - 1)
          = (C_c / P) * (T_h * ln (T_0 / T) - (T_0 - T)).

    Carrier: Mathlib `intervalIntegral.integral_one_div` and constant
    integration (via the identity between set integrals over `Icc` and
    interval integrals). -/
theorem cooling_time_integral_eval (regime : RegimeAssumptions) :
    (∫ T' in Set.Icc tempFinal tempInitial,
        (heatCapacityBody / inputPower) * (tempHot / T' - 1))
      = (heatCapacityBody / inputPower) *
          (tempHot * Real.log (tempInitial / tempFinal)
            - (tempInitial - tempFinal)) := by
  have hle : tempFinal ≤ tempInitial := le_of_lt regime.final_lt_initial
  have hb : (0:ℝ) ∉ Set.uIcc tempFinal tempInitial := by
    rw [Set.uIcc_of_le hle]
    simp only [Set.mem_Icc, not_and]
    intro h1 _
    linarith [regime.tempFinal_pos]
  rw [show (∫ T' in Set.Icc tempFinal tempInitial,
        (heatCapacityBody / inputPower) * (tempHot / T' - 1))
      = ∫ T' in tempFinal..tempInitial, (heatCapacityBody / inputPower) * (tempHot / T' - 1) from by
    rw [intervalIntegral.integral_of_le hle]
    exact setIntegral_congr_set Ioc_ae_eq_Icc.symm]
  have hcont : ContinuousOn (fun x => tempHot * x⁻¹) (Set.uIcc tempFinal tempInitial) :=
    continuousOn_const.mul (continuousOn_inv₀.mono (Set.subset_compl_singleton_iff.mpr hb))
  have hsplit : IntervalIntegrable (fun x => tempHot * x⁻¹) volume tempFinal tempInitial :=
    hcont.intervalIntegrable
  have hsplit1 : IntervalIntegrable (fun _x => (1:ℝ)) volume tempFinal tempInitial :=
    intervalIntegral.intervalIntegrable_const
  have step1 : (∫ T' in tempFinal..tempInitial, (heatCapacityBody / inputPower) * (tempHot / T' - 1))
      = ∫ T' in tempFinal..tempInitial, (heatCapacityBody / inputPower) * (tempHot * T'⁻¹ - 1) := by
    apply intervalIntegral.integral_congr
    intro x _
    simp only [div_eq_mul_inv]
  rw [step1,
      intervalIntegral.integral_const_mul (heatCapacityBody / inputPower) (fun x => tempHot * x⁻¹ - 1),
      intervalIntegral.integral_sub hsplit hsplit1,
      intervalIntegral.integral_const_mul tempHot (fun x => x⁻¹),
      integral_inv hb,
      integral_one]

/-- **Subquestion C.4 (main target).**

    The body of heat capacity `C_c` is cooled from `T_0` to `T` at constant
    input power `P` and constant hot-reservoir temperature `T_h` in elapsed
    time

        t = (C_c * T_h / P) * (ln (T_0 / T) - (T_0 - T) / T_h).

    The right-hand side (the recorded official answer) is purely
    conclusion-side: the hypotheses only bundle the per-cycle governing laws
    (`IsCoolingRun`, composed of the Carnot heat ratio, the first law, the
    constant-power law, and the calorimetric law) and the operational
    definition of the elapsed time (`haccum`).  Proof route:
    `elapsedTime_eq_integral` ∘ `cooling_time_integral_eval`, then the field
    algebra
    `(C_c/P) * (T_h ln(T_0/T) − (T_0−T)) = (C_c T_h/P) * (ln(T_0/T) − (T_0−T)/T_h)`.

    Blueprint label: `thm:physics:IPhO_2026_3_C_4:target`. -/
theorem c4_elapsed_time
    (regime : RegimeAssumptions)
    (run : CoolingRun) (hrun : IsCoolingRun run)
    (haccum : elapsedTime
      = ∫ T' in Set.Icc tempFinal tempInitial, run.residenceDensity T') :
    elapsedTime
      = (heatCapacityBody * tempHot / inputPower) *
          (Real.log (tempInitial / tempFinal)
            - (tempInitial - tempFinal) / tempHot) := by
  rw [elapsedTime_eq_integral regime run hrun haccum,
      cooling_time_integral_eval regime]
  have hTh : tempHot ≠ 0 := ne_of_gt regime.tempHot_pos
  field_simp

end PhysicsContracts

end IPhO2026.Problem3.C4
