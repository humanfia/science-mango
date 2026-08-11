import Mathlib
import IChO2026Chem

/-!
# IChO 2026, Theory Problem 2, part 2.5 (target T2-A5)

**Period of oscillations of the Belousov–Zhabotinsky reaction.**

## Source contract

The BZ mechanism (elementary steps (1)–(7) with constants `k₁ … k₇`) and
the maintained reactant concentrations are shared with T2-A2/T2-A3 and live
in `IChO2026Chem.Kinetics.BelousovZhabotinsky`.  This file adds the
part-2.5 contract:

*Assumptions (source-given data).*
- kinetic constants `k₁ = 1.0 × 10⁴`, `k₂ = 6.2 × 10⁴`, `k₃ = 4.0 × 10⁷`
  (`M⁻² s⁻¹`), `k₄ = 2.0 × 10⁹` (`M⁻² s⁻¹`), `k₅ = 2.1` (`M⁻³ s⁻¹`),
  `k₆ = 8.2`, `k₇ = 1.0 × 10²` (`M⁻¹ s⁻¹`);
- maintained concentrations `[BrO₃⁻] = 0.06 M`, `[H⁺] = 0.8 M`,
  `[MA] = 0.1 M` (reactants other than Ce⁴⁺, plus pH, are held constant);
- `[Br⁻]max = 7.0 × 10⁻⁴ M` (text following part 2.4);
- during Process B the solution is colourless, `[Ce⁴⁺] ≈ 0`, so the
  step-(7) bromide production `k₇[Ce⁴⁺][BMA]` is negligible (source
  eq. 5.1) and the bromide balance is
  `-d[Br⁻]/dt = k₄[HBrO₂][Br⁻][H⁺] + k₅[BrO₃⁻][Br⁻][H⁺]²` (eq. 5.2);
- with `[HBrO₂] = [HBrO₂]B` stationary and bromate/proton maintained, this
  is the first-order decay `-d[Br⁻]/dt = k*·[Br⁻]` with
  `k* = k₄[HBrO₂]B[H⁺] + k₅[BrO₃⁻][H⁺]²` (eq. 5.3);
- the period `τ` is the time for `[Br⁻]` to fall from `[Br⁻]max` to
  `[Br⁻]critical`, the return to `[Br⁻]max` being almost immediate.

*Natural-language prerequisites from previous parts* (policy
`natural_language_prerequisite_only`; restated as definitions carrying the
previous conclusions, not imported from other problem files):
- T2-A2: `[HBrO₂]B = (k₅/k₄)·[BrO₃⁻]·[H⁺] = 5.04 × 10⁻¹¹ M`;
- T2-A3: `[Br⁻]critical = (k₁/k₄)·[BrO₃⁻] = 3.0 × 10⁻⁷ M`.

*Target (requested output).*  The period of oscillations in seconds:
`[Br⁻]critical = [Br⁻]max·e^(−k*τ)`, i.e.
`τ = ln([Br⁻]max / [Br⁻]critical) / k*` (eq. 5.4), with `k* = 0.16128 s⁻¹`
and `τ ≈ 48 s` (recorded answer `48`; exact value ≈ 48.08).

All concentrations, rate constants, and times are scalar numerical readouts
in the units printed by the source, following the shared module convention.
-/

namespace IChO2026.T2.A5

open IChO2026Chem.Kinetics.BelousovZhabotinsky

/-! ## Source-given data -/

/-- The seven elementary rate constants of the BZ mechanism as printed in
the source (Processes A, B, C). -/
def sourceParameters : KineticParameters where
  k1 := 1.0e4
  k2 := 6.2e4
  k3 := 4.0e7
  k4 := 2.0e9
  k5 := 2.1
  k6 := 8.2
  k7 := 1.0e2

/-- Maintained bromate concentration `[BrO₃⁻] = 0.06 M`. -/
def bromateConc : MolarConcentration := 0.06

/-- Maintained proton concentration `[H⁺] = 0.8 M`. -/
def protonConc : MolarConcentration := 0.8

/-- Maintained malonic acid concentration `[MA] = 0.1 M`.  Recorded for
contract completeness; it does not enter the part-2.5 bromide balance
because step (6) feeds only the neglected step (7). -/
def malonicAcidConc : MolarConcentration := 0.1

/-- Initial cerium(IV) concentration `[Ce⁴⁺]₀ = 0.001 M`.  Recorded for
contract completeness; during Process B `[Ce⁴⁺] ≈ 0` (source eq. 5.1), so
the step-(7) bromide production is dropped from the balance. -/
def ceIVInitialConc : MolarConcentration := 0.001

/-- Maximum bromide concentration in the phase portrait,
`[Br⁻]max = 7.0 × 10⁻⁴ M` (source text following part 2.4). -/
def bromideMax : MolarConcentration := 7.0e-4

/-! ## Prerequisites from T2-A2 and T2-A3 -/

/-- Stationary HBrO₂ concentration during Process B, restating the T2-A2
conclusion `[HBrO₂]B = (k₅/k₄)·[BrO₃⁻]·[H⁺]` (source eq. 2.6). -/
noncomputable def hbro2StationaryB : MolarConcentration :=
  sourceParameters.k5 / sourceParameters.k4 * bromateConc * protonConc

/-- The T2-A2 numerical conclusion `[HBrO₂]B = 5.04 × 10⁻¹¹ M`. -/
theorem hbro2StationaryB_value : hbro2StationaryB = 5.04e-11 := by
  norm_num [hbro2StationaryB, sourceParameters, bromateConc, protonConc]

/-- Critical bromide concentration at the A↔B switch-over, restating the
T2-A3 conclusion `[Br⁻]critical = (k₁/k₄)·[BrO₃⁻]` (source eq. 3.2). -/
noncomputable def bromideCritical : MolarConcentration :=
  sourceParameters.k1 / sourceParameters.k4 * bromateConc

/-- The T2-A3 numerical conclusion `[Br⁻]critical = 3.0 × 10⁻⁷ M`. -/
theorem bromideCritical_value : bromideCritical = 3.0e-7 := by
  norm_num [bromideCritical, sourceParameters, bromateConc]

theorem bromideCritical_pos : 0 < bromideCritical := by
  norm_num [bromideCritical, sourceParameters, bromateConc]

theorem bromideMax_pos : 0 < bromideMax := by
  norm_num [bromideMax]

/-- Bromide decreases from its maximum down to the critical value during
Process B (source text following part 2.4). -/
theorem bromideCritical_lt_bromideMax : bromideCritical < bromideMax := by
  norm_num [bromideCritical, bromideMax, sourceParameters, bromateConc]

/-! ## The Process-B first-order bromide decay (eqs. 5.1–5.3) -/

/-- The effective first-order bromide-decay constant of Process B,
`k* = k₄·[HBrO₂]B·[H⁺] + k₅·[BrO₃⁻]·[H⁺]²` (source eq. 5.3), in `s⁻¹`. -/
noncomputable def effectiveRateConstant : ℝ :=
  sourceParameters.k4 * hbro2StationaryB * protonConc +
    sourceParameters.k5 * bromateConc * protonConc ^ 2

/-- The source's numerical evaluation `k* = 0.16128 s⁻¹`. -/
theorem effectiveRateConstant_value : effectiveRateConstant = 0.16128 := by
  norm_num [effectiveRateConstant, hbro2StationaryB, sourceParameters,
    bromateConc, protonConc]

theorem effectiveRateConstant_pos : 0 < effectiveRateConstant := by
  norm_num [effectiveRateConstant, hbro2StationaryB, sourceParameters,
    bromateConc, protonConc]

/-- The Process-B background state as a function of the current bromide
concentration: stationary `[HBrO₂]B`, maintained bromate and proton, and
the varying bromide.  The remaining species do not participate in steps
(4)–(5) and are set to `0`. -/
noncomputable def processBState (bromide : MolarConcentration) : State := fun
  | .hbro2 => hbro2StationaryB
  | .bromate => bromateConc
  | .bromide => bromide
  | .proton => protonConc
  | _ => 0

/-- Bridge between the elementary mass-action rates and the first-order
model: during Process B the bromide consumption rate of steps (4) and (5)
(source eq. 5.2, with the step-(7) production already dropped by the
`[Ce⁴⁺] ≈ 0` approximation of eq. 5.1) factors as `k*·[Br⁻]` (eq. 5.3). -/
theorem bromide_consumption_rate (b : MolarConcentration) :
    rate4 sourceParameters (processBState b) +
        rate5 sourceParameters (processBState b) =
      effectiveRateConstant * b := by
  simp only [rate4, rate5, processBState, effectiveRateConstant]
  ring

/-! ## Generic first-order decay and the period formula (eq. 5.4) -/

/-- A positive quantity undergoing exact first-order decay `dy/dt = −k·y`
(`k > 0`) from `initial` at time `0` down to `final < initial` at time
`duration`.  This packages the source's first-order kinetic equation for
`[Br⁻]` during Process B; the positivity side conditions keep every
logarithm and division of the period formula well-defined. -/
structure FirstOrderDecay where
  /-- Effective first-order rate constant `k` (in `s⁻¹`). -/
  rateConstant : ℝ
  /-- Concentration trajectory (in `M`) as a function of time (in `s`). -/
  trajectory : ℝ → ℝ
  /-- Concentration at the start of the decay branch (in `M`). -/
  initial : ℝ
  /-- Concentration at the end of the decay branch (in `M`). -/
  final : ℝ
  /-- Duration of the decay branch (in `s`). -/
  duration : ℝ
  rateConstant_pos : 0 < rateConstant
  initial_pos : 0 < initial
  final_pos : 0 < final
  final_lt_initial : final < initial
  /-- The decay starts at the initial concentration. -/
  starts : trajectory 0 = initial
  /-- The decay reaches the final concentration at the end of the branch. -/
  ends : trajectory duration = final
  /-- The first-order kinetic equation `-dy/dt = k·y`. -/
  ode : ∀ t : ℝ, HasDerivAt trajectory (-(rateConstant * trajectory t)) t

/-- First form of source eq. 5.4: the endpoint relation
`final = initial·e^(−k·duration)`. -/
theorem FirstOrderDecay.final_eq_exp (d : FirstOrderDecay) :
    d.final = d.initial * Real.exp (-(d.rateConstant * d.duration)) := by
  -- The integrating factor makes `g(t) = y(t)·e^(k·t)` constant.
  have hderiv : ∀ t : ℝ, HasDerivAt
      (fun s : ℝ ↦ d.trajectory s * Real.exp (d.rateConstant * s)) 0 t := by
    intro t
    have hexp : HasDerivAt (fun s : ℝ ↦ Real.exp (d.rateConstant * s))
        (Real.exp (d.rateConstant * t) * d.rateConstant) t := by
      simpa only [id_eq, mul_one] using
        ((hasDerivAt_id t).const_mul d.rateConstant).exp
    have hmul := (d.ode t).mul hexp
    rw [show (0 : ℝ) = -(d.rateConstant * d.trajectory t) * Real.exp (d.rateConstant * t) +
        d.trajectory t * (Real.exp (d.rateConstant * t) * d.rateConstant) by ring]
    exact hmul
  have hdiff : Differentiable ℝ
      (fun s : ℝ ↦ d.trajectory s * Real.exp (d.rateConstant * s)) :=
    fun t ↦ (hderiv t).differentiableAt
  have hconst := is_const_of_deriv_eq_zero hdiff (fun t ↦ (hderiv t).deriv) d.duration 0
  simp only [mul_zero, Real.exp_zero, mul_one, d.starts, d.ends] at hconst
  -- hconst : d.final * Real.exp (d.rateConstant * d.duration) = d.initial
  have hexp_ne : Real.exp (d.rateConstant * d.duration) ≠ 0 := (Real.exp_pos _).ne'
  calc d.final = d.initial / Real.exp (d.rateConstant * d.duration) := by
        rw [eq_div_iff hexp_ne]; exact hconst
    _ = d.initial * Real.exp (-(d.rateConstant * d.duration)) := by
        rw [div_eq_mul_inv, ← Real.exp_neg]

/-- Second form of source eq. 5.4: the elapsed time of a first-order decay
is `duration = ln(initial / final) / k`. -/
theorem FirstOrderDecay.duration_eq (d : FirstOrderDecay) :
    d.duration = Real.log (d.initial / d.final) / d.rateConstant := by
  have hfinal := d.final_eq_exp
  have hk : d.rateConstant ≠ 0 := d.rateConstant_pos.ne'
  have hlog : Real.log (d.initial / d.final) = d.rateConstant * d.duration := by
    rw [Real.log_div d.initial_pos.ne' d.final_pos.ne', hfinal,
      Real.log_mul d.initial_pos.ne' (Real.exp_pos _).ne', Real.log_exp]
    ring
  rw [hlog, mul_div_cancel_left₀ _ hk]

/-! ## Main target: the oscillation period -/

/-- **IChO 2026 T2, part 2.5.**  Under the Process-B first-order bromide
decay from `[Br⁻]max = 7.0 × 10⁻⁴ M` to `[Br⁻]critical = 3.0 × 10⁻⁷ M` with
the effective constant `k* = 0.16128 s⁻¹` of eq. 5.3 — the return from
`[Br⁻]critical` to `[Br⁻]max` being almost immediate, so the decay time is
the oscillation period — the period of oscillations is
`τ = ln([Br⁻]max / [Br⁻]critical) / k*` (eq. 5.4), i.e. `τ ≈ 48 s`. -/
theorem oscillation_period (d : FirstOrderDecay)
    (hk : d.rateConstant = effectiveRateConstant)
    (h0 : d.initial = bromideMax)
    (hT : d.final = bromideCritical) :
    d.duration = Real.log (bromideMax / bromideCritical) / effectiveRateConstant ∧
      |d.duration - 48| ≤ 0.5 := by
  have hdur := d.duration_eq
  rw [hk, h0, hT] at hdur
  refine ⟨hdur, ?_⟩
  -- Numerical bounds on the logarithm of the concentration ratio
  -- `[Br⁻]max / [Br⁻]critical = 7000/3 = 2¹¹ · (875/768)`.
  have hratio : (7.0e-4 : ℝ) / 3.0e-7 = 7000 / 3 := by norm_num
  have hsplit : Real.log ((7000 : ℝ) / 3) = 11 * Real.log 2 + Real.log (875 / 768) := by
    have h1 : (7000 : ℝ) / 3 = 2 ^ 11 * (875 / 768) := by norm_num
    rw [h1, Real.log_mul (by norm_num) (by norm_num), Real.log_pow]
    norm_num
  have h875lo : (107 / 875 : ℝ) ≤ Real.log (875 / 768) := by
    have h := Real.one_sub_inv_le_log_of_pos (show (0 : ℝ) < 875 / 768 by norm_num)
    have h2 : (1 : ℝ) - (875 / 768)⁻¹ = 107 / 875 := by norm_num
    rwa [h2] at h
  have h875hi : Real.log (875 / 768) ≤ (107 / 768 : ℝ) := by
    have h := Real.log_le_sub_one_of_pos (show (0 : ℝ) < 875 / 768 by norm_num)
    have h2 : (875 / 768 : ℝ) - 1 = 107 / 768 := by norm_num
    rwa [h2] at h
  have hL : (7.6608 : ℝ) ≤ Real.log (7000 / 3) := by
    rw [hsplit]
    calc (7.6608 : ℝ) ≤ 11 * 0.6931471803 + 107 / 875 := by norm_num
      _ ≤ 11 * Real.log 2 + Real.log (875 / 768) :=
          add_le_add (mul_le_mul_of_nonneg_left Real.log_two_gt_d9.le (by norm_num))
            h875lo
  have hU : Real.log (7000 / 3) ≤ (7.82208 : ℝ) := by
    rw [hsplit]
    calc 11 * Real.log 2 + Real.log (875 / 768)
          ≤ 11 * 0.6931471808 + 107 / 768 :=
          add_le_add (mul_le_mul_of_nonneg_left Real.log_two_lt_d9.le (by norm_num))
            h875hi
      _ ≤ (7.82208 : ℝ) := by norm_num
  -- Assemble the bound on `τ = ln(7000/3) / 0.16128`.
  rw [hdur, effectiveRateConstant_value, bromideCritical_value]
  show |Real.log ((7.0e-4 : ℝ) / 3.0e-7) / 0.16128 - 48| ≤ 0.5
  rw [hratio]
  have hlo : (47.5 : ℝ) ≤ Real.log (7000 / 3) / 0.16128 := by
    rw [le_div_iff₀ (by norm_num : (0 : ℝ) < 0.16128)]
    calc (47.5 : ℝ) * 0.16128 = 7.6608 := by norm_num
      _ ≤ Real.log (7000 / 3) := hL
  have hhi : Real.log (7000 / 3) / 0.16128 ≤ (48.5 : ℝ) := by
    rw [div_le_iff₀ (by norm_num : (0 : ℝ) < 0.16128)]
    calc Real.log (7000 / 3) ≤ 7.82208 := hU
      _ = 48.5 * 0.16128 := by norm_num
  rw [abs_le]
  exact ⟨by linarith, by linarith⟩

end IChO2026.T2.A5
