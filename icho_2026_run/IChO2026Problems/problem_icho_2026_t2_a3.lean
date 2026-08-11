import Mathlib
import IChO2026Chem

/-!
# IChO 2026, Theory Problem 2, subquestion 2.3 — critical bromide concentration

## Source contract

58th International Chemistry Olympiad (Tashkent, Uzbekistan, 2026), Theory
Problem 2: kinetics of the Belousov–Zhabotinsky (BZ) reaction.  The mechanism
prints the elementary steps relevant here as

* (1) `HBrO₂ + BrO₃⁻ + H⁺ → 2 BrO₂• + H₂O`, `k₁ = 1.0 × 10⁴ M⁻² s⁻¹`
  (Process A),
* (4) `HBrO₂ + Br⁻ + H⁺ → 2 HBrO`, `k₄ = 2.0 × 10⁹ M⁻² s⁻¹` (Process B),

and the experiment holds `[BrO₃⁻]₀ = 0.06 M`, `[MA]₀ = 0.1 M` and the pH
(`[H⁺]₀ = 0.8 M`) constant throughout the reaction, while `Ce⁴⁺` (initially
`0.001 M`) is the oscillating catalyst.  Subquestion 2.3 asks for the critical
bromide concentration `[Br⁻]critical` at which the system switches over
between Process A and Process B, given that switching from A to B requires the
reaction rate of the elementary step (4) to exceed that of the elementary
step (1), and vice versa.

## Assumption/target split

Assumptions (sourced data and side conditions):

* the sourced kinetic constants `k₁, …, k₇` (`sourcedKineticParameters`);
* the maintained reactant concentrations `IsMaintainedState`
  (`[BrO₃⁻] = 0.06 M`, `[MA] = 0.1 M`, `[H⁺] = 0.8 M`);
* positivity of the `HBrO₂` intermediate concentration at the switchover;
* the defining rate balance of the switchover, `IsCriticalBromide`
  (source equation 3.1).

Targets (requested conclusions):

* the algebraic switchover relation `k₁ [BrO₃⁻] = k₄ [Br⁻]critical`, obtained
  from equation (3.1) by cancelling the common positive factors `[HBrO₂]` and
  `[H⁺]` (`k1_bromate_eq_k4_bromide_critical`);
* the closed form `[Br⁻]critical = (k₁ / k₄) [BrO₃⁻]`
  (`bromide_critical_eq_ratio`, source equation 3.2);
* the threshold characterization: step (4) outruns step (1) exactly when the
  bromide concentration is supercritical, and vice versa
  (`rate1_lt_rate4_iff_bromide_critical_lt`);
* the numerical value `[Br⁻]critical = 3.0 × 10⁻⁷ M` (`bromide_critical_value`).

No conclusion of subquestions 2.1 or 2.2 is assumed: the `[HBrO₂]` factor
cancels from the rate balance, so the natural-language prerequisite on the
previous part enters only through the shared mass-action infrastructure in
`IChO2026Chem.Kinetics.BelousovZhabotinsky`.
-/

open IChO2026Chem.Kinetics.BelousovZhabotinsky

namespace Icho2026T2A3

/-- The seven sourced rate constants of the BZ mechanism, as printed in the
problem: `k₁, k₂, k₄` in `M⁻² s⁻¹`, `k₃, k₆, k₇` in `M⁻¹ s⁻¹` and `k₅` in
`M⁻³ s⁻¹`; each field is the numerical readout in its source unit. -/
def sourcedKineticParameters : KineticParameters where
  k1 := 1.0e4
  k2 := 6.2e4
  k3 := 4.0e7
  k4 := 2.0e9
  k5 := 2.1
  k6 := 8.2
  k7 := 1.0e2

/-- The reactant concentrations maintained constant throughout the BZ
reaction: `[BrO₃⁻] = 0.06 M`, `[MA] = 0.1 M` and `[H⁺] = 0.8 M` (constant pH).
`Ce⁴⁺` is deliberately absent: it is the oscillating catalyst, not a
maintained reactant. -/
def IsMaintainedState (state : State) : Prop :=
  state .bromate = 0.06 ∧ state .malonicAcid = 0.1 ∧ state .proton = 0.8

/-- The defining property of the critical bromide concentration
`[Br⁻]critical`: at the state obtained by setting the bromide concentration to
this value (every other concentration unchanged), the mass-action rate of the
elementary step (4), `HBrO₂ + Br⁻ + H⁺ → 2 HBrO`, equals the mass-action rate
of the elementary step (1), `HBrO₂ + BrO₃⁻ + H⁺ → 2 BrO₂• + H₂O`.  This is
source equation (3.1); above `[Br⁻]critical` step (4) outruns step (1) and
Process B replaces Process A, and vice versa. -/
def IsCriticalBromide (parameters : KineticParameters) (state : State)
    (bromideCritical : MolarConcentration) : Prop :=
  rate1 parameters state =
    rate4 parameters (Function.update state .bromide bromideCritical)

/-- Source equation (3.1), simplified: since the `HBrO₂` and `H⁺`
concentrations are positive at the switchover, they cancel from the defining
rate balance and leave `k₁ [BrO₃⁻] = k₄ [Br⁻]critical`. -/
theorem k1_bromate_eq_k4_bromide_critical
    (parameters : KineticParameters) (state : State)
    {bromideCritical : MolarConcentration}
    (hhbro2 : 0 < state .hbro2) (hproton : 0 < state .proton)
    (hcritical : IsCriticalBromide parameters state bromideCritical) :
    parameters.k1 * state .bromate = parameters.k4 * bromideCritical := by
  unfold IsCriticalBromide at hcritical
  rw [rate4_update_bromide] at hcritical
  unfold rate1 at hcritical
  have hne : state .hbro2 * state .proton ≠ 0 :=
    mul_ne_zero (ne_of_gt hhbro2) (ne_of_gt hproton)
  apply mul_left_cancel₀ hne
  linear_combination hcritical

/-- Source equation (3.2): the closed form of the critical bromide
concentration, `[Br⁻]critical = (k₁ / k₄) [BrO₃⁻]`. -/
theorem bromide_critical_eq_ratio
    (parameters : KineticParameters) (state : State)
    {bromideCritical : MolarConcentration}
    (hhbro2 : 0 < state .hbro2) (hproton : 0 < state .proton)
    (hk4 : 0 < parameters.k4)
    (hcritical : IsCriticalBromide parameters state bromideCritical) :
    bromideCritical = parameters.k1 / parameters.k4 * state .bromate := by
  have h := k1_bromate_eq_k4_bromide_critical parameters state hhbro2 hproton hcritical
  have hk4' : parameters.k4 ≠ 0 := ne_of_gt hk4
  have h2 : bromideCritical = parameters.k1 * state .bromate / parameters.k4 := by
    rw [h, mul_div_cancel_left₀ _ hk4']
  rw [h2, div_mul_eq_mul_div]

/-- The ratio candidate of equation (3.2) indeed realises the defining rate
balance, so a critical bromide concentration exists for any positive `k₄`. -/
theorem isCriticalBromide_ratio
    (parameters : KineticParameters) (state : State)
    (hk4 : 0 < parameters.k4) :
    IsCriticalBromide parameters state
      (parameters.k1 / parameters.k4 * state .bromate) := by
  have hk4' : parameters.k4 ≠ 0 := ne_of_gt hk4
  have hmul : parameters.k4 * (parameters.k1 / parameters.k4 * state .bromate) =
      parameters.k1 * state .bromate := by
    rw [div_mul_eq_mul_div, mul_div_cancel₀ _ hk4']
  unfold IsCriticalBromide rate1
  rw [rate4_update_bromide]
  linear_combination -(state .hbro2 * state .proton) * hmul

/-- The switching criterion of the problem statement: with positive rate
constants and positive `HBrO₂`, `BrO₃⁻` and `H⁺` concentrations, the rate of
step (4) exceeds the rate of step (1) — so that Process A switches to
Process B — exactly when the bromide concentration exceeds `[Br⁻]critical`,
and vice versa. -/
theorem rate1_lt_rate4_iff_bromide_critical_lt
    (parameters : KineticParameters) (state : State)
    {bromideCritical : MolarConcentration}
    (hk1 : 0 < parameters.k1) (hk4 : 0 < parameters.k4)
    (hhbro2 : 0 < state .hbro2) (hproton : 0 < state .proton)
    (hbromate : 0 < state .bromate)
    (hcritical : IsCriticalBromide parameters state bromideCritical) :
    rate1 parameters state < rate4 parameters state ↔
      bromideCritical < state .bromide := by
  have h := k1_bromate_eq_k4_bromide_critical parameters state hhbro2 hproton hcritical
  have hpos : 0 < state .hbro2 * state .proton := mul_pos hhbro2 hproton
  have hr1 : rate1 parameters state =
      (state .hbro2 * state .proton) * (parameters.k1 * state .bromate) := by
    unfold rate1; ring
  have hr4 : rate4 parameters state =
      (state .hbro2 * state .proton) * (parameters.k4 * state .bromide) := by
    unfold rate4; ring
  rw [hr1, hr4, mul_lt_mul_iff_right₀ hpos, h, mul_lt_mul_iff_right₀ hk4]

/-- Subquestion 2.3: under the sourced conditions of the BZ experiment, the
critical bromide concentration is `[Br⁻]critical = 3.0 × 10⁻⁷ M`
(`(k₁ / k₄) [BrO₃⁻] = (1.0 × 10⁴ / 2.0 × 10⁹) × 0.06`). -/
theorem bromide_critical_value (state : State)
    {bromideCritical : MolarConcentration}
    (hhbro2 : 0 < state .hbro2)
    (hmaintained : IsMaintainedState state)
    (hcritical : IsCriticalBromide sourcedKineticParameters state
      bromideCritical) :
    bromideCritical = 3.0 * (10 : ℝ) ^ (-7 : ℤ) := by
  unfold IsMaintainedState at hmaintained
  obtain ⟨hbromate, _, hproton_eq⟩ := hmaintained
  have hproton : 0 < state .proton := by rw [hproton_eq]; norm_num
  have hk4 : 0 < sourcedKineticParameters.k4 := by
    norm_num [sourcedKineticParameters]
  have hratio := bromide_critical_eq_ratio sourcedKineticParameters state
    hhbro2 hproton hk4 hcritical
  rw [hratio, hbromate]
  norm_num [sourcedKineticParameters]

end Icho2026T2A3
