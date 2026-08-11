import Mathlib
import IChO2026Chem

/-!
# IChO 2026, Theory Problem T2, Subquestion 2.2

**Kinetics of the Belousov–Zhabotinsky reaction — stationary HBrO₂
concentrations.**

Source: 58th International Chemistry Olympiad, Tashkent 2026, theory problem
T2 (problem PDF page 16, printed page 2) and the official marking scheme.
Primary visual evidence: `T2_page-1.png` (problem statement, oscillation
scheme, points table) and `T2_page-2.png` (mechanism table with the rate
constants, the assumption block, and subquestion 2.2).

## Source contract

Species (carried by `IChO2026Chem.Kinetics.BelousovZhabotinsky.Species`):
HBrO₂, BrO₃⁻, Br⁻, H⁺, BrO₂•, HBrO, Ce³⁺, Ce⁴⁺, BMA (CHBr(COOH)₂), and MA
(CH₂(COOH)₂).

Elementary steps and sourced rate constants (mechanism table):

* Process A — (1) `HBrO₂ + BrO₃⁻ + H⁺ → 2 BrO₂• + H₂O`,
  `k₁ = 1.0 × 10⁴ M⁻² s⁻¹`; (2) `BrO₂• + Ce³⁺ + H⁺ → HBrO₂ + Ce⁴⁺`,
  `k₂ = 6.2 × 10⁴ M⁻² s⁻¹`; (3) `2 HBrO₂ → BrO₃⁻ + HBrO + H⁺`,
  `k₃ = 4.0 × 10⁷ M⁻¹ s⁻¹`.
* Process B — (4) `HBrO₂ + Br⁻ + H⁺ → 2 HBrO`, `k₄ = 2.0 × 10⁹ M⁻² s⁻¹`;
  (5) `BrO₃⁻ + Br⁻ + 2 H⁺ → HBrO + HBrO₂`, `k₅ = 2.1 M⁻³ s⁻¹`;
  (6) `HBrO + MA → BMA + H₂O`, `k₆ = 8.2 M⁻¹ s⁻¹`.
* Process C — (7) `Ce⁴⁺ + BMA → Ce³⁺ + Br⁻ + other products`,
  `k₇ = 1.0 × 10² M⁻¹ s⁻¹`.

Assumption block: Process C occurs continuously while Processes A and B
alternate; during A the solution is yellow (Ce⁴⁺) and B practically does not
occur, during B it is colourless (Ce³⁺) and A practically does not occur;
`[BrO₃⁻]₀ = 0.06 M`, `[MA]₀ = 0.1 M`, `[H⁺]₀ = 0.8 M`, `[Ce⁴⁺]₀ = 0.001 M`;
the concentrations of the reactants (except Ce⁴⁺) and the pH are maintained
constant throughout the reaction.

Requested outputs (subquestion 2.2, 11 points): the stationary molar
concentrations `[HBrO₂]ₐ` and `[HBrO₂]ᵦ` of HBrO₂ in Processes A and B under
the steady-state approximation.

## Assumption/target split

* **Given (premises):** the mechanism with its stoichiometry and the seven
  sourced rate constants; the maintained reactant concentrations
  `[BrO₃⁻] = 0.06 M` and `[H⁺] = 0.8 M`; the steady-state approximation for
  the intermediates, i.e. the mass-action net production rates of BrO₂• and
  HBrO₂ vanish in the running process; positivity of the factors that the
  marking scheme cancels (`[HBrO₂]` in Process A; `[Br⁻]` and `[H⁺]` in
  Process B).
* **Target (conclusions only):** the rubric relations
  `[HBrO₂]ₐ = (k₁ / (2 k₃)) [BrO₃⁻] [H⁺]` (eq. 2.4) and
  `[HBrO₂]ᵦ = (k₅ / k₄) [BrO₃⁻] [H⁺]` (eq. 2.6), together with the requested
  numerical values `6.0 × 10⁻⁶ M` and `5.04 × 10⁻¹¹ M`.  Neither value occurs
  in any premise, structure field, or definition.

## Source-to-Lean bridge

* Concentrations and rate constants are real numerical readouts in the source
  units, following the inherited convention of the shared module
  `IChO2026Chem.Kinetics.BelousovZhabotinsky`.
* The steady-state approximation is encoded exactly as the marking scheme
  states it: the net production rate of each intermediate is zero (rubric
  equations 2.1, 2.2 and 2.5).  Because Processes A and B alternate in time,
  the two stationary concentrations live on two distinct states `sA` and
  `sB`.  Process C does not contribute to the HBrO₂ or BrO₂• balances (step
  (7) involves neither species), and steps (4)–(6) resp. (1)–(3) are switched
  off by the alternation assumption.
-/

open IChO2026Chem.Kinetics.BelousovZhabotinsky

namespace IChO2026.T2.A2

/-! ## Sourced data of the T2 assumption block -/

/-- The seven rate constants printed in the IChO 2026 T2 mechanism table, as
real readouts in the source units (`k₁, k₂, k₄` in `M⁻² s⁻¹`; `k₃, k₆, k₇` in
`M⁻¹ s⁻¹`; `k₅` in `M⁻³ s⁻¹`). -/
def officialKineticParameters : KineticParameters where
  k1 := 1.0e4
  k2 := 6.2e4
  k3 := 4.0e7
  k4 := 2.0e9
  k5 := 2.1
  k6 := 8.2
  k7 := 1.0e2

/-- The reactant concentrations named in the T2 assumption block.  All except
`ceIV` are maintained constant throughout the reaction; `ceIV` is the initial
value `[Ce⁴⁺]₀` only, since Ce⁴⁺ is explicitly exempted from the
maintained-constant assumption.  Subquestion 2.2 consumes only `bromate` and
`proton`; the remaining entries are recorded because the source lists them in
the same assumption block used by later subquestions. -/
structure GivenReactantConcentrations where
  /-- `[BrO₃⁻]₀ = 0.06 M`, maintained constant. -/
  bromate : MolarConcentration
  /-- `[MA]₀ = 0.1 M`, maintained constant. -/
  malonicAcid : MolarConcentration
  /-- `[H⁺]₀ = 0.8 M`, maintained constant (constant pH). -/
  proton : MolarConcentration
  /-- `[Ce⁴⁺]₀ = 0.001 M`, initial value only. -/
  ceIV : MolarConcentration

/-- The official values of the T2 assumption block. -/
def officialGivenReactantConcentrations : GivenReactantConcentrations where
  bromate := 0.06
  malonicAcid := 0.1
  proton := 0.8
  ceIV := 0.001

/-! ## Net production rates of the intermediates

The left-hand sides of rubric equations (2.1), (2.2) and (2.5): mass-action
balances carrying the stoichiometric coefficients of the mechanism. -/

/-- Net production rate of the BrO₂• radical while Process A runs (steps
(1)–(3) only): step (1) produces two BrO₂• and step (2) consumes one, so
`d[BrO₂•]/dt = 2 r₁ − r₂`.  Set to zero, this is rubric equation (2.1). -/
def bro2RadicalNetRateA (p : KineticParameters) (s : State) : ℝ :=
  2 * rate1 p s - rate2 p s

/-- Net production rate of HBrO₂ while Process A runs (steps (1)–(3) only):
step (1) consumes one HBrO₂, step (2) produces one, and the bimolecular step
(3) consumes two, so `d[HBrO₂]/dt = −r₁ + r₂ − 2 r₃`.  Set to zero, this is
rubric equation (2.2). -/
def hbro2NetRateA (p : KineticParameters) (s : State) : ℝ :=
  -rate1 p s + rate2 p s - 2 * rate3 p s

/-- Net production rate of HBrO₂ while Process B runs (steps (4)–(6) only):
step (4) consumes one HBrO₂, step (5) produces one, and step (6) does not
involve HBrO₂, so `d[HBrO₂]/dt = −r₄ + r₅`.  Set to zero, this is rubric
equation (2.5). -/
def hbro2NetRateB (p : KineticParameters) (s : State) : ℝ :=
  -rate4 p s + rate5 p s

/-! ## The steady-state approximation -/

/-- The steady-state approximation for Process A: both intermediates have
vanishing net production rates (rubric equations (2.1) and (2.2)
simultaneously). -/
def ProcessASteadyState (p : KineticParameters) (s : State) : Prop :=
  bro2RadicalNetRateA p s = 0 ∧ hbro2NetRateA p s = 0

/-- The steady-state approximation for Process B: the HBrO₂ net production
rate vanishes (rubric equation (2.5)). -/
def ProcessBSteadyState (p : KineticParameters) (s : State) : Prop :=
  hbro2NetRateB p s = 0

/-! ## Symbolic stationary concentrations (rubric equations (2.3), (2.4), (2.6)) -/

/-- Rubric equation (2.3): adding the two Process-A steady-state equations
eliminates the BrO₂• radical and leaves `r₁ = 2 r₃`, i.e.
`k₁ [HBrO₂] [BrO₃⁻] [H⁺] = 2 k₃ [HBrO₂]²`. -/
theorem processA_steadyState_rate1_eq_two_mul_rate3
    (p : KineticParameters) (s : State) (hss : ProcessASteadyState p s) :
    rate1 p s = 2 * rate3 p s := by
  obtain ⟨h1, h2⟩ := hss
  unfold bro2RadicalNetRateA at h1
  unfold hbro2NetRateA at h2
  linarith

/-- Rubric equation (2.4): the stationary HBrO₂ concentration in Process A is
`[HBrO₂]ₐ = (k₁ / (2 k₃)) [BrO₃⁻] [H⁺]`.  The trivial zero stationary value
of equation (2.3) is excluded by the positivity of the intermediate. -/
theorem hbro2_stationary_processA
    (p : KineticParameters) (s : State)
    (hss : ProcessASteadyState p s) (hhbro2 : 0 < s .hbro2) (hk3 : p.k3 ≠ 0) :
    s .hbro2 = p.k1 / (2 * p.k3) * s .bromate * s .proton := by
  have h := processA_steadyState_rate1_eq_two_mul_rate3 p s hss
  unfold rate1 rate3 at h
  -- `h : p.k1 * s.hbro2 * s.bromate * s.proton = 2 * (p.k3 * s.hbro2 ^ 2)`;
  -- cancel the positive factor `s.hbro2`.
  have h' : p.k1 * s .bromate * s .proton = 2 * p.k3 * s .hbro2 := by
    apply mul_left_cancel₀ (ne_of_gt hhbro2)
    calc s .hbro2 * (p.k1 * s .bromate * s .proton)
        = p.k1 * s .hbro2 * s .bromate * s .proton := by ring
      _ = 2 * (p.k3 * s .hbro2 ^ 2) := h
      _ = s .hbro2 * (2 * p.k3 * s .hbro2) := by ring
  have h2k3 : (2 : ℝ) * p.k3 ≠ 0 := mul_ne_zero two_ne_zero hk3
  rw [div_mul_eq_mul_div, div_mul_eq_mul_div, eq_div_iff_mul_eq h2k3]
  linear_combination -h'

/-- Rubric equation (2.6): the stationary HBrO₂ concentration in Process B is
`[HBrO₂]ᵦ = (k₅ / k₄) [BrO₃⁻] [H⁺]`.  The common factor `[Br⁻] [H⁺]` of the
competing steps (4) and (5) is positive during Process B and cancels. -/
theorem hbro2_stationary_processB
    (p : KineticParameters) (s : State)
    (hss : ProcessBSteadyState p s)
    (hbromide : 0 < s .bromide) (hproton : 0 < s .proton) (hk4 : p.k4 ≠ 0) :
    s .hbro2 = p.k5 / p.k4 * s .bromate * s .proton := by
  have h0 : hbro2NetRateB p s = 0 := hss
  unfold hbro2NetRateB at h0
  have h : rate5 p s = rate4 p s := by linarith
  unfold rate4 rate5 at h
  -- `h : p.k5 * s.bromate * s.bromide * s.proton ^ 2
  --     = p.k4 * s.hbro2 * s.bromide * s.proton`;
  -- cancel the positive factor `s.bromide * s.proton`.
  have h' : p.k5 * s .bromate * s .proton = p.k4 * s .hbro2 := by
    apply mul_left_cancel₀ (mul_ne_zero (ne_of_gt hbromide) (ne_of_gt hproton))
    calc (s .bromide * s .proton) * (p.k5 * s .bromate * s .proton)
        = p.k5 * s .bromate * s .bromide * s .proton ^ 2 := by ring
      _ = p.k4 * s .hbro2 * s .bromide * s .proton := h
      _ = (s .bromide * s .proton) * (p.k4 * s .hbro2) := by ring
  rw [div_mul_eq_mul_div, div_mul_eq_mul_div, eq_div_iff_mul_eq hk4]
  linear_combination -h'

/-! ## The requested numerical values -/

/-- First requested value: with the official rate constants and the maintained
concentrations `[BrO₃⁻] = 0.06 M` and `[H⁺] = 0.8 M`, the stationary HBrO₂
concentration in Process A is `[HBrO₂]ₐ = 6.0 × 10⁻⁶ M`. -/
theorem hbro2_processA_official (s : State)
    (hss : ProcessASteadyState officialKineticParameters s)
    (hhbro2 : 0 < s .hbro2)
    (hbromate : s .bromate = 0.06) (hproton : s .proton = 0.8) :
    s .hbro2 = 6.0e-6 := by
  have hk3 : officialKineticParameters.k3 ≠ 0 := by
    norm_num [officialKineticParameters]
  have h := hbro2_stationary_processA officialKineticParameters s hss hhbro2 hk3
  rw [hbromate, hproton] at h
  rw [h]
  norm_num [officialKineticParameters]

/-- Second requested value: with the official rate constants and the
maintained concentrations `[BrO₃⁻] = 0.06 M` and `[H⁺] = 0.8 M`, the
stationary HBrO₂ concentration in Process B is `[HBrO₂]ᵦ = 5.04 × 10⁻¹¹ M`.
Bromide is present while Process B runs (`0 < [Br⁻]`), so it cancels from
rubric equation (2.5). -/
theorem hbro2_processB_official (s : State)
    (hss : ProcessBSteadyState officialKineticParameters s)
    (hbromide : 0 < s .bromide)
    (hbromate : s .bromate = 0.06) (hproton : s .proton = 0.8) :
    s .hbro2 = 5.04e-11 := by
  have hk4 : officialKineticParameters.k4 ≠ 0 := by
    norm_num [officialKineticParameters]
  have hprotonpos : (0 : ℝ) < s .proton := by
    rw [hproton]; norm_num
  have h := hbro2_stationary_processB officialKineticParameters s hss hbromide
    hprotonpos hk4
  rw [hbromate, hproton] at h
  rw [h]
  norm_num [officialKineticParameters]

/-- **Subquestion 2.2 target.**  The two stationary molar concentrations of
HBrO₂ requested by IChO 2026 T2.2: `[HBrO₂]ₐ = 6.0 × 10⁻⁶ M` while Process A
runs and `[HBrO₂]ᵦ = 5.04 × 10⁻¹¹ M` while Process B runs.  The two values
belong to distinct states because the two processes alternate in time. -/
theorem icho_2026_t2_a2 (sA sB : State)
    (hssA : ProcessASteadyState officialKineticParameters sA)
    (hhbro2A : 0 < sA .hbro2)
    (hbromateA : sA .bromate = 0.06) (hprotonA : sA .proton = 0.8)
    (hssB : ProcessBSteadyState officialKineticParameters sB)
    (hbromideB : 0 < sB .bromide)
    (hbromateB : sB .bromate = 0.06) (hprotonB : sB .proton = 0.8) :
    sA .hbro2 = 6.0e-6 ∧ sB .hbro2 = 5.04e-11 := by
  exact ⟨hbro2_processA_official sA hssA hhbro2A hbromateA hprotonA,
    hbro2_processB_official sB hssB hbromideB hbromateB hprotonB⟩

end IChO2026.T2.A2
