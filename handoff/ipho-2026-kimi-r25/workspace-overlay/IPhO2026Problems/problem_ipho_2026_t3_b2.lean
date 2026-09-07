import Mathlib

/-!
# IPhO 2026 · Theory problem T3-B2 — "Chasing the absolute zero": adiabatic
temperature change of the paramagnetic torus (Pm-T)

Autoformalization of IPhO 2026 T3-B2 (source:
`reports/ipho_2026/problem_ipho_2026_t3_b2.source.json`; problem pages
`ipho_2026_source/image/T3_page-2.png` (T3-B header: ideal-gas/Pm-T comparison
table with the governing laws, fixed-volume note, fallback-work note) and
`ipho_2026_source/image/T3_page-3.png` (T3-B2 statement)).

## Physical scenario (shared context)

The setup is the paramagnetic torus ("Pm-T") of parts T3-A: a homogeneous
isotropic paramagnetic torus (mean radius `R`, tube radius `r ≪ R`, volume `V`,
cross-sectional area `A`) densely wound with `N` turns carrying the current
driven by an external voltage source; the fields `H⃗`, `B⃗`, `M⃗` are azimuthal
with (approximately) constant magnitudes `H`, `B`, `M` throughout the torus,
`M⃗ ∥ H⃗`, `B⃗ = μ₀ H⃗ + μ₀ M⃗`.

The T3-B header (page 12) gives the thermodynamic model of the Pm-T in a
comparison table with the ideal gas, with the explicit license "You may use the
equations provided in the table directly without proving them":

* state functions: `H`, `M` and temperature `T` (the volume `V` of the torus is
  constant, "so that there is no work due to pressure" — the only work is the
  magnetic work below);
* constants: `K`, `λ` (material constants, "given by the material in the
  torus") and the number of moles `n`;
* equation of state: `T·M·V = n·K·H`;
* heat capacity at constant `M`: `C_M = n·λ / T²`;
* internal energy in any process: `dU = C_M·dT`;
* magnetic work done on the material: `dW = μ₀·V·H·dM`;
* sign convention: work `W` and heat `Q` are positive when they flow into the
  Pm-T (so the first law reads `dU = đQ + dW`).

**Previous-part dependency (T3-A3).**  Policy
`derive_inline_from_problem_only_material`.  The T3-A3 result `dW = μ₀·V·H·dM`
is given verbatim in this subquestion's shared context ("the magnetic work on
the material is dW = mu_0*V*H*dM"), so it enters here directly as a governing
law (`MaterialWorkLawAlongProcess`); it coincides with the conclusion
`IPhO2026.T3A3.material_work` of the sibling T3-A3 file (no sibling file is
imported).  The printed T3-B fallback "if you did not find an answer for `dW`
in question T3-A3, you may use `dW = αVμ₀HdM` where `α` is a number" is realized
with `α = 1`, as stated in the shared context.

**Subquestion T3-B2 (page 13, 1.5 pts).**  "If the magnitude of `H⃗` changes
adiabatically from `H_i` to `H_f`, the temperature of the Pm-T changes from
`T_i` to `T_f`.  Write `ΔT = T_f − T_i` in terms of `μ₀`, `V`, `n`, `K`, `λ`,
`H_i`, `H_f`, and `T_i`."

## Process model (quasistatic adiabatic path)

Unlike the purely differential T3-A questions, T3-B2 asks for a *finite*
temperature change, so the model represents the quasistatic adiabatic process
explicitly as a path of states parametrized by `s : ℝ`, with the initial state
at `s = 0` and the final state at `s = 1`:

* `H s`, `M s`, `T s` — the state functions (field magnitude, magnetization
  magnitude, temperature); quasistaticity is encoded by the equation of state
  holding at *every* parameter value (`hEOS`);
* `U s` — the internal energy; `Q s`, `W s` — the *cumulative* heat absorbed
  and work received (into-system sign convention) between parameter `0` and
  `s`, so that `đQ`, `dW` of an infinitesimal step are `deriv Q s`, `deriv W s`;
* the given differential laws hold pointwise along the path
  (`InternalEnergyLawAlongProcess`, `MaterialWorkLawAlongProcess`,
  `FirstLawAlongProcess`), and adiabaticity is `deriv Q s = 0`
  (`AdiabaticAlongProcess`);
* regularity: `H`, `T` are `C¹` (needed for the separation-of-variables
  integration step), `M`, `U`, `Q`, `W` differentiable.

## Derivation (answer-blind, from the given laws only)

1. Energy balance (`adiabatic_energy_balance`): the first law with `đQ = 0`
   gives `dU = dW`; with `dU = C_M·dT` and `dW = μ₀·V·H·dM`:
   `(n·λ/T²)·dT = μ₀·V·H·dM` along the path.
2. Differentiating the equation of state
   (`equationOfState_deriv_along_path`): `T'·M·V + T·M'·V = n·K·H'`.
3. Eliminating `M` and `M'` between the two equations and the pointwise EOS
   (`adiabatic_differential_relation`): `(λ + μ₀·K·H²)·dT = μ₀·K·T·H·dH`.
   Note that `n` and `V` cancel at this step.
4. Separation of variables (`adiabatic_log_evolution`):
   `d(ln T) = d(½·ln(λ + μ₀·K·H²))`.
5. Integration from the initial to the final state
   (`adiabatic_log_balance_endpoints`, fundamental theorem of calculus):
   `ln T_f − ln T_i = ½·ln(λ + μ₀·K·H_f²) − ½·ln(λ + μ₀·K·H_i²)`.
6. Exponentiating (`adiabatic_temperature_change`):
   `T_f = T_i·√((λ + μ₀·K·H_f²)/(λ + μ₀·K·H_i²))`, hence
   `ΔT = T_i·(√((λ + μ₀·K·H_f²)/(λ + μ₀·K·H_i²)) − 1)`.

Every step uses only the problem-given laws and calculus; no official answer
was consulted.

## Current target (conclusion side only)

`adiabatic_temperature_change` / `adiabatic_DeltaT`: under the equation of
state, the internal-energy law, the first law, adiabaticity and the magnetic
work law along the quasistatic path, the temperature change of the Pm-T is

    ΔT = T_i · (√((λ + μ₀·K·H_f²)/(λ + μ₀·K·H_i²)) − 1),

in terms of the allowed variables `μ₀`, `V`, `n`, `K`, `λ`, `H_i`, `H_f`, `T_i`
— the derived closed form is independent of `V` and `n`, which cancel in the
derivation (they remain parameters of the governing laws).  The raw requested
combinations are recorded as `adiabaticFinalTempExpr` / `adiabaticDeltaTExpr`;
no hypothesis, premise or local definition mentions the closed form, and the
main target equation appears only on the conclusion side.  Branch coherence:
`H_i² < H_f²` (adiabatic magnetization) heats the Pm-T (`ΔT > 0`), and
`H_f² < H_i²` (adiabatic demagnetization) cools it (`ΔT < 0`) — the
magnetocaloric effect behind the problem title "chasing the absolute zero".

## Units

All quantities are real numbers carrying SI units, recorded per declaration:
`T`, `T_i`, `T_f`, `ΔT` in K; `H`, `M`, `H_i`, `H_f` in A/m; `V` in m³;
`n` in mol; `μ₀` in N/A² (H/m); the material constants `K` in K·m³/mol
(from `T·M·V = n·K·H`) and `λ` in J·K/mol (from `C_M = nλ/T²`, J/K);
`U`, `Q`, `W` in J.  Consistency checks: `μ₀·V·H·dM` has units
(N/A²)·m³·(A/m)·(A/m) = N·m = J ✓; `μ₀·K·H²` has units
(N/A²)·(K·m³/mol)·(A²/m²) = N·K·m/mol = J·K/mol, matching `λ` ✓, so the square
root is a dimensionless ratio and `ΔT` is in K ✓.

## Grounding (LeanExplore, packages Mathlib + Physlib)

LeanExplore finds no ready-made API for this paramagnetic thermodynamic system:
Physlib's `Physlib.Thermodynamics.IdealGas.Basic` (`adiabatic_relation_log`,
`adiabatic_relation_UaUbVaVb`) axiomatizes the *ideal-gas* entropy
`S = c·N·R·log(U/U₀) + N·R·log(V/V₀)` — precisely the other column of the
problem's comparison table and a near miss for the Pm-T laws
(`T·M·V = n·K·H`, `C_M = nλ/T²`, `dW = μ₀VH dM`), which are therefore kept as
faithful local governing-law predicates.  The calculus infrastructure is
grounded in Mathlib: `deriv`, `deriv_fun_mul`, `deriv_mul_const_field`,
`deriv_const_mul_field`, `deriv.log`, `Real.deriv_log`, `ContDiff ℝ 1` with
`ContDiff.differentiable_one`, the fundamental theorem of calculus
`intervalIntegral.integral_deriv_eq_sub`, and the real logarithm/square-root
lemmas `Real.log_div`, `Real.log_sqrt`, `Real.exp_log`, `Real.log_injOn_pos`.
-/

namespace IPhO2026.T3B2

/-! ## Energy-transfer sign convention (shared context) -/

/-- Sign convention for work (given): a signed work value `W` represents energy
flowing *into* the paramagnetic torus exactly when it is positive. -/
def WorkFlowsIntoSystem (W : ℝ) : Prop := 0 < W

/-- Sign convention for heat (given): a signed heat value `Q` represents energy
flowing *into* the paramagnetic torus exactly when it is positive.  With both
conventions the first law reads `dU = đQ + dW`
(`FirstLawAlongProcess`). -/
def HeatFlowsIntoSystem (Q : ℝ) : Prop := 0 < Q

/-! ## Governing laws (given by the T3-B comparison table / shared context) -/

/-- **Equation of state of the paramagnetic material** (given governing law,
T3-B table): `T·M·V = n·K·H`, relating the temperature `T` (K), the
magnetization magnitude `M` (A/m), the (fixed) torus volume `V` (m³), the mole
count `n` (mol), the material constant `K` (K·m³/mol) and the `H`-field
magnitude `H` (A/m).  In T3-B2 it holds at every state of the quasistatic
adiabatic process. -/
def EquationOfState (T M V n K H : ℝ) : Prop := T * M * V = n * K * H

/-- Heat capacity at constant magnetization (given expression, T3-B table):
`C_M = n·λ / T²`, with `λ` the material constant (J·K/mol).  Units: J/K.
This records the given formula; the internal-energy law built from it is
`InternalEnergyLawAlongProcess`. -/
noncomputable def heatCapacityAtConstM (n lam T : ℝ) : ℝ := n * lam / T ^ 2

/-- **Internal-energy law** (given governing law, T3-B table: "Internal energy
`U` in any process satisfies `dU = C_M·dT`"): along any process of the Pm-T,
the rate of change of the internal energy equals the heat capacity at constant
`M` times the rate of change of temperature.  Note that `C_M` is evaluated at
the instantaneous temperature, so the right-hand side involves `T s` — the law
is *not* a constant-coefficient one.  Units: each side in J per unit
process parameter. -/
def InternalEnergyLawAlongProcess (n lam : ℝ) (U T : ℝ → ℝ) : Prop :=
  ∀ s, deriv U s = heatCapacityAtConstM n lam (T s) * deriv T s

/-- **Magnetic work done on the paramagnetic material** (given governing law,
shared context of T3-B2 — the T3-A3 result, cf. `IPhO2026.T3A3.material_work`;
the volume `V` is fixed, so there is no pressure work): the infinitesimal work
done *on* the material when the magnetization changes is `dW = μ₀·V·H·dM`;
along a process the cumulative received work `W s` therefore satisfies
`deriv W s = μ₀·V·H s·deriv M s`.  Units: J per unit process parameter. -/
def MaterialWorkLawAlongProcess (μ₀ V : ℝ) (W H M : ℝ → ℝ) : Prop :=
  ∀ s, deriv W s = μ₀ * V * H s * deriv M s

/-- **First law of thermodynamics for the Pm-T** (governing law, with the given
sign convention that work and heat entering the torus are positive): the
internal energy change of the material equals the heat absorbed plus the work
received, `dU = đQ + dW`; along a process,
`deriv U s = deriv Q s + deriv W s` for the cumulative `Q`, `W`. -/
def FirstLawAlongProcess (U Q W : ℝ → ℝ) : Prop :=
  ∀ s, deriv U s = deriv Q s + deriv W s

/-- **Adiabatic process** (the T3-B2 process condition): no heat is exchanged
with the environment, `đQ = 0` along the whole process, i.e. the cumulative
absorbed heat is constant (`deriv Q s = 0` at every parameter value). -/
def AdiabaticAlongProcess (Q : ℝ → ℝ) : Prop := ∀ s, deriv Q s = 0

/-! ## Bridge lemmas (proofs deferred to the prover stage) -/

/-- **Adiabatic energy balance** (bridge 1): the first law `dU = đQ + dW` with
the adiabatic condition `đQ = 0` collapses to `dU = dW`; substituting the
internal-energy law `dU = C_M·dT` and the magnetic work law `dW = μ₀·V·H·dM`
gives the energy balance of the adiabatic Pm-T process,
`(n·λ/T²)·dT = μ₀·V·H·dM`, at every point of the path. -/
theorem adiabatic_energy_balance {μ₀ V n lam : ℝ} {H M T U Q W : ℝ → ℝ}
    (hULaw : InternalEnergyLawAlongProcess n lam U T)
    (hFirstLaw : FirstLawAlongProcess U Q W)
    (hAd : AdiabaticAlongProcess Q)
    (hWork : MaterialWorkLawAlongProcess μ₀ V W H M) :
    ∀ s, heatCapacityAtConstM n lam (T s) * deriv T s = μ₀ * V * H s * deriv M s := by
  intro s
  -- First law with `đQ = 0`: `deriv U s = deriv W s`.
  have h2 : deriv U s = deriv Q s + deriv W s := hFirstLaw s
  rw [hAd s, zero_add, hWork s] at h2
  -- Substitute `dU = C_M dT`.
  rw [hULaw s] at h2
  exact h2

/-- **Differentiated equation of state** (bridge 2): the equation of state
`T·M·V = n·K·H` holds at every parameter value, with `V`, `n`, `K` constant, so
the two sides are equal as functions of the process parameter and their
derivatives agree: `T'·M·V + T·M'·V = n·K·H'`.
Proof route: `funext` the pointwise EOS to an equality of functions, apply
`deriv` at `s` (`congr_arg`), evaluate with `deriv_mul_const_field`,
`deriv_fun_mul` and `deriv_const_mul_field`, then `linear_combination`. -/
theorem equationOfState_deriv_along_path {V n K : ℝ} {H M T : ℝ → ℝ}
    (hT : Differentiable ℝ T) (hM : Differentiable ℝ M)
    (hEOS : ∀ s, EquationOfState (T s) (M s) V n K (H s)) :
    ∀ s, deriv T s * M s * V + T s * deriv M s * V = n * K * deriv H s := by
  intro s
  have hEq : (fun s => T s * M s * V) = fun s => n * K * H s := funext fun s => hEOS s
  have h := congr_arg (fun f => deriv f s) hEq
  rw [deriv_mul_const_field V, deriv_fun_mul (hT s) (hM s),
    deriv_const_mul_field (n * K)] at h
  linear_combination h

/-- **Adiabatic differential relation** (bridge 3): eliminating the
magnetization and its rate between the energy balance, the differentiated
equation of state and the pointwise EOS gives the separated differential
relation of the adiabatic Pm-T process,
`(λ + μ₀·K·H²)·dT = μ₀·K·T·H·dH`.
Proof route: at each `s`, solve the differentiated EOS for `deriv M s`
(needs `T s ≠ 0`, `V ≠ 0`), substitute into the energy balance, eliminate the
remaining `M s` by the pointwise EOS (needs `T s ≠ 0`, `V ≠ 0`), and clear the
factors `T s` and `n` (needs `n ≠ 0`): ring arithmetic over the field of real
numbers. -/
theorem adiabatic_differential_relation {μ₀ V n K lam : ℝ} {H M T : ℝ → ℝ}
    (hV : 0 < V) (hn : 0 < n) (hTpos : ∀ s, 0 < T s)
    (hEOS : ∀ s, EquationOfState (T s) (M s) V n K (H s))
    (hBalance : ∀ s, heatCapacityAtConstM n lam (T s) * deriv T s =
      μ₀ * V * H s * deriv M s)
    (hEOSder : ∀ s, deriv T s * M s * V + T s * deriv M s * V = n * K * deriv H s) :
    ∀ s, (lam + μ₀ * K * (H s) ^ 2) * deriv T s = μ₀ * K * T s * H s * deriv H s := by
  intro s
  -- `hV` is part of the physical model (positive fixed volume); the volume
  -- cancels in the elimination below, so it is not needed arithmetically.
  have := hV
  have hTs0 : T s ≠ 0 := ne_of_gt (hTpos s)
  have hn0 : n ≠ 0 := ne_of_gt hn
  have hE : T s * M s * V = n * K * H s := hEOS s
  have hB := hBalance s
  have hD := hEOSder s
  -- Expose the heat-capacity formula and clear its denominator `T s ^ 2`.
  simp only [heatCapacityAtConstM] at hB
  rw [div_mul_eq_mul_div, div_eq_iff (pow_ne_zero 2 hTs0)] at hB
  -- Multiply the goal by `n` and close by ring arithmetic over the three laws.
  have key : n * ((lam + μ₀ * K * (H s) ^ 2) * deriv T s - μ₀ * K * T s * H s * deriv H s)
      = 0 := by
    linear_combination hB + μ₀ * H s * T s * hD - μ₀ * H s * deriv T s * hE
  rcases mul_eq_zero.mp key with hnz | hzero
  · exact absurd hnz hn0
  · exact sub_eq_zero.mp hzero

/-- Positivity of the adiabatic denominator `λ + μ₀·K·H²` (used by the
separation-of-variables step): for positive material constants and vacuum
permeability it is a sum of a positive and a nonnegative term. -/
theorem adiabatic_denominator_pos {μ₀ K lam H : ℝ}
    (hμ₀ : 0 < μ₀) (hK : 0 < K) (hlam : 0 < lam) :
    0 < lam + μ₀ * K * H ^ 2 := by
  have h1 : (0 : ℝ) ≤ μ₀ * K * H ^ 2 :=
    mul_nonneg (mul_nonneg hμ₀.le hK.le) (sq_nonneg H)
  linarith

/-- **Separated (logarithmic) form of the adiabatic relation** (bridge 4):
the differential relation `(λ + μ₀·K·H²)·dT = μ₀·K·T·H·dH` divided by
`T·(λ + μ₀·K·H²)` (both positive along the path) reads
`dT/T = μ₀·K·H·dH/(λ + μ₀·K·H²)`, i.e. the exact-derivative identity
`d(ln T)/ds = d(½·ln(λ + μ₀·K·H²))/ds`.
Proof route: chain rule on both sides (`deriv.log`, `Real.deriv_log`;
the inner derivative of `λ + μ₀·K·H²` is `2·μ₀·K·H·H'` via
`deriv_const_mul_field`, `deriv_pow`/square rules), then divide the given
differential relation by `T s · (λ + μ₀·K·(H s)²) ≠ 0`. -/
theorem adiabatic_log_evolution {μ₀ K lam : ℝ} {H T : ℝ → ℝ}
    (hμ₀ : 0 < μ₀) (hK : 0 < K) (hlam : 0 < lam)
    (hT : Differentiable ℝ T) (hH : Differentiable ℝ H)
    (hTpos : ∀ s, 0 < T s)
    (hRel : ∀ s, (lam + μ₀ * K * (H s) ^ 2) * deriv T s =
      μ₀ * K * T s * H s * deriv H s) :
    ∀ s, deriv (fun s => Real.log (T s)) s =
      deriv (fun s => (1 / 2) * Real.log (lam + μ₀ * K * (H s) ^ 2)) s := by
  intro s
  have hTs0 : T s ≠ 0 := ne_of_gt (hTpos s)
  have hD : 0 < lam + μ₀ * K * (H s) ^ 2 := adiabatic_denominator_pos hμ₀ hK hlam
  have hD0 : lam + μ₀ * K * (H s) ^ 2 ≠ 0 := ne_of_gt hD
  -- Left-hand side: `d(log T)/ds = T'/T` by the chain rule.
  have hL : deriv (fun s => Real.log (T s)) s = deriv T s / T s :=
    ((hT s).hasDerivAt.log hTs0).deriv
  -- Inner function `λ + μ₀·K·H²`: derivative `μ₀·K·(H'·H + H·H') = 2 μ₀ K H H'`.
  have hsq : HasDerivAt (fun s => (H s) ^ 2) (deriv H s * H s + H s * deriv H s) s := by
    have hmul : HasDerivAt (fun s => H s * H s) (deriv H s * H s + H s * deriv H s) s :=
      (hH s).hasDerivAt.mul (hH s).hasDerivAt
    simpa only [pow_two] using hmul
  have hinner : HasDerivAt (fun s => lam + μ₀ * K * (H s) ^ 2)
      (μ₀ * K * (deriv H s * H s + H s * deriv H s)) s :=
    (hsq.const_mul (μ₀ * K)).const_add lam
  -- Right-hand side: chain rule and the constant factor `1/2`.
  have hR : deriv (fun s => (1 / 2) * Real.log (lam + μ₀ * K * (H s) ^ 2)) s =
      (1 / 2) * (μ₀ * K * (deriv H s * H s + H s * deriv H s) /
        (lam + μ₀ * K * (H s) ^ 2)) :=
    ((hinner.log hD0).const_mul (1 / 2 : ℝ)).deriv
  rw [hL, hR, ← mul_div_assoc, div_eq_div_iff hTs0 hD0]
  -- Cleared of denominators, this is the given differential relation.
  linear_combination hRel s

/-- **Integrated adiabatic balance at the endpoints** (bridge 5): the
separated relation, integrated along the process from the initial state
(`s = 0`) to the final state (`s = 1`), gives
`ln(T 1) − ln(T 0) = ½·ln(λ + μ₀·K·(H 1)²) − ½·ln(λ + μ₀·K·(H 0)²)`.
Proof route: both sides of `adiabatic_log_evolution` are derivatives of `C¹`
functions (compositions of `Real.log` with the positive `C¹` functions `T` and
`λ + μ₀·K·H²`); apply the fundamental theorem of calculus
(`intervalIntegral.integral_deriv_eq_sub`) to both on `[0, 1]` — the
derivatives are continuous, hence interval-integrable — and equate the two
evaluations of the common integral. -/
theorem adiabatic_log_balance_endpoints {μ₀ K lam : ℝ} {H T : ℝ → ℝ}
    (hH : ContDiff ℝ 1 H) (hT : ContDiff ℝ 1 T)
    (hTpos : ∀ s, 0 < T s)
    (hDpos : ∀ s, 0 < lam + μ₀ * K * (H s) ^ 2)
    (hLog : ∀ s, deriv (fun s => Real.log (T s)) s =
      deriv (fun s => (1 / 2) * Real.log (lam + μ₀ * K * (H s) ^ 2)) s) :
    Real.log (T 1) - Real.log (T 0) =
      (1 / 2) * Real.log (lam + μ₀ * K * (H 1) ^ 2) -
        (1 / 2) * Real.log (lam + μ₀ * K * (H 0) ^ 2) := by
  have hTd : Differentiable ℝ T := hT.differentiable_one
  have hHd : Differentiable ℝ H := hH.differentiable_one
  -- The two sides of `hLog` are derivatives of everywhere-differentiable
  -- functions of the process parameter.
  have hfdiff : Differentiable ℝ (fun s => Real.log (T s)) := fun s =>
    (hTd s).log (ne_of_gt (hTpos s))
  have hgdiff : Differentiable ℝ (fun s => (1 / 2) * Real.log (lam + μ₀ * K * (H s) ^ 2)) :=
    fun s =>
      (((hHd s).pow 2 |>.const_mul (μ₀ * K)).const_add lam |>.log
        (ne_of_gt (hDpos s))).const_mul (1 / 2)
  -- Their difference has derivative `0` everywhere, hence is constant.
  have hdiff : Differentiable ℝ
      (fun s => Real.log (T s) - (1 / 2) * Real.log (lam + μ₀ * K * (H s) ^ 2)) :=
    hfdiff.sub hgdiff
  have hderiv0 : ∀ s,
      deriv (fun s => Real.log (T s) - (1 / 2) * Real.log (lam + μ₀ * K * (H s) ^ 2)) s = 0 := by
    intro s
    rw [deriv_fun_sub (hfdiff s) (hgdiff s), hLog s, sub_self]
  have hconst := is_const_of_deriv_eq_zero hdiff hderiv0 1 0
  linarith

/-! ## Raw requested expressions -/

/-- Raw end-to-end expression for the final temperature (derived candidate):
`T_i·√((λ + μ₀·K·H_f²)/(λ + μ₀·K·H_i²))`, in (a subset of) the allowed
variables `μ₀`, `V`, `n`, `K`, `λ`, `H_i`, `H_f`, `T_i` — the volume `V` and
the mole count `n` cancel in the derivation, so the closed form does not depend
on them.  The definition only records the requested combination; that the
actual final temperature equals it is the content of
`adiabatic_temperature_change`.  Dimensionless ratio under the square root;
the result is in K. -/
noncomputable def adiabaticFinalTempExpr (μ₀ K lam H_i H_f T_i : ℝ) : ℝ :=
  T_i * Real.sqrt ((lam + μ₀ * K * H_f ^ 2) / (lam + μ₀ * K * H_i ^ 2))

/-- Raw end-to-end expression requested by T3-B2 (derived candidate): the
temperature change
`ΔT = T_i·(√((λ + μ₀·K·H_f²)/(λ + μ₀·K·H_i²)) − 1)`.  The definition only
records the requested combination; that the actual `T_f − T_i` equals it is the
content of `adiabatic_DeltaT`.  Units: K. -/
noncomputable def adiabaticDeltaTExpr (μ₀ K lam H_i H_f T_i : ℝ) : ℝ :=
  T_i * (Real.sqrt ((lam + μ₀ * K * H_f ^ 2) / (lam + μ₀ * K * H_i ^ 2)) - 1)

/-! ## Main targets (T3-B2) -/

/-- **T3-B2 main target.**  For the paramagnetic torus undergoing a quasistatic
adiabatic change of the field magnitude from `H_i` to `H_f` (initial
temperature `T_i`), starting and ending on the equation of state, the final
temperature of the Pm-T is

    `T_f = T_i · √((λ + μ₀·K·H_f²)/(λ + μ₀·K·H_i²))`,

in terms of the vacuum permeability `μ₀`, the material constants `K`, `λ`, the
endpoint field magnitudes `H_i`, `H_f` and the initial temperature `T_i` (the
allowed-variable list additionally contains `V` and `n`, which cancel in the
derivation).

Derivation chain: `adiabatic_energy_balance` (first law, adiabaticity, energy
and work laws), `equationOfState_deriv_along_path` (differentiated EOS),
`adiabatic_differential_relation` (elimination of `M`),
`adiabatic_log_evolution` (separation of variables),
`adiabatic_log_balance_endpoints` (fundamental theorem of calculus over the
process); rewriting the endpoints by `H 0 = H_i`, `H 1 = H_f`, `T 0 = T_i`,
`T 1 = T_f` gives `log T_f − log T_i = ½·log(D_f/D_i)` with
`D = λ + μ₀·K·H²`; exponentiating via `Real.log_injOn_pos`, `Real.log_sqrt`,
`Real.exp_log` (all arguments positive by `hTpos`, `adiabatic_denominator_pos`)
yields the closed form. -/
theorem adiabatic_temperature_change
    {μ₀ V n K lam H_i H_f T_i T_f : ℝ}
    (hμ₀ : 0 < μ₀) (hV : 0 < V) (hn : 0 < n) (hK : 0 < K) (hlam : 0 < lam)
    {H M T U Q W : ℝ → ℝ}
    (hH : ContDiff ℝ 1 H) (hM : Differentiable ℝ M) (hT : ContDiff ℝ 1 T)
    (hU : Differentiable ℝ U) (hQ : Differentiable ℝ Q) (hW : Differentiable ℝ W)
    (hTpos : ∀ s, 0 < T s)
    (hEOS : ∀ s, EquationOfState (T s) (M s) V n K (H s))
    (hULaw : InternalEnergyLawAlongProcess n lam U T)
    (hFirstLaw : FirstLawAlongProcess U Q W)
    (hAd : AdiabaticAlongProcess Q)
    (hWork : MaterialWorkLawAlongProcess μ₀ V W H M)
    (hH0 : H 0 = H_i) (hH1 : H 1 = H_f)
    (hT0 : T 0 = T_i) (hT1 : T 1 = T_f) :
    T_f = T_i * Real.sqrt ((lam + μ₀ * K * H_f ^ 2) / (lam + μ₀ * K * H_i ^ 2)) := by
  -- Bridge 1: adiabatic energy balance `(n·λ/T²)·dT = μ₀·V·H·dM`.
  -- The regularity hypotheses `hU`, `hQ`, `hW` belong to the process model; the
  -- laws `hULaw`, `hFirstLaw`, `hAd`, `hWork` already carry `U`, `Q`, `W`.
  have := hU; have := hQ; have := hW
  have hBalance := adiabatic_energy_balance hULaw hFirstLaw hAd hWork
  -- Bridge 2: differentiated equation of state.
  have hTd : Differentiable ℝ T := hT.differentiable_one
  have hHd : Differentiable ℝ H := hH.differentiable_one
  have hEOSder := equationOfState_deriv_along_path hTd hM hEOS
  -- Bridge 3: eliminate `M` and its rate.
  have hRel := adiabatic_differential_relation hV hn hTpos hEOS hBalance hEOSder
  -- Bridge 4: separated (logarithmic) form.
  have hLog := adiabatic_log_evolution hμ₀ hK hlam hTd hHd hTpos hRel
  -- Bridge 5: integrate to the endpoints `s = 0` and `s = 1`.
  have hDpos : ∀ s, 0 < lam + μ₀ * K * (H s) ^ 2 := fun s =>
    adiabatic_denominator_pos hμ₀ hK hlam
  have hEnds := adiabatic_log_balance_endpoints hH hT hTpos hDpos hLog
  rw [hH0, hH1, hT0, hT1] at hEnds
  -- Positivity of the quantities entering the logarithms.
  have hTi : 0 < T_i := hT0 ▸ hTpos 0
  have hTf : 0 < T_f := hT1 ▸ hTpos 1
  have hDi : 0 < lam + μ₀ * K * H_i ^ 2 := adiabatic_denominator_pos hμ₀ hK hlam
  have hDf : 0 < lam + μ₀ * K * H_f ^ 2 := adiabatic_denominator_pos hμ₀ hK hlam
  have hratio : 0 < (lam + μ₀ * K * H_f ^ 2) / (lam + μ₀ * K * H_i ^ 2) := div_pos hDf hDi
  have hsqrt : 0 < Real.sqrt ((lam + μ₀ * K * H_f ^ 2) / (lam + μ₀ * K * H_i ^ 2)) :=
    Real.sqrt_pos.2 hratio
  -- Exponentiate: compare `log` of both sides and use injectivity on `ℝ⁺`.
  have hlogeq : Real.log T_f =
      Real.log (T_i * Real.sqrt ((lam + μ₀ * K * H_f ^ 2) / (lam + μ₀ * K * H_i ^ 2))) := by
    rw [Real.log_mul (ne_of_gt hTi) (ne_of_gt hsqrt), Real.log_sqrt hratio.le,
      Real.log_div (ne_of_gt hDf) (ne_of_gt hDi)]
    linarith [hEnds]
  exact Real.log_injOn_pos (Set.mem_Ioi.2 hTf) (Set.mem_Ioi.2 (mul_pos hTi hsqrt)) hlogeq

/-- Packaged form of the main target: the final temperature equals the raw
requested expression `adiabaticFinalTempExpr`.
Proof route: `adiabaticFinalTempExpr` unfolds definitionally to the closed
form; apply `adiabatic_temperature_change`. -/
theorem adiabatic_final_temp_eq_expr
    {μ₀ V n K lam H_i H_f T_i T_f : ℝ}
    (hμ₀ : 0 < μ₀) (hV : 0 < V) (hn : 0 < n) (hK : 0 < K) (hlam : 0 < lam)
    {H M T U Q W : ℝ → ℝ}
    (hH : ContDiff ℝ 1 H) (hM : Differentiable ℝ M) (hT : ContDiff ℝ 1 T)
    (hU : Differentiable ℝ U) (hQ : Differentiable ℝ Q) (hW : Differentiable ℝ W)
    (hTpos : ∀ s, 0 < T s)
    (hEOS : ∀ s, EquationOfState (T s) (M s) V n K (H s))
    (hULaw : InternalEnergyLawAlongProcess n lam U T)
    (hFirstLaw : FirstLawAlongProcess U Q W)
    (hAd : AdiabaticAlongProcess Q)
    (hWork : MaterialWorkLawAlongProcess μ₀ V W H M)
    (hH0 : H 0 = H_i) (hH1 : H 1 = H_f)
    (hT0 : T 0 = T_i) (hT1 : T 1 = T_f) :
    T_f = adiabaticFinalTempExpr μ₀ K lam H_i H_f T_i := by
  show T_f = T_i * Real.sqrt ((lam + μ₀ * K * H_f ^ 2) / (lam + μ₀ * K * H_i ^ 2))
  exact adiabatic_temperature_change hμ₀ hV hn hK hlam hH hM hT hU hQ hW hTpos hEOS hULaw
    hFirstLaw hAd hWork hH0 hH1 hT0 hT1

/-- **T3-B2, the requested `ΔT` form.**  Under the same adiabatic-process
model, the temperature change of the Pm-T is

    `ΔT = T_f − T_i = T_i · (√((λ + μ₀·K·H_f²)/(λ + μ₀·K·H_i²)) − 1)`.

Proof route: rewrite `T_f` by `adiabatic_temperature_change`; the remaining
identity `T_i·√r − T_i = T_i·(√r − 1)` is `ring`. -/
theorem adiabatic_DeltaT
    {μ₀ V n K lam H_i H_f T_i T_f : ℝ}
    (hμ₀ : 0 < μ₀) (hV : 0 < V) (hn : 0 < n) (hK : 0 < K) (hlam : 0 < lam)
    {H M T U Q W : ℝ → ℝ}
    (hH : ContDiff ℝ 1 H) (hM : Differentiable ℝ M) (hT : ContDiff ℝ 1 T)
    (hU : Differentiable ℝ U) (hQ : Differentiable ℝ Q) (hW : Differentiable ℝ W)
    (hTpos : ∀ s, 0 < T s)
    (hEOS : ∀ s, EquationOfState (T s) (M s) V n K (H s))
    (hULaw : InternalEnergyLawAlongProcess n lam U T)
    (hFirstLaw : FirstLawAlongProcess U Q W)
    (hAd : AdiabaticAlongProcess Q)
    (hWork : MaterialWorkLawAlongProcess μ₀ V W H M)
    (hH0 : H 0 = H_i) (hH1 : H 1 = H_f)
    (hT0 : T 0 = T_i) (hT1 : T 1 = T_f) :
    T_f - T_i =
      T_i * (Real.sqrt ((lam + μ₀ * K * H_f ^ 2) / (lam + μ₀ * K * H_i ^ 2)) - 1) := by
  rw [adiabatic_temperature_change hμ₀ hV hn hK hlam hH hM hT hU hQ hW hTpos hEOS hULaw
    hFirstLaw hAd hWork hH0 hH1 hT0 hT1]
  ring

/-- Packaged form of the requested `ΔT`: the temperature change equals the raw
requested expression `adiabaticDeltaTExpr`. -/
theorem adiabatic_DeltaT_eq_expr
    {μ₀ V n K lam H_i H_f T_i T_f : ℝ}
    (hμ₀ : 0 < μ₀) (hV : 0 < V) (hn : 0 < n) (hK : 0 < K) (hlam : 0 < lam)
    {H M T U Q W : ℝ → ℝ}
    (hH : ContDiff ℝ 1 H) (hM : Differentiable ℝ M) (hT : ContDiff ℝ 1 T)
    (hU : Differentiable ℝ U) (hQ : Differentiable ℝ Q) (hW : Differentiable ℝ W)
    (hTpos : ∀ s, 0 < T s)
    (hEOS : ∀ s, EquationOfState (T s) (M s) V n K (H s))
    (hULaw : InternalEnergyLawAlongProcess n lam U T)
    (hFirstLaw : FirstLawAlongProcess U Q W)
    (hAd : AdiabaticAlongProcess Q)
    (hWork : MaterialWorkLawAlongProcess μ₀ V W H M)
    (hH0 : H 0 = H_i) (hH1 : H 1 = H_f)
    (hT0 : T 0 = T_i) (hT1 : T 1 = T_f) :
    T_f - T_i = adiabaticDeltaTExpr μ₀ K lam H_i H_f T_i := by
  show T_f - T_i =
    T_i * (Real.sqrt ((lam + μ₀ * K * H_f ^ 2) / (lam + μ₀ * K * H_i ^ 2)) - 1)
  exact adiabatic_DeltaT hμ₀ hV hn hK hlam hH hM hT hU hQ hW hTpos hEOS hULaw
    hFirstLaw hAd hWork hH0 hH1 hT0 hT1

/-- **Adiabatic state invariant** (packaged equivalent form): along the
quasistatic adiabats of the Pm-T, `T/√(λ + μ₀·K·H²)` is constant; squared and
cross-multiplied, the endpoint states satisfy
`T_f²/(λ + μ₀·K·H_f²) = T_i²/(λ + μ₀·K·H_i²)`.  This is the adiabat equation of
the Pm-T (the T3-C Carnot-cycle legs 2→3 and 4→1 run along such adiabats).
Proof route: from `adiabatic_temperature_change`,
`T_f² = T_i²·(D_f/D_i)` by squaring (`Real.sq_sqrt`, ratio nonnegative), then
division algebra with `D_i, D_f > 0` (`adiabatic_denominator_pos`). -/
theorem adiabatic_state_invariant
    {μ₀ V n K lam H_i H_f T_i T_f : ℝ}
    (hμ₀ : 0 < μ₀) (hV : 0 < V) (hn : 0 < n) (hK : 0 < K) (hlam : 0 < lam)
    {H M T U Q W : ℝ → ℝ}
    (hH : ContDiff ℝ 1 H) (hM : Differentiable ℝ M) (hT : ContDiff ℝ 1 T)
    (hU : Differentiable ℝ U) (hQ : Differentiable ℝ Q) (hW : Differentiable ℝ W)
    (hTpos : ∀ s, 0 < T s)
    (hEOS : ∀ s, EquationOfState (T s) (M s) V n K (H s))
    (hULaw : InternalEnergyLawAlongProcess n lam U T)
    (hFirstLaw : FirstLawAlongProcess U Q W)
    (hAd : AdiabaticAlongProcess Q)
    (hWork : MaterialWorkLawAlongProcess μ₀ V W H M)
    (hH0 : H 0 = H_i) (hH1 : H 1 = H_f)
    (hT0 : T 0 = T_i) (hT1 : T 1 = T_f) :
    T_f ^ 2 / (lam + μ₀ * K * H_f ^ 2) = T_i ^ 2 / (lam + μ₀ * K * H_i ^ 2) := by
  have hmain := adiabatic_temperature_change hμ₀ hV hn hK hlam hH hM hT hU hQ hW hTpos hEOS
    hULaw hFirstLaw hAd hWork hH0 hH1 hT0 hT1
  have hDi : 0 < lam + μ₀ * K * H_i ^ 2 := adiabatic_denominator_pos hμ₀ hK hlam
  have hDf : 0 < lam + μ₀ * K * H_f ^ 2 := adiabatic_denominator_pos hμ₀ hK hlam
  have hDi0 : (lam + μ₀ * K * H_i ^ 2) ≠ 0 := ne_of_gt hDi
  have hDf0 : (lam + μ₀ * K * H_f ^ 2) ≠ 0 := ne_of_gt hDf
  rw [hmain, mul_pow, Real.sq_sqrt (div_nonneg hDf.le hDi.le)]
  field_simp

/-! ## Branch coherence (sign of `ΔT`) -/

/-- Sign of the raw requested expression, magnetization branch: for positive
constants and positive initial temperature, `ΔT` is positive exactly when the
squared field magnitude increases.  (Since `H` is a magnitude, physically
`0 ≤ H_i < H_f` implies `H_i² < H_f²`; the squared form is sign-free.)
Proof route: unfold `adiabaticDeltaTExpr`; with
`D_i, D_f > 0` (`adiabatic_denominator_pos`), `H_i² < H_f²` iff
`1 < D_f/D_i` iff `1 < √(D_f/D_i)` (`Real.one_lt_sqrt`,
`Real.sqrt_lt_sqrt`-type monotonicity), then multiply by `T_i > 0`. -/
theorem adiabaticDeltaTExpr_pos_iff {μ₀ K lam H_i H_f T_i : ℝ}
    (hμ₀ : 0 < μ₀) (hK : 0 < K) (hlam : 0 < lam) (hTi : 0 < T_i) :
    0 < adiabaticDeltaTExpr μ₀ K lam H_i H_f T_i ↔ H_i ^ 2 < H_f ^ 2 := by
  have hDi : 0 < lam + μ₀ * K * H_i ^ 2 := adiabatic_denominator_pos hμ₀ hK hlam
  have hμ₀K : 0 < μ₀ * K := mul_pos hμ₀ hK
  show 0 < T_i * (Real.sqrt ((lam + μ₀ * K * H_f ^ 2) / (lam + μ₀ * K * H_i ^ 2)) - 1) ↔
    H_i ^ 2 < H_f ^ 2
  rw [mul_pos_iff_of_pos_left hTi, sub_pos, Real.lt_sqrt zero_le_one, one_pow,
    one_lt_div hDi, add_lt_add_iff_left lam, mul_lt_mul_iff_right₀ hμ₀K]

/-- Sign of the raw requested expression, demagnetization branch: `ΔT` is
negative exactly when the squared field magnitude decreases.
Proof route: as in `adiabaticDeltaTExpr_pos_iff` with the reversed
inequalities (`Real.sqrt_lt_sqrt`). -/
theorem adiabaticDeltaTExpr_neg_iff {μ₀ K lam H_i H_f T_i : ℝ}
    (hμ₀ : 0 < μ₀) (hK : 0 < K) (hlam : 0 < lam) (hTi : 0 < T_i) :
    adiabaticDeltaTExpr μ₀ K lam H_i H_f T_i < 0 ↔ H_f ^ 2 < H_i ^ 2 := by
  have hDi : 0 < lam + μ₀ * K * H_i ^ 2 := adiabatic_denominator_pos hμ₀ hK hlam
  have hμ₀K : 0 < μ₀ * K := mul_pos hμ₀ hK
  -- With `T_i > 0`, the sign of the product is the sign of the second factor.
  have hmulneg : ∀ X : ℝ, T_i * X < 0 ↔ X < 0 := fun X => by
    have h := mul_lt_mul_iff_right₀ hTi (a := T_i) (b := X) (c := 0)
    simpa using h
  show T_i * (Real.sqrt ((lam + μ₀ * K * H_f ^ 2) / (lam + μ₀ * K * H_i ^ 2)) - 1) < 0 ↔
    H_f ^ 2 < H_i ^ 2
  rw [hmulneg, sub_neg, Real.sqrt_lt' one_pos, one_pow, div_lt_one hDi,
    add_lt_add_iff_left lam, mul_lt_mul_iff_right₀ hμ₀K]

/-- **Adiabatic magnetization heats the Pm-T**: on the branch `H_i² < H_f²`
(the field magnitude grows along the process), the adiabatic temperature change
is positive, `0 < T_f − T_i`.
Proof route: `adiabatic_DeltaT_eq_expr` identifies `T_f − T_i` with
`adiabaticDeltaTExpr`; apply `adiabaticDeltaTExpr_pos_iff` (its side conditions
hold from the model's positivity hypotheses, and `0 < T_i` from `hTpos 0` via
`hT0`). -/
theorem adiabatic_magnetization_heats
    {μ₀ V n K lam H_i H_f T_i T_f : ℝ}
    (hμ₀ : 0 < μ₀) (hV : 0 < V) (hn : 0 < n) (hK : 0 < K) (hlam : 0 < lam)
    {H M T U Q W : ℝ → ℝ}
    (hH : ContDiff ℝ 1 H) (hM : Differentiable ℝ M) (hT : ContDiff ℝ 1 T)
    (hU : Differentiable ℝ U) (hQ : Differentiable ℝ Q) (hW : Differentiable ℝ W)
    (hTpos : ∀ s, 0 < T s)
    (hEOS : ∀ s, EquationOfState (T s) (M s) V n K (H s))
    (hULaw : InternalEnergyLawAlongProcess n lam U T)
    (hFirstLaw : FirstLawAlongProcess U Q W)
    (hAd : AdiabaticAlongProcess Q)
    (hWork : MaterialWorkLawAlongProcess μ₀ V W H M)
    (hH0 : H 0 = H_i) (hH1 : H 1 = H_f)
    (hT0 : T 0 = T_i) (hT1 : T 1 = T_f)
    (hBranch : H_i ^ 2 < H_f ^ 2) :
    0 < T_f - T_i := by
  have hTi : 0 < T_i := hT0 ▸ hTpos 0
  rw [adiabatic_DeltaT_eq_expr hμ₀ hV hn hK hlam hH hM hT hU hQ hW hTpos hEOS hULaw
    hFirstLaw hAd hWork hH0 hH1 hT0 hT1]
  exact (adiabaticDeltaTExpr_pos_iff hμ₀ hK hlam hTi).mpr hBranch

/-- **Adiabatic demagnetization cools the Pm-T**: on the branch
`H_f² < H_i²` (the field magnitude drops along the process — the
demagnetization step of "chasing the absolute zero"), the adiabatic
temperature change is negative, `T_f − T_i < 0`.
Proof route: as `adiabatic_magnetization_heats`, via
`adiabaticDeltaTExpr_neg_iff`. -/
theorem adiabatic_demagnetization_cools
    {μ₀ V n K lam H_i H_f T_i T_f : ℝ}
    (hμ₀ : 0 < μ₀) (hV : 0 < V) (hn : 0 < n) (hK : 0 < K) (hlam : 0 < lam)
    {H M T U Q W : ℝ → ℝ}
    (hH : ContDiff ℝ 1 H) (hM : Differentiable ℝ M) (hT : ContDiff ℝ 1 T)
    (hU : Differentiable ℝ U) (hQ : Differentiable ℝ Q) (hW : Differentiable ℝ W)
    (hTpos : ∀ s, 0 < T s)
    (hEOS : ∀ s, EquationOfState (T s) (M s) V n K (H s))
    (hULaw : InternalEnergyLawAlongProcess n lam U T)
    (hFirstLaw : FirstLawAlongProcess U Q W)
    (hAd : AdiabaticAlongProcess Q)
    (hWork : MaterialWorkLawAlongProcess μ₀ V W H M)
    (hH0 : H 0 = H_i) (hH1 : H 1 = H_f)
    (hT0 : T 0 = T_i) (hT1 : T 1 = T_f)
    (hBranch : H_f ^ 2 < H_i ^ 2) :
    T_f - T_i < 0 := by
  have hTi : 0 < T_i := hT0 ▸ hTpos 0
  rw [adiabatic_DeltaT_eq_expr hμ₀ hV hn hK hlam hH hM hT hU hQ hW hTpos hEOS hULaw
    hFirstLaw hAd hWork hH0 hH1 hT0 hT1]
  exact (adiabaticDeltaTExpr_neg_iff hμ₀ hK hlam hTi).mpr hBranch

end IPhO2026.T3B2
