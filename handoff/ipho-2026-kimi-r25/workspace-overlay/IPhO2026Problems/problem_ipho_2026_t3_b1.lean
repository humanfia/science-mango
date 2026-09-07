import Mathlib

/-!
# IPhO 2026 · Theory problem T3-B1 — "Chasing the absolute zero": heat transferred
in an isothermal change of the field

Autoformalization of IPhO 2026 T3-B1 (source:
`reports/ipho_2026/problem_ipho_2026_t3_b1.source.json`; problem pages
`ipho_2026_source/image/T3_page-2.png` (T3-B preamble and ideal-gas/Pm-T
comparison table) and `ipho_2026_source/image/T3_page-3.png` (T3-B1 statement)).

## Shared problem context (page 12, T3-B preamble and table)

Continuing with the paramagnetic torus (Pm-T), the T3-B table prescribes the
thermodynamic model, with the standing instruction "You may use the equations
provided in the table directly without proving them":

* *State functions*: `H` (magnitude of the `H⃗`-field), `M` (magnitude of the
  magnetization `M⃗`) and the temperature `T`.
* *Constants*: `K`, `λ` (material constants of the torus) and the number of
  moles `n`.
* *Equation of state*: `T·M·V = n·K·H`.
* *Heat capacity at constant `M`*: `C_M = n·λ/T²`.
* *Internal energy*: in any process, `dU = C_M·dT`.
* The volume `V` of the torus is constant, so there is no work due to pressure;
  the only work mode is the magnetic work on the material,
  `dW = μ₀·V·H·dM` (the T3-A3 result, restated in the shared context; see the
  dependency note below).
* Sign convention: work `W` and heat `Q` are positive when they flow into the
  Pm-T (`WorkFlowsIntoSystem`, `HeatFlowsIntoSystem`).

## Subquestion T3-B1 (page 13, 1.5 pts)

"If the magnitude of `H⃗` changes from `H_i` to `H_f` at a constant temperature
`T`, an energy `Q` is transferred between the Pm-T and its environment.
Write `Q` in terms of `μ₀`, `n`, `V`, `K`, `H_i`, `H_f`, and `T`."

## Previous-part dependency (T3-A3)

Policy: `derive_inline_from_problem_only_material`.  The T3-A3 result
`dW = μ₀·V·H·dM` is *problem-side material for part B*: the T3-B preamble
(page 12) instructs to use the answer of T3-A3 and explicitly provides the
fallback "you may use `dW = αVμ₀HdM` where `α` is a number", while the B1
shared context states the work law outright.  The model therefore introduces
the step law as a governing-law predicate `MaterialWorkStep` (no sibling file
is imported, and nothing from the winding/Ampère machinery of part A — which
is not part of the B1 context — is re-assumed).  The printed fallback shape is
recorded as `fallbackWorkForm`, and `materialWorkStep_eq_fallback_alpha_one`
shows the stated law realizes it with the derived value `α = 1` (conclusion
side only).

## Physical model (assumptions)

1. *Equation of state* (`EquationOfState`, table law): `T·M·V = n·K·H`,
   assumed at every equilibrium state visited by the process.
2. *Heat capacity at constant `M`* (`heatCapacityAtConstM`, `HeatCapacityLaw`,
   table law): `C_M = n·λ/T²`.  Carried by the model for completeness — it is
   the coefficient of `dT` in the internal-energy law — although it drops out
   of the isothermal answer (it multiplies `dT = 0`); it is the B2
   (adiabatic) subquestion where `λ` survives.
3. *Internal-energy law* (`InternalEnergyStep`, table law): `dU = C_M·dT` in
   any process.  Its accumulated form along a path is `EnergyChangeAlongPath`.
4. *Magnetic work on the material* (`MaterialWorkStep`): `dW = μ₀·V·H·dM`,
   the T3-A3 law as restated in the B-part context.  Its accumulated form
   along a path is `WorkAlongPath`.  Because the volume is fixed (problem
   text), there is no `−P·dV` term: the magnetic work is the total work, which
   is what `FirstLawProcess` consumes.
5. *First law of thermodynamics* (`FirstLawStep`, accumulated
   `FirstLawProcess`): with the problem's sign convention (work and heat
   entering the torus are positive), `dU = đQ + đW`, hence for the finite
   process `ΔU = Q + W`.
6. *Quasistatic process model*: the change of `H` from `H_i` to `H_f` at
   constant temperature proceeds through equilibrium states (the table speaks
   of state functions and of `dU`, `dW` along the process), so the process is
   a path in the `(H, M, T)` state space, parametrized by the driving field
   `H` itself.  Along the path the equation of state holds pointwise
   (`EquationOfStatePath`) and the temperature is constant
   (`IsothermalTemperaturePath`); the path functions are recorded for all
   field values, as the equilibrium laws they come from hold for every state,
   not just the visited segment.  The infinitesimal laws accumulate to
   interval integrals over the path parameter: `W = ∫ μ₀·V·H·(dM/dH) dH` and
   `ΔU = ∫ C_M(T(H))·(dT/dH) dH` over `H_i..H_f`.
7. *Positivity* (physical ranges): `0 < T` (kelvin), `0 < V`; for the sign
   analysis also `0 < μ₀`, `0 < n`, `0 < K`.  `H_i`, `H_f` are field
   *magnitudes* (nonnegative on the physical branch); the closed form only
   involves their squares, so the signed-scalar model is safe.

## Derivation (answer-blind, from the laws above only)

* Equation of state at the fixed temperature `T`, solved for the path
  magnetization: `M(H) = n·K·H/(T·V)`, so `dM/dH = n·K/(T·V)`
  (`magnetization_path_eval`, `magnetization_path_deriv`); the exact step form
  is `T·V·dM = n·K·dH` (`equationOfState_step`).
* Work accumulated along the isothermal path
  (`work_along_isothermal_path`):
  `W = ∫_{H_i}^{H_f} μ₀·V·H·(n·K/(T·V)) dH = (μ₀·n·K/T)·∫_{H_i}^{H_f} H dH
     = (μ₀·n·K/(2T))·(H_f² − H_i²)`.
  The volume `V` cancels in the integrand — the answer is independent of `V`
  (the problem's list of allowed variables is permissive, not mandatory).
* Internal energy change along the isothermal path
  (`energy_change_isothermal`): `ΔU = ∫ C_M·(dT/dH) dH = 0` since `dT/dH = 0`.
* First law: `Q = ΔU − W = −W = (μ₀·n·K/(2T))·(H_i² − H_f²)`.

Every step is an exact substitution plus one interval integral of the identity
(`integral_id`); the only side conditions needed are `T ≠ 0`, `V ≠ 0`.

## Current target (conclusion side only)

`isothermal_heat`: under the equation of state along the isothermal path, the
accumulated T3-A3 magnetic-work law, the accumulated internal-energy law, and
the first law, the heat transferred into the torus is

    `Q = (μ₀·n·K/(2T))·(H_i² − H_f²)`,

in terms of the allowed variables (with `V` cancelling).  The raw requested
combination is recorded as `isothermalHeatExpr`; the target relation and its
packaged form are to be proved from the model — nothing about the value of
`Q` is assumed, and no hypothesis mentions the expression
`μ₀·n·K/(2T)·(H_i² − H_f²)`.

*Branch/orientation record*: `Q` is signed with the into-system convention.
`isothermal_heat_neg_iff` shows `Q < 0 ↔ H_i² < H_f²` (for positive material
constants); `heat_flows_out_when_magnetized` records that increasing the field
magnitude (`0 ≤ H_i < H_f`) pushes heat *out* of the torus, while
`heat_flows_in_when_demagnetized` records that decreasing it
(`0 ≤ H_f < H_i`) draws heat *in* — the magnetocaloric direction behind the
adiabatic-demagnetization cooling theme of the problem.

## Units

All quantities are real numbers carrying SI units, recorded per declaration:
`T` in K; `H, M` in A/m; `V` in m³; `n` in mol; from `T·M·V = n·K·H` the
material constant `K` carries K·m³/mol; from `C_M = nλ/T²` in J/K the constant
`λ` carries J·K/mol; `C_M` in J/K; `U, Q, W` in J; `μ₀` in N/A² (H/m).
Consistency check of the target: `μ₀·n·K·H²/T` has units
(N/A²)·mol·(K·m³/mol)·(A/m)²/K = N·m = J. ✓

## Grounding (LeanExplore, packages Mathlib + Physlib)

LeanExplore finds no scalar paramagnet-thermodynamics API: Physlib's
electromagnetism is the full spacetime vector-field machinery (near miss for
the uniform-magnitude scalar model), and there is no ready-made
magnetic-work/heat-capacity formalization; the model therefore keeps the
problem's own scalar state functions and states the table laws as local
governing-law predicates.  The integration layer is grounded in Mathlib:
`intervalIntegral` notation `∫ H in H_i..H_f, …`,
`intervalIntegral.integral_const_mul`, `integral_id` for
`∫ H in a..b, H = (b² − a²)/2`, and `deriv`/`deriv_const_mul_id`,
`deriv_const` for the path rates.
-/

namespace IPhO2026.T3B1

/-! ## The thermodynamic table: state functions and governing laws -/

/-- **Equation of state of the paramagnetic torus** (table law, given): the
state functions `H` (field magnitude), `M` (magnetization magnitude) and `T`
(temperature) satisfy `T·M·V = n·K·H`, with `V` the (fixed) torus volume, `n`
the number of moles and `K` a material constant.  Units: K·(A/m)·m³ on the
left, mol·(K·m³/mol)·(A/m) on the right. -/
def EquationOfState (T M V n K H : ℝ) : Prop := T * M * V = n * K * H

/-- **Heat capacity at constant magnetization** (table law, given):
`C_M = n·λ/T²`, with `λ` the second material constant.  Units: J/K (λ carries
J·K/mol).  In T3-B1 it only ever multiplies `dT = 0`; it is recorded here as
part of the stated model and becomes essential in the adiabatic part T3-B2. -/
noncomputable def heatCapacityAtConstM (n lam T : ℝ) : ℝ := n * lam / T ^ 2

/-- The heat-capacity law as a predicate on a heat-capacity value `C_M`:
`C_M` equals the table's `n·λ/T²`. -/
def HeatCapacityLaw (C_M n lam T : ℝ) : Prop := C_M = heatCapacityAtConstM n lam T

/-- **Internal-energy law, step form** (table law, given): in any process the
internal energy of the Pm-T satisfies `dU = C_M·dT` — in particular `U` changes
only through temperature changes.  Units: J. -/
def InternalEnergyStep (dU C_M dT : ℝ) : Prop := dU = C_M * dT

/-- **Magnetic work done on the paramagnetic material, step form** (the T3-A3
result, restated as part of the B-part shared context: "the magnetic work on
the material is `dW = μ₀·V·H·dM`"; the volume is fixed, so this is the total
work on the material — there is no pressure work): a change `dM` of the
magnetization at field `H` absorbs the work `dW = μ₀·V·H·dM`, positive when
flowing into the torus (`WorkFlowsIntoSystem`).  Units: J
((N/A²)·m³·(A/m)·(A/m) = N·m). -/
def MaterialWorkStep (dW μ₀ V H dM : ℝ) : Prop := dW = μ₀ * V * H * dM

/-- Fallback answer shape printed in the T3-B preamble (page 12, problem-side
material): "if you did not find an answer for `dW` in question T3-A3, you may
use `dW = αVμ₀HdM` where `α` is a number."  This definition records the
fallback shape; the stated work law realizes it with `α = 1`
(`materialWorkStep_eq_fallback_alpha_one`).  Units: J for dimensionless `α`. -/
noncomputable def fallbackWorkForm (α V μ₀ H dM : ℝ) : ℝ := α * V * μ₀ * H * dM

/-- **First law of thermodynamics, step form**, with the problem's sign
convention (work and heat entering the torus are positive): the internal-energy
change equals the heat plus the work flowing in, `dU = đQ + đW`.  Units: J. -/
def FirstLawStep (dU dQ dW : ℝ) : Prop := dU = dQ + dW

/-- Sign convention for work (shared context): a signed work value `W`
represents energy flowing *into* the paramagnetic torus exactly when it is
positive. -/
def WorkFlowsIntoSystem (W : ℝ) : Prop := 0 < W

/-- Sign convention for heat (shared context): a signed heat value `Q`
represents energy flowing *into* the paramagnetic torus exactly when it is
positive.  The `Q` of T3-B1 is such a signed heat. -/
def HeatFlowsIntoSystem (Q : ℝ) : Prop := 0 < Q

/-! ## The isothermal process: quasistatic path model and accumulation laws -/

/-- **Equation of state along the path** (governing law, process form): the
isothermal change of the field is quasistatic, so at field magnitude `H` the
torus is in an equilibrium state `(H, M_of H, T)` satisfying the equation of
state at the fixed temperature `T`.  `M_of` is the magnetization as a state
function of `H` along (and beyond) the visited segment — the equation of state
is a property of every equilibrium state, so the predicate is recorded for all
field values.  Units: `M_of H` in A/m. -/
def EquationOfStatePath (M_of : ℝ → ℝ) (T V n K : ℝ) : Prop :=
  ∀ H, EquationOfState T (M_of H) V n K H

/-- **Isothermal condition** (process hypothesis, given verbatim by T3-B1: the
change happens "at a constant temperature `T`"): the temperature along the
path is the constant `T` for every value of the path parameter.  Written with
a global temperature path so that `deriv T_path = 0` everywhere; only the
visited segment `H_i..H_f` is physical. -/
def IsothermalTemperaturePath (T_path : ℝ → ℝ) (T : ℝ) : Prop := ∀ H, T_path H = T

/-- **Work accumulated along the path** (accumulated form of the T3-A3 step law
`MaterialWorkStep`): the total magnetic work done on the material as the field
magnitude goes from `H_i` to `H_f` is the integral of the infinitesimal work
`dW = μ₀·V·H·dM` along the path, i.e. of `μ₀·V·H·(dM/dH)` over the interval
`H_i..H_f`.  Since the volume is fixed, this is the total work entering the
torus (no pressure work).  Units: J. -/
def WorkAlongPath (W μ₀ V : ℝ) (M_of : ℝ → ℝ) (H_i H_f : ℝ) : Prop :=
  W = ∫ H in H_i..H_f, μ₀ * V * H * deriv M_of H

/-- **Internal-energy change accumulated along the path** (accumulated form of
the table law `InternalEnergyStep` with the table's `C_M = n·λ/T²`
instantiated): the total internal-energy change as the field goes from `H_i`
to `H_f` is the integral of `dU = C_M·dT` along the path, i.e. of
`C_M(T_path H)·(dT_path/dH)` over `H_i..H_f`.  Units: J. -/
def EnergyChangeAlongPath (ΔU n lam : ℝ) (T_path : ℝ → ℝ) (H_i H_f : ℝ) : Prop :=
  ΔU = ∫ H in H_i..H_f, heatCapacityAtConstM n lam (T_path H) * deriv T_path H

/-- **First law for the finite process** (accumulated `FirstLawStep`): the
total internal-energy change equals the total heat plus the total work flowing
into the torus, `ΔU = Q + W`, with the problem's into-system sign convention.
Units: J. -/
def FirstLawProcess (ΔU Q W : ℝ) : Prop := ΔU = Q + W

/-! ## Bridge lemmas -/

/-- **Equation-of-state step form** (exact): comparing the equation of state
before and after a change `(dH, dM)` at fixed temperature and volume gives
`T·V·dM = n·K·dH` — the affine EOS holds to all orders, no approximation.
Proof route: unfold `EquationOfState` at both hypotheses and subtract;
`linear_combination`. -/
theorem equationOfState_step {T V n K H M dH dM : ℝ}
    (h₁ : EquationOfState T M V n K H)
    (h₂ : EquationOfState T (M + dM) V n K (H + dH)) :
    T * V * dM = n * K * dH := by
  have h1 : T * M * V = n * K * H := h₁
  have h2 : T * (M + dM) * V = n * K * (H + dH) := h₂
  linear_combination h2 - h1

/-- The stated work law realizes the printed fallback shape `dW = α·V·μ₀·H·dM`
with the derived value `α = 1`.
Proof route: unfold both predicates; `linear_combination`. -/
theorem materialWorkStep_eq_fallback_alpha_one {dW μ₀ V H dM : ℝ}
    (h : MaterialWorkStep dW μ₀ V H dM) : dW = fallbackWorkForm 1 V μ₀ H dM := by
  have h' : dW = μ₀ * V * H * dM := h
  unfold fallbackWorkForm
  linear_combination h'

/-- The table's heat capacity `C_M = n·λ/T²` is positive for positive mole
number, material constant and temperature.  Records the physical range of
`C_M`; not needed for the isothermal algebra.
Proof route: unfold; `positivity`. -/
theorem heatCapacityAtConstM_pos {n lam T : ℝ} (hn : 0 < n) (hlam : 0 < lam) (hT : 0 < T) :
    0 < heatCapacityAtConstM n lam T := by
  unfold heatCapacityAtConstM
  positivity

/-- The internal-energy step law with the table's heat capacity substituted:
`dU = (n·λ/T²)·dT`.
Proof route: rewrite `C_M` by `HeatCapacityLaw` in `InternalEnergyStep`. -/
theorem internalEnergyStep_of_heatCapacityLaw {dU C_M dT n lam T : ℝ}
    (hCM : HeatCapacityLaw C_M n lam T) (hU : InternalEnergyStep dU C_M dT) :
    dU = heatCapacityAtConstM n lam T * dT := by
  have h1 : C_M = heatCapacityAtConstM n lam T := hCM
  have h2 : dU = C_M * dT := hU
  rw [h1] at h2
  exact h2

/-- **Equation of state solved for the magnetization** at fixed `T` (and fixed
`V`, `n`, `K`): `M = n·K·H/(T·V)`.
Proof route: `eq_div_iff` with `T·V ≠ 0`; `linear_combination`. -/
theorem magnetization_of_field {T M V n K H : ℝ}
    (hEOS : EquationOfState T M V n K H) (hT : T ≠ 0) (hV : V ≠ 0) :
    M = n * K * H / (T * V) := by
  have h : T * M * V = n * K * H := hEOS
  rw [eq_div_iff (mul_ne_zero hT hV)]
  linear_combination h

/-- Pointwise evaluation of the path magnetization: along the isothermal path,
`M_of H = n·K·H/(T·V)` for every field magnitude `H`.
Proof route: `magnetization_of_field` applied to the pointwise EOS. -/
theorem magnetization_path_eval {M_of : ℝ → ℝ} {T V n K : ℝ}
    (hEOS : EquationOfStatePath M_of T V n K) (hT : T ≠ 0) (hV : V ≠ 0) (H : ℝ) :
    M_of H = n * K * H / (T * V) :=
  magnetization_of_field (hEOS H) hT hV

/-- **Magnetization rate along the path**: the equation of state forces
`M_of` to be the affine function `H ↦ (n·K/(T·V))·H`, so
`dM/dH = n·K/(T·V)` at every field value.
Proof route: `funext` from `magnetization_path_eval`, then
`deriv_const_mul_id`. -/
theorem magnetization_path_deriv {M_of : ℝ → ℝ} {T V n K H : ℝ}
    (hEOS : EquationOfStatePath M_of T V n K) (hT : T ≠ 0) (hV : V ≠ 0) :
    deriv M_of H = n * K / (T * V) := by
  have hfun : M_of = fun x => (n * K / (T * V)) * x := by
    funext x
    rw [magnetization_path_eval hEOS hT hV x]
    ring
  rw [hfun, deriv_const_mul_id]

/-- **No internal-energy change on an isothermal path**: accumulating
`dU = C_M·dT` along a path whose temperature is constant gives `ΔU = 0`,
independently of the value of `C_M` (hence `λ` does not enter T3-B1).
Proof route: `T_path = fun _ => T` by `funext`; `deriv_const` makes the
integrand vanish; `simp` closes with the interval integral of zero
(`intervalIntegral.integral_zero`). -/
theorem energy_change_isothermal {ΔU n lam T : ℝ} {T_path : ℝ → ℝ} {H_i H_f : ℝ}
    (hAcc : EnergyChangeAlongPath ΔU n lam T_path H_i H_f)
    (hIso : IsothermalTemperaturePath T_path T) :
    ΔU = 0 := by
  have hfun : T_path = fun _ => T := funext hIso
  have h : ΔU = ∫ H in H_i..H_f, heatCapacityAtConstM n lam (T_path H) * deriv T_path H := hAcc
  rw [hfun] at h
  simp [deriv_const] at h
  exact h

/-- **Work done on the material along the isothermal path**: substituting the
EOS-implied rate `dM/dH = n·K/(T·V)` into the accumulated T3-A3 work gives
`W = (μ₀·n·K/T)·∫_{H_i}^{H_f} H dH = (μ₀·n·K/(2T))·(H_f² − H_i²)`.  The volume
cancels in the integrand: the work per unit field change, and hence the heat,
is independent of `V`.
Proof route: rewrite the integrand via `magnetization_path_deriv` under
`funext` (algebra with `T, V ≠ 0`), then `intervalIntegral.integral_const_mul`
and `integral_id`, and clear fractions. -/
theorem work_along_isothermal_path {W μ₀ V n K T H_i H_f : ℝ} {M_of : ℝ → ℝ}
    (hWork : WorkAlongPath W μ₀ V M_of H_i H_f)
    (hEOS : EquationOfStatePath M_of T V n K)
    (hT : 0 < T) (hV : 0 < V) :
    W = μ₀ * n * K / (2 * T) * (H_f ^ 2 - H_i ^ 2) := by
  have hT' : T ≠ 0 := ne_of_gt hT
  have hV' : V ≠ 0 := ne_of_gt hV
  have hder : ∀ H : ℝ, deriv M_of H = n * K / (T * V) :=
    fun H => magnetization_path_deriv hEOS hT' hV'
  have hfun : (fun H => μ₀ * V * H * deriv M_of H) = fun H => (μ₀ * n * K / T) * H := by
    funext H
    show μ₀ * V * H * deriv M_of H = (μ₀ * n * K / T) * H
    rw [hder H]
    field_simp
  have hW : W = ∫ H in H_i..H_f, μ₀ * V * H * deriv M_of H := hWork
  rw [hfun, intervalIntegral.integral_const_mul, integral_id] at hW
  rw [hW]
  field_simp

/-! ## Main target (T3-B1) -/

/-- Raw end-to-end expression requested by T3-B1 (derived candidate): the
combination `(μ₀·n·K/(2T))·(H_i² − H_f²)` built from the allowed variables
`μ₀, n, V, K, H_i, H_f, T` (with `V` cancelling out of the derivation, so the
answer depends on the listed variables only through `μ₀, n, K, H_i, H_f, T`).
The definition only records the derived combination; that the actual heat
equals it is the content of `isothermal_heat`, and nothing in the model
assumptions mentions this expression.  Units: J
((N/A²)·mol·(K·m³/mol)·(A/m)²/K = N·m). -/
noncomputable def isothermalHeatExpr (μ₀ n K T H_i H_f : ℝ) : ℝ :=
  μ₀ * n * K / (2 * T) * (H_i ^ 2 - H_f ^ 2)

/-- **T3-B1 main target.**  For the paramagnetic torus whose state functions
obey the table's equation of state `T·M·V = n·K·H`, heat capacity
`C_M = n·λ/T²` and internal-energy law `dU = C_M·dT`, with the T3-A3 magnetic
work `dW = μ₀·V·H·dM` as the only work mode (fixed volume): when the field
magnitude changes from `H_i` to `H_f` at the constant temperature `T`, the
heat transferred into the torus (into-system sign convention) is

    `Q = (μ₀·n·K/(2T))·(H_i² − H_f²)`,

in terms of `μ₀`, `n`, `V`, `K`, `H_i`, `H_f` and `T` as requested (the
derivation shows `V` cancels and `λ` does not enter at constant temperature).

Derivation chain: `energy_change_isothermal` gives `ΔU = 0`;
`work_along_isothermal_path` gives `W = (μ₀·n·K/(2T))·(H_f² − H_i²)`;
substituting both into the first law `ΔU = Q + W` leaves
`Q = −W = (μ₀·n·K/(2T))·(H_i² − H_f²)` by rearrangement
(`linear_combination -hF`).  (The route was machine-checked end-to-end in a
scratch validation before the final body was deferred to the prover stage.) -/
theorem isothermal_heat {μ₀ V n K lam T H_i H_f Q W ΔU : ℝ} {M_of T_path : ℝ → ℝ}
    (hT : 0 < T) (hV : 0 < V)
    (hEOS : EquationOfStatePath M_of T V n K)
    (hIso : IsothermalTemperaturePath T_path T)
    (hWork : WorkAlongPath W μ₀ V M_of H_i H_f)
    (hEnergy : EnergyChangeAlongPath ΔU n lam T_path H_i H_f)
    (hFirst : FirstLawProcess ΔU Q W) :
    Q = μ₀ * n * K / (2 * T) * (H_i ^ 2 - H_f ^ 2) := by
  have hΔU : ΔU = 0 := energy_change_isothermal hEnergy hIso
  have hW : W = μ₀ * n * K / (2 * T) * (H_f ^ 2 - H_i ^ 2) :=
    work_along_isothermal_path hWork hEOS hT hV
  have hF : ΔU = Q + W := hFirst
  linear_combination -hF + hΔU - hW

/-- Packaged form of the main target (naming expansion): the heat transferred
into the torus equals the raw requested expression `isothermalHeatExpr`.
Proof route: `isothermal_heat`; `isothermalHeatExpr` unfolds definitionally to
`μ₀·n·K/(2T)·(H_i² − H_f²)`. -/
theorem isothermal_heat_eq_expr {μ₀ V n K lam T H_i H_f Q W ΔU : ℝ} {M_of T_path : ℝ → ℝ}
    (hT : 0 < T) (hV : 0 < V)
    (hEOS : EquationOfStatePath M_of T V n K)
    (hIso : IsothermalTemperaturePath T_path T)
    (hWork : WorkAlongPath W μ₀ V M_of H_i H_f)
    (hEnergy : EnergyChangeAlongPath ΔU n lam T_path H_i H_f)
    (hFirst : FirstLawProcess ΔU Q W) :
    Q = isothermalHeatExpr μ₀ n K T H_i H_f := by
  unfold isothermalHeatExpr
  exact isothermal_heat hT hV hEOS hIso hWork hEnergy hFirst

/-- **Sign/orientation record**: for positive `μ₀`, `n`, `K`, `T` (and positive
volume), the signed heat is negative exactly when the field magnitude grows:
`Q < 0 ↔ H_i² < H_f²`.  This keeps the branch information of the signed
answer on record: increasing the field isothermally expels heat from the
torus, decreasing it absorbs heat.
Proof route: rewrite `Q` by `isothermal_heat`; the positive prefactor
`μ₀·n·K/(2T)` (`div_pos`, `mul_pos`) reduces the statement to
`H_i² − H_f² < 0 ↔ H_i² < H_f²` (`neg_of_mul_neg_right`,
`mul_neg_of_pos_of_neg`, `sub_neg`). -/
theorem isothermal_heat_neg_iff {μ₀ V n K lam T H_i H_f Q W ΔU : ℝ} {M_of T_path : ℝ → ℝ}
    (hμ₀ : 0 < μ₀) (hn : 0 < n) (hK : 0 < K) (hT : 0 < T) (hV : 0 < V)
    (hEOS : EquationOfStatePath M_of T V n K)
    (hIso : IsothermalTemperaturePath T_path T)
    (hWork : WorkAlongPath W μ₀ V M_of H_i H_f)
    (hEnergy : EnergyChangeAlongPath ΔU n lam T_path H_i H_f)
    (hFirst : FirstLawProcess ΔU Q W) :
    Q < 0 ↔ H_i ^ 2 < H_f ^ 2 := by
  have hQ : Q = μ₀ * n * K / (2 * T) * (H_i ^ 2 - H_f ^ 2) :=
    isothermal_heat hT hV hEOS hIso hWork hEnergy hFirst
  have hc : 0 < μ₀ * n * K / (2 * T) :=
    div_pos (mul_pos (mul_pos hμ₀ hn) hK) (mul_pos (by norm_num) hT)
  rw [hQ]
  constructor
  · intro h
    rcases mul_neg_iff.mp h with ⟨-, h2⟩ | ⟨h1, -⟩
    · exact sub_neg.mp h2
    · exact absurd h1 (not_lt_of_ge hc.le)
  · intro h
    exact mul_neg_of_pos_of_neg hc (sub_neg.mpr h)

/-- **Magnetization branch**: increasing the field magnitude
(`0 ≤ H_i < H_f`) at constant temperature transfers heat *out of* the torus
(`Q < 0` under the into-system convention) — the work done on the material
leaves as heat since `ΔU = 0`.  This is the heat that must be removed to keep
the torus isothermal while magnetizing.
Proof route: `isothermal_heat_neg_iff` reduces to `H_i² < H_f²`, which follows
from `pow_lt_pow_left₀`. -/
theorem heat_flows_out_when_magnetized {μ₀ V n K lam T H_i H_f Q W ΔU : ℝ} {M_of T_path : ℝ → ℝ}
    (hμ₀ : 0 < μ₀) (hn : 0 < n) (hK : 0 < K) (hT : 0 < T) (hV : 0 < V)
    (hEOS : EquationOfStatePath M_of T V n K)
    (hIso : IsothermalTemperaturePath T_path T)
    (hWork : WorkAlongPath W μ₀ V M_of H_i H_f)
    (hEnergy : EnergyChangeAlongPath ΔU n lam T_path H_i H_f)
    (hFirst : FirstLawProcess ΔU Q W)
    (hHi : 0 ≤ H_i) (hHif : H_i < H_f) :
    Q < 0 := by
  have hiff := isothermal_heat_neg_iff hμ₀ hn hK hT hV hEOS hIso hWork hEnergy hFirst
  have hsq : H_i ^ 2 < H_f ^ 2 := pow_lt_pow_left₀ hHif hHi two_ne_zero
  exact hiff.mpr hsq

/-- **Demagnetization branch**: decreasing the field magnitude
(`0 ≤ H_f < H_i`) at constant temperature draws heat *into* the torus
(`HeatFlowsIntoSystem Q`) — the magnetocaloric direction exploited for
cooling by adiabatic demagnetization in the rest of the problem.
Proof route: rewrite `Q` by `isothermal_heat`; with the positive prefactor,
`0 < Q ↔ H_f² < H_i²` (`mul_pos_iff_of_pos_left`, `sub_pos`), closed by
`pow_lt_pow_left₀`. -/
theorem heat_flows_in_when_demagnetized {μ₀ V n K lam T H_i H_f Q W ΔU : ℝ} {M_of T_path : ℝ → ℝ}
    (hμ₀ : 0 < μ₀) (hn : 0 < n) (hK : 0 < K) (hT : 0 < T) (hV : 0 < V)
    (hEOS : EquationOfStatePath M_of T V n K)
    (hIso : IsothermalTemperaturePath T_path T)
    (hWork : WorkAlongPath W μ₀ V M_of H_i H_f)
    (hEnergy : EnergyChangeAlongPath ΔU n lam T_path H_i H_f)
    (hFirst : FirstLawProcess ΔU Q W)
    (hHf : 0 ≤ H_f) (hHfi : H_f < H_i) :
    HeatFlowsIntoSystem Q := by
  have hQ : Q = μ₀ * n * K / (2 * T) * (H_i ^ 2 - H_f ^ 2) :=
    isothermal_heat hT hV hEOS hIso hWork hEnergy hFirst
  unfold HeatFlowsIntoSystem
  rw [hQ]
  have hc : 0 < μ₀ * n * K / (2 * T) :=
    div_pos (mul_pos (mul_pos hμ₀ hn) hK) (mul_pos (by norm_num) hT)
  have hsq : H_f ^ 2 < H_i ^ 2 := pow_lt_pow_left₀ hHfi hHf two_ne_zero
  exact mul_pos hc (sub_pos.mpr hsq)

end IPhO2026.T3B1
