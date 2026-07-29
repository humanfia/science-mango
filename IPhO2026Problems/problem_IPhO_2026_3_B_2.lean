/-
Formalization of IPhO 2026, Problem 3, part B.2 — paramagnetic torus,
adiabatic change of the applied magnetic field.

Physical model (from `blueprint/src/chapters/IPhO2026Problems_problem_IPhO_2026_3_B_2.tex`):
- Equation of state of the paramagnetic material:  `T·M·V = n·K·H`.
- Heat capacity at constant magnetization:  `C_M = n·λ/T²`, with `dU = C_M·dT`.
- Fixed volume; magnetic work done *on* the material:  `dW = μ₀·V·H·dM`
  (result of part A.3, used here as a natural-language prerequisite).
- Sign convention: work and heat entering the torus are positive.

Target (B.2): for an adiabatic change `H_i → H_f` starting at temperature `T_i`,
the temperature change is
  `ΔT = T_i·(√((λ + μ₀·K·H_f²)/(λ + μ₀·K·H_i²)) − 1)`.

Derivation sketch carried by the bridge lemmas below:
adiabatic first law `C_M dT = −μ₀ V H dM`, with `M = nKH/(TV)` from the
equation of state, gives `(λ/T²)·dT = −μ₀·K·H·dH/T`, i.e.
`dT/T = −(μ₀K/λ)·H dH`.  Integrating from `(T_i, H_i)` to `(T_f, H_f)` yields
`T_f²·(λ + μ₀·K·H_f²) = T_i²·(λ + μ₀·K·H_i²)`, hence the closed form for `ΔT`.
-/

import Physlib.Electromagnetism.Dynamics.Basic
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic

open Electromagnetism Real

namespace IPhO2026_3_B_2

/-- **State of the paramagnetic torus** (IPhO 2026 T3).  A macrostate of the
torus is determined by the (scalar, collinear) applied magnetic field
`field H`, the magnetization `magnetization M`, and the absolute temperature
`temperature T`, all recorded as real numbers in SI units.  This is the
smallest abstraction preserving the physical roles: PhysLean currently has no
magnetization/thermodynamic-state object, so we introduce one locally rather
than aliasing the quantities to bare reals at the type level. -/
structure ParamagneticTorusState where
  /-- Applied magnetic field strength `H` (A/m), scalar component along the
  torus axis; signed, since the field may be ramped up or down. -/
  field : ℝ
  /-- Magnetization `M` of the paramagnetic material (A/m), scalar component
  along the same axis. -/
  magnetization : ℝ
  /-- Absolute temperature `T` of the material (K). -/
  temperature : ℝ

/-- **Path** of quasistatic states, indexed by a real parameter `t`
(e.g. rescaled time).  The adiabatic change of part B.2 follows such a path. -/
abbrev StatePath := ℝ → ParamagneticTorusState

/-- **Fixed parameters of the torus and its material.**
- `V` — fixed volume of the torus (m³), positive.
- `n` — amount of paramagnetic substance (mol), positive.
- `K` — Curie-type material constant in the equation of state
  `T·M·V = n·K·H`, positive.
- `lam` — the constant `λ` in the heat capacity `C_M = n·λ/T²`, positive.
- `mu0` — permeability of free space `μ₀` (H/m), positive.

`μ₀` is recorded as a parameter hypothesis instead of a PhysLean `FreeSpace`
instance because the thermodynamic model stated in the problem treats `μ₀` as
the bare dimensional constant appearing in the work `dW = μ₀·V·H·dM`; no other
electromagnetic structure is used. -/
structure TorusParameters where
  V : ℝ
  n : ℝ
  K : ℝ
  lam : ℝ
  mu0 : ℝ
  V_pos : 0 < V
  n_pos : 0 < n
  K_pos : 0 < K
  lam_pos : 0 < lam
  mu0_pos : 0 < mu0

/-- **Governing laws** of the paramagnetic torus along a quasistatic path `p`
with parameter `params`.

The fields are exactly the physical laws stated in the problem (plus the
positive-temperature regularity needed to divide by `T`):

- `temp_pos`: the temperature stays positive along the path (regularity
  hypothesis, needed for `C_M = nλ/T²` and for dividing by `T`).
- `eq_of_state`: equation of state `T·M·V = n·K·H` at every point of the path.
- `heat_capacity`: an integrable heat-capacity function `C_M(t) = n·λ/T(t)²`
  along the path — the modelling content is the defining equation, not the
  bare existential witness.
- `work_rate`: an integrable magnetic-work-rate function
  `μ₀·V·H(t)·dM/dt` along the path, expressing the magnetic work
  `dW = μ₀·V·H·dM` on the material (part A.3 result) applied to this path.

The `IntervalIntegrable` clauses bundle the regularity (smoothness of the
quasistatic process) needed to integrate the differential forms, so the
predicate is constraining: it yields pointwise equations plus integrability
facts, not merely a witness of an opaque relation. -/
structure ParamagneticTorusLaws (params : TorusParameters) (p : StatePath) : Prop where
  temp_pos : ∀ t, 0 < (p t).temperature
  eq_of_state :
    ∀ t, (p t).temperature * (p t).magnetization * params.V
      = params.n * params.K * (p t).field
  heat_capacity :
    ∃ Cm : ℝ → ℝ,
      (∀ t, Cm t = params.n * params.lam / (p t).temperature ^ 2) ∧
      (∀ a b, IntervalIntegrable Cm MeasureTheory.volume a b)
  work_rate :
    ∃ w : ℝ → ℝ,
      (∀ t, w t = params.mu0 * params.V * (p t).field * deriv
        (fun s => (p s).magnetization) t) ∧
      (∀ a b, IntervalIntegrable w MeasureTheory.volume a b)

/-- **Adiabatic process law.**  Along an adiabatic path no heat enters the
torus (`δQ = 0`), so by the first law `dU = δQ + dW` with the stated sign
convention (work and heat entering the torus positive) and `dU = C_M dT`,
the heat-capacity term balances the magnetic work rate as functions along
the path:
    `Cm(t) · dT/dt = − w(t)`,
where `Cm` and `w` are the heat-capacity and work-rate functions identified
in `ParamagneticTorusLaws`.  This is the physical first law for zero heat
transfer, not the final temperature formula. -/
def IsAdiabaticPath (params : TorusParameters) (p : StatePath)
    (_laws : ParamagneticTorusLaws params p) : Prop :=
  ∃ Cm w : ℝ → ℝ,
    (∀ t, Cm t = params.n * params.lam / (p t).temperature ^ 2) ∧
    (∀ t, w t = params.mu0 * params.V * (p t).field * deriv
      (fun s => (p s).magnetization) t) ∧
    ∀ t,
      Cm t * deriv (fun s => (p s).temperature) t = -w t

/-- The adiabatic invariant of the process: `T²·(λ + μ₀·K·H²)`, conserved
along any adiabatic path of the torus. -/
noncomputable def adiabaticInvariant (params : TorusParameters)
    (T H : ℝ) : ℝ :=
  T ^ 2 * (params.lam + params.mu0 * params.K * H ^ 2)

/-- Initial data of the adiabatic ramp: the path passes through field `Hi`
at temperature `Ti`, with `Hi ≥ 0` and `Ti > 0` (matching the physical
setup in which the signed ramp starts from a nonnegative field). -/
structure AdiabaticEndpoints (p : StatePath) (Hi Ti : ℝ) : Prop where
  Hi_nonneg : 0 ≤ Hi
  Ti_pos : 0 < Ti
  initial : ∃ t0, (p t0).field = Hi ∧ (p t0).temperature = Ti

/-- **Bridge lemma 1 — the integrated adiabat.**
From the governing laws (`ParamagneticTorusLaws`) and the adiabatic
first-law balance (`IsAdiabaticPath`), any two states of one adiabatic path
share the same value of `T²·(λ + μ₀·K·H²)`.  Carrier of the
integration step `dT/T = −(μ₀K/λ)·H dH`. -/
theorem adiabatic_invariant_along_path (params : TorusParameters)
    (p : StatePath) (laws : ParamagneticTorusLaws params p)
    (hadiabatic : IsAdiabaticPath params p laws) (t₁ t₂ : ℝ) :
    adiabaticInvariant params (p t₁).temperature (p t₁).field
      = adiabaticInvariant params (p t₂).temperature (p t₂).field := by
  sorry

/-- **Bridge lemma 2 — endpoint to endpoint.**
Specialized to the recorded endpoints `(H_i, T_i)` and `(H_f, T_f)` of the
ramp, the invariant equality gives
`T_f²·(λ + μ₀·K·H_f²) = T_i²·(λ + μ₀·K·H_i²)`. -/
theorem endpoint_relation (params : TorusParameters) (p : StatePath)
    (laws : ParamagneticTorusLaws params p)
    (hadiabatic : IsAdiabaticPath params p laws)
    {Hi Hf Ti Tf : ℝ}
    (hendpoints : AdiabaticEndpoints p Hi Ti)
    (hfinal : ∃ tf, (p tf).field = Hf ∧ (p tf).temperature = Tf) :
    Tf ^ 2 * (params.lam + params.mu0 * params.K * Hf ^ 2)
      = Ti ^ 2 * (params.lam + params.mu0 * params.K * Hi ^ 2) := by
  sorry

/-- Positive bracket: `λ + μ₀·K·H² > 0` for the positive parameters of the
problem and any signed field `H` — records why the square root and the
quotient in the final answer are well-defined for either ramp direction. -/
theorem lam_add_mu0_K_sq_pos (params : TorusParameters) (H : ℝ) :
    0 < params.lam + params.mu0 * params.K * H ^ 2 := by
  have hK : 0 < params.K := params.K_pos
  have hmu : 0 < params.mu0 := params.mu0_pos
  have hlam : 0 < params.lam := params.lam_pos
  positivity

/-- **Main target (B.2).**  For an adiabatic change `H_i → H_f` of the
paramagnetic torus starting at temperature `T_i`, the temperature change is
    `ΔT = T_f − T_i
        = T_i·(√((λ + μ₀·K·H_f²)/(λ + μ₀·K·H_i²)) − 1)`.

The final relation is only on the conclusion side: the hypotheses are the
governing laws (`ParamagneticTorusLaws`), the first-law adiabatic balance
(`IsAdiabaticPath`), positive parameters (`TorusParameters`), endpoint and
readout data (`AdiabaticEndpoints` and the final-state witness), and the
direction/regularity data `H_i ≥ 0`, `T_i > 0`, `T_f > 0`.  The square-root
answer expression appears nowhere in the premises. -/
theorem adiabatic_temperature_change (params : TorusParameters)
    (p : StatePath) (laws : ParamagneticTorusLaws params p)
    (hadiabatic : IsAdiabaticPath params p laws)
    {Hi Hf Ti Tf : ℝ}
    (hendpoints : AdiabaticEndpoints p Hi Ti)
    (hfinal : ∃ tf, (p tf).field = Hf ∧ (p tf).temperature = Tf)
    (hTf_pos : 0 < Tf) :
    Tf - Ti
      = Ti * (Real.sqrt
          ((params.lam + params.mu0 * params.K * Hf ^ 2)
            / (params.lam + params.mu0 * params.K * Hi ^ 2)) - 1) := by
  sorry

end IPhO2026_3_B_2
