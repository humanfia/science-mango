import Mathlib

/-!
# IPhO 2026, Problem 3, Part B.1 — Paramagnetic torus: isothermal heat transfer

A paramagnetic material fills a torus of fixed volume `V` and amount `n` (moles).
Governing laws (given in the problem statement):

* Equation of state (paramagnet): `T * M * V = n * K * H`, with `K` a material
  constant of the paramagnet.
* Heat capacity at constant magnetization: `C_M T = n * lambda / T^2`,
  with `dU = C_M T * dT` at constant `M` (internal energy depends on `T` alone).
* Magnetic work done **on** the material (result of part A.3):
  `dW = μ₀ * V * H * dM` along quasistatic processes.
* First law of thermodynamics with the source sign convention
  ("work and heat entering the torus are positive"):
  `Q = ΔU - W_on` for each quasistatic process, and along an isothermal
  process `ΔU = 0` because `dU = C_M dT`, so `Q = -W_on` there.

Current subquestion: at fixed temperature `T`, `H` changes from `H_i` to `H_f`;
find the heat `Q` transferred into the torus.

Recorded official answer:
`Q = -(μ₀ * n * K / (2 * T)) * (H_f^2 - H_i^2)`.

This file is an autoformalization: all proof bodies are `by sorry`.
-/

namespace IPhO2026.Problem3.B1

open Real

/-- Constant parameters of the paramagnetic torus experiment.  `K` is the
material constant of the paramagnet appearing in the equation of state
`T * M * V = n * K * H` (it absorbs Curie-type constants); `lambda` is the
coefficient of the heat capacity `C_M = n * lambda / T^2` at constant
magnetization.  All fields are physical scalars; positivity/regularity
constraints are stated separately as hypotheses where they are needed. -/
structure TorusParams where
  /-- Permeability of free space, in SI units. -/
  mu0 : ℝ
  /-- Fixed volume of the torus. -/
  V : ℝ
  /-- Amount of paramagnetic material, in moles. -/
  n : ℝ
  /-- Material constant of the paramagnet in the equation of state. -/
  K : ℝ
  /-- Heat-capacity coefficient: `C_M = n * lambda / T^2`. -/
  lambda : ℝ

/-- State variables that vary along a quasistatic process of the torus:
temperature `T`, magnetization `M`, and applied magnetic field strength `H`.
The volume is fixed and therefore lives in `TorusParams`, not here. -/
structure TorusState where
  /-- Thermodynamic temperature. -/
  T : ℝ
  /-- Magnetization of the material (magnetic moment per unit volume). -/
  M : ℝ
  /-- Applied magnetic field strength. -/
  H : ℝ

/-- The magnetic equation of state of the torus material:
`T * M * V = n * K * H`.  This is a governing law, not the current target. -/
def SatisfiesEOS (p : TorusParams) (s : TorusState) : Prop :=
  s.T * s.M * p.V = p.n * p.K * s.H

/-- The heat capacity at constant magnetization as given by the problem:
`C_M T = n * lambda / T^2`. -/
noncomputable def heatCapacityConstM (p : TorusParams) (T : ℝ) : ℝ :=
  p.n * p.lambda / T ^ 2

/-- Characterization of the material's internal energy: at constant
magnetization `dU = C_M dT`, i.e. `U` depends on temperature alone and is
differentiable with derivative `C_M T`. -/
def HasHeatCapacityLaw (p : TorusParams) (U : ℝ → ℝ) : Prop :=
  ∀ T : ℝ, T ≠ 0 → HasDerivAt U (heatCapacityConstM p T) T

/-- Magnetic work differential supplied to the torus along a quasistatic
process parametrized by the magnetization: the magnetic work of part A.3
`dW_on = μ₀ * V * H * dM` is recorded as the pointwise density
`workDensity M = μ₀ * V * H_of_M M`, so the work done on the material from
magnetization `M₀` to `M₁` is `∫ M in M₀..M₁, workDensity M`.  This is the
reusable conclusion of part A.3 (natural-language prerequisite), recorded as
a governing law for the present subquestion, not as a target. -/
def IsMagneticWorkDensity (p : TorusParams)
    (H_of_M workDensity : ℝ → ℝ) : Prop :=
  ∀ M : ℝ, workDensity M = p.mu0 * p.V * H_of_M M

/-- First law of thermodynamics for the torus along a quasistatic
isothermal process at temperature `T_iso`.  With the sign convention of the
source ("work and heat entering the torus are positive") and the internal
energy obeying `dU = C_M dT` (`HasHeatCapacityLaw p U`), the
internal-energy change over an isothermal leg vanishes
(`U T_iso − U T_iso = 0`), so the balance for every leg tracked from
magnetization `M₀` to magnetization `M_target` reads

`Q_in M_target - Q_in M₀ = (U T_iso − U T_iso) − ∫ M₀..M_target heatDensity`

with `Q_in` the cumulative heat transferred into the torus along the
isotherm and `heatDensity M` the supplied density of the
work-on-the-torus differential `dW_on = μ₀ V H dM`.  Given
`HasHeatCapacityLaw p U` (supplied by the caller), this predicate delivers,
for every leg, the balance equation together with the vanishing of the
`U`-bracket.  This is a governing law, not the current target; it is
constraining (real equations), not an opaque witness. -/
def ObeysFirstLawMagnetic (p : TorusParams) (U : ℝ → ℝ)
    (T_iso : ℝ) (heatDensity Q_in : ℝ → ℝ) : Prop :=
  HasHeatCapacityLaw p U →
    ∀ (M₀ M_target : ℝ),
      Q_in M_target - Q_in M₀ =
        (U T_iso - U T_iso) - ∫ M in M₀..M_target, heatDensity M

/-- An isothermal change of the applied field from `H_i` to `H_f`, with the
material tracking the equation of state at every intermediate instant.

Calibration: the heat transferred into the torus is measured against the
demagnetized reference state `M = 0`, where the cumulative heat readout is
normalized to zero; the initial and final states of the process sit at
`M_of_H H_i`, `M_of_H H_f` on the same EOS branch `T M V = n K H` as the
reference state (the reference field `0` is included in the tracked range via
`Set.uIcc 0 (max H_i H_f)`, so the presence of `0` in the EOS field-range is
part of the record, regardless of which field endpoint is smaller). -/
structure IsothermalFieldChange (p : TorusParams) where
  /-- Fixed temperature of the process. -/
  T : ℝ
  /-- Initial applied field. -/
  H_i : ℝ
  /-- Final applied field. -/
  H_f : ℝ
  /-- Magnetization along the process, parametrized by the applied field. -/
  M_of_H : ℝ → ℝ
  /-- Cumulative heat transferred into the torus along the isothermal
  ramp, as a function of the magnetization of the current state (the
  temperature is fixed at `T`, so it is not an argument). -/
  Q_in : ℝ → ℝ
  /-- The temperature stays fixed, at a nonzero (physical) value. -/
  hT : T ≠ 0
  /-- The equation of state holds along the whole tracked field range:
  the convex hull of the two endpoints and the demagnetized reference field
  `0`, so both endpoint states and the reference state lie on the same EOS
  branch of the isotherm. -/
  h_eos : ∀ H ∈ Set.Icc (min 0 (min H_i H_f)) (max 0 (max H_i H_f)),
    SatisfiesEOS p ⟨T, M_of_H H, H⟩
  /-- Heat-readout calibration: the demagnetized state carries zero
  cumulative transferred heat. -/
  h_ref : Q_in 0 = 0
  /-- Orientation branch of the field ramp: `true` when the final
  magnetization is at least the initial one. -/
  field_increases : Bool
  /-- The branch flag agrees with the actual endpoints. -/
  h_branch : field_increases = decide (M_of_H H_i ≤ M_of_H H_f)

/-- The recorded closed-form value of the heat transferred into the torus
along an isothermal field change,

`Q = -(μ₀ * n * K / (2 * T)) * (H_f^2 - H_i^2)`.

This definition only *names* the quantity the target theorem speaks about
(the answer carrier); no theorem hypothesis states that the physical heat
equals this value — the proof obligation is to derive that equality from the
EOS, the work law `dW = μ₀ V H dM`, and the first law via the two integrals
`∫_{H_i}^{H_f} μ₀ (n K / T) H dH` (equivalently
`∫_{M_i}^{M_f} μ₀ V H_of_M dM`, FTC-consistent since the integrands agree
along the EOS trajectory). -/
noncomputable def heat_into_torus_value (p : TorusParams)
    (proc : IsothermalFieldChange p) : ℝ :=
  -(p.mu0 * p.n * p.K / (2 * proc.T)) * (proc.H_f ^ 2 - proc.H_i ^ 2)

/-- **Bridge lemma.** Along the tracked isotherm, the magnetization is
pinned by the equation of state to the linear function of the applied field

`M_of_H H = n * K * H / (T * V)`

at every field in the recorded range — this is the pointwise solution of the
EOS (`h_eos`) for the magnetization, using `V ≠ 0` and `T ≠ 0`.  It is the
content needed to rewrite the work density into a linear function of `M`
(bridge to `integral_pow`); it does not presuppose any part of the closed
form for the heat. -/
theorem magnetization_eq_eos_solution (p : TorusParams)
    (proc : IsothermalFieldChange p)
    (hV : p.V ≠ 0) {H : ℝ}
    (hH : H ∈ Set.Icc (min 0 (min proc.H_i proc.H_f))
      (max 0 (max proc.H_i proc.H_f))) :
    proc.M_of_H H = p.n * p.K * H / (proc.T * p.V) := by
  have h := proc.h_eos H hH
  have hT : proc.T ≠ 0 := proc.hT
  unfold SatisfiesEOS at h
  field_simp
  linear_combination h

/-- **Bridge lemma.** The magnetization-ramp leg from the demagnetized
reference `0` to any tracked endpoint magnetization `M_of_H H` stays inside
the tracked field range, so the equation of state — and hence
`magnetization_eq_eos_solution` — applies to every point of the work
integrals `∫ M in 0..M_of_H H, workDensity M`.  The proof is a case
analysis on the position of `M ∈ Set.uIcc 0 (M_of_H H)` against the
endpoint membership `h_eos`-range bounds; the range endpoints are
`min`/`max` combinations, so `min_comm`/`max_comm` + `le_min`/`max_le`
chaining closes it.  It is a pure set-inclusion obligation with no physical
content beyond the convexity of the tracked range. -/
theorem leg_mem_tracked_range (p : TorusParams)
    (proc : IsothermalFieldChange p)
    (H : ℝ) (hH : H ∈ Set.Icc (min 0 (min proc.H_i proc.H_f))
      (max 0 (max proc.H_i proc.H_f)))
    (M : ℝ) (hM : M ∈ Set.uIcc 0 (proc.M_of_H H)) :
    M ∈ Set.Icc (min 0 (min proc.H_i proc.H_f))
      (max 0 (max proc.H_i proc.H_f)) := by
  sorry

/-- **Bridge lemma (evaluation of one isothermal leg).** The work delivered
on the torus along the isothermal ramp from the demagnetized reference to
field `H` equals

`∫ M in 0..M_of_H H, μ₀ V M_of_H M = (μ₀ * n * K / (2 * T)) * (M_of_H H)^2`,

obtained by rewriting the integrand with the EOS solution
(`magnetization_eq_eos_solution`, applicable pointwise on the leg by
`leg_mem_tracked_range` via `intervalIntegral.integral_congr`) and then
evaluating `∫ c * M dM` with `intervalIntegral.integral_const_mul` +
`integral_id`.  This is the micro-evaluation used once per endpoint in the
target proof; it still requires the algebra, so nothing here assumes the
final closed form. -/
theorem leg_work_integral_eval (p : TorusParams)
    (proc : IsothermalFieldChange p)
    (hV : p.V ≠ 0) {H : ℝ}
    (hH : H ∈ Set.Icc (min 0 (min proc.H_i proc.H_f))
      (max 0 (max proc.H_i proc.H_f)))
    (workDensity : ℝ → ℝ)
    (hdens : IsMagneticWorkDensity p proc.M_of_H workDensity) :
    ∫ M in (0)..proc.M_of_H H, workDensity M =
      (p.mu0 * p.n * p.K / (2 * proc.T)) * (proc.M_of_H H) ^ 2 := by
  sorry

/-- The physical heat transferred into the torus between the initial and
final states of the isothermal field change: the difference of the tracked
cumulative heat readout.  This is the quantity the target theorem
characterizes; the recorded answer is its closed form, which must still be
derived — nothing asserts it in advance. -/
noncomputable def heatTransferredIntoTorus (p : TorusParams)
    (proc : IsothermalFieldChange p) : ℝ :=
  proc.Q_in (proc.M_of_H proc.H_f) - proc.Q_in (proc.M_of_H proc.H_i)

/-- **Target.** Along an isothermal field change of the paramagnetic torus
satisfying the equation of state, with the magnetic work `dW = μ₀ V H dM`
of part A.3 (recorded in the first-law density below) and the first law of
thermodynamics, the heat transferred into the torus
(`heatTransferredIntoTorus`, the difference of the tracked heat readout
between the final and initial states) equals the recorded closed form

`Q = -(μ₀ * n * K / (2 * T)) * (H_f^2 - H_i^2)`

(`heat_into_torus_value`).  No hypothesis states this closed form: the
first-law hypothesis only supplies leg balances `Q_in M_target - Q_in M₀ =
(U T − U T) − ∫ M₀..M_target workDensity` against the demagnetized
reference, and deriving the value of the integral is the proof obligation:
`leg_work_integral_eval` (built on `magnetization_eq_eos_solution` +
`leg_mem_tracked_range` + `intervalIntegral.integral_congr` +
`intervalIntegral.integral_const_mul` + `integral_id`) evaluates each leg,
then `magnetization_eq_eos_solution` at `H_i, H_f` and `field_simp`/`ring`
reduce the difference to the closed form.

Blueprint label: `thm:physics:IPhO_2026_3_B_1:target`. -/
theorem isothermal_heat_into_torus (p : TorusParams) (U : ℝ → ℝ)
    (proc : IsothermalFieldChange p)
    (hU : HasHeatCapacityLaw p U)
    (hV : p.V ≠ 0)
    (h_first_law : ∀ (workDensity : ℝ → ℝ),
      IsMagneticWorkDensity p proc.M_of_H workDensity →
      ObeysFirstLawMagnetic p U proc.T workDensity proc.Q_in)
    (Q : ℝ) (hQ : Q = heatTransferredIntoTorus p proc) :
    Q = heat_into_torus_value p proc := by
  sorry

/-- **Recorded official answer (checking form).** The heat
`heat_into_torus_value p proc` carried by the target theorem equals the
closed form recorded in the answer key,

`Q = -(μ₀ * n * K / (2 * T)) * (H_f^2 - H_i^2)`.

This is conclusion-side only: it pins the closed form of
`heat_into_torus_value`, it is not used as a hypothesis of any theorem. -/
theorem official_answer_value (p : TorusParams)
    (proc : IsothermalFieldChange p) :
    heat_into_torus_value p proc =
      -(p.mu0 * p.n * p.K / (2 * proc.T)) * (proc.H_f ^ 2 - proc.H_i ^ 2) :=
  rfl
end IPhO2026.Problem3.B1
