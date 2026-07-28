import Mathlib
import Physlib.Thermodynamics.Temperature.Basic

/-!
# IPhO 2026, Experimental Problem 4 (E1), Part C.7 — Acrylic thermal conductivity

This file autoformalizes blueprint chapter
`blueprint/src/chapters/IPhO2026Problems_problem_IPhO_2026_4_C_7.tex`
(marked `% archon:physics`).

## Physical setup (from the official source pages and Figure 17)

Water in the inner cylinder (IC) and the outer cylinder (OC) exchanges heat
radially through the acrylic cylindrical wall that separates them. The
apparatus records the water temperatures `T_IC` and `T_OC` as functions of
time. Two governing relations are given in the problem text:

* Equation (4) (lumped heat-flow model): `dQ/dt = (T_OC − T_IC) / R_Th`,
  where `R_Th` is the effective thermal resistance of the wall (its value
  `R_Th = 1.17 ± 0.03 K/W` was determined in part C.6 from the C5 graph).
* Equation (6) (Fourier's law for radial conduction through a slim
  cylindrical wall): `dQ/dt = −λ·A·dT/dr`, where `A` is the area of the
  wall, `λ` the thermal conductivity of the wall material, and `r` the
  distance from the cylinder axis.

Figure 17 dimensions used along the proof route: IC bore diameter
`33.7 ± 0.1 mm` and IC wall thickness `t = 6.4 ± 0.1 mm`, from which the
acrylic wall's inner and outer radii are
`r₁ = 33.7/2 mm = 16.85 mm`, `r₂ = r₁ + t = 23.25 mm`. The wetted wall
height is the IC water level `h = 10 cm` (Procedure step 3); the lateral
area at radius `r` is `A(r) = 2·π·r·h`.

The current subquestion (C.7, 1.6 pt): using equations (4) and (6),
determine the acrylic conductivity `λ`, indicating the formula used.
Recorded answer: `λ = ln(r₂/r₁) / (2·π·h·R_Th)`; official sample value
`λ = 0.25 ± 0.01 W/(m·K)`.

## What is proved where

* `acrylicConductivity_formula` — the derivation formula
  `λ = ln(r₂/r₁) / (2·π·h·R_Th)` follows from the two governing laws plus
  the radial steady-state integration. This is the "formula that you used"
  part of C.7. (The proof needs quantitative integration of Fourier's law
  and is left `sorry` at the autoformalize stage.)
* `acrylicConductivity_officialSample` — propagation of the C.6
  measurement `R_Th ∈ [1.14, 1.20] K/W` and Figure-17 geometry
  `r₂/r₁ = 23.25/16.85`, `h = 0.1 m` through the C.7 formula: the
  contract is the uncertainty window `|λ − 0.25| ≤ 0.01 W/(m·K)` reported
  in the official sample. (Arithmetic interval/refinement bound, left
  `sorry`.)
-/

open Real

namespace IPhO2026.Problem4.C7

/-! ### Scalar readouts of the physical quantities

The problem's quantities are physical (temperatures, powers, lengths,
conductivity), but the current subquestion only ever manipulates their
numerical values in SI units, so scalar real-number fields for the
readouts are appropriate; the physical roles and laws are carried by the
structures below. -/

/-- Figure-17/datasheet geometry of the acrylic wall separating the inner
(IC) and outer (OC) cylinders, plus the wetted wall height. The radii
come from the IC bore diameter `33.7 mm` and wall thickness `6.4 mm` of
Fig. 17 (`r₁ = 16.85 mm`, `r₂ = 23.25 mm`); the height `h` is the IC water
level set to `10 cm` in Procedure step 3. Lengths are stored in metres. -/
structure CylindricalWallGeometry where
  /-- Inner radius of the acrylic wall (IC bore radius), in metres. -/
  r₁ : ℝ
  /-- Outer radius of the acrylic wall (interface to the OC), in metres. -/
  r₂ : ℝ
  /-- Wetted height of the wall exchanging heat (IC water level), in metres. -/
  h : ℝ
  r₁_pos : 0 < r₁
  r₁_lt_r₂ : r₁ < r₂
  h_pos : 0 < h

namespace CylindricalWallGeometry

/-- Lateral area of the cylindrical wall at radius `r`:
`A(r) = 2·π·r·h`. This is the area `A` appearing in Fourier's law (6) for
radial conduction through a slim cylindrical wall; it grows linearly with
the distance `r` from the cylinder axis. -/
noncomputable def lateralArea (G : CylindricalWallGeometry) (r : ℝ) : ℝ :=
  2 * π * r * G.h

end CylindricalWallGeometry

/-- Scalar numerical data read off the experiment in SI units: measured
wall thermal resistance from part C.6 (`1.17 ± 0.03 K/W`, of which only
the interval is used here) and the recorded water temperatures of the two
cylinders. -/
structure ThermalExperimentData where
  /-- Effective wall thermal resistance measured in part C.6, in K/W. -/
  R_Th : ℝ
  /-- Water temperature in the inner cylinder, in K. -/
  T_IC : ℝ
  /-- Water temperature in the outer cylinder, in K. -/
  T_OC : ℝ

/-! ### Governing-law interfaces -/

/-- Equation (4) of the problem (lumped heat-flow model): the heat
received by the water in the IC through the wall per unit time is
`dQ/dt = (T_OC − T_IC)/R_Th`. This is taken as a modeling hypothesis
(governing law), not as the definition of `R_Th` nor of the heat current
`P`; it only asserts the proportionality of an already-given current to
the temperature difference. -/
def LumpedHeatFlowLaw (D : ThermalExperimentData) (P : ℝ) : Prop :=
  P = (D.T_OC - D.T_IC) / D.R_Th

/-- Steady 1-D radial Fourier conduction through a slim cylindrical wall
(Equation (6) of the problem, `dQ/dt = −λ·A·dT/dr`, with the steady-state
consequence that the heat current is independent of `r`):

* `steady` is the physical steady-state/homogenization branch (the pump
  homogenizes the water temperatures so the profile is stationary),
  expressed as constancy of the outward heat current `P : ℝ → ℝ` on the
  whole wall `r ∈ [r₁, r₂]`;
* `fourier` is Fourier's law at every radius: the outward current equals
  `−λ·A(r)·T'(r)` with `A(r) = 2·π·r·h`.

The predicate is eliminable: `wall_current` extracts the constant value of
the current, and `fourier`/`steady` directly provide the pointwise
equations a proof can integrate over `[r₁, r₂]`. -/
structure RadialFourierConduction
    (G : CylindricalWallGeometry) (lam : ℝ)
    (T : ℝ → ℝ) (P : ℝ → ℝ) : Prop where
  /-- Steady state: the radial heat current is constant across the wall. -/
  steady : ∀ r ∈ Set.Icc G.r₁ G.r₂, ∀ r' ∈ Set.Icc G.r₁ G.r₂, P r = P r'
  /-- Fourier's law (6) at radius `r`: `P r = −λ · (2·π·r·h) · dT/dr`. -/
  fourier : ∀ r ∈ Set.Icc G.r₁ G.r₂,
    P r = -lam * G.lateralArea r * deriv T r

namespace RadialFourierConduction

/-- The constant wall heat current delivered by the `steady` field of a
`RadialFourierConduction` witness. -/
theorem wall_current {G : CylindricalWallGeometry} {lam : ℝ}
    {T P : ℝ → ℝ} (hF : RadialFourierConduction G lam T P)
    {r r' : ℝ} (hr : r ∈ Set.Icc G.r₁ G.r₂)
    (hr' : r' ∈ Set.Icc G.r₁ G.r₂) : P r = P r' :=
  hF.steady r hr r' hr'

end RadialFourierConduction

/-! ### Target conclusions of subquestion C.7 -/

/-- **C.7 derivation formula** (the "formula that you used").

Combining the lumped heat-flow model (4) `dQ/dt = (T_OC − T_IC)/R_Th`
with steady radial Fourier conduction (6) `dQ/dt = −λ·A·dT/dr` through
the wall `[r₁, r₂]`, and imposing the boundary temperatures
`T(r₁) = T_IC` (the wall's inner face is at the IC water temperature) and
`T(r₂) = T_OC` (the outer face is at the OC water temperature), the
acrylic conductivity is

`λ = ln(r₂/r₁) / (2·π·h·R_Th)`.

The formal content (to be proved in the prover stage) is the integration
of Fourier's law: constancy and positivity of
`P = (T_OC − T_IC)/R_Th > 0` give `dT/dr < 0` (outward-decreasing
temperature profile, so `deriv T` exists almost everywhere on `(r₁, r₂)`),
and integrating `P/(2·π·λ·h·r) = −dT/dr` over `[r₁, r₂]` yields
`P·ln(r₂/r₁)/(2·π·λ·h) = T_IC − T_OC`; substituting (4) and solving for
`λ` gives the claimed formula. Carrier of this bridge: this theorem's
contract (Mathlib: `deriv_inv`, `intervalIntegral.integral_const_mul`,
`integral_one_div` / `integral_inv`). -/
theorem acrylicConductivity_formula
    (G : CylindricalWallGeometry) (D : ThermalExperimentData)
    (lam : ℝ) (T : ℝ → ℝ) (P : ℝ → ℝ)
    (hflow : LumpedHeatFlowLaw D (P G.r₁))
    (hfourier : RadialFourierConduction G lam T P)
    (hR : D.R_Th ≠ 0) (hlam : lam ≠ 0)
    (hT_inner : T G.r₁ = D.T_IC) (hT_outer : T G.r₂ = D.T_OC)
    (hΔT : D.T_IC < D.T_OC) :
    lam = Real.log (G.r₂ / G.r₁) / (2 * π * G.h * D.R_Th) := by
  -- PROVER REPORT (redraft requested — see task_results/IPhO_2026_4_C_7.md).
  -- The stated equality is NOT derivable from the hypotheses: the
  -- mathematical content flips sign.  Under `hΔT : T_IC < T_OC`, Eq. (4)
  -- gives `P = (T_OC - T_IC)/R_Th > 0` (for `R_Th > 0`), i.e. heat flows
  -- from the outer cylinder INWARD, so the temperature DECREASES outward:
  -- `dT/dr < 0`.  Fourier's law `P = -lam·A·dT/dr` with `A > 0`, `P > 0`,
  -- `dT/dr < 0` forces `lam < 0`, while
  -- `Real.log (r₂/r₁) / (2·π·h·R_Th) > 0` because `r₂ > r₁ > 0`, `h > 0`.
  -- A machine-checked countermodel (this exact statement refuted while all
  -- hypotheses hold): `G = {r₁:=1, r₂:=2, h:=1}`,
  -- `D = {R_Th := Real.log 2 / (2π), T_IC := 0, T_OC := Real.log 2 / (2π)}`,
  -- `lam = -1`, `T r = (2π)⁻¹ * Real.log r`, `P = fun _ => 1`.
  -- Then `hfourier.steady` holds by `rfl`, `hfourier.fourier` holds because
  -- `deriv T r = (2π)⁻¹ r⁻¹` (via `Real.deriv_log`) so
  -- `-(-1)·(2π·r·1)·((2π)⁻¹·r⁻¹) = 1 = P r`, all side conditions compute,
  -- yet the claimed RHS equals `+1 ≠ -1 = lam`.
  -- Faithful minimal fix: reverse the drive to `D.T_OC < D.T_IC`
  -- (outward heat flow, `dT/dr ≥ 0`), or add the missing modeling
  -- hypothesis `0 < lam`/`0 < D.R_Th ∧ lam < 0` as appropriate;
  -- then `P·log(r₂/r₁)/(2π lam h) = T(r₂) - T(r₁)` integrates to the
  -- stated formula via `integral_inv`.
  -- Partial progress: establish that the wall current is constant and
  -- equal to the lumped value everywhere on `[r₁, r₂]` (the eliminable
  -- bridge the derivation integrates against), then leave the focused gap.
  have hP_const : ∀ r ∈ Set.Icc G.r₁ G.r₂, P r = P G.r₁ :=
    fun r hr => hfourier.wall_current hr (Set.left_mem_Icc.mpr G.r₁_lt_r₂.le)
  have hP0 : P G.r₁ = (D.T_OC - D.T_IC) / D.R_Th := hflow
  have hΔ : 0 < D.T_OC - D.T_IC := sub_pos.mpr hΔT
  -- The remaining step — integrating
  --   `deriv T r = -P G.r₁ / (lam · 2π h r)` over `[r₁, r₂]` and matching
  -- against `T(r₂) - T(r₁) = T_OC - T_IC`, then solving for `lam` — is
  -- impossible for the stated sign convention (countermodel above).
  -- Note: `hΔT`, `hT_inner`, `hT_outer`, and the positivity of the
  -- right-hand side (shown below) are exactly the ingredients that make the
  -- stated equation unprovable; recorded for the redraft.
  have hr2r1_gt_one : (1:ℝ) < G.r₂ / G.r₁ := by
    rw [one_lt_div G.r₁_pos]
    exact G.r₁_lt_r₂
  have hlog_pos : 0 < Real.log (G.r₂ / G.r₁) := Real.log_pos hr2r1_gt_one
  have hnum_pos : (0:ℝ) < 2 * π * G.h := mul_pos (mul_pos two_pos Real.pi_pos) G.h_pos
  -- Under the missing hypothesis `0 < D.R_Th`, `hnum_pos` and `hlog_pos`
  -- would give `0 < RHS`; combined with the `lam < 0` forced by the
  -- countermodel analysis this contradicts the goal. With only
  -- `D.R_Th ≠ 0` the step `0 < 2 * π * G.h * D.R_Th` is the precise
  -- point the redraft must supply.
  rcases lt_or_gt_of_ne hR with hRneg | hRpos
  · sorry
  · sorry

/-- **C.7 official sample value with propagated uncertainty.**

The official sample takes `R_Th = 1.17 ± 0.03 K/W` (the C.6 measurement,
used here as the interval `R_Th ∈ [1.14, 1.20]`), the Figure-17 geometry
`r₂/r₁ = 23.25/16.85` and wetted height `h = 0.10 m`, and reports
`λ = 0.25 ± 0.01 W/(m·K)`. The theorem contract preserves the uncertainty
as stated: the input window is the hypothesis `hR_central /
hR_uncert` (the C.6 measurement lies in `1.17 ± 0.03 K/W`), and deriving
the `± 0.01` output window from the `± 0.03` resistance window is
interval arithmetic/refinement through the (already separate) derivation
formula, which is taken as the hypothesis `hformula` here because
`acrylicConductivity_formula` is proved independently. -/
theorem acrylicConductivity_officialSample
    (lam R_Th : ℝ)
    (hformula : lam = Real.log ((23.25e-3 : ℝ) / 16.85e-3) /
      (2 * π * (0.10 : ℝ) * R_Th))
    (hR_central : R_Th = 1.17) (hR_uncert : |R_Th - 1.17| ≤ 0.03) :
    |lam - 0.25| ≤ 0.01 := by
  -- PROVER REPORT (redraft requested — see task_results/IPhO_2026_4_C_7.md).
  -- The conclusion is numerically FALSE at the stated inputs: substituting
  -- `R_Th = 1.17` (which satisfies `|R_Th - 1.17| ≤ 0.03`) gives
  -- `lam = log(465/337) / (2π·0.10·1.17) ≈ 0.43795`, so
  -- `|lam - 0.25| ≈ 0.18795 > 0.01`.
  -- Machine-checked refutation chain (used to build this report):
  -- `Real.lt_log_one_add_of_pos` gives `128/401 < log(465/337)`
  -- (with `2·(128/337)/((128/337)+2) = 128/401` by `field_simp; ring`),
  -- `Real.pi_lt_d20` gives `π < 3.141592654`, hence
  -- `lam > (128/401)/(2·3.141592654·0.10·1.17) > 0.43 > 0.26`,
  -- so `|lam - 0.25| > 0.01` — the negation of the goal is provable.
  -- Root cause: with heights in metres as stated, the official answer
  -- `0.25 W/(m·K)` requires `R_Th ≈ 2.05 K/W` or `h ≈ 0.175 m`;
  -- the frozen geometric inputs `r₂/r₁ = 465/337`, `h = 0.10`,
  -- `R_Th = 1.17` are inconsistent with the recorded band at any sign
  -- convention; a redraft must change the numeric inputs (e.g. the wetted
  -- height in the correct SI value or the C.6 resistance) or weaken the
  -- conclusion window. Partial progress: substitute the central value and
  -- split `|·| ≤` into the two one-sided bounds; the upper half
  -- `lam - 0.25 ≤ 0.01` is exactly the disprovable one (see above).
  rw [hR_central] at hformula
  rw [hformula]
  rw [abs_le]
  constructor
  · sorry
  · sorry

end IPhO2026.Problem4.C7
