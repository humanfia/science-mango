import Mathlib
import Physlib.Electromagnetism.Dynamics.Basic

/-!
# IPhO 2026, Problem 3 (T3), Part A.3 — Work done on the paramagnetic material

Source: IPhO 2026 Theoretical Exam, Problem T3, part T3-A3 (0.2 pts).
Blueprint chapter: `blueprint/src/chapters/IPhO2026Problems_problem_IPhO_2026_3_A_3.tex`,
covering declaration label `thm:physics:IPhO_2026_3_A_3:target`.

## Physical setup

A homogeneous isotropic paramagnetic torus (the "Pm-T") has mean radius `R`,
inner (winding) radius `r` with `r ≪ R`, cross-sectional area `A`, and volume
`V = 2πR·A` (so the mean circumference is `2πR = V/A`). An insulated
conducting wire is wound densely around it with `N` turns carrying
instantaneous current `I`. The magnetic field intensity `H`, flux density `B`,
and magnetization `M` are approximately uniform throughout the core.

Governing laws (T3-A hint and problem statement):

* Ampère's law for the H-field: `∮ H·dℓ = I_C`, where `I_C = N·I` is the net
  free current through the area bounded by the closed curve `C` (the mean
  circle of the torus). With uniformity and `2πR = V/A`, this yields
  `H = N·I·A / V` (part A.1). The sign of `H` tracks the sign of `I`
  (orientation of the winding relative to `C`).
* Constitutive relation in the material: `B = μ₀·H + μ₀·M`, hence for
  increments `dB = μ₀·dH + μ₀·dM`.
* Sign convention: work and heat **entering** the paramagnetic torus are
  positive.

Previous part (A.2, natural-language prerequisite): the work performed by the
external voltage source when `B` changes by `dB` is `dW_emf = V·H·dB`.

## Current subquestion (A.3)

The total work `dW_emf` done by the voltage source splits into
`dW_vac`, the work that would change the magnetic field if the toroid had a
vacuum core, and `dW`, the work done on the paramagnetic material itself:

`dW_emf = dW_vac + dW`

Subtracting the vacuum-core contribution (`dW_vac = μ₀·V·H·dH`, the A.2 law
applied to a core with `M = 0`) gives the recorded answer:

`dW = μ₀·V·H·dM`.

## Scope

This file is an autoformalization: all proof bodies are `by sorry`. The
declarations preserve the physical quantities, dimensional roles, governing
laws, sign conventions, and the final relation of the source. The current
target conclusion `dW = μ₀·V·H·dM` appears **only** as the conclusion of
`dW_eq_mu0_V_H_dM`; it never occurs as a hypothesis, structure field, or
definition.
-/

open Electromagnetism

namespace IPhO2026.T3A3

/-- Geometry of the thin paramagnetic torus (the Pm-T).

Dims: `R`, `r` in meters; `A` in m²; `V` in m³. The volume identity
`V = 2πR·A` expresses that the torus is thin (`r ≪ R`): its volume is the
cross-sectional area times the mean circumference `2πR`. -/
structure PmTTorus where
  /-- Mean radius `R` of the torus (m). -/
  R : ℝ
  /-- Inner (winding) radius `r` of the torus (m). -/
  r : ℝ
  /-- Cross-sectional area `A` of the core (m²). -/
  A : ℝ
  /-- Volume `V` of the core (m³). -/
  V : ℝ
  /-- The inner radius is positive. -/
  r_pos : 0 < r
  /-- Thin-torus regime: `r < R` (source: `r ≪ R`). -/
  r_lt_R : r < R
  /-- The cross-sectional area is positive. -/
  A_pos : 0 < A
  /-- The volume is positive. -/
  V_pos : 0 < V
  /-- Thin-torus volume identity: `V = 2πR·A`. -/
  V_eq : V = 2 * Real.pi * R * A

/-- The insulated wire wound densely around the torus: `N` turns carrying an
instantaneous current `I` (A). The current is a signed real: its sign fixes
the orientation of the drive relative to the chosen positive H direction. -/
structure PmTWinding where
  /-- Number of turns `N` (dimensionless). -/
  N : ℕ
  /-- Instantaneous current `I` in the wire (A). -/
  I : ℝ
  /-- The winding has at least one turn. -/
  N_pos : 0 < N

/-- Ampère's law for the H-field, specialized to the densely wound thin torus:
`∮ H·dℓ = I_C` over the mean circle `C` gives `H·(2πR) = N·I`, i.e.
`H = N·I·A/V` using `2πR = V/A`. The sign of `H` follows the sign of `I`. -/
def AmpereLawTorus (t : PmTTorus) (w : PmTWinding) (H : ℝ) : Prop :=
  H = (w.N : ℝ) * w.I * t.A / t.V

/-- The mean circumference of the torus is `2πR = V/A`; this is the geometric
bridge from `∮ H·dℓ = H·(2πR)` to the `V/A` form used in `AmpereLawTorus`. -/
lemma meanCircumference_eq (t : PmTTorus) : 2 * Real.pi * t.R = t.V / t.A := by
  rw [t.V_eq, mul_div_cancel_right₀ _ (ne_of_gt t.A_pos)]

/-- Instantaneous, approximately uniform electromagnetic state of the core.

Dims: `H`, `M` in A/m; `B` in tesla. -/
structure PmTFieldState where
  /-- Magnetic field intensity `H` in the torus (A/m). -/
  H : ℝ
  /-- Magnetic flux density `B` in the torus (T). -/
  B : ℝ
  /-- Magnetization `M` of the paramagnetic material (A/m). -/
  M : ℝ

/-- Constitutive relation of the material (governing law):
`B = μ₀·H + μ₀·M`, with `μ₀` the magnetic permeability of free space as
supplied by the PhysLean `FreeSpace` structure. -/
def ConstitutiveBH (𝓕 : FreeSpace) (s : PmTFieldState) : Prop :=
  s.B = 𝓕.μ₀ * s.H + 𝓕.μ₀ * s.M

/-- An admissible infinitesimal process of the Pm-T: a current state plus the
increments `dB`, `dH`, `dM` (dims T, A/m, A/m) produced when the source
current changes slightly.

The field hypotheses are governing laws, not target conclusions:
Ampère's law fixes the state `H`; the constitutive law constrains both the
state and its increments. The differential consequence
`dB = μ₀·dH + μ₀·dM` is what makes the vacuum-core subtraction work. -/
structure PmTVariation (t : PmTTorus) (w : PmTWinding) (𝓕 : FreeSpace) where
  /-- Current field state of the core. -/
  s : PmTFieldState
  /-- Ampère's law for the densely wound torus (Hint of T3-A). -/
  H_ampere : AmpereLawTorus t w s.H
  /-- Constitutive relation `B = μ₀·H + μ₀·M` in the current state. -/
  BH : ConstitutiveBH 𝓕 s
  /-- Infinitesimal change of `B` (T). -/
  dB : ℝ
  /-- Infinitesimal change of `H` (A/m). -/
  dH : ℝ
  /-- Infinitesimal change of the magnetization `M` (A/m). -/
  dM : ℝ
  /-- The increments respect the (linear) constitutive relation:
  `dB = μ₀·dH + μ₀·dM`. -/
  dBH : dB = 𝓕.μ₀ * dH + 𝓕.μ₀ * dM

/-- For a vacuum core (`M = 0`, hence `dM = 0`) the constitutive relation
reduces the B-increment to `dB = μ₀·dH`. This is the bridge justifying the
`vacuum_part` field of `PmTWorkBudget`: the A.2 source-work law applied to a
vacuum core involves exactly this `dB`. -/
lemma dB_of_vacuum_core (𝓕 : FreeSpace) {dB dH : ℝ}
    (h : dB = 𝓕.μ₀ * dH + 𝓕.μ₀ * 0) : dB = 𝓕.μ₀ * dH := by
  rwa [mul_zero, add_zero] at h

/-- The infinitesimal work budget of the Pm-T (all entries in joules, with the
sign convention that work entering the paramagnetic torus is positive).

The fields `emf_source`, `split`, and `vacuum_part` are the licensed inputs
of subquestion A.3 — a previous-part result, the problem statement's
decomposition, and the source-work law applied to a vacuum core. The A.3
answer `dW = μ₀·V·H·dM` is **not** among them. -/
structure PmTWorkBudget (t : PmTTorus) (w : PmTWinding) (𝓕 : FreeSpace)
    (v : PmTVariation t w 𝓕) where
  /-- `dW_emf`: infinitesimal work performed by the external voltage
  source (J). -/
  dW_emf : ℝ
  /-- `dW_vac`: the part of `dW_emf` that would change the magnetic field if
  the toroid had a vacuum core (J). -/
  dW_vac : ℝ
  /-- `dW`: the work done on the paramagnetic material itself (J). -/
  dW : ℝ
  /-- Previous part A.2 (reusable conclusion): the voltage-source work for a
  change `dB` of `B` is `dW_emf = V·H·dB`. -/
  emf_source : dW_emf = t.V * v.s.H * v.dB
  /-- Problem statement of A.3: the source work divides into the vacuum-core
  part and the work done on the paramagnetic material itself. -/
  split : dW_emf = dW_vac + dW
  /-- Vacuum-core contribution: the A.2 source-work law applied to a core with
  `M = 0`, whose B-increment is `dB = μ₀·dH` (see `dB_of_vacuum_core`).
  `H` is unchanged between the two cores because Ampère's law sees only the
  free current `N·I`. -/
  vacuum_part : dW_vac = 𝓕.μ₀ * t.V * v.s.H * v.dH

/-- The defining move of A.3: subtracting the vacuum-core contribution from
the voltage-source work isolates the work done on the material,
`dW = dW_emf - dW_vac`. -/
lemma dW_eq_sub_vac (t : PmTTorus) (w : PmTWinding) (𝓕 : FreeSpace)
    (v : PmTVariation t w 𝓕) (b : PmTWorkBudget t w 𝓕 v) :
    b.dW = b.dW_emf - b.dW_vac := by
  linarith [b.split]

/-- Substituting the A.2 law and the vacuum-core contribution expresses the
material work through the increments of `H` and `B`:
`dW = V·H·(dB - μ₀·dH)`. Together with `dB = μ₀·dH + μ₀·dM` this is one ring
step away from the A.3 answer. -/
lemma dW_eq_VH_dB_sub_mu0_dH (t : PmTTorus) (w : PmTWinding) (𝓕 : FreeSpace)
    (v : PmTVariation t w 𝓕) (b : PmTWorkBudget t w 𝓕 v) :
    b.dW = t.V * v.s.H * (v.dB - 𝓕.μ₀ * v.dH) := by
  have h1 := dW_eq_sub_vac t w 𝓕 v b
  rw [h1, b.emf_source, b.vacuum_part]
  ring

/-- **Subquestion A.3 target.** The work done on the paramagnetic material
itself when the magnetization changes by `dM` is

`dW = μ₀·V·H·dM`.

(Recorded official answer: `dW = α·V·μ₀·H·dM` with `α = 1`.) -/
theorem dW_eq_mu0_V_H_dM (t : PmTTorus) (w : PmTWinding) (𝓕 : FreeSpace)
    (v : PmTVariation t w 𝓕) (b : PmTWorkBudget t w 𝓕 v) :
    b.dW = 𝓕.μ₀ * t.V * v.s.H * v.dM := by
  rw [dW_eq_VH_dB_sub_mu0_dH t w 𝓕 v b, v.dBH]
  ring

end IPhO2026.T3A3
