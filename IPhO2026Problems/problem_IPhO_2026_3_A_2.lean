import Mathlib
import Physlib.Electromagnetism.Dynamics.Basic

/-!
# IPhO 2026, Problem 3, Part A.2

A homogeneous isotropic paramagnetic torus has mean radius `R`, inner radius `r`
with `r << R`, volume `V`, and cross-sectional area `A`.  An insulated conducting
wire is wound densely around it with `N` turns and instantaneous current `I`.
The fields `H` and `B` and the magnetization `M` are approximately uniform in the torus.
The governing laws are `B = μ₀ H + μ₀ M`, Ampère's law, and the sign convention that
work and heat entering the paramagnetic torus are positive.

**Current subquestion.**  Find the work `dW_emf` performed by the external voltage
source when `B` changes by `dB`.

**Recorded answer.**  `dW_emf = V * H * dB` (conclusion-side only).

Recorded answer context comes from the official IPhO 2026 T3 package (Part A.2).
The previous part A.1 (`H = N * I * A / V`) is used only as a natural-language
prerequisite describing the geometry; it is not imported as a Lean dependency —
it appears only as the derivable bridge lemma
`fieldStrength_eq_N_mul_I_mul_A_div_V`.
-/

namespace IPhO2026_3_A_2

open Electromagnetism

/-- Local self-contained positive-real constraint carrying the physical role
"this scalar is a strictly positive amount" (length, area, volume, turn count,
elapsed time).  It is a local stand-in for the PhysLean `IsPositive` constraint
(memory pattern for wave-3 repairs); it is kept local because the import policy
for this project allows only one targeted `Physlib` import per file, which here
is `Physlib.Electromagnetism.Dynamics.Basic` (the `FreeSpace` constants). -/
inductive IsPositive (x : ℝ) : Prop
  | intro : 0 < x → IsPositive x

/-- The geometry of the torus and its winding: mean radius `R`, inner radius `r`
(thin-ring approximation `r ≪ R`), cross-sectional area `A`, volume `V` of the
paramagnetic material, and the number `N` of densely wound wire turns.
The record fields carry the stated dimensional constraints `V = 2 π R A` (the ring
volume formula used implicitly in Part A.1) and positivity/non-negativity side
conditions, so that a `ToroidData` value cannot be interpreted arbitrarily. -/
structure ToroidData where
  /-- Mean radius of the torus. -/
  R : ℝ
  /-- Inner radius of the torus. -/
  r : ℝ
  /-- Volume of the paramagnetic material. -/
  V : ℝ
  /-- Cross-sectional area of the torus. -/
  A : ℝ
  /-- Number of turns wound around the torus. -/
  N : ℝ
  /-- The mean radius is positive. -/
  R_pos : IsPositive R
  /-- The inner radius is positive. -/
  r_pos : IsPositive r
  /-- Thin-ring (slender torus) approximation `r ≪ R`. -/
  thin_ring : r < R
  /-- The cross-sectional area is positive. -/
  A_pos : IsPositive A
  /-- The volume is positive. -/
  V_pos : IsPositive V
  /-- At least one turn is wound around the torus. -/
  N_pos : IsPositive N
  /-- Ring volume law: `V = 2 π R · A`. -/
  volume_eq : V = 2 * Real.pi * R * A

/-- The operating state of a uniformly magnetized torus at one instant:
the instantaneous current `I` in the winding, the magnetic field strength `H`,
the magnetic flux density `B`, and the magnetization `M`, all spatially uniform
inside the torus, subject to the constitutive law `B = μ₀ H + μ₀ M` and to
Ampère's law along the mean circumference, giving `H = N I / (2 π R)`. -/
structure UniformToroidOperatingPoint (fs : FreeSpace) (t : ToroidData) where
  /-- Instantaneous current in the winding. -/
  I : ℝ
  /-- Magnetic field strength, uniform in the torus. -/
  H : ℝ
  /-- Magnetic flux density, uniform in the torus. -/
  B : ℝ
  /-- Magnetization of the paramagnetic material, uniform in the torus. -/
  M : ℝ
  /-- Constitutive relation `B = μ₀ H + μ₀ M`. -/
  constitutive : B = fs.μ₀ * H + fs.μ₀ * M
  /-- Ampère's law along the mean circumference `2 π R` linking the free
  current `N · I`, giving `H = N · I / (2 π R)`. -/
  ampere : H = t.N * I / (2 * Real.pi * t.R)

/-- Bridge to the previous part A.1, whose recorded conclusion writes the field
magnitude as `H = N · I · A / V`.  The same field is expressed here through the
present file's data; the two forms agree because `V = 2 π R · A`
(the `ToroidData.volume_eq` law).  This is a derivable bridge lemma on the
conclusion side, not an assumption. -/
lemma fieldStrength_eq_N_mul_I_mul_A_div_V
    (fs : FreeSpace) (t : ToroidData) (op : UniformToroidOperatingPoint fs t) :
    op.H = t.N * op.I * t.A / t.V := by
  have hA : t.A ≠ 0 := ne_of_gt t.A_pos.1
  have h2πR : 2 * Real.pi * t.R = t.V / t.A := by
    rw [t.volume_eq, mul_div_cancel_right₀ _ hA]
  rw [op.ampere, h2πR, div_div_eq_mul_div]

/-- A small quasistatic change of the operating point, together with the
electromotive force `emf` induced in the `N`-turn winding over the elapsed
time `dt` while the flux density changes by `dB`.

Governing law carried as a field (Faraday's law of induction for a thin toroid
with uniform `B` and cross-section `A`): the flux through each of the `N` turns
changes by `A · dB`, so the source supplies `emf · dt = N · A · dB` against the
induced EMF.  The field is an equation, so it eliminates to a usable constraint
in proofs; it is the physical law of induction, not the Part A.2 answer (the
answer expresses the work as `V · H · dB`, which does not appear here). -/
structure InducedEMFChange (t : ToroidData) where
  /-- Electromotive force across the winding during the change. -/
  emf : ℝ
  /-- Elapsed (short) time of the change. -/
  dt : ℝ
  /-- Change of the magnetic flux density inside the torus. -/
  dB : ℝ
  /-- The elapsed time is strictly positive. -/
  dt_pos : IsPositive dt
  /-- Faraday's law integrated over the change: `emf · dt = N · A · dB`. -/
  faraday : emf * dt = t.N * t.A * dB

/-- Energy amount delivered by the external voltage source to the torus
circuit, as a typed scalar quantity with its sign convention: positive means
work entering the paramagnetic torus (the IPhO T3 convention).  The wrapper
distinguishes this physical energy readout from a bare real number; `val` is
the documented scalar projection.  No nonnegativity invariant is bundled:
withdrawal of energy (`dW < 0`), as when `B` decreases, is physical. -/
structure WorkOnSource where
  /-- The scalar energy readout, positive when work enters the torus. -/
  val : ℝ

/-- The work performed by the external voltage source over an induced-EMF
change at operating point `op`: the electrical power `emf · I` integrated
over the elapsed time `dt`.  This is the energy-balance law of a voltage
source (`P = ε · I`); by itself it does not state the Part A.2 answer. -/
noncomputable def sourceWork (fs : FreeSpace) (t : ToroidData)
    (op : UniformToroidOperatingPoint fs t) (e : InducedEMFChange t) :
    WorkOnSource :=
  ⟨e.emf * op.I * e.dt⟩

/-- **Part A.2 target.**  Under an infinitesimal change `dB` of the magnetic
flux density, the work performed by the external voltage source is
`dW_emf = V · H · dB` (recorded official answer, conclusion-side only).
The sign convention is that work entering the paramagnetic torus is positive,
so a positive `dW_emf` corresponds to energy delivered by the source.
The conclusion is not among the hypotheses: the assumptions are the governing
laws (constitutive relation, Ampère's law, Faraday's law, ring-volume law,
source power law), and reaching `V · H · dB` still requires combining them. -/
theorem work_emf_eq_V_mul_H_mul_dB
    (fs : FreeSpace) (t : ToroidData) (op : UniformToroidOperatingPoint fs t)
    (e : InducedEMFChange t) :
    sourceWork fs t op e = ⟨t.V * op.H * e.dB⟩ := by
  have hV : t.V ≠ 0 := ne_of_gt t.V_pos.1
  have key : t.N * op.I * t.A = t.V * op.H := by
    rw [fieldStrength_eq_N_mul_I_mul_A_div_V fs t op, mul_div_cancel₀ _ hV]
  unfold sourceWork
  congr 1
  linear_combination key * e.dB + e.faraday * op.I

end IPhO2026_3_A_2
