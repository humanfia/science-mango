import Mathlib

/-!
# IPhO 2026 · Theory problem T3-A2 — "Chasing the absolute zero": work of the
external voltage source

Autoformalization of IPhO 2026 T3-A2 (source:
`reports/ipho_2026/problem_ipho_2026_t3_a2.source.json`; problem pages
`ipho_2026_source/image/T3_page-1.png` (setup, Fig. 3a) and
`ipho_2026_source/image/T3_page-2.png` (T3-A2 statement)).

## Physical scenario (shared context, page 11)

A torus ("Pm-T") of mean radius `R` and inner (tube) radius `r`, made of a
homogeneous isotropic paramagnetic material, is densely wound with an insulated
conducting wire of `N` turns in total, whose ends are connected to an external
voltage source (emf); the resistance of the wire is so low that Joule heating
losses in the wire can be neglected.  The wire carries the instantaneous
current `I`.  Because `r ≪ R`, the fields `H⃗`, `B⃗` and the magnetization `M⃗`
have approximately constant magnitudes `H`, `B`, `M` throughout the torus.
`V` and `A` are the volume and the cross-sectional area of the torus.
For the paramagnetic material `M⃗` is parallel to `H⃗` and
`B⃗ = μ₀ H⃗ + μ₀ M⃗`.  Sign convention: work `W` and heat `Q` are positive when
they flow into the Pm-T.

**Subquestion T3-A2 (page 12, 0.6 pts).**  Let `dW_emf` be the work that the
external voltage source performs to change the magnitude of `B⃗` by `dB`.
Write `dW_emf` in terms of `V`, `H`, and `dB`.

**Hint (printed above T3-A1, shared by all of part A).**  In magnetic
materials, `∮_C H⃗ · dℓ⃗ = I_C`, where `I_C` is the net free current passing
through the area bounded by the closed curve `C` (Ampère's circuital law for
the `H`-field).

## Figure 3a readout

* `R` is the radius from the torus centre to the centreline of the tube (mean
  radius); the label `2r` spans the tube diameter, so the circular
  cross-section has radius `r` and area `A = π r²`.
* The winding threads the hole of the torus: each of the `N` turns passes once
  through the area bounded by any mean circular Amperian loop of radius `R`
  inside the torus, so such a loop links the net free current `N · I`.
* The azimuthal field `B⃗` is perpendicular to the tube cross-section and of
  approximately constant magnitude over it, so each turn links the flux
  `B · A` and the winding's total flux linkage is `N · B · A`.
* The torus is a tube of constant cross-section `A` whose centreline has length
  `2πR` (the mean circumference), giving the volume relation `V = (2πR) · A`
  (Pappus' centroid theorem; the geometric content of the problem's `r ≪ R`
  model).

## Previous-part dependency (T3-A1)

Policy: `derive_inline_from_problem_only_material`.  The T3-A1 result
`H = N·I·A / V` is re-derived inline below (`field_magnitude_T3A1`) from the
same problem-only governing laws (Ampère's law on the mean circle and the
torus volume–geometry); no sibling file is imported and no previous-part
conclusion is assumed as a hypothesis.  The T3-A2 main theorem in fact uses
the underlying laws directly (the elimination `H·V = N·I·A`,
`field_times_volume`), not the T3-A1 closed form.

## Physical model (assumptions)

1. *Ampère's circuital law* (printed hint; governing law), as in T3-A1:
   `AmpereLawMeanCircle` — the circulation `H·(2πR)` of the approximately
   uniform azimuthal field around the mean circle equals the linked free
   current `N·I`.
2. *Torus volume–geometry* (`TorusVolumeGeometry`): `V = (2πR)·A` (Fig. 3a /
   Pappus readout).  `CircularCrossSection` records the companion readout
   `A = π r²` and `ThinTorus` records the `r ≪ R` thin-torus idealization
   (`0 < r < R`) that legitimizes the uniform-field model.
3. *Faraday's law of induction for the winding* (governing law;
   `FaradaysLawWinding`, with `fluxLinkage`): with total flux linkage
   `λ = N·B·A`, the induced emf has magnitude `ε = dλ/dt`; only `B` changes
   (the geometry `N`, `A` is fixed), so a change `dB` over a time `dt` gives
   the step form `ε·dt = N·dB·A`.  Orientation: `ε` is the voltage the source
   must supply *against* the induced (Lenz) emf, positive in the winding sense
   that carries the current `I` producing `H⃗`; `dB` is the signed change of
   the magnitude of `B⃗` along the fixed field direction (`B⃗ ∥ H⃗`).
4. *Work performed by the external voltage source* (governing law;
   `SourceWorkStep`): maintaining the instantaneous current `I` against the
   emf `ε` for the duration `dt`, the source performs `dW = I·ε·dt`.  The
   wire's resistance is negligible (problem text), so no Joule-loss term
   appears: this work is entirely the energy flowing from the source into the
   magnetic field and the paramagnetic material — the "work performed by the
   external voltage source" of T3-A2, with the into-system sign convention.
5. *Constitutive relation* (`ConstitutiveRelation`): `B = μ₀·H + μ₀·M` for the
   scalar magnitudes.  Shared context; not needed for T3-A2 itself (it first
   enters in T3-A3) but part of the stated model.
6. *Paramagnetic alignment* (`MagnetizationParallel`): `M⃗ ∥ H⃗`, scalarly
   `0 ≤ M·H`.  Shared context.
7. *Sign convention* (`WorkFlowsIntoSystem`, `HeatFlowsIntoSystem`): signed
   work/heat are positive exactly when flowing into the Pm-T.  Coherence with
   the derived formula is recorded in `emf_work_positive`: increasing the
   field along its own direction (`0 < dB` with `0 < H`) requires positive
   work into the system.
8. *Idealization*: the "approximately uniform" fields are treated as exactly
   uniform — the requested expression is exact within this standard
   thin-torus (`r ≪ R`) model, which is the model the problem asks to use.

## Derivation (answer-blind, from the laws above only)

`dW_emf = I·ε·dt` (source work) `= I·(ε·dt) = I·(N·dB·A)` (Faraday step)
`= (N·I·A)·dB = (H·V)·dB` (Ampère + volume geometry) `= V·H·dB`.
Every step is a substitution of one governing-law equation into another; no
division and no extra side condition is needed.

## Current target (conclusion side only)

`emf_work`: under the source-work law, Faraday's law, Ampère's law and the
torus volume–geometry, the work performed by the external voltage source when
the magnitude of `B⃗` changes by `dB` is

    dW_emf = V·H·dB,

in the requested variables `V`, `H`, `dB`.  The raw requested combination is
recorded as `emfWorkExpr`; both the target relation and its packaged form are
to be proved from the model — nothing about the value of `dW_emf` is assumed,
and no assumption mentions the expression `V·H·dB`.

## Units

All quantities are real numbers carrying SI units, recorded per declaration:
`R, r` in m; `A` in m²; `V` in m³; `I` in A; `H, M` in A/m; `B, dB` in T;
`ε` in V; `dt` in s; `ε·dt` and the flux linkage in Wb = V·s; `dW_emf` in J;
`μ₀` in N/A² (H/m); `N` a dimensionless turn count.
Consistency check: `V·H·dB` has units m³·(A/m)·T = m²·A·(V·s/m²) = A·V·s = J. ✓

## Grounding (LeanExplore, packages Mathlib + Physlib)

LeanExplore finds no scalar magneto-quasistatics API for this model: Physlib's
electromagnetism is the full spacetime vector-field machinery
(`Electromagnetism.ElectromagneticPotential.magneticField`,
`Electromagnetism.MagneticField`), a near miss for the problem's
uniform-magnitude treatment, and there is no ready-made Faraday's-law /
flux-linkage / circuit-emf declaration.  `Electromagnetism.FreeSpace` bundles
a positive `μ₀` together with `ε₀` (and `c`); following the sibling T3-A1
file, the model keeps `μ₀` as a named real parameter of the constitutive
relation and all field magnitudes as real scalars — exactly the scalarization
the problem itself prescribes ("the fields … have approximately constant
magnitudes throughout the torus").
-/

namespace IPhO2026.T3A2

/-! ## Geometry and figure readouts (Fig. 3a) — shared Pm-T model, restated locally -/

/-- Length of the mean circular path inside the torus (the centreline of the
tube, at the mean radius `R`): `2πR`.  This is the natural closed Amperian
loop `C` of the hint.  Units: metres. -/
noncomputable def meanCircumference (R : ℝ) : ℝ := 2 * Real.pi * R

/-- Volume of the torus from its mean circumference and cross-sectional area:
`(2πR) · A` — a tube of constant cross-section `A` whose centreline has length
`2πR` (Pappus' centroid theorem; the geometric content of the `r ≪ R` model).
Units: m³. -/
noncomputable def torusVolumeFromMeanPath (R A : ℝ) : ℝ := meanCircumference R * A

/-- Area of the circular tube cross-section of radius `r`: `π r²` (Fig. 3a
labels the tube diameter `2r`).  Units: m². -/
noncomputable def circularCrossSectionArea (r : ℝ) : ℝ := Real.pi * r ^ 2

/-- Torus volume–geometry readout (figure/geometry assumption): the volume `V`,
the mean radius `R` and the cross-sectional area `A` of the torus are related
by `V = (2πR) · A`. -/
def TorusVolumeGeometry (R A V : ℝ) : Prop := V = torusVolumeFromMeanPath R A

/-- Circular cross-section readout (figure assumption): the cross-sectional
area is that of a disk of radius `r`, `A = π r²`. -/
def CircularCrossSection (A r : ℝ) : Prop := A = circularCrossSectionArea r

/-- Thin-torus idealization (problem text: `r ≪ R`): the tube radius is
positive and small compared to the mean radius, so the fields are treated as
exactly uniform throughout the torus.  Recorded as `0 < r < R`; the model
identifies the "approximately uniform" fields with exactly uniform ones. -/
def ThinTorus (r R : ℝ) : Prop := 0 < r ∧ r < R

/-! ## Governing laws I — Ampère, constitutive relation, alignment (shared context) -/

/-- Circulation of the azimuthal `H`-field around the mean circular path in the
thin-torus model: with the field parallel to the path and of approximately
constant magnitude `H` (problem's `r ≪ R` assumption), the line integral
`∮_C H⃗ · dℓ⃗` of the hint evaluates to `H · (2πR)`.  Units: A (A/m × m). -/
noncomputable def uniformAzimuthalCirculation (H R : ℝ) : ℝ := H * meanCircumference R

/-- Net free current linked by the mean circular path (figure/winding readout):
the dense winding of `N` turns threads the hole of the torus, so each of the
`N` turns carries the instantaneous current `I` once through the area bounded
by the path; the linked free current of the hint is `I_C = N · I`.
Units: amperes. -/
noncomputable def linkedFreeCurrent (N : ℕ) (I : ℝ) : ℝ := (N : ℝ) * I

/-- **Ampère's circuital law for the Pm-T** (governing law; the printed hint
`∮_C H⃗ · dℓ⃗ = I_C` instantiated on the mean circular path): the circulation
of the approximately uniform azimuthal `H`-field around the mean circle of
radius `R` equals the net free current `N · I` linked through the dense
winding. -/
def AmpereLawMeanCircle (H R : ℝ) (N : ℕ) (I : ℝ) : Prop :=
  uniformAzimuthalCirculation H R = linkedFreeCurrent N I

/-- Constitutive relation of the paramagnetic material (given governing law):
`B = μ₀·H + μ₀·M` for the scalar magnitudes — legitimate because the azimuthal
vectors are parallel (`M⃗ ∥ H⃗` in a paramagnet) and of constant magnitude.
Units: tesla on both sides.  Shared context; first used in T3-A3. -/
def ConstitutiveRelation (μ₀ H B M : ℝ) : Prop := B = μ₀ * H + μ₀ * M

/-- Paramagnetic alignment (given): `M⃗` is parallel to `H⃗` (same direction, as
opposed to a diamagnet where they are antiparallel); for the signed scalar
magnitudes along the common azimuthal axis this is `0 ≤ M · H`. -/
def MagnetizationParallel (M H : ℝ) : Prop := 0 ≤ M * H

/-! ## Governing laws II — energy-transfer sign convention (shared context) -/

/-- Sign convention for work: a signed work value `W` represents energy flowing
*into* the paramagnetic torus (the system) exactly when it is positive.  The
work `dW_emf` performed by the external voltage source in T3-A2 is such a
signed work. -/
def WorkFlowsIntoSystem (W : ℝ) : Prop := 0 < W

/-- Sign convention for heat: a signed heat value `Q` represents energy flowing
*into* the paramagnetic torus exactly when it is positive.  Shared context;
first used in T3-B. -/
def HeatFlowsIntoSystem (Q : ℝ) : Prop := 0 < Q

/-! ## Governing laws III — flux linkage, Faraday's law, work of the source -/

/-- Total flux linkage of the dense winding: the azimuthal field `B⃗` is
perpendicular to the tube cross-section and has approximately constant
magnitude `B` over it, so each of the `N` turns links the flux `B · A` and the
winding's total flux linkage is `λ = N · B · A`.  Units: Wb (V·s). -/
noncomputable def fluxLinkage (N : ℕ) (B A : ℝ) : ℝ := (N : ℝ) * B * A

/-- **Faraday's law of induction for the winding, step form** (governing law):
the emf induced by a change of the total flux linkage `λ = N·B·A` has
magnitude `ε = dλ/dt`; since only `B` changes (the geometry `N`, `A` is
fixed), a change `dB` of the field magnitude over a time `dt` gives
`ε · dt = N · dB · A`, the corresponding change of `fluxLinkage N B A`
(`fluxLinkage_change`).

Orientation: `ε` is the voltage the external voltage source must supply
*against* the induced (Lenz) emf, taken positive in the winding sense that
carries the instantaneous current `I` which produces `H⃗` (the Ampère
right-hand sense of `AmpereLawMeanCircle`); `dB` is the signed change of the
magnitude of `B⃗` along the fixed field direction (`B⃗ ∥ H⃗` throughout the
process: the field pattern of the winding is fixed and the material stays
paramagnetic).  Units: `ε · dt` in V·s = Wb. -/
def FaradaysLawWinding (emf dt : ℝ) (N : ℕ) (dB A : ℝ) : Prop :=
  emf * dt = fluxLinkage N dB A

/-- **Work performed by the external voltage source, step form** (governing
law): maintaining the instantaneous current `I` against the emf `ε` for the
duration `dt` of the step, the source performs the work `dW = I · ε · dt`
(power `I·ε` integrated over the step).  The wire's resistance is negligible
(problem text), so there is no Joule-loss term: this work is entirely the
energy flowing from the source into the magnetic field and the paramagnetic
material — the "work performed by the external voltage source" of T3-A2, taken
with the into-system sign convention (`WorkFlowsIntoSystem`).
Units: J (A × V × s). -/
def SourceWorkStep (dW I emf dt : ℝ) : Prop := dW = I * emf * dt

/-! ## Bridge lemmas (proofs deferred to the prover stage) -/

/-- The change of the total flux linkage when the field magnitude changes from
`B` to `B + dB` (geometry `N`, `A` fixed) is exactly `fluxLinkage N dB A =
N · dB · A` — the right-hand side of `FaradaysLawWinding`.  This justifies the
step form of Faraday's law from the differential form `ε = dλ/dt`.
Proof route: unfold `fluxLinkage`; `ring`. -/
theorem fluxLinkage_change (N : ℕ) (B dB A : ℝ) :
    fluxLinkage N (B + dB) A - fluxLinkage N B A = fluxLinkage N dB A := by
  unfold fluxLinkage
  ring

/-- Combining the source-work law with Faraday's law eliminates the emf and the
step duration: the work performed by the external voltage source over the step
equals the current times the change of flux linkage, `dW = I · (N·dB·A)`.
Proof route: `dW = I·ε·dt = I·(ε·dt)` by `mul_assoc`, then substitute
`FaradaysLawWinding`. -/
theorem source_work_of_linkage_change {dW I emf dt dB A : ℝ} {N : ℕ}
    (hWork : SourceWorkStep dW I emf dt)
    (hFaraday : FaradaysLawWinding emf dt N dB A) :
    dW = I * fluxLinkage N dB A := by
  have hW : dW = I * emf * dt := hWork
  have hF : emf * dt = fluxLinkage N dB A := hFaraday
  rw [hW, mul_assoc, hF]

/-- Core geometric bridge (as in T3-A1): combining Ampère's law
`H · (2πR) = N · I` with the volume geometry `V = (2πR) · A` eliminates the
mean radius, giving `H · V = N · I · A`.
Proof route: rewrite `V`, reassociate, substitute Ampère's equation. -/
theorem field_times_volume {H R A V : ℝ} {N : ℕ} {I : ℝ}
    (hAmp : AmpereLawMeanCircle H R N I) (hGeom : TorusVolumeGeometry R A V) :
    H * V = (N : ℝ) * I * A := by
  have hA : H * meanCircumference R = (N : ℝ) * I := hAmp
  have hG : V = meanCircumference R * A := hGeom
  calc H * V = H * (meanCircumference R * A) := by rw [hG]
    _ = (H * meanCircumference R) * A := (mul_assoc H _ A).symm
    _ = (N : ℝ) * I * A := by rw [hA]

/-- **T3-A1 previous-part result, derived inline** (policy
`derive_inline_from_problem_only_material`; same statement as
`IPhO2026.T3A1.field_magnitude`, re-derived here from the problem-only
governing laws — no sibling file is imported): the field magnitude in the
torus is `H = N·I·A / V`, in terms of `N`, `I`, `A`, `V` as requested by
T3-A1.  Proof route: `field_times_volume` gives `H·V = N·I·A`; divide by
`V ≠ 0`. -/
theorem field_magnitude_T3A1 {H R A V : ℝ} {N : ℕ} {I : ℝ}
    (hV : 0 < V) (hAmp : AmpereLawMeanCircle H R N I)
    (hGeom : TorusVolumeGeometry R A V) :
    H = (N : ℝ) * I * A / V := by
  have h := field_times_volume hAmp hGeom
  rw [eq_div_iff (ne_of_gt hV)]
  exact h

/-- Figure coherence: with the circular cross-section `A = π r²`, the torus
volume takes the classical form `V = 2π²·R·r²`.  Not needed for T3-A2; records
the compatibility of the two figure readouts.
Proof route: substitute both readouts; `ring`. -/
theorem crossSection_consistency {R r A V : ℝ}
    (hGeom : TorusVolumeGeometry R A V) (hCirc : CircularCrossSection A r) :
    V = 2 * Real.pi ^ 2 * R * r ^ 2 := by
  have hG : V = 2 * Real.pi * R * A := hGeom
  have hC : A = Real.pi * r ^ 2 := hCirc
  rw [hG, hC]
  ring

/-! ## Main target (T3-A2) -/

/-- Raw end-to-end expression requested by T3-A2 (derived candidate): the
combination `V · H · dB` in the requested variables `V`, `H`, `dB`.  The
definition only records the requested combination; that the actual work
performed by the external voltage source equals it is the content of
`emf_work`, and nothing in the model assumptions mentions this expression.
Units: J (m³ × A/m × T). -/
noncomputable def emfWorkExpr (V H dB : ℝ) : ℝ := V * H * dB

/-- **T3-A2 main target.**  For the densely wound paramagnetic torus in the
thin-torus (`r ≪ R`) uniform-field model, the work `dW` performed by the
external voltage source when the magnitude of `B⃗` changes by `dB` is

    `dW = V · H · dB`,

in terms of the torus volume `V`, the `H`-field magnitude `H` and the field
change `dB`, as requested.  Derivation chain: the source-work law and
Faraday's law give `dW = I · (N·dB·A)` (`source_work_of_linkage_change`);
Ampère's law with the volume geometry gives `H·V = N·I·A`
(`field_times_volume`); substituting `N·I·A = H·V` into
`I·(N·dB·A) = (N·I·A)·dB` yields `dW = (H·V)·dB = V·H·dB`.  No division is
used, so no positivity side conditions are needed. -/
theorem emf_work {dW I emf dt dB A V H R : ℝ} {N : ℕ}
    (hWork : SourceWorkStep dW I emf dt)
    (hFaraday : FaradaysLawWinding emf dt N dB A)
    (hAmp : AmpereLawMeanCircle H R N I)
    (hGeom : TorusVolumeGeometry R A V) :
    dW = V * H * dB := by
  have h1 : dW = I * fluxLinkage N dB A := source_work_of_linkage_change hWork hFaraday
  have h2 : H * V = (N : ℝ) * I * A := field_times_volume hAmp hGeom
  rw [h1]
  calc I * fluxLinkage N dB A = ((N : ℝ) * I * A) * dB := by
        unfold fluxLinkage; ring
    _ = (H * V) * dB := by rw [← h2]
    _ = V * H * dB := by ring

/-- Packaged form of the main target: the work performed by the external
voltage source equals the raw requested expression `emfWorkExpr`.
Proof route: `emf_work`; `emfWorkExpr` unfolds definitionally to `V·H·dB`. -/
theorem emf_work_eq_expr {dW I emf dt dB A V H R : ℝ} {N : ℕ}
    (hWork : SourceWorkStep dW I emf dt)
    (hFaraday : FaradaysLawWinding emf dt N dB A)
    (hAmp : AmpereLawMeanCircle H R N I)
    (hGeom : TorusVolumeGeometry R A V) :
    dW = emfWorkExpr V H dB := by
  show dW = V * H * dB
  exact emf_work hWork hFaraday hAmp hGeom

/-- Sign-convention coherence: increasing the field magnitude along the field
direction (`0 < dB`, with `0 < H` and positive volume) requires positive work
from the source, i.e. work flowing *into* the Pm-T — exactly the problem's
sign convention (`WorkFlowsIntoSystem`).
Proof route: rewrite `dW` by `emf_work`; `V·H·dB > 0` by threefold `mul_pos`. -/
theorem emf_work_positive {dW I emf dt dB A V H R : ℝ} {N : ℕ}
    (hV : 0 < V) (hH : 0 < H) (hdB : 0 < dB)
    (hWork : SourceWorkStep dW I emf dt)
    (hFaraday : FaradaysLawWinding emf dt N dB A)
    (hAmp : AmpereLawMeanCircle H R N I)
    (hGeom : TorusVolumeGeometry R A V) :
    WorkFlowsIntoSystem dW := by
  show 0 < dW
  rw [emf_work hWork hFaraday hAmp hGeom]
  exact mul_pos (mul_pos hV hH) hdB

end IPhO2026.T3A2
