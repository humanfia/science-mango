import Mathlib

/-!
# IPhO 2026 · Theory problem T3-A3 — "Chasing the absolute zero": work done on
the paramagnetic material

Autoformalization of IPhO 2026 T3-A3 (source:
`reports/ipho_2026/problem_ipho_2026_t3_a3.source.json`; problem pages
`ipho_2026_source/image/T3_page-1.png` (setup, Fig. 3a, constitutive relation,
sign convention) and `ipho_2026_source/image/T3_page-2.png` (T3-A3 statement)).

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

**Hint (printed above T3-A1, shared by all of part A).**  In magnetic
materials, `∮_C H⃗ · dℓ⃗ = I_C`, where `I_C` is the net free current passing
through the area bounded by the closed curve `C` (Ampère's circuital law for
the `H`-field).

**Subquestion T3-A3 (page 12, 0.2 pts).**  "The total work done by the voltage
source, `dW_emf`, can be divided in two parts: the work that would be performed
to change the magnetic field if the toroid had a vacuum core, `dW_vac`, and the
work done on the paramagnetic material itself, `dW`.  Write `dW` in terms of
`μ₀`, `H`, `V` and `dM`."

**Fallback form printed in T3-B (page 12, problem-side material).**  "If you
did not find an answer for `dW` in question T3-A3, you may use
`dW = αVμ₀HdM` where `α` is a number."  The derivation below realizes this
shape with the derived value `α = 1` (conclusion side only, see
`material_work_fallback_alpha_one`).

## Figure 3a readout (as in T3-A1/T3-A2)

* `R` is the mean radius (torus centre to tube centreline); the label `2r`
  spans the tube diameter, so the circular cross-section has radius `r` and
  area `A = π r²`.
* The dense winding threads the hole of the torus: each of the `N` turns passes
  once through the area bounded by any mean circular Amperian loop of radius
  `R`, so such a loop links the net free current `N · I`.
* The azimuthal field `B⃗` is perpendicular to the tube cross-section and of
  approximately constant magnitude over it, so each turn links the flux `B·A`
  and the winding's total flux linkage is `N·B·A`.
* The torus is a tube of constant cross-section `A` whose centreline has length
  `2πR`, giving the volume relation `V = (2πR)·A` (Pappus' centroid theorem;
  the geometric content of the problem's `r ≪ R` model).

## Previous-part dependency (T3-A2)

Policy: `derive_inline_from_problem_only_material`.  The T3-A2 result
`dW_emf = V·H·dB` is re-derived inline below (`emf_work_T3A2`, via the
parametrized derivation `source_work_generic`) from the same problem-only
governing laws (source work, Faraday's law, Ampère's law on the mean circle,
torus volume–geometry); no sibling file is imported and no previous-part
conclusion is assumed as a hypothesis.  The T3-A1 closed form
`H = N·I·A / V` is likewise re-derived inline (`field_magnitude_T3A1`); it
witnesses the core-independence of `H` that legitimizes the vacuum-core
comparison (see `VacuumCoreStep`).

## Physical model (assumptions)

1. *Ampère's circuital law* (printed hint; governing law), as in T3-A1/T3-A2:
   `AmpereLawMeanCircle` — the circulation `H·(2πR)` of the approximately
   uniform azimuthal field around the mean circle equals the linked free
   current `N·I`.  Note that this law fixes `H` from the free current and the
   geometry alone: it does not involve the core material, so the material-core
   process and the vacuum-core comparison process driven by the same current
   share the same `H` and the same change `dH`.  The model encodes this by
   using the *same* variables `H`, `dH`, `I`, `N`, `A`, `V`, `R`, `dt` in both
   branches.
2. *Torus volume–geometry* (`TorusVolumeGeometry`): `V = (2πR)·A` (Fig. 3a /
   Pappus readout).  `CircularCrossSection` records the companion readout
   `A = π r²` and `ThinTorus` records the `r ≪ R` thin-torus idealization
   (`0 < r < R`) that legitimizes the uniform-field model.
3. *Faraday's law of induction for the winding* (governing law;
   `FaradaysLawWinding`, with `fluxLinkage`), step form `ε·dt = N·dB·A`,
   applied separately to the two branches: the material branch (field change
   `dB`, compensating voltage `emf`) and the vacuum-core branch (field change
   `dB_vac`, compensating voltage `emf_vac`).  Orientation: each `ε` is the
   voltage the source must supply *against* the induced (Lenz) emf, positive in
   the winding sense that carries the current `I` producing `H⃗`; `dB`, `dB_vac`
   are the signed changes of the field magnitudes along the fixed azimuthal
   field direction (`B⃗ ∥ H⃗` throughout).
4. *Work performed by the external voltage source* (governing law;
   `SourceWorkStep`), step form `dW = I·ε·dt`, applied to both branches
   (`dW_emf` from `emf`, `dW_vac` from `emf_vac`), with the same instantaneous
   current `I` and the same step duration `dt` — the vacuum-core work is the
   work the same source would perform driving the same current process with a
   vacuum core.  Negligible wire resistance (problem text) means no Joule-loss
   term appears.
5. *Constitutive relation* (`ConstitutiveRelation`): `B = μ₀·H + μ₀·M` for the
   scalar magnitudes, assumed both before and after the change
   (`hConst`, `hConstStep`); the bridge `constitutive_step` extracts the step
   form `dB = μ₀·dH + μ₀·dM`.  This is the governing law that first enters in
   T3-A3.
6. *Vacuum-core constitutive relation, step form* (`VacuumCoreStep`): with a
   vacuum core `M ≡ 0`, so `B_vac = μ₀·H` at all times and a change `dH` of
   the (shared, core-independent) `H`-field gives `dB_vac = μ₀·dH`.
7. *Division of the source work* (`WorkDivision`): given verbatim by the T3-A3
   statement — `dW_emf` divides into the vacuum-core part `dW_vac` and the part
   `dW` done on the paramagnetic material: `dW_emf = dW_vac + dW`.  This is the
   problem-stated definition of the quantity `dW` whose expression is
   requested; it is not the requested expression itself.
8. *Paramagnetic alignment* (`MagnetizationParallel`): `M⃗ ∥ H⃗`, scalarly
   `0 ≤ M·H`.  Shared context.
9. *Sign convention* (`WorkFlowsIntoSystem`, `HeatFlowsIntoSystem`): signed
   work/heat are positive exactly when flowing into the Pm-T.  Coherence with
   the derived formula is recorded in `material_work_positive`: increasing the
   magnetization along the field (`0 < dM` with `0 < H`, `0 < μ₀`) requires
   positive work flowing into the material.
10. *Idealization*: the "approximately uniform" fields are treated as exactly
    uniform — the requested expression is exact within this standard
    thin-torus (`r ≪ R`) model, which is the model the problem asks to use.

## Derivation (answer-blind, from the laws above only)

* Material branch (T3-A2 inline): `dW_emf = I·ε·dt = I·(N·dB·A)
  = (N·I·A)·dB = (H·V)·dB = V·H·dB`.
* Vacuum-core branch (same derivation with `dB_vac`):
  `dW_vac = V·H·dB_vac = V·H·(μ₀·dH)`.
* Constitutive step: `dB = μ₀·dH + μ₀·dM`.
* Problem-stated division:
  `dW = dW_emf − dW_vac = V·H·(μ₀·dH + μ₀·dM) − V·H·(μ₀·dH) = μ₀·H·V·dM`.

Every step is a substitution of one governing-law equation into another plus
ring arithmetic; no division and no extra side condition is needed.

## Current target (conclusion side only)

`material_work`: under the source-work law, Faraday's law, Ampère's law and the
torus volume–geometry (both branches), the vacuum-core step law, the
constitutive relation before and after the change, and the problem-stated
division of the source work, the work done on the paramagnetic material when
its magnetization changes by `dM` is

    dW = μ₀·H·V·dM,

in the requested variables `μ₀`, `H`, `V`, `dM`.  The raw requested combination
is recorded as `materialWorkExpr`; both the target relation and its packaged
forms are to be proved from the model — nothing about the value of `dW` is
assumed, and no assumption mentions the expression `μ₀·H·V·dM` (the
`WorkDivision` premise is the problem's own definition of `dW`, not the
requested closed form).

## Units

All quantities are real numbers carrying SI units, recorded per declaration:
`R, r` in m; `A` in m²; `V` in m³; `I` in A; `H, M, dH, dM` in A/m;
`B, dB, dB_vac` in T; `emf, emf_vac` in V; `dt` in s; flux linkage in
Wb = V·s; `dW_emf, dW_vac, dW` in J; `μ₀` in N/A² (H/m); `N` a dimensionless
turn count.  Consistency check: `μ₀·H·V·dM` has units
(N/A²)·(A/m)·m³·(A/m) = N·m = J. ✓

## Grounding (LeanExplore, packages Mathlib + Physlib)

LeanExplore finds no scalar magneto-quasistatics API for this model: Physlib's
electromagnetism is the full spacetime vector-field machinery
(`Electromagnetism.ElectromagneticPotential.magneticField`,
`Electromagnetism.MagneticField`), a near miss for the problem's
uniform-magnitude treatment, and there is no ready-made Faraday's-law /
flux-linkage / magnetic-work declaration.  `Electromagnetism.FreeSpace` bundles
a positive `μ₀` (`μ₀_nonneg`, `μ₀_ne_zero`) together with `ε₀` (and `c`);
following the sibling T3-A1/T3-A2 files, the model keeps `μ₀` as a named real
parameter of the constitutive relation and all field magnitudes as real
scalars — exactly the scalarization the problem itself prescribes ("the fields
… have approximately constant magnitudes throughout the torus").
-/

namespace IPhO2026.T3A3

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
winding.  The law involves only the free current and the geometry — not the
core material — so `H` (and its change `dH`) is the same in the material-core
and vacuum-core processes driven by the same current. -/
def AmpereLawMeanCircle (H R : ℝ) (N : ℕ) (I : ℝ) : Prop :=
  uniformAzimuthalCirculation H R = linkedFreeCurrent N I

/-- Constitutive relation of the paramagnetic material (given governing law):
`B = μ₀·H + μ₀·M` for the scalar magnitudes — legitimate because the azimuthal
vectors are parallel (`M⃗ ∥ H⃗` in a paramagnet) and of constant magnitude.
Units: tesla on both sides.  In T3-A3 this law is assumed both before and
after the change (`constitutive_step` extracts the step form). -/
def ConstitutiveRelation (μ₀ H B M : ℝ) : Prop := B = μ₀ * H + μ₀ * M

/-- Paramagnetic alignment (given): `M⃗` is parallel to `H⃗` (same direction, as
opposed to a diamagnet where they are antiparallel); for the signed scalar
magnitudes along the common azimuthal axis this is `0 ≤ M · H`.  Shared
context. -/
def MagnetizationParallel (M H : ℝ) : Prop := 0 ≤ M * H

/-! ## Governing laws II — energy-transfer sign convention (shared context) -/

/-- Sign convention for work: a signed work value `W` represents energy flowing
*into* the paramagnetic torus (the system) exactly when it is positive.  The
works `dW_emf`, `dW_vac` and `dW` of T3-A3 are such signed works. -/
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
process).  In T3-A3 this law is instantiated twice: for the material branch
(`dB`, `emf`) and for the vacuum-core branch (`dB_vac`, `emf_vac`).
Units: `ε · dt` in V·s = Wb. -/
def FaradaysLawWinding (emf dt : ℝ) (N : ℕ) (dB A : ℝ) : Prop :=
  emf * dt = fluxLinkage N dB A

/-- **Work performed by the external voltage source, step form** (governing
law): maintaining the instantaneous current `I` against the emf `ε` for the
duration `dt` of the step, the source performs the work `dW = I · ε · dt`
(power `I·ε` integrated over the step).  The wire's resistance is negligible
(problem text), so there is no Joule-loss term: this work is entirely the
energy flowing from the source into the magnetic field and (for the material
branch) the paramagnetic material, taken with the into-system sign convention
(`WorkFlowsIntoSystem`).  Units: J (A × V × s). -/
def SourceWorkStep (dW I emf dt : ℝ) : Prop := dW = I * emf * dt

/-! ## T3-A3 model — vacuum-core comparison and division of the source work -/

/-- **Vacuum-core constitutive relation, step form** (governing law for the
vacuum-core comparison process of T3-A3): with a vacuum core the magnetization
vanishes identically, so the constitutive relation `B = μ₀·H + μ₀·M` reduces
to `B_vac = μ₀·H` at all times; a change `dH` of the `H`-field magnitude
therefore changes the vacuum-core flux density by `dB_vac = μ₀ · dH`.

The `H`-field used here is the same variable as in the material branch: by
Ampère's law (`AmpereLawMeanCircle`, solved in `field_magnitude_T3A1`) `H`
depends only on the winding, the current and the geometry — not on the core —
so the vacuum-core torus driven by the same current process has the same `H`
and the same change `dH`.  Units: `dB_vac` in tesla, `μ₀·dH` in
(N/A²)·(A/m) = T. -/
def VacuumCoreStep (μ₀ dH dB_vac : ℝ) : Prop := dB_vac = μ₀ * dH

/-- **Division of the source work** (given verbatim in the T3-A3 statement):
the total work `dW_emf` performed by the external voltage source divides into
the part `dW_vac` that would be performed to change the magnetic field if the
toroid had a vacuum core and the part `dW` done on the paramagnetic material
itself: `dW_emf = dW_vac + dW`.  All three works carry the into-system sign
convention (`WorkFlowsIntoSystem`).  This is the problem's own definition of
the quantity `dW`; the requested expression of `dW` in terms of `μ₀`, `H`,
`V`, `dM` remains on the conclusion side (`material_work`).  Units: joules. -/
def WorkDivision (dW_emf dW_vac dW : ℝ) : Prop := dW_emf = dW_vac + dW

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

/-- Core geometric bridge (as in T3-A1/T3-A2): combining Ampère's law
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

/-- **Constitutive step** (the T3-A3 input from the constitutive relation):
the relation `B = μ₀·H + μ₀·M` holds both before and after the change, so by
linearity the changes satisfy `dB = μ₀·dH + μ₀·dM`.  Exact (no approximation):
the relation is affine with constant coefficient `μ₀`.
Proof route: unfold `ConstitutiveRelation` at both hypotheses and subtract the
first equation from the second; `linearith`/`ring`-normal forms close it. -/
theorem constitutive_step {μ₀ H B M dH dB dM : ℝ}
    (hConst : ConstitutiveRelation μ₀ H B M)
    (hConstStep : ConstitutiveRelation μ₀ (H + dH) (B + dB) (M + dM)) :
    dB = μ₀ * dH + μ₀ * dM := by
  have h1 : B = μ₀ * H + μ₀ * M := hConst
  have h2 : B + dB = μ₀ * (H + dH) + μ₀ * (M + dM) := hConstStep
  linear_combination h2 - h1

/-- **T3-A1 previous-part result, re-derived inline** (policy
`derive_inline_from_problem_only_material`; same statement as
`IPhO2026.T3A1.field_magnitude`, re-derived here from the problem-only
governing laws — no sibling file is imported): the field magnitude in the
torus is `H = N·I·A / V`.  Its role in T3-A3 is to witness that `H` (and hence
its change `dH`) is determined by the winding, the current and the geometry
alone — independent of the core material — which legitimizes the shared-`H`
vacuum-core comparison encoded by `VacuumCoreStep`.
Proof route: `field_times_volume` gives `H·V = N·I·A`; divide by `V ≠ 0`. -/
theorem field_magnitude_T3A1 {H R A V : ℝ} {N : ℕ} {I : ℝ}
    (hV : 0 < V) (hAmp : AmpereLawMeanCircle H R N I)
    (hGeom : TorusVolumeGeometry R A V) :
    H = (N : ℝ) * I * A / V := by
  have h := field_times_volume hAmp hGeom
  rw [eq_div_iff (ne_of_gt hV)]
  exact h

/-- Figure coherence: with the circular cross-section `A = π r²`, the torus
volume takes the classical form `V = 2π²·R·r²`.  Not needed for T3-A3; records
the compatibility of the two figure readouts.
Proof route: substitute both readouts; `ring`. -/
theorem crossSection_consistency {R r A V : ℝ}
    (hGeom : TorusVolumeGeometry R A V) (hCirc : CircularCrossSection A r) :
    V = 2 * Real.pi ^ 2 * R * r ^ 2 := by
  have hG : V = 2 * Real.pi * R * A := hGeom
  have hC : A = Real.pi * r ^ 2 := hCirc
  rw [hG, hC]
  ring

/-- **Generic source-work evaluation** (the T3-A2 derivation, parametrized by
the signed field change `dB'`): for the densely wound torus in the thin-torus
uniform-field model, the work performed by the external voltage source when the
field magnitude changes by `dB'` is `dW' = V · H · dB'`.  Stated generically so
that it serves both branches of T3-A3: the material branch (with the actual
change `dB`) and the vacuum-core branch (with `dB_vac`).
Proof route: `source_work_of_linkage_change` gives `dW' = I·(N·dB'·A) =
(N·I·A)·dB'`; `field_times_volume` gives `H·V = N·I·A`; substitute and
reassociate (`ring`).  No division is used, so no positivity side conditions
are needed. -/
theorem source_work_generic {dW' I emf' dt dB' A V H R : ℝ} {N : ℕ}
    (hWork : SourceWorkStep dW' I emf' dt)
    (hFaraday : FaradaysLawWinding emf' dt N dB' A)
    (hAmp : AmpereLawMeanCircle H R N I)
    (hGeom : TorusVolumeGeometry R A V) :
    dW' = V * H * dB' := by
  have h1 : dW' = I * fluxLinkage N dB' A := source_work_of_linkage_change hWork hFaraday
  have h2 : H * V = (N : ℝ) * I * A := field_times_volume hAmp hGeom
  rw [h1]
  calc I * fluxLinkage N dB' A = ((N : ℝ) * I * A) * dB' := by
        unfold fluxLinkage; ring
    _ = (H * V) * dB' := by rw [← h2]
    _ = V * H * dB' := by ring

/-- **T3-A2 previous-part result, re-derived inline** (policy
`derive_inline_from_problem_only_material`; same statement as
`IPhO2026.T3A2.emf_work`, re-derived here from the problem-only governing laws
— no sibling file is imported and no previous-part conclusion is assumed as a
hypothesis): the work performed by the external voltage source when the
magnitude of `B⃗` changes by `dB` is `dW_emf = V · H · dB`.
Proof route: `source_work_generic` instantiated at the material branch. -/
theorem emf_work_T3A2 {dW_emf I emf dt dB A V H R : ℝ} {N : ℕ}
    (hWork : SourceWorkStep dW_emf I emf dt)
    (hFaraday : FaradaysLawWinding emf dt N dB A)
    (hAmp : AmpereLawMeanCircle H R N I)
    (hGeom : TorusVolumeGeometry R A V) :
    dW_emf = V * H * dB := by
  exact source_work_generic hWork hFaraday hAmp hGeom

/-- **Vacuum-core work**: the same source-work evaluation applied to the
vacuum-core branch gives `dW_vac = V·H·dB_vac`; rewriting the vacuum-core
field change by the vacuum constitutive step `dB_vac = μ₀·dH`
(`VacuumCoreStep`) yields `dW_vac = V · H · (μ₀ · dH)`.
Proof route: `source_work_generic` instantiated at the vacuum branch, then
substitute `hVacStep`. -/
theorem vacuum_core_work {dW_vac I emf_vac dt dB_vac dH A V H R μ₀ : ℝ} {N : ℕ}
    (hWorkVac : SourceWorkStep dW_vac I emf_vac dt)
    (hFaradayVac : FaradaysLawWinding emf_vac dt N dB_vac A)
    (hVacStep : VacuumCoreStep μ₀ dH dB_vac)
    (hAmp : AmpereLawMeanCircle H R N I)
    (hGeom : TorusVolumeGeometry R A V) :
    dW_vac = V * H * (μ₀ * dH) := by
  have h : dW_vac = V * H * dB_vac := source_work_generic hWorkVac hFaradayVac hAmp hGeom
  have hV : dB_vac = μ₀ * dH := hVacStep
  rw [hV] at h
  exact h

/-! ## Main target (T3-A3) -/

/-- Raw end-to-end expression requested by T3-A3 (derived candidate): the
combination `μ₀ · H · V · dM` in the requested variables `μ₀`, `H`, `V`, `dM`
(listed in the order they appear in the subquestion).  The definition only
records the requested combination; that the actual work done on the
paramagnetic material equals it is the content of `material_work`, and nothing
in the model assumptions mentions this expression.  Units: J
((N/A²) × A/m × m³ × A/m). -/
noncomputable def materialWorkExpr (μ₀ H V dM : ℝ) : ℝ := μ₀ * H * V * dM

/-- Fallback answer shape printed in T3-B (problem-side material): "if you did
not find an answer for `dW` in question T3-A3, you may use `dW = αVμ₀HdM`
where `α` is a number."  This definition records the fallback shape; the
derived candidate realizes it with `α = 1` (`material_work_fallback_alpha_one`,
conclusion side only).  Units: J for dimensionless `α`. -/
noncomputable def fallbackWorkForm (α V μ₀ H dM : ℝ) : ℝ := α * V * μ₀ * H * dM

/-- **T3-A3 main target.**  For the densely wound paramagnetic torus in the
thin-torus (`r ≪ R`) uniform-field model, the work `dW` done on the
paramagnetic material itself — the total source work minus the work that would
be performed with a vacuum core (`WorkDivision`, as stated in T3-A3) — when the
magnetization changes by `dM` is

    `dW = μ₀ · H · V · dM`,

in terms of the vacuum permeability `μ₀`, the `H`-field magnitude `H`, the
torus volume `V` and the magnetization change `dM`, as requested.

Derivation chain: `emf_work_T3A2` gives `dW_emf = V·H·dB` (material branch);
`vacuum_core_work` gives `dW_vac = V·H·(μ₀·dH)` (vacuum branch, same `H`);
`constitutive_step` gives `dB = μ₀·dH + μ₀·dM`; substituting all three into
the problem-stated division `dW_emf = dW_vac + dW` leaves
`V·H·(μ₀·dH + μ₀·dM) = V·H·(μ₀·dH) + dW`, i.e. `dW = μ₀·H·V·dM` by
rearrangement (`linear_combination -hDiv`, i.e. ring arithmetic on the
substituted division equation).  No division is used, so no positivity side
conditions are needed.  (This route was machine-checked end-to-end in a
scratch validation before the body was deferred to the prover stage.) -/
theorem material_work {dW dW_emf dW_vac I emf emf_vac dt dB dB_vac dH dM B M A V H R μ₀ : ℝ}
    {N : ℕ}
    (hWork : SourceWorkStep dW_emf I emf dt)
    (hFaraday : FaradaysLawWinding emf dt N dB A)
    (hWorkVac : SourceWorkStep dW_vac I emf_vac dt)
    (hFaradayVac : FaradaysLawWinding emf_vac dt N dB_vac A)
    (hVacStep : VacuumCoreStep μ₀ dH dB_vac)
    (hAmp : AmpereLawMeanCircle H R N I)
    (hGeom : TorusVolumeGeometry R A V)
    (hConst : ConstitutiveRelation μ₀ H B M)
    (hConstStep : ConstitutiveRelation μ₀ (H + dH) (B + dB) (M + dM))
    (hDiv : WorkDivision dW_emf dW_vac dW) :
    dW = μ₀ * H * V * dM := by
  have hEmf : dW_emf = V * H * dB := emf_work_T3A2 hWork hFaraday hAmp hGeom
  have hVac : dW_vac = V * H * (μ₀ * dH) :=
    vacuum_core_work hWorkVac hFaradayVac hVacStep hAmp hGeom
  have hStep : dB = μ₀ * dH + μ₀ * dM := constitutive_step hConst hConstStep
  have hDiv' : dW_emf = dW_vac + dW := hDiv
  rw [hEmf, hVac, hStep] at hDiv'
  linear_combination -hDiv'

/-- Packaged form of the main target: the work done on the paramagnetic
material equals the raw requested expression `materialWorkExpr`.
Proof route: `material_work`; `materialWorkExpr` unfolds definitionally to
`μ₀·H·V·dM`. -/
theorem material_work_eq_expr {dW dW_emf dW_vac I emf emf_vac dt dB dB_vac dH dM B M A V H R μ₀ : ℝ}
    {N : ℕ}
    (hWork : SourceWorkStep dW_emf I emf dt)
    (hFaraday : FaradaysLawWinding emf dt N dB A)
    (hWorkVac : SourceWorkStep dW_vac I emf_vac dt)
    (hFaradayVac : FaradaysLawWinding emf_vac dt N dB_vac A)
    (hVacStep : VacuumCoreStep μ₀ dH dB_vac)
    (hAmp : AmpereLawMeanCircle H R N I)
    (hGeom : TorusVolumeGeometry R A V)
    (hConst : ConstitutiveRelation μ₀ H B M)
    (hConstStep : ConstitutiveRelation μ₀ (H + dH) (B + dB) (M + dM))
    (hDiv : WorkDivision dW_emf dW_vac dW) :
    dW = materialWorkExpr μ₀ H V dM := by
  show dW = μ₀ * H * V * dM
  exact material_work hWork hFaraday hWorkVac hFaradayVac hVacStep hAmp hGeom hConst
    hConstStep hDiv

/-- Compatibility with the fallback shape printed in T3-B: the derived work
realizes `dW = α·V·μ₀·H·dM` with the derived value `α = 1`.
Proof route: `material_work`; unfold `fallbackWorkForm`; `ring`. -/
theorem material_work_fallback_alpha_one
    {dW dW_emf dW_vac I emf emf_vac dt dB dB_vac dH dM B M A V H R μ₀ : ℝ}
    {N : ℕ}
    (hWork : SourceWorkStep dW_emf I emf dt)
    (hFaraday : FaradaysLawWinding emf dt N dB A)
    (hWorkVac : SourceWorkStep dW_vac I emf_vac dt)
    (hFaradayVac : FaradaysLawWinding emf_vac dt N dB_vac A)
    (hVacStep : VacuumCoreStep μ₀ dH dB_vac)
    (hAmp : AmpereLawMeanCircle H R N I)
    (hGeom : TorusVolumeGeometry R A V)
    (hConst : ConstitutiveRelation μ₀ H B M)
    (hConstStep : ConstitutiveRelation μ₀ (H + dH) (B + dB) (M + dM))
    (hDiv : WorkDivision dW_emf dW_vac dW) :
    dW = fallbackWorkForm 1 V μ₀ H dM := by
  show dW = 1 * V * μ₀ * H * dM
  rw [material_work hWork hFaraday hWorkVac hFaradayVac hVacStep hAmp hGeom hConst
    hConstStep hDiv]
  ring

/-- Sign-convention coherence: increasing the magnetization along the field
direction (`0 < dM`, with `0 < H`, positive volume and positive vacuum
permeability) requires positive work done on the paramagnetic material, i.e.
work flowing *into* the Pm-T — exactly the problem's sign convention
(`WorkFlowsIntoSystem`).  For a paramagnet, raising the field along its own
direction raises `M` (`MagnetizationParallel`), so this is the physical
branch of the signed formula.
Proof route: rewrite `dW` by `material_work`; `μ₀·H·V·dM > 0` by repeated
`mul_pos`. -/
theorem material_work_positive
    {dW dW_emf dW_vac I emf emf_vac dt dB dB_vac dH dM B M A V H R μ₀ : ℝ}
    {N : ℕ}
    (hμ₀ : 0 < μ₀) (hV : 0 < V) (hH : 0 < H) (hdM : 0 < dM)
    (hWork : SourceWorkStep dW_emf I emf dt)
    (hFaraday : FaradaysLawWinding emf dt N dB A)
    (hWorkVac : SourceWorkStep dW_vac I emf_vac dt)
    (hFaradayVac : FaradaysLawWinding emf_vac dt N dB_vac A)
    (hVacStep : VacuumCoreStep μ₀ dH dB_vac)
    (hAmp : AmpereLawMeanCircle H R N I)
    (hGeom : TorusVolumeGeometry R A V)
    (hConst : ConstitutiveRelation μ₀ H B M)
    (hConstStep : ConstitutiveRelation μ₀ (H + dH) (B + dB) (M + dM))
    (hDiv : WorkDivision dW_emf dW_vac dW) :
    WorkFlowsIntoSystem dW := by
  show 0 < dW
  rw [material_work hWork hFaraday hWorkVac hFaradayVac hVacStep hAmp hGeom hConst
    hConstStep hDiv]
  exact mul_pos (mul_pos (mul_pos hμ₀ hH) hV) hdM

end IPhO2026.T3A3
