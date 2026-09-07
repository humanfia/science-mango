import Mathlib

/-!
# IPhO 2026 · Theory problem T3-A1 — "Chasing the absolute zero": Work in the Pm-T

Autoformalization of IPhO 2026 T3-A1 (source:
`reports/ipho_2026/problem_ipho_2026_t3_a1.source.json`; problem pages
`ipho_2026_source/image/T3_page-1.png` (setup, Fig. 3a) and
`ipho_2026_source/image/T3_page-2.png` (T3-A1 statement and Ampère-law hint)).

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

**Subquestion T3-A1 (page 12, 0.2 pts).**  Let `H` be the magnitude of `H⃗` in
the torus.  Write `H` in terms of `N`, `A`, `V` and the instantaneous electric
current `I` in the wire.

**Hint (printed above T3-A1).**  In magnetic materials, `∮_C H⃗ · dℓ⃗ = I_C`,
where `I_C` is the net free current passing through the area bounded by the
closed curve `C` (Ampère's circuital law for the H-field).

## Figure 3a readout

* `R` is the radius from the torus centre to the centreline of the tube (mean
  radius); the label `2r` spans the tube diameter, so the circular
  cross-section has radius `r` and area `A = π r²`.
* The winding threads the hole of the torus: each of the `N` turns passes once
  through the area bounded by any mean circular Amperian loop of radius `R`
  inside the torus, so such a loop links the net free current `N · I`.
* The torus is a tube of constant cross-section `A` whose centreline has length
  `2πR` (the mean circumference), giving the volume relation `V = (2πR) · A`
  (Pappus' centroid theorem; exact for the circular-cross-section torus and the
  geometric content of the problem's `r ≪ R` model).

## Physical model (assumptions)

1. *Ampère's circuital law* (problem hint, governing law): the circulation of
   `H⃗` around the mean circular path equals the net linked free current.
   In the `r ≪ R` model the azimuthal field has constant magnitude `H` along
   the path, so the circulation is `H · (2πR)` (`uniformAzimuthalCirculation`);
   the dense winding links `N · I` (`linkedFreeCurrent`).  This is encoded by
   the predicate `AmpereLawMeanCircle`.
2. *Torus volume–geometry* (`TorusVolumeGeometry`): `V = (2πR) · A`, a figure/
   geometry readout as described above; `CircularCrossSection` records the
   companion readout `A = π r²` (tube diameter `2r` in Fig. 3a).
3. *Constitutive relation* (`ConstitutiveRelation`): `B = μ₀·H + μ₀·M` for the
   scalar magnitudes (the vectors are azimuthal and `M⃗ ∥ H⃗`, so the vector
   law reduces to this scalar one).  Shared context; not needed for T3-A1
   itself but part of the stated model and used from T3-A2 on.
4. *Paramagnetic alignment* (`MagnetizationParallel`): `M⃗` parallel to `H⃗`
   (same direction, not antiparallel), scalarly `0 ≤ M · H`.  Shared context.
5. *Sign convention* (`WorkFlowsIntoSystem`, `HeatFlowsIntoSystem`): signed
   work/heat are positive exactly when flowing into the Pm-T.  Shared context;
   first used by T3-A2/T3-B.
6. *Idealization*: the "approximately uniform" fields are treated as exactly
   uniform — the requested expression is exact within this standard
   thin-torus (`r ≪ R`) model, which is the model the problem asks to use.

## Current target (conclusion side only)

`field_magnitude`: under Ampère's law on the mean circle and the torus
volume–geometry, the field magnitude satisfies `H = N·I·A / V`.  The raw
requested combination is recorded as `fieldMagnitudeExpr`; both the target
relation and its packaged form are proved from the model — nothing about the
value of `H` is assumed.

## Units

All quantities are real numbers carrying SI units, recorded per declaration:
`R, r` in m; `A` in m²; `V` in m³; `I` in A; `H, M` in A/m; `B` in T;
`μ₀` in N/A² (H/m); `N` a dimensionless turn count.  LeanExplore found no
ready-made magnetostatics API for this scalar model: Physlib's
`Electromagnetism.MagneticField` is a full spacetime vector-field API
(`Time → Space d → EuclideanSpace ℝ (Fin d)`), a near miss for the problem's
uniform-magnitude treatment, and `Electromagnetism.FreeSpace.μ₀` is a grounded
positive-real permeability but arrives bundled with the (here irrelevant)
permittivity `ε₀`; the model therefore keeps `μ₀` as a named positive real
constant and the uniform field magnitudes as real scalars — exactly the
scalarization the problem itself prescribes ("let `H` be the magnitude of `H⃗`").
-/

namespace IPhO2026.T3A1

/-! ## Geometry and figure readouts (Fig. 3a) -/

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

/-! ## Governing laws -/

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
`∮_C H⃗ · dℓ⃗ = I_C` instantiated on the mean circular path): the circulation of
the approximately uniform azimuthal `H`-field around the mean circle of radius
`R` equals the net free current `N · I` linked through the dense winding. -/
def AmpereLawMeanCircle (H R : ℝ) (N : ℕ) (I : ℝ) : Prop :=
  uniformAzimuthalCirculation H R = linkedFreeCurrent N I

/-- Constitutive relation of the paramagnetic material (given governing law):
`B = μ₀·H + μ₀·M` for the scalar magnitudes — legitimate because the azimuthal
vectors are parallel (`M⃗ ∥ H⃗` in a paramagnet) and of constant magnitude.
Units: tesla on both sides.  Shared context; used from T3-A2 onward. -/
def ConstitutiveRelation (μ₀ H B M : ℝ) : Prop := B = μ₀ * H + μ₀ * M

/-- Paramagnetic alignment (given): `M⃗` is parallel to `H⃗` (same direction, as
opposed to a diamagnet where they are antiparallel); for the signed scalar
magnitudes along the common azimuthal axis this is `0 ≤ M · H`. -/
def MagnetizationParallel (M H : ℝ) : Prop := 0 ≤ M * H

/-! ## Energy-transfer sign convention (shared context; first used by T3-A2) -/

/-- Sign convention for work: a signed work value `W` represents energy flowing
*into* the paramagnetic torus (the system) exactly when it is positive. -/
def WorkFlowsIntoSystem (W : ℝ) : Prop := 0 < W

/-- Sign convention for heat: a signed heat value `Q` represents energy flowing
*into* the paramagnetic torus exactly when it is positive. -/
def HeatFlowsIntoSystem (Q : ℝ) : Prop := 0 < Q

/-! ## Bridge lemmas (proofs deferred to the prover stage) -/

/-- The mean circumference of a torus of positive mean radius is positive. -/
theorem meanCircumference_pos {R : ℝ} (hR : 0 < R) : 0 < meanCircumference R := by
  have h2 : (0 : ℝ) < 2 := by norm_num
  exact mul_pos (mul_pos h2 Real.pi_pos) hR

/-- The torus volume `(2πR)·A` is positive for positive mean radius and
cross-sectional area. -/
theorem torusVolume_pos {R A : ℝ} (hR : 0 < R) (hA : 0 < A) :
    0 < torusVolumeFromMeanPath R A := by
  exact mul_pos (meanCircumference_pos hR) hA

/-- Ampère's law solved for the field magnitude: from
`H · (2πR) = N · I` one obtains `H = N·I / (2πR)` (the H-field of the densely
wound torus in terms of the mean radius). -/
theorem ampere_circulation_solves_H {H R : ℝ} {N : ℕ} {I : ℝ}
    (hAmp : AmpereLawMeanCircle H R N I) (hR : 0 < R) :
    H = linkedFreeCurrent N I / meanCircumference R := by
  -- Unfold Ampère's law to the scalar circulation equation `H · (2πR) = N·I`.
  have h : H * meanCircumference R = linkedFreeCurrent N I := hAmp
  have hc : meanCircumference R ≠ 0 := ne_of_gt (meanCircumference_pos hR)
  -- Divide both sides by the (nonzero) mean circumference.
  calc H = H * meanCircumference R / meanCircumference R :=
        (mul_div_cancel_right₀ H hc).symm
    _ = linkedFreeCurrent N I / meanCircumference R := by rw [h]

/-- Core bridge: combining Ampère's law `H · (2πR) = N · I` with the volume
geometry `V = (2πR) · A` eliminates the mean radius, giving
`H · V = N · I · A`. -/
theorem field_times_volume {H R A V : ℝ} {N : ℕ} {I : ℝ}
    (hAmp : AmpereLawMeanCircle H R N I) (hGeom : TorusVolumeGeometry R A V) :
    H * V = (N : ℝ) * I * A := by
  -- Ampère: `H · (2πR) = N·I`; geometry: `V = (2πR) · A`.
  have h : H * meanCircumference R = (N : ℝ) * I := hAmp
  have hV : V = meanCircumference R * A := hGeom
  rw [hV]
  -- Multiply Ampère's equation by `A` and reassociate.
  calc H * (meanCircumference R * A) = (H * meanCircumference R) * A :=
        (mul_assoc H (meanCircumference R) A).symm
    _ = (N : ℝ) * I * A := by rw [h]

/-- Figure coherence: with the circular cross-section `A = π r²`, the torus
volume takes the classical form `V = 2π²·R·r²`.  Not needed for T3-A1; records
the compatibility of the two figure readouts. -/
theorem crossSection_consistency {R r A V : ℝ}
    (hGeom : TorusVolumeGeometry R A V) (hCirc : CircularCrossSection A r) :
    V = 2 * Real.pi ^ 2 * R * r ^ 2 := by
  -- Geometry: `V = (2πR) · A`; cross-section: `A = π r²`.
  have hV : V = meanCircumference R * A := hGeom
  have hA : A = Real.pi * r ^ 2 := hCirc
  rw [hV, hA]
  -- `2πR · πr² = 2π²Rr²` by commutativity/associativity of multiplication.
  show 2 * Real.pi * R * (Real.pi * r ^ 2) = 2 * Real.pi ^ 2 * R * r ^ 2
  ring

/-! ## Main target (T3-A1) -/

/-- Raw end-to-end expression requested by T3-A1 (derived candidate): the
combination `N·I·A / V` in the requested variables `N`, `I`, `A`, `V`.  The
definition only records the requested combination; that the actual field
magnitude in the torus equals it is the content of `field_magnitude`, and
nothing in the model assumptions mentions this expression.  Units: A/m. -/
noncomputable def fieldMagnitudeExpr (N : ℕ) (I A V : ℝ) : ℝ := (N : ℝ) * I * A / V

/-- **T3-A1 main target.**  For the densely wound paramagnetic torus in the
thin-torus (`r ≪ R`) uniform-field model, Ampère's circuital law on the mean
circular path together with the torus volume–geometry relation determines the
magnitude of the `H`-field inside the torus as

    `H = N · I · A / V`,

in terms of the turn count `N`, the instantaneous current `I`, the
cross-sectional area `A` and the volume `V`, as requested. -/
theorem field_magnitude {H R A V : ℝ} {N : ℕ} {I : ℝ}
    (hR : 0 < R) (hA : 0 < A) (hV : 0 < V)
    (hAmp : AmpereLawMeanCircle H R N I) (hGeom : TorusVolumeGeometry R A V) :
    H = (N : ℝ) * I * A / V := by
  -- From Ampère + geometry: `H · V = N·I·A`; divide by the (nonzero) volume.
  have h : H * V = (N : ℝ) * I * A := field_times_volume hAmp hGeom
  have hV' : V ≠ 0 := ne_of_gt hV
  -- Positivity coherence: the geometry `V = (2πR)·A` with `R, A > 0` indeed
  -- yields a positive volume, consistently with the stated hypothesis `hV`.
  have _hVpos : 0 < torusVolumeFromMeanPath R A := torusVolume_pos hR hA
  calc H = H * V / V := (mul_div_cancel_right₀ H hV').symm
    _ = (N : ℝ) * I * A / V := by rw [h]

/-- Packaged form of the main target: the field magnitude equals the raw
requested expression `fieldMagnitudeExpr`. -/
theorem field_magnitude_eq_expr {H R A V : ℝ} {N : ℕ} {I : ℝ}
    (hR : 0 < R) (hA : 0 < A) (hV : 0 < V)
    (hAmp : AmpereLawMeanCircle H R N I) (hGeom : TorusVolumeGeometry R A V) :
    H = fieldMagnitudeExpr N I A V := by
  -- `fieldMagnitudeExpr N I A V` unfolds definitionally to `N·I·A / V`.
  exact field_magnitude hR hA hV hAmp hGeom

end IPhO2026.T3A1
