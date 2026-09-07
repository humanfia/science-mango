import Mathlib

/-!
# IPhO 2026 · Theory problem T2-B3 — "Solar Cooker": the container radius giving `P = 5 P₀`

Autoformalization of IPhO 2026 T2-B3 (source:
`reports/ipho_2026/problem_ipho_2026_t2_b3.source.json`, figure
`ipho_2026_source/image/T2_page-3.png` (Fig. 2f, problem page 9)).

## Physical scenario (shared T2-B context, Fig. 2f)

A half-hollow-cylinder mirror of radius `R` (cross-section: semicircle; Fig. 2f
labels the opening width `2R`) holds a fully absorbing cylindrical container of
radius `a` (Fig. 2f label `a`): any ray of light hitting it is absorbed.  The
two axes are parallel and the centre of the container is `R/2` from the centre
of the mirror on the system's symmetry plane (Fig. 2f label `R/2`).  Sunlight
has constant uniform intensity (power per unit area) and all rays are parallel
to the optical axis of the mirror.  The radius `a` is such that any ray
absorbed by the container reflects from the mirror **at most once**.  `θ_max`
is the maximum angle of incidence on the mirror (measured with respect to the
normal drawn at the point of incidence) of any reflected ray striking the
container, and `P₀` is the power the cylinder would receive without the mirror.

**Subquestion T2-B3.** If `R = 1.0 m`, write the value of `a` such that
`P = 5 P₀`.  Give the answer in cm.

## Physical model (cross-section, governing laws)

The model is the shared T2-B model of `problem_ipho_2026_t2_b1.lean` /
`problem_ipho_2026_t2_b2.lean`, re-derived inline in this file per the
`derive_inline_from_problem_only_material` previous-part policy.  By
translation invariance along the cylinder axes one cross-sectional plane
suffices; both `P` and `P₀` are proportional to the cylinder length `L`, so we
work with **power per unit length** throughout (`L` cancels in the ratio).
Conventions: the mirror cross-section is the upper semicircle of radius `R`
centred at the origin `O` (`mirrorArc`), the aperture is the diameter segment
of width `2R` (`aperture`), the `y`-axis is the optical axis, sunlight travels
in `+y` (`sunlightDir`), and the container cross-section is the closed disk
(`containerDisk`; closed because a grazing ray still hits and is absorbed) of
radius `a` centred at `C = (0, R/2)` (`containerCenter`).

Governing laws:

1. *Straight-line propagation* between mirror and container (`reflectedRay`).
2. *Law of specular reflection* at the circle (`specularReflect`):
   `d ↦ d − 2⟪d, n⟫ • n` with the radial unit normal (`outwardUnitNormal`);
   the angle of incidence equals the angle of reflection
   (`specularReflect_normal_component_neg`), and the mirror parameter `θ` *is*
   the incidence angle of the problem statement (`incidence_angle_eq`).
3. *Total absorption*: `ReflectedRayStrikesContainer` for once-reflected rays
   and `DirectRayStrikesContainer a x ↔ |x| ≤ a` for unreflected ones.
4. *Energy flux for uniform parallel light*: power per unit length is the
   uniform intensity `I` times the width of the absorbed impact-parameter set
   (`powerWithMirrorPerLength`, `powerWithoutMirrorPerLength`).

Problem regime hypotheses: the container sits strictly inside the bowl
(`ContainerClearOfMirror`, Fig. 2f), and every absorbed ray reflects at most
once (`SingleReflectionRegime`).  `θ_max` is the problem's own maximum
incidence angle of a reflected striking ray (`IsMaxIncidenceAngle`).

## Previous parts, re-derived inline (answer-blind)

* **T2-B1** (`container_radius_eq`, from `dist_at_max_eq` — the extremal
  striking ray grazes the container — and `distToLine_container`):
  `a = R·sin θ_max − (R/2)·sin(2 θ_max)`, i.e. `α = R`, `β = −R/2`; factored
  form `container_radius_eq_factored`: `a = R·sin θ_max·(1 − cos θ_max)`.
* **T2-B2** (`power_ratio`, from `absorbedImpactSet_eq_Icc` — the absorbed
  impact set is exactly `[−R sin θ_max, R sin θ_max]`):
  `P / P₀ = 1 / (1 − cos θ_max)`.

## Derivation of the B3 candidate (problem-side material only, answer-blind)

Imposing the B3 condition `P = 5 P₀` on the T2-B2 ratio (with `P₀ > 0`, since
`0 < a` and `0 < I`; `powerWithoutMirrorPerLength_pos`):

```
1 / (1 − cos θ_max) = 5   ⇒   cos θ_max = 4/5        (cos_thetaMax_of_power_five)
```

The branch is fixed by the geometry: `θ_max ∈ (0, π/2]` (`thetaMax_pos` from
`IsMaxIncidenceAngle` and `0 < a`), so `sin θ_max > 0` and the Pythagorean
identity gives the positive root

```
sin θ_max = 3/5            (sin_thetaMax_of_power_five)
sin(2 θ_max) = 24/25       (sin_two_thetaMax_of_power_five)
```

The required angle is unique on `[0, π/2]` because `cos` is strictly antitone
on `[0, π]` (`thetaMax_unique_of_cos_eq`), so "the value of `a`" is well
defined.  Substituting into the factored T2-B1 relation:

```
a = R·(3/5)·(1 − 1/5) = 3R/25      (container_radius_of_power_five)
```

With `R = 1.0 m` (all lengths measured in metres, `R = 1`): `a = 3/25 m`, and
in centimetres (`mToCm l = 100 l`)

```
a = 100 · 3/25 cm = 12 cm          (t2_b3_container_radius_cm, main target)
```

The value is exactly `12`, so the source-derived reporting rule ("give your
answer in cm") is applied by the exact conversion `mToCm`; no rounding is
needed.  The candidate is feasible: `0 < 3R/25 < R/2`
(`candidate_radius_mem_range`), so it lies in the admissible
single-reflection range `a < R/2` (cf. `container_radius_lt_half`).

No hypothesis, predicate, structure field, or definition in this file mentions
the values `4/5`, `3/5`, `24/25`, `3R/25` or `12`; they occur only in
conclusions of the B3 lemmas.

## Orientation and branch information

* Sunlight travels in `+y` (Fig. 2f; same convention as T2-A1/T2-B1/T2-B2):
  `sunlightDir = (0, 1)`.
* The reflected ray is the post-reflection branch `t > 0` of `reflectedRay`;
  the closest approach to `C` lies on it (`footParam_pos`).
* Left-right symmetry (`strikes_neg`) folds the two halves of the mirror onto
  `θ ∈ [0, π/2]`; `absorbedImpactSet` uses `|x| = R sin θ` for both branches.
* The incidence angle is measured from the normal at the point of incidence
  (`incidence_angle_eq`), as the problem requires; `θ_max` is attained (the
  grazing ray touches the *closed* disk).
* The sign branch of `sin θ_max = +3/5` is selected by `θ_max ∈ (0, π/2]`
  (`thetaMax_pos`), not by the answer.

## Units, conversion, rounding, uncertainty

`R` and `a` carry units of length (kept symbolic as real numbers); for the
numeric question the metre is chosen as the unit, so `R = 1` encodes
"`R = 1.0 m`" and `mToCm l = 100 l` converts the resulting metre value to the
requested centimetres.  `I` carries power/area; `P/L`, `P₀/L` carry
power/length; `θ_max` and `P/P₀` are dimensionless.  The derived value
`a = 3/25 m = 12 cm` is an exact rational number, so the "report in cm" rule
introduces no rounding.  The source reports no measurement uncertainties
(uncertainty propagation: not applicable).

LeanExplore found no PhysLean ray-optics / law-of-reflection or radiative-flux
API (queries recorded in the task result); the reflection law is grounded in
the Mathlib real inner product `⟪·, ·⟫` on `EuclideanSpace ℝ (Fin 2)`, and the
flux bookkeeping in `MeasureTheory.volume`/`Real.volume_Icc`, exactly as in
`problem_ipho_2026_t2_b2.lean`.  The sign/uniqueness step is grounded in
`Real.sin_sq_add_cos_sq` and `Real.strictAntiOn_cos` (`StrictAntiOn.injOn`).
-/

namespace IPhO2026.T2B3

open scoped RealInnerProductSpace

/-! ## The cross-sectional plane and Figure 2f geometry (shared T2-B model) -/

/-- The cross-sectional plane of Fig. 2f (perpendicular to the cylinder axes):
the Euclidean plane with coordinates `(x, y)`, `x` transverse and `y` along the
optical axis. -/
abbrev Plane := EuclideanSpace ℝ (Fin 2)

/-- Transverse coordinate of a point: the signed distance from the optical axis.
Units: length. -/
noncomputable def xCoord (p : Plane) : ℝ := p 0

/-- Coordinate along the optical axis (the `y` of the figure).  Units: length. -/
noncomputable def yCoord (p : Plane) : ℝ := p 1

/-- The circular cross-section of the half-cylinder: the circle of radius `R`
centred at the mirror centre `O`.  Units of `R`: length. -/
noncomputable def mirrorCircle (R : ℝ) : Set Plane := {p | ‖p‖ = R}

/-- The reflecting surface: the open upper semicircle `y > 0` (the concave side
faces the aperture).  Same mirror as in `problem_ipho_2026_t2_b1.lean`. -/
noncomputable def mirrorArc (R : ℝ) : Set Plane := {p | p ∈ mirrorCircle R ∧ 0 < yCoord p}

/-- The open aperture of the half-cylinder: the diameter segment
`{y = 0, |x| < R}` of width `2R` (the `2R` label of Fig. 2f).  Sunlight enters
through it; there is no mirror here. -/
noncomputable def aperture (R : ℝ) : Set Plane := {p | yCoord p = 0 ∧ |xCoord p| < R}

/-- The centre `C` of the container cross-section: the point `R/2` from the
mirror centre `O` on the symmetry axis, inside the bowl (the `R/2` label of
Fig. 2f; equivalently `R/2` below the vertex `(0, R)` of the mirror).
Units: length. -/
noncomputable def containerCenter (R : ℝ) : Plane := !₂[(0 : ℝ), R / 2]

/-- The container cross-section: the *closed* disk of radius `a` about `C`.
Closed because a grazing ray still hits the container and is absorbed (the
cylinder is fully absorbing).  Units of `a`: length. -/
noncomputable def containerDisk (R a : ℝ) : Set Plane := Metric.closedBall (containerCenter R) a

/-! ## Governing laws: straight-line propagation and specular reflection -/

/-- Direction of the sunlight: `+y`, parallel to the optical axis, arriving from
a distant source (all rays share it — "sunlight is of constant and uniform
intensity, rays parallel to the optical axis"). -/
noncomputable def sunlightDir : Plane := !₂[(0 : ℝ), 1]

/-- The outward unit normal to the circle of radius `R` at a point `p` on it:
the radial direction `R⁻¹ • p`.  Unit length is certified by
`outwardUnitNormal_norm`. -/
noncomputable def outwardUnitNormal (R : ℝ) (p : Plane) : Plane := R⁻¹ • p

/-- **Law of specular reflection** (governing law), vector form: a ray with
direction `d` reflecting at a point with unit normal `n` acquires the direction
`d − 2⟪d, n⟫ • n`; the tangential component is preserved and the normal
component changes sign, i.e. the angle of incidence equals the angle of
reflection (see `specularReflect_normal_component_neg`).  Grounded in the
Mathlib inner product; this is the explicit form of the hyperplane reflection
`Submodule.reflection (ℝ ∙ n)ᗮ`. -/
noncomputable def specularReflect (n d : Plane) : Plane := d - (2 * ⟪d, n⟫) • n

/-! ## Incidence point, incidence angle, and the reflected ray -/

/-- Point of incidence on the mirror of the ray whose transverse coordinate is
`x = R sin θ`: parametrized by its angular distance `θ` from the optical axis as
`M(θ) = (R sin θ, R cos θ)`.  For `θ ∈ [0, π/2]` this ranges over the right half
of the arc from the vertex `(0, R)` to the rim `(R, 0)`.  By `incidence_angle_eq`
the parameter `θ` is exactly the angle of incidence of the problem statement. -/
noncomputable def incidencePoint (R θ : ℝ) : Plane := !₂[R * Real.sin θ, R * Real.cos θ]

/-- Direction of the ray after its (single) reflection at `M(θ)`: the law of
specular reflection applied to `sunlightDir` in the radial normal there. -/
noncomputable def reflectedDir (R θ : ℝ) : Plane :=
  specularReflect (outwardUnitNormal R (incidencePoint R θ)) sunlightDir

/-- The reflected ray: the straight line (governing law 1, straight-line
propagation) starting at the incidence point `M(θ)` along `reflectedDir R θ`,
parametrized by arc length `t` (`reflectedDir` is a unit vector, see
`reflectedDir_norm`); `t > 0` is the post-reflection branch. -/
noncomputable def reflectedRay (R θ t : ℝ) : Plane := incidencePoint R θ + t • reflectedDir R θ

/-! ## Distances and the container-strike predicates -/

/-- The 2D cross product (signed area / `z`-component of the 3D cross product):
`cross₂(u, v) = u₁v₂ − u₂v₁`.  For a unit vector `v`, `|cross₂(p − q, v)|` is
the perpendicular distance from `p` to the line through `q` along `v`. -/
noncomputable def cross2 (u v : Plane) : ℝ := xCoord u * yCoord v - yCoord u * xCoord v

/-- Perpendicular distance from the point `p` to the line through `q` with
direction `v` (meaningful for `v ≠ 0`; used with unit `v`). -/
noncomputable def distToLine (p q v : Plane) : ℝ := |cross2 (p - q) v| / ‖v‖

/-- Closest-approach parameter along the reflected ray: the arc-length parameter
of the foot of the perpendicular from `C` to the reflected line (valid because
`reflectedDir` is a unit vector).  Positivity (`footParam_pos`) means the
closest approach lies on the forward, post-reflection branch. -/
noncomputable def footParam (R θ : ℝ) : ℝ :=
  ⟪containerCenter R - incidencePoint R θ, reflectedDir R θ⟫

/-- **Absorption predicate** (governing law 3) for reflected rays: the ray
reflected once at incidence angle `θ` strikes the container — some point of its
forward branch lies in the closed container disk (grazing contact included: the
cylinder is fully absorbing). -/
def ReflectedRayStrikesContainer (R a θ : ℝ) : Prop :=
  ∃ t : ℝ, 0 < t ∧ reflectedRay R θ t ∈ containerDisk R a

/-- Direct (unreflected) absorption: an incident ray entering the aperture at
transverse coordinate `x` meets the container disk iff `|x| ≤ a`.  These are the
rays absorbed without the mirror — their power is the shared-context quantity
`P₀`. -/
def DirectRayStrikesContainer (a x : ℝ) : Prop := |x| ≤ a

/-! ## Regime hypotheses (problem assumptions) -/

/-- Geometric readout of Fig. 2f: the container sits strictly inside the bowl —
its closed absorbing disk is disjoint from the reflecting arc.  (Together with
`SingleReflectionRegime` this is the content of "`a` is such that any ray
absorbed by the cylinder reflects from the mirror at most once".) -/
def ContainerClearOfMirror (R a : ℝ) : Prop :=
  ∀ p : Plane, p ∈ mirrorArc R → p ∉ containerDisk R a

/-- **Single-reflection hypothesis** (problem assumption): along any reflected
ray that strikes the container, every would-be second meeting with the mirror
arc at parameter `t` is preceded by absorption at some earlier parameter
`s < t` — so no absorbed ray reflects twice.  This certifies that every
geometrically striking reflected ray contributes its power to `P`: none is
re-reflected away before reaching the container. -/
def SingleReflectionRegime (R a : ℝ) : Prop :=
  ∀ θ : ℝ, θ ∈ Set.Icc 0 (Real.pi / 2) → ReflectedRayStrikesContainer R a θ →
    ∀ t : ℝ, 0 < t → reflectedRay R θ t ∈ mirrorArc R →
      ∃ s : ℝ, 0 < s ∧ s < t ∧ reflectedRay R θ s ∈ containerDisk R a

/-- **`θ_max` as defined by the problem**: the maximum angle of incidence on the
mirror (measured with respect to the normal at the point of incidence) of any
reflected ray striking the container.  Since the incidence angle at `M(θ)`
equals `θ` (`incidence_angle_eq`) and the setup is symmetric (`strikes_neg`),
this is: `θ_max ∈ [0, π/2]`, the ray at `θ_max` strikes (the maximum is
attained — the grazing ray touches the closed disk), and no striking ray has a
larger parameter. -/
def IsMaxIncidenceAngle (R a θmax : ℝ) : Prop :=
  θmax ∈ Set.Icc 0 (Real.pi / 2) ∧
  ReflectedRayStrikesContainer R a θmax ∧
  ∀ θ : ℝ, θ ∈ Set.Icc 0 (Real.pi / 2) → ReflectedRayStrikesContainer R a θ → θ ≤ θmax

/-! ## The two powers (governing law 4: flux = intensity × impact width) -/

/-- Power the container would receive **per unit length** without the mirror
(the `P₀` of the problem, divided by the cylinder length `L`): with uniform
solar intensity `I` (power per unit area) the container presents the projected
width `2a` to the direct sunlight (`DirectRayStrikesContainer`), so
`P₀ / L = 2 a I`.  Units of `I`: power/area; of `2 a I`: power/length. -/
noncomputable def powerWithoutMirrorPerLength (I a : ℝ) : ℝ := 2 * a * I

/-- The **absorbed impact-parameter set** with the mirror present: the
transverse coordinates `x` of incoming parallel rays that are absorbed by the
container, either directly (`|x| ≤ a`, the container-shadow strip) or after
exactly one mirror reflection at some incidence angle `θ ∈ [0, π/2]` with
`|x| = R sin θ`.  The `|x|` form folds the left-right symmetric branch onto
`θ ∈ [0, π/2]` via `strikes_neg`.  Membership of a reflected ray certifies
absorption (not merely line intersection) thanks to `SingleReflectionRegime`:
the strike precedes any second mirror encounter.  Rays with `|x| ≥ R` miss the
aperture entirely and carry no power to the container. -/
def absorbedImpactSet (R a : ℝ) : Set ℝ :=
  {x : ℝ | DirectRayStrikesContainer a x} ∪
    {x : ℝ | ∃ θ : ℝ, θ ∈ Set.Icc 0 (Real.pi / 2) ∧
      ReflectedRayStrikesContainer R a θ ∧ |x| = R * Real.sin θ}

/-- Power the container receives **per unit length** with the mirror present
(the `P` of the problem, divided by `L`): uniform intensity `I` times the total
width (Lebesgue measure) of the absorbed impact-parameter set
(`absorbedImpactSet`) — governing law 4.  Units: power/length. -/
noncomputable def powerWithMirrorPerLength (I R a : ℝ) : ℝ :=
  I * (MeasureTheory.volume (absorbedImpactSet R a)).toReal

/-! ## Auxiliary coordinate lemmas (proof infrastructure, no physical content) -/

/-- Auxiliary: the real inner product of two plane vectors in coordinates. -/
private theorem inner_coords (u v : Plane) : ⟪u, v⟫ = u 0 * v 0 + u 1 * v 1 := by
  rw [PiLp.inner_apply, Fin.sum_univ_two]
  simp [RCLike.inner_apply]
  ring

/-- Auxiliary: the norm of a plane vector in coordinates. -/
private theorem norm_coords (p : Plane) : ‖p‖ = Real.sqrt (p 0 ^ 2 + p 1 ^ 2) := by
  rw [EuclideanSpace.norm_eq, Fin.sum_univ_two]
  simp [Real.norm_eq_abs, sq_abs]

/-- Auxiliary: the squared norm of a plane vector in coordinates. -/
private theorem norm_sq_coords (p : Plane) : ‖p‖ ^ 2 = p 0 ^ 2 + p 1 ^ 2 := by
  rw [norm_coords, Real.sq_sqrt (by positivity)]

/-- Auxiliary: the inner product of the incident direction with the radial normal
at `M(θ)` is `cos θ` (used in `incidence_angle_eq` and `reflectedDir_eq`). -/
private theorem inner_sunlight_normal (R θ : ℝ) (hR : 0 < R) :
    ⟪sunlightDir, outwardUnitNormal R (incidencePoint R θ)⟫ = Real.cos θ := by
  simp only [inner_coords, sunlightDir, outwardUnitNormal, incidencePoint, PiLp.smul_apply,
    smul_eq_mul, Matrix.cons_val_zero, Matrix.cons_val_one]
  rw [zero_mul, one_mul, zero_add, ← mul_assoc, inv_mul_cancel₀ hR.ne', one_mul]

/-! ## Bridge lemmas: reflection algebra (shared model, proofs deferred) -/

/-- The incident direction is a unit vector. -/
theorem sunlightDir_norm : ‖sunlightDir‖ = 1 := by
  rw [sunlightDir, norm_coords]
  simp

/-- The radial normal at a point of the circle is a unit vector. -/
theorem outwardUnitNormal_norm (R : ℝ) (hR : 0 < R) {p : Plane}
    (hp : p ∈ mirrorCircle R) :
    ‖outwardUnitNormal R p‖ = 1 := by
  have hp' : ‖p‖ = R := hp
  simp only [outwardUnitNormal, norm_smul, Real.norm_of_nonneg (inv_nonneg.mpr hR.le), hp',
    inv_mul_cancel₀ hR.ne']

/-- Reflection in a unit normal preserves unit vectors. -/
theorem specularReflect_norm {n d : Plane} (hn : ‖n‖ = 1) (hd : ‖d‖ = 1) :
    ‖specularReflect n d‖ = 1 := by
  have hnn : ⟪n, n⟫ = 1 := by rw [real_inner_self_eq_norm_sq, hn]; norm_num
  have hdd : ⟪d, d⟫ = 1 := by rw [real_inner_self_eq_norm_sq, hd]; norm_num
  have key : ⟪specularReflect n d, specularReflect n d⟫ = 1 := by
    simp only [specularReflect, inner_sub_left, inner_sub_right, real_inner_smul_left,
      real_inner_smul_right, hnn, hdd, real_inner_comm n d]
    ring
  rw [norm_eq_sqrt_real_inner, key, Real.sqrt_one]

/-- Angle form of the law of reflection: the normal component of the direction
flips sign at a reflection, i.e. the angle of incidence equals the angle of
reflection with respect to the normal. -/
theorem specularReflect_normal_component_neg {n d : Plane} (hn : ‖n‖ = 1) :
    ⟪specularReflect n d, n⟫ = -⟪d, n⟫ := by
  have hnn : ⟪n, n⟫ = 1 := by rw [real_inner_self_eq_norm_sq, hn]; norm_num
  simp only [specularReflect, inner_sub_left, real_inner_smul_left, hnn]
  ring

/-- The incidence point lies on the mirror circle. -/
theorem incidencePoint_mem_circle (R θ : ℝ) (hR : 0 < R) :
    incidencePoint R θ ∈ mirrorCircle R := by
  show ‖incidencePoint R θ‖ = R
  rw [incidencePoint, norm_coords]
  have hsq : (!₂[R * Real.sin θ, R * Real.cos θ] : Plane) 0 ^ 2
      + (!₂[R * Real.sin θ, R * Real.cos θ] : Plane) 1 ^ 2 = R ^ 2 := by
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one]
    rw [mul_pow, mul_pow, ← mul_add, Real.sin_sq_add_cos_sq, mul_one]
  rw [hsq, Real.sqrt_sq hR.le]

/-- For `|θ| < π/2` the incidence point lies on the reflecting arc
(`y = R cos θ > 0`). -/
theorem incidencePoint_mem_arc (R θ : ℝ) (hR : 0 < R)
    (hθ : θ ∈ Set.Ioo (-(Real.pi / 2)) (Real.pi / 2)) :
    incidencePoint R θ ∈ mirrorArc R := by
  refine ⟨incidencePoint_mem_circle R θ hR, ?_⟩
  show 0 < yCoord (incidencePoint R θ)
  simp only [yCoord, incidencePoint, Matrix.cons_val_one]
  exact mul_pos hR (Real.cos_pos_of_mem_Ioo hθ)

/-- **The parameter `θ` is the angle of incidence** (the bridge between the
mirror parametrization and the `θ` of the problem statement): the angle between
the incident direction and the normal at `M(θ)`, measured with respect to the
normal as the problem requires, is `arccos(cos θ) = θ` on `[0, π/2]`.
Proof route: `⟪sunlightDir, outwardUnitNormal R (M θ)⟫ = cos θ` by direct
computation, then `Real.arccos_cos` (`0 ≤ θ ≤ π`). -/
theorem incidence_angle_eq (R θ : ℝ) (hR : 0 < R)
    (hθ : θ ∈ Set.Icc 0 (Real.pi / 2)) :
    Real.arccos ⟪sunlightDir, outwardUnitNormal R (incidencePoint R θ)⟫ = θ := by
  rw [inner_sunlight_normal R θ hR]
  exact Real.arccos_cos hθ.1
    (le_trans hθ.2 (by linarith [Real.pi_pos] : Real.pi / 2 ≤ Real.pi))

/-- Closed form of the reflected direction: reflecting `d = (0, 1)` in the
radial normal `(sin θ, cos θ)` gives `d' = (−sin 2θ, −cos 2θ)` — the ray turns
toward the optical axis, by twice the incidence angle.  Proof route: unfold
`reflectedDir`, `specularReflect`, `outwardUnitNormal`, `incidencePoint`, use
`Real.sin_two_mul`, `Real.cos_two_mul` and `hR` for the `R⁻¹ R` cancellation. -/
theorem reflectedDir_eq (R θ : ℝ) (hR : 0 < R) :
    reflectedDir R θ = !₂[-Real.sin (2 * θ), -Real.cos (2 * θ)] := by
  have hinner := inner_sunlight_normal R θ hR
  ext i
  simp only [reflectedDir, specularReflect]
  rw [hinner]
  fin_cases i <;>
    simp only [PiLp.sub_apply, PiLp.smul_apply, smul_eq_mul, outwardUnitNormal,
      incidencePoint, sunlightDir, Matrix.cons_val_zero, Matrix.cons_val_one, Fin.reduceFinMk]
  · rw [Real.sin_two_mul]
    field_simp
    ring
  · rw [Real.cos_two_mul]
    field_simp
    ring

/-- The reflected direction is a unit vector (so `t` in `reflectedRay` is arc
length).  Proof route: `specularReflect_norm` with `outwardUnitNormal_norm`
(`incidencePoint_mem_circle`) and `sunlightDir_norm`. -/
theorem reflectedDir_norm (R θ : ℝ) (hR : 0 < R) :
    ‖reflectedDir R θ‖ = 1 := by
  simp only [reflectedDir]
  exact specularReflect_norm
    (outwardUnitNormal_norm R hR (incidencePoint_mem_circle R θ hR)) sunlightDir_norm

/-! ## Bridge lemmas: distance to the container and the strike characterization
(shared T2-B model, as in `problem_ipho_2026_t2_b2.lean`) -/

/-- **Distance identity** (the geometric heart of the T2-B parts): the
perpendicular distance from the container centre `C = (0, R/2)` to the
reflected line at incidence angle `θ ∈ [0, π/2]` is `R·sin θ·(1 − cos θ)`.
Proof route: unfold via `reflectedDir_eq`; the 2D cross product of
`C − M = (−R sin θ, R/2 − R cos θ)` with `d' = (−sin 2θ, −cos 2θ)` simplifies
with `Real.sin_two_mul` / `Real.cos_two_mul` to `−R sin θ (1 − cos θ)`; take the
absolute value (`sin θ, 1 − cos θ ≥ 0` on the range) and divide by
`‖d'‖ = 1` (`reflectedDir_norm`). -/
theorem distToLine_container (R θ : ℝ) (hR : 0 < R)
    (hθ : θ ∈ Set.Icc 0 (Real.pi / 2)) :
    distToLine (containerCenter R) (incidencePoint R θ) (reflectedDir R θ)
      = R * Real.sin θ * (1 - Real.cos θ) := by
  have hcross : cross2 (containerCenter R - incidencePoint R θ) (reflectedDir R θ)
      = -(R * Real.sin θ * (1 - Real.cos θ)) := by
    rw [reflectedDir_eq R θ hR]
    simp only [cross2, xCoord, yCoord, containerCenter, incidencePoint, PiLp.sub_apply,
      Matrix.cons_val_zero, Matrix.cons_val_one]
    rw [Real.sin_two_mul, Real.cos_two_mul]
    ring
  have hsin : 0 ≤ Real.sin θ :=
    Real.sin_nonneg_of_mem_Icc ⟨hθ.1, le_trans hθ.2 (by linarith [Real.pi_pos])⟩
  have hcos : 0 ≤ 1 - Real.cos θ := sub_nonneg.mpr (Real.cos_le_one θ)
  simp only [distToLine, hcross, reflectedDir_norm R θ hR, div_one, abs_neg]
  exact abs_of_nonneg (mul_nonneg (mul_nonneg hR.le hsin) hcos)

/-- Closest-approach parameter in closed form: `R cos θ − (R/2) cos 2θ`.
Proof route: unfold `footParam` with `reflectedDir_eq` and the inner product;
use `Real.sin_two_mul`, `Real.cos_two_mul`, `Real.cos_sq` and the cosine
subtraction law `Real.cos_sub` backwards: `sin θ sin 2θ + cos θ cos 2θ = cos θ`. -/
theorem footParam_eq (R θ : ℝ) (hR : 0 < R) :
    footParam R θ = R * Real.cos θ - (R / 2) * Real.cos (2 * θ) := by
  have hcos : Real.sin θ * Real.sin (2 * θ) + Real.cos θ * Real.cos (2 * θ)
      = Real.cos θ := by
    have h := Real.cos_sub (2 * θ) θ
    rw [show 2 * θ - θ = θ by ring] at h
    linarith
  simp only [footParam]
  rw [reflectedDir_eq R θ hR, inner_coords]
  simp only [containerCenter, incidencePoint, PiLp.sub_apply, Matrix.cons_val_zero,
    Matrix.cons_val_one]
  linear_combination R * hcos

/-- The closest approach is on the forward branch: `R cos θ − (R/2) cos 2θ > 0`
on `[0, π/2]`.  Proof route: on `[0, π/4]`, `cos θ ≥ cos 2θ > 0` gives
`cos θ − (1/2) cos 2θ ≥ (1/2) cos 2θ > 0`; on `(π/4, π/2]`, `cos 2θ ≤ 0` and
`cos θ ≥ 0` with not both zero. -/
theorem footParam_pos (R θ : ℝ) (hR : 0 < R)
    (hθ : θ ∈ Set.Icc 0 (Real.pi / 2)) :
    0 < footParam R θ := by
  rw [footParam_eq R θ hR, Real.cos_two_mul]
  have hc0 : 0 ≤ Real.cos θ :=
    Real.cos_nonneg_of_mem_Icc ⟨le_trans (by linarith [Real.pi_pos]) hθ.1, hθ.2⟩
  have hc1 : Real.cos θ ≤ 1 := Real.cos_le_one θ
  have heq : R * Real.cos θ - R / 2 * (2 * Real.cos θ ^ 2 - 1)
      = R * Real.cos θ * (1 - Real.cos θ) + R / 2 := by ring
  rw [heq]
  have h1 : 0 ≤ R * Real.cos θ * (1 - Real.cos θ) :=
    mul_nonneg (mul_nonneg hR.le hc0) (sub_nonneg.mpr hc1)
  linarith

/-- **Strike characterization**: a reflected ray at incidence angle
`θ ∈ [0, π/2]` strikes the container iff the perpendicular distance from `C` to
its line is at most `a`.  Proof route: for a unit direction `v`
(`reflectedDir_norm`) the map `t ↦ ‖q + t • v − C‖` is minimized at
`t = ⟪C − q, v⟫ = footParam R θ` with minimum exactly
`distToLine C q v`; the minimum is attained at a positive parameter
(`footParam_pos`), and membership in `Metric.closedBall` is `dist ≤ a`
(`Metric.mem_closedBall`, `dist_eq_norm`). -/
theorem strikes_iff_dist_le (R a θ : ℝ) (hR : 0 < R) (ha : 0 < a)
    (hθ : θ ∈ Set.Icc 0 (Real.pi / 2)) :
    ReflectedRayStrikesContainer R a θ ↔
      distToLine (containerCenter R) (incidencePoint R θ) (reflectedDir R θ) ≤ a := by
  have hv : ‖reflectedDir R θ‖ = 1 := reflectedDir_norm R θ hR
  have hvv : ⟪reflectedDir R θ, reflectedDir R θ⟫ = 1 := by
    rw [real_inner_self_eq_norm_sq, hv]; norm_num
  have hvv2 : reflectedDir R θ 0 * reflectedDir R θ 0
      + reflectedDir R θ 1 * reflectedDir R θ 1 = 1 := by
    rw [← inner_coords]; exact hvv
  -- Squared distance from `C` to the point at parameter `t` on the reflected line,
  -- as the sum of the tangential and perpendicular parts (2D Lagrange identity).
  have key : ∀ t : ℝ,
      ‖t • reflectedDir R θ - (containerCenter R - incidencePoint R θ)‖ ^ 2
        = (t - ⟪reflectedDir R θ, containerCenter R - incidencePoint R θ⟫) ^ 2
          + cross2 (containerCenter R - incidencePoint R θ) (reflectedDir R θ) ^ 2 := by
    intro t
    simp only [norm_sq_coords, inner_coords, cross2, xCoord, yCoord, PiLp.sub_apply,
      PiLp.smul_apply, smul_eq_mul]
    linear_combination
      (t ^ 2 - ((containerCenter R 0 - incidencePoint R θ 0) ^ 2
        + (containerCenter R 1 - incidencePoint R θ 1) ^ 2)) * hvv2
  -- Membership in the closed disk, measured along the line.
  have hmem : ∀ t : ℝ, reflectedRay R θ t ∈ containerDisk R a ↔
      ‖t • reflectedDir R θ - (containerCenter R - incidencePoint R θ)‖ ≤ a := by
    intro t
    have hdecomp : reflectedRay R θ t - containerCenter R
        = t • reflectedDir R θ - (containerCenter R - incidencePoint R θ) := by
      simp only [reflectedRay]; abel
    simp only [containerDisk, Metric.mem_closedBall, dist_eq_norm, hdecomp]
  -- The perpendicular distance is `|cross2|`, since the direction is a unit vector.
  have hd : distToLine (containerCenter R) (incidencePoint R θ) (reflectedDir R θ)
      = |cross2 (containerCenter R - incidencePoint R θ) (reflectedDir R θ)| := by
    simp only [distToLine, hv, div_one]
  constructor
  · rintro ⟨t, -, ht⟩
    rw [hmem t] at ht
    have hsq : cross2 (containerCenter R - incidencePoint R θ) (reflectedDir R θ) ^ 2
        ≤ ‖t • reflectedDir R θ - (containerCenter R - incidencePoint R θ)‖ ^ 2 := by
      rw [key t]
      exact le_add_of_nonneg_left (sq_nonneg _)
    have habs : |cross2 (containerCenter R - incidencePoint R θ) (reflectedDir R θ)|
        ≤ ‖t • reflectedDir R θ - (containerCenter R - incidencePoint R θ)‖ := by
      have h := Real.sqrt_le_sqrt hsq
      rwa [Real.sqrt_sq_eq_abs, Real.sqrt_sq (norm_nonneg _)] at h
    rw [hd]
    exact le_trans habs ht
  · intro hdist
    rw [hd] at hdist
    have hfoot : 0 < ⟪reflectedDir R θ, containerCenter R - incidencePoint R θ⟫ := by
      have hfp := footParam_pos R θ hR hθ
      simp only [footParam] at hfp
      rwa [real_inner_comm (reflectedDir R θ) (containerCenter R - incidencePoint R θ)] at hfp
    refine ⟨⟪reflectedDir R θ, containerCenter R - incidencePoint R θ⟫, hfoot, ?_⟩
    rw [hmem]
    have hsq : ‖⟪reflectedDir R θ, containerCenter R - incidencePoint R θ⟫
          • reflectedDir R θ - (containerCenter R - incidencePoint R θ)‖ ^ 2 ≤ a ^ 2 := by
      rw [key, sub_self, zero_pow (two_ne_zero), zero_add]
      exact sq_le_sq' (abs_le.mp hdist).1 (abs_le.mp hdist).2
    have hnorm := abs_le_of_sq_le_sq hsq ha.le
    rwa [abs_of_nonneg (norm_nonneg _)] at hnorm

/-- **Left-right symmetry** of Fig. 2f: reflection across the optical axis
conjugates the ray at `−θ` to the ray at `θ` (the container disk is centred on
the axis), so one strikes iff the other does.  This legitimizes restricting the
incidence angle to `[0, π/2]` and folding both impact-parameter branches into
`|x| = R sin θ` in `absorbedImpactSet`. -/
theorem strikes_neg (R a θ : ℝ) (hR : 0 < R) :
    ReflectedRayStrikesContainer R a (-θ) ↔ ReflectedRayStrikesContainer R a θ := by
  -- Pointwise: the ray at `-θ` is the mirror image (flip of the transverse coordinate)
  -- of the ray at `θ`, and the container disk is invariant under the flip.
  have hpoint : ∀ t : ℝ, reflectedRay R (-θ) t ∈ containerDisk R a ↔
      reflectedRay R θ t ∈ containerDisk R a := by
    intro t
    have e0 : (reflectedRay R (-θ) t - containerCenter R) 0
        = -((reflectedRay R θ t - containerCenter R) 0) := by
      simp only [reflectedRay, reflectedDir_eq R (-θ) hR, reflectedDir_eq R θ hR,
        incidencePoint, containerCenter, PiLp.sub_apply, PiLp.add_apply, PiLp.smul_apply,
        smul_eq_mul, Matrix.cons_val_zero, Real.sin_neg, Real.cos_neg, mul_neg, neg_neg]
      ring
    have e1 : (reflectedRay R (-θ) t - containerCenter R) 1
        = (reflectedRay R θ t - containerCenter R) 1 := by
      simp only [reflectedRay, reflectedDir_eq R (-θ) hR, reflectedDir_eq R θ hR,
        incidencePoint, containerCenter, PiLp.sub_apply, PiLp.add_apply, PiLp.smul_apply,
        smul_eq_mul, Matrix.cons_val_one, Real.sin_neg, Real.cos_neg, mul_neg, neg_neg]
    simp only [containerDisk, Metric.mem_closedBall, dist_eq_norm, norm_coords, e0, e1,
      neg_sq]
  constructor
  · rintro ⟨t, ht0, ht⟩
    exact ⟨t, ht0, (hpoint t).mp ht⟩
  · rintro ⟨t, ht0, ht⟩
    exact ⟨t, ht0, (hpoint t).mpr ht⟩

/-- **Monotonicity of the distance**: `θ ↦ R sin θ (1 − cos θ)` is strictly
increasing on `[0, π/2]` (derivative `R (cos θ − cos 2θ) > 0` on `(0, π/2)`,
or a direct estimate from `Real.strictMonoOn_sin` and strict antitonicity of
`cos` on `[0, π]`, `Real.strictAntiOn_cos`).  Hence the striking rays form an
initial angular interval `[0, θ_max]`. -/
theorem dist_strictMonoOn (R : ℝ) (hR : 0 < R) :
    StrictMonoOn (fun θ : ℝ => R * Real.sin θ * (1 - Real.cos θ))
      (Set.Icc 0 (Real.pi / 2)) := by
  intro x hx y hy hxy
  have hhalf : Real.pi / 2 ≤ Real.pi := by linarith [Real.pi_pos]
  have hsin : Real.sin x < Real.sin y :=
    Real.strictMonoOn_sin
      ⟨le_trans (by linarith [Real.pi_pos] : -(Real.pi / 2) ≤ 0) hx.1, hx.2⟩
      ⟨le_trans (by linarith [Real.pi_pos] : -(Real.pi / 2) ≤ 0) hy.1, hy.2⟩ hxy
  have hcos : Real.cos y < Real.cos x :=
    Real.strictAntiOn_cos ⟨hx.1, le_trans hx.2 hhalf⟩ ⟨hy.1, le_trans hy.2 hhalf⟩ hxy
  have h1 : (0:ℝ) ≤ Real.sin x :=
    Real.sin_nonneg_of_mem_Icc ⟨hx.1, le_trans hx.2 hhalf⟩
  have hy0 : (0:ℝ) < y := lt_of_le_of_lt hx.1 hxy
  have hcosy1 : Real.cos y < 1 := by
    have h0 : (0:ℝ) ∈ Set.Icc 0 Real.pi := ⟨le_refl 0, Real.pi_pos.le⟩
    have := Real.strictAntiOn_cos h0 ⟨hy.1, le_trans hy.2 hhalf⟩ hy0
    rwa [Real.cos_zero] at this
  have h2 : (0:ℝ) < 1 - Real.cos y := sub_pos.mpr hcosy1
  have hb : 1 - Real.cos x ≤ 1 - Real.cos y := sub_le_sub_left hcos.le 1
  have hprod : Real.sin x * (1 - Real.cos x) < Real.sin y * (1 - Real.cos y) :=
    lt_of_le_of_lt (mul_le_mul_of_nonneg_left hb h1) (mul_lt_mul_of_pos_right hsin h2)
  calc R * Real.sin x * (1 - Real.cos x)
      = R * (Real.sin x * (1 - Real.cos x)) := by ring
    _ < R * (Real.sin y * (1 - Real.cos y)) := mul_lt_mul_of_pos_left hprod hR
    _ = R * Real.sin y * (1 - Real.cos y) := by ring

/-- The distance function is continuous (used to locate the extremal ray at the
grazing contact). -/
theorem dist_continuous (R : ℝ) :
    Continuous (fun θ : ℝ => R * Real.sin θ * (1 - Real.cos θ)) := by
  exact (continuous_const.mul Real.continuous_sin).mul
    (continuous_const.sub Real.continuous_cos)

/-! ## Bridge lemmas: the extremal ray grazes the container (T2-B1 route) -/

/-- The vertex `(0, R)` of the mirror lies on the reflecting arc. -/
theorem topPoint_mem_arc (R : ℝ) (hR : 0 < R) :
    !₂[(0 : ℝ), R] ∈ mirrorArc R := by
  refine ⟨?_, ?_⟩
  · show ‖!₂[(0 : ℝ), R]‖ = R
    rw [norm_coords]
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one]
    rw [zero_pow two_ne_zero, zero_add, Real.sqrt_sq hR.le]
  · show (0 : ℝ) < yCoord (!₂[(0 : ℝ), R])
    simp only [yCoord, Matrix.cons_val_one]
    exact hR

/-- The container radius is less than `R/2`: the vertex `(0, R)` of the mirror
is at distance `R/2` from `C`, and it must clear the absorbing disk
(`ContainerClearOfMirror` at `topPoint_mem_arc`). -/
theorem container_radius_lt_half (R a : ℝ) (hR : 0 < R)
    (hclear : ContainerClearOfMirror R a) :
    a < R / 2 := by
  have hnot := hclear _ (topPoint_mem_arc R hR)
  simp only [containerDisk, Metric.mem_closedBall, dist_eq_norm] at hnot
  have hnorm : ‖!₂[(0:ℝ), R] - containerCenter R‖ = R / 2 := by
    rw [norm_coords]
    have hsq : (!₂[(0:ℝ), R] - containerCenter R) 0 ^ 2
        + (!₂[(0:ℝ), R] - containerCenter R) 1 ^ 2 = (R / 2) ^ 2 := by
      simp only [containerCenter, PiLp.sub_apply, Matrix.cons_val_zero, Matrix.cons_val_one]
      ring
    rw [hsq, Real.sqrt_sq (by linarith : (0:ℝ) ≤ R / 2)]
  rw [hnorm] at hnot
  exact lt_of_not_ge hnot

/-- **Grazing contact at the extremal angle**: the ray at `θ_max` is tangent to
the container — the distance from `C` to its line equals `a` exactly.
Proof route: `dist(θ_max) ≤ a` from `strikes_iff_dist_le`.  If it were `< a`,
then `dist(θ_max) < a < R/2 < R = dist(π/2)` (`container_radius_lt_half`,
`distToLine_container` at `π/2`), so by `dist_strictMonoOn` and
`dist_continuous` there is `θ' ∈ (θ_max, π/2)` with `dist(θ') ≤ a`, i.e. a
striking ray with larger incidence angle — contradicting the maximality in
`IsMaxIncidenceAngle`. -/
theorem dist_at_max_eq (R a θmax : ℝ) (hR : 0 < R) (ha : 0 < a)
    (hclear : ContainerClearOfMirror R a) (hmax : IsMaxIncidenceAngle R a θmax) :
    distToLine (containerCenter R) (incidencePoint R θmax) (reflectedDir R θmax)
      = a := by
  obtain ⟨hθm, hstrike, hbound⟩ := hmax
  have hD : ∀ φ : ℝ, φ ∈ Set.Icc 0 (Real.pi / 2) →
      distToLine (containerCenter R) (incidencePoint R φ) (reflectedDir R φ)
        = R * Real.sin φ * (1 - Real.cos φ) :=
    fun φ hφ => distToLine_container R φ hR hφ
  have hle : R * Real.sin θmax * (1 - Real.cos θmax) ≤ a := by
    have h := (strikes_iff_dist_le R a θmax hR ha hθm).mp hstrike
    rwa [hD θmax hθm] at h
  by_contra hne
  rw [hD θmax hθm] at hne
  have hlt : R * Real.sin θmax * (1 - Real.cos θmax) < a := lt_of_le_of_ne hle hne
  have haR : a < R / 2 := container_radius_lt_half R a hR hclear
  have hcont : ContinuousOn (fun θ => R * Real.sin θ * (1 - Real.cos θ))
      (Set.Icc 0 (Real.pi / 2)) := (dist_continuous R).continuousOn
  have hval0 : (fun θ => R * Real.sin θ * (1 - Real.cos θ)) 0 = 0 := by simp
  have hval : (fun θ => R * Real.sin θ * (1 - Real.cos θ)) (Real.pi / 2) = R := by
    simp [Real.sin_pi_div_two, Real.cos_pi_div_two]
  have haIcc : a ∈ Set.Icc ((fun θ => R * Real.sin θ * (1 - Real.cos θ)) 0)
      ((fun θ => R * Real.sin θ * (1 - Real.cos θ)) (Real.pi / 2)) := by
    rw [hval0, hval]
    exact ⟨ha.le, by linarith⟩
  obtain ⟨θ', hθ', hθ'eq⟩ := intermediate_value_Icc
    (by positivity : (0:ℝ) ≤ Real.pi / 2) hcont haIcc
  have hθ'eq' : R * Real.sin θ' * (1 - Real.cos θ') = a := hθ'eq
  have hlt2 : θmax < θ' := by
    by_contra hnot
    rcases lt_or_eq_of_le (le_of_not_gt hnot) with h | h
    · have hmono := dist_strictMonoOn R hR hθ' hθm h
      have hmono' : R * Real.sin θ' * (1 - Real.cos θ')
          < R * Real.sin θmax * (1 - Real.cos θmax) := hmono
      linarith
    · subst h; linarith
  have hstrike' : ReflectedRayStrikesContainer R a θ' := by
    rw [strikes_iff_dist_le R a θ' hR ha hθ', hD θ' hθ', hθ'eq']
  have := hbound θ' hθ' hstrike'
  linarith

/-- Double-angle expansion of the distance:
`R sin θ (1 − cos θ) = R sin θ + (−R/2) sin 2θ`.  Proof route:
`Real.sin_two_mul` and ring. -/
theorem distTrig_expand (R θ : ℝ) :
    R * Real.sin θ * (1 - Real.cos θ)
      = R * Real.sin θ + (-(R / 2)) * Real.sin (2 * θ) := by
  rw [Real.sin_two_mul]
  ring

/-- **T2-B1 previous-part result** (derived inline from problem-only material,
per the `derive_inline_from_problem_only_material` policy — same statement as
`IPhO2026.T2B1.container_radius_eq`): under the problem's assumptions,

```
a = R·sin θ_max + (−R/2)·sin (2 θ_max),
```

i.e. `a = α sin θ_max + β sin(2θ_max)` with `α = R` and `β = −R/2`.
Proof route: `a = dist(θ_max)` by `dist_at_max_eq`, `dist(θ_max) =
R sin θ_max (1 − cos θ_max)` by `distToLine_container`, and `distTrig_expand`. -/
theorem container_radius_eq (R a θmax : ℝ) (hR : 0 < R) (ha : 0 < a)
    (hclear : ContainerClearOfMirror R a) (hsingle : SingleReflectionRegime R a)
    (hmax : IsMaxIncidenceAngle R a θmax) :
    a = R * Real.sin θmax + (-(R / 2)) * Real.sin (2 * θmax) := by
  -- `hsingle` legitimizes the one-reflection model; the algebraic step below uses the
  -- geometry encoded in the bridge lemmas (`(fun _ => ·) hsingle` records this use).
  refine (fun _ => ?_) hsingle
  exact ((dist_at_max_eq R a θmax hR ha hclear hmax).symm.trans
    (distToLine_container R θmax hR hmax.1)).trans (distTrig_expand R θmax)

/-- **Factored form of the T2-B1 relation**: `a = R·sin θ_max·(1 − cos θ_max)`.
This is the form that eliminates `a` from the power ratio and that yields the
B3 radius by direct substitution.  Proof route: `dist_at_max_eq` and
`distToLine_container` at `θ_max` (`hmax.1` gives `θ_max ∈ [0, π/2]`). -/
theorem container_radius_eq_factored (R a θmax : ℝ) (hR : 0 < R) (ha : 0 < a)
    (hclear : ContainerClearOfMirror R a) (hsingle : SingleReflectionRegime R a)
    (hmax : IsMaxIncidenceAngle R a θmax) :
    a = R * Real.sin θmax * (1 - Real.cos θmax) := by
  refine (fun _ => ?_) hsingle
  exact ((dist_at_max_eq R a θmax hR ha hclear hmax).symm.trans
    (distToLine_container R θmax hR hmax.1))

/-! ## Bridge lemmas: signs of the trigonometric factors at `θ_max` -/

/-- `θ_max` is strictly positive: `θ_max ∈ [0, π/2]` (from `hmax.1`) and if
`θ_max = 0` then `a = dist(0) = R·sin 0·(1 − cos 0) = 0` by `dist_at_max_eq`
and `distToLine_container`, contradicting `0 < a`.  This fixes the positive
branch for `sin θ_max` in the B3 computation. -/
theorem thetaMax_pos (R a θmax : ℝ) (hR : 0 < R) (ha : 0 < a)
    (hclear : ContainerClearOfMirror R a) (hmax : IsMaxIncidenceAngle R a θmax) :
    0 < θmax := by
  have hdist := dist_at_max_eq R a θmax hR ha hclear hmax
  obtain ⟨hθm, -, -⟩ := hmax
  rcases eq_or_lt_of_le hθm.1 with h0 | hpos
  · exfalso
    rw [distToLine_container R θmax hR hθm, ← h0] at hdist
    simp only [Real.sin_zero, Real.cos_zero, sub_self, mul_zero] at hdist
    linarith
  · exact hpos

/-- `sin θ > 0` on `(0, π/2]`.  Proof route:
`Real.sin_pos_of_pos_of_lt_pi` with `0 < θ` and `θ ≤ π/2 < π`. -/
theorem sin_pos_of_theta_range {θ : ℝ} (hθ : θ ∈ Set.Ioc 0 (Real.pi / 2)) :
    0 < Real.sin θ := by
  exact Real.sin_pos_of_pos_of_lt_pi hθ.1
    (lt_of_le_of_lt hθ.2 (by linarith [Real.pi_pos] : Real.pi / 2 < Real.pi))

/-- `1 − cos θ > 0` on `(0, π/2]`.  Proof route: `cos` is strictly antitone on
`[0, π]` (`Real.strictAntiOn_cos`), so `cos θ < cos 0 = 1` for `0 < θ ≤ π/2`. -/
theorem one_sub_cos_pos_of_theta_range {θ : ℝ} (hθ : θ ∈ Set.Ioc 0 (Real.pi / 2)) :
    0 < 1 - Real.cos θ := by
  have h0 : (0:ℝ) ∈ Set.Icc 0 Real.pi := ⟨le_refl 0, Real.pi_pos.le⟩
  have hθ' : θ ∈ Set.Icc 0 Real.pi :=
    ⟨hθ.1.le, le_trans hθ.2 (by linarith [Real.pi_pos] : Real.pi / 2 ≤ Real.pi)⟩
  have h := Real.strictAntiOn_cos h0 hθ' hθ.1
  rw [Real.cos_zero] at h
  exact sub_pos.mpr h

/-! ## Bridge lemmas: the absorbed impact set is the full interval -/

/-- **Strike iff below the maximum**: a reflected ray at incidence angle
`θ ∈ [0, π/2]` strikes the container iff `θ ≤ θ_max`.
Proof route: `strikes_iff_dist_le` reduces to `dist(θ) ≤ a`; by
`dist_at_max_eq` the right-hand side is `dist(θ_max)`, and
`dist_strictMonoOn.le_iff_le` (with `distToLine_container` identifying the
function) turns `dist(θ) ≤ dist(θ_max)` into `θ ≤ θ_max`; the forward
direction is the maximality clause of `IsMaxIncidenceAngle`. -/
theorem strikes_iff_le_max (R a θmax : ℝ) (hR : 0 < R) (ha : 0 < a)
    (hclear : ContainerClearOfMirror R a) (hmax : IsMaxIncidenceAngle R a θmax)
    {θ : ℝ} (hθ : θ ∈ Set.Icc 0 (Real.pi / 2)) :
    ReflectedRayStrikesContainer R a θ ↔ θ ≤ θmax := by
  have hθm := hmax.1
  have hD : ∀ φ : ℝ, φ ∈ Set.Icc 0 (Real.pi / 2) →
      distToLine (containerCenter R) (incidencePoint R φ) (reflectedDir R φ)
        = R * Real.sin φ * (1 - Real.cos φ) :=
    fun φ hφ => distToLine_container R φ hR hφ
  have hdistmax := dist_at_max_eq R a θmax hR ha hclear hmax
  rw [hD θmax hθm] at hdistmax
  rw [strikes_iff_dist_le R a θ hR ha hθ, hD θ hθ, ← hdistmax]
  exact (dist_strictMonoOn R hR).le_iff_le hθ hθm

/-- **Coverage of the impact strip**: every value `y ∈ [0, sin θ_max]` is
`sin θ` for some `θ ∈ [0, θ_max]`.  Proof route: take `θ = Real.arcsin y`;
`Real.sin_arcsin'` (with `0 ≤ y ≤ sin θ_max ≤ 1`) gives `sin θ = y`, and
`Real.monotone_arcsin` with `Real.arcsin_sin` (valid on `[0, π/2]`) gives
`arcsin y ≤ arcsin (sin θ_max) = θ_max`. -/
theorem sin_surj_upto {θmax : ℝ} (hθmax : θmax ∈ Set.Icc 0 (Real.pi / 2))
    {y : ℝ} (hy : y ∈ Set.Icc 0 (Real.sin θmax)) :
    ∃ θ : ℝ, θ ∈ Set.Icc 0 θmax ∧ Real.sin θ = y := by
  have hs1 : Real.sin θmax ≤ 1 := Real.sin_le_one θmax
  have hy1 : y ∈ Set.Icc (-1 : ℝ) 1 :=
    ⟨le_trans (by norm_num : (-1:ℝ) ≤ 0) hy.1, le_trans hy.2 hs1⟩
  refine ⟨Real.arcsin y, ⟨?_, ?_⟩, Real.sin_arcsin' hy1⟩
  · have h := Real.monotone_arcsin hy.1
    rwa [Real.arcsin_zero] at h
  · have hle : Real.arcsin y ≤ Real.arcsin (Real.sin θmax) := Real.monotone_arcsin hy.2
    rwa [Real.arcsin_sin
      (le_trans (by linarith [Real.pi_pos] : -(Real.pi / 2) ≤ 0) hθmax.1) hθmax.2] at hle

/-- **The absorbed impact set is exactly `[−R sin θ_max, R sin θ_max]`** — the
geometric heart of T2-B2: every ray with `|x| ≤ R sin θ_max` is absorbed and no
ray beyond is.
Proof route: extensionality on `x`.
* (`⊆`) Direct rays: `|x| ≤ a ≤ R sin θ_max` (using
  `container_radius_eq_factored`: `a = R sin θ_max (1 − cos θ_max) ≤ R sin θ_max`
  since `0 ≤ 1 − cos θ_max ≤ 1` and `sin θ_max ≥ 0`).  Reflected rays: from
  `|x| = R sin θ` and `strikes_iff_le_max`, `θ ≤ θ_max`, so
  `|x| = R sin θ ≤ R sin θ_max` by `Real.strictMonoOn_sin.monotoneOn` and
  `0 < R`.
* (`⊇`) If `|x| ≤ a`, direct absorption.  If `a < |x| ≤ R sin θ_max`, set
  `y = |x|/R ∈ [0, sin θ_max]`; `sin_surj_upto` yields `θ ∈ [0, θ_max]` with
  `R sin θ = |x|`, and `strikes_iff_le_max` shows the reflected ray strikes the
  container; `SingleReflectionRegime` certifies the strike is an absorption
  (the container is met before any second mirror encounter), and `|x| > a`
  certifies the ray was not intercepted by the container on its way to the
  mirror. -/
theorem absorbedImpactSet_eq_Icc (R a θmax : ℝ) (hR : 0 < R) (ha : 0 < a)
    (hclear : ContainerClearOfMirror R a) (hsingle : SingleReflectionRegime R a)
    (hmax : IsMaxIncidenceAngle R a θmax) :
    absorbedImpactSet R a = Set.Icc (-(R * Real.sin θmax)) (R * Real.sin θmax) := by
  -- `hsingle` certifies that a geometric strike is an absorption (physical contract);
  -- the set equality itself is proved from the strike characterization.
  refine (fun _ => ?_) hsingle
  have hθm := hmax.1
  have hfact : a = R * Real.sin θmax * (1 - Real.cos θmax) :=
    container_radius_eq_factored R a θmax hR ha hclear hsingle hmax
  have hsinm : 0 ≤ Real.sin θmax :=
    Real.sin_nonneg_of_mem_Icc ⟨hθm.1, le_trans hθm.2 (by linarith [Real.pi_pos])⟩
  have hcosm0 : 0 ≤ Real.cos θmax :=
    Real.cos_nonneg_of_mem_Icc
      ⟨le_trans (by linarith [Real.pi_pos] : -(Real.pi / 2) ≤ 0) hθm.1, hθm.2⟩
  have ha_le : a ≤ R * Real.sin θmax := by
    rw [hfact]
    calc R * Real.sin θmax * (1 - Real.cos θmax)
        ≤ R * Real.sin θmax * 1 :=
          mul_le_mul_of_nonneg_left (by linarith : 1 - Real.cos θmax ≤ 1)
            (mul_nonneg hR.le hsinm)
      _ = R * Real.sin θmax := mul_one _
  ext x
  constructor
  · intro hx
    rw [Set.mem_Icc, ← abs_le]
    simp only [absorbedImpactSet, Set.mem_union, Set.mem_setOf_eq] at hx
    rcases hx with hx | ⟨θ, hθ, hstrike, habs⟩
    · exact le_trans hx ha_le
    · rw [habs]
      have hθle : θ ≤ θmax := (strikes_iff_le_max R a θmax hR ha hclear hmax hθ).mp hstrike
      have hsinle : Real.sin θ ≤ Real.sin θmax :=
        Real.strictMonoOn_sin.monotoneOn
          ⟨le_trans (by linarith [Real.pi_pos] : -(Real.pi / 2) ≤ 0) hθ.1, hθ.2⟩
          ⟨le_trans (by linarith [Real.pi_pos] : -(Real.pi / 2) ≤ 0) hθm.1, hθm.2⟩ hθle
      exact mul_le_mul_of_nonneg_left hsinle hR.le
  · intro hx
    rw [Set.mem_Icc, ← abs_le] at hx
    simp only [absorbedImpactSet, Set.mem_union, Set.mem_setOf_eq]
    right
    have hy0 : (0:ℝ) ≤ |x| / R := div_nonneg (abs_nonneg x) hR.le
    have hy1 : |x| / R ≤ Real.sin θmax := by
      rw [div_le_iff₀ hR, mul_comm]
      exact hx
    obtain ⟨θ, hθI, hsinθ⟩ := sin_surj_upto hθm ⟨hy0, hy1⟩
    have hθmem : θ ∈ Set.Icc 0 (Real.pi / 2) := ⟨hθI.1, le_trans hθI.2 hθm.2⟩
    refine ⟨θ, hθmem, (strikes_iff_le_max R a θmax hR ha hclear hmax hθmem).mpr hθI.2, ?_⟩
    rw [hsinθ]
    field_simp

/-- The total width of the absorbed impact set is `2 R sin θ_max`.
Proof route: `absorbedImpactSet_eq_Icc`, then `Real.volume_Icc`
(`volume (Icc u v) = ENNReal.ofReal (v − u)`) and
`R sin θ_max − (−R sin θ_max) = 2 R sin θ_max` by ring. -/
theorem volume_absorbedImpactSet (R a θmax : ℝ) (hR : 0 < R) (ha : 0 < a)
    (hclear : ContainerClearOfMirror R a) (hsingle : SingleReflectionRegime R a)
    (hmax : IsMaxIncidenceAngle R a θmax) :
    MeasureTheory.volume (absorbedImpactSet R a)
      = ENNReal.ofReal (2 * R * Real.sin θmax) := by
  rw [absorbedImpactSet_eq_Icc R a θmax hR ha hclear hsingle hmax, Real.volume_Icc]
  congr 1
  ring

/-! ## Bridge lemmas: the power ratio (T2-B2 route) -/

/-- **Received power in closed form**: per unit length, `P = 2·R·sin θ_max·I`
(intensity times the width `2 R sin θ_max` of the absorbed impact set).
Proof route: unfold `powerWithMirrorPerLength`, rewrite with
`volume_absorbedImpactSet`, apply `ENNReal.toReal_ofReal`
(`0 ≤ 2 R sin θ_max` since `sin θ_max ≥ 0` on `[0, π/2]`), and ring. -/
theorem powerWithMirror_eq (I R a θmax : ℝ) (hR : 0 < R) (ha : 0 < a)
    (hclear : ContainerClearOfMirror R a) (hsingle : SingleReflectionRegime R a)
    (hmax : IsMaxIncidenceAngle R a θmax) :
    powerWithMirrorPerLength I R a = 2 * R * Real.sin θmax * I := by
  have hsinm : 0 ≤ Real.sin θmax :=
    Real.sin_nonneg_of_mem_Icc ⟨hmax.1.1, le_trans hmax.1.2 (by linarith [Real.pi_pos])⟩
  have hnonneg : (0:ℝ) ≤ 2 * R * Real.sin θmax :=
    mul_nonneg (mul_nonneg (by norm_num) hR.le) hsinm
  rw [powerWithMirrorPerLength, volume_absorbedImpactSet R a θmax hR ha hclear hsingle hmax,
    ENNReal.toReal_ofReal hnonneg]
  ring

/-- **The ratio before eliminating `a`**: `P / P₀ = R·sin θ_max / a`.
Proof route: `powerWithMirror_eq` and the definition
`powerWithoutMirrorPerLength I a = 2 a I`; cancel `2 I ≠ 0` (`0 < I`) by
`field_simp`/`mul_div_mul_right`. -/
theorem power_ratio_eq_sin (I R a θmax : ℝ) (hI : 0 < I) (hR : 0 < R) (ha : 0 < a)
    (hclear : ContainerClearOfMirror R a) (hsingle : SingleReflectionRegime R a)
    (hmax : IsMaxIncidenceAngle R a θmax) :
    powerWithMirrorPerLength I R a / powerWithoutMirrorPerLength I a
      = R * Real.sin θmax / a := by
  have hI' : I ≠ 0 := hI.ne'
  have ha' : a ≠ 0 := ha.ne'
  rw [powerWithMirror_eq I R a θmax hR ha hclear hsingle hmax, powerWithoutMirrorPerLength]
  field_simp

/-- **T2-B2 previous-part result** (derived inline from problem-only material,
per the `derive_inline_from_problem_only_material` policy — same statement as
`IPhO2026.T2B2.power_ratio`): under the problem's assumptions,

```
P / P₀ = 1 / (1 − cos θ_max).
```

Proof route: `power_ratio_eq_sin` gives `P/P₀ = R sin θ_max / a`; the T2-B1
relation in factored form (`container_radius_eq_factored`) gives
`a = R sin θ_max (1 − cos θ_max)` with `R sin θ_max ≠ 0` (`thetaMax_pos`,
`sin_pos_of_theta_range`) and `1 − cos θ_max ≠ 0`
(`one_sub_cos_pos_of_theta_range`); cancel by `field_simp`. -/
theorem power_ratio (I R a θmax : ℝ) (hI : 0 < I) (hR : 0 < R) (ha : 0 < a)
    (hclear : ContainerClearOfMirror R a) (hsingle : SingleReflectionRegime R a)
    (hmax : IsMaxIncidenceAngle R a θmax) :
    powerWithMirrorPerLength I R a / powerWithoutMirrorPerLength I a
      = 1 / (1 - Real.cos θmax) := by
  have hθpos := thetaMax_pos R a θmax hR ha hclear hmax
  have hsinpos : 0 < Real.sin θmax := sin_pos_of_theta_range ⟨hθpos, hmax.1.2⟩
  have hcospos : 0 < 1 - Real.cos θmax := one_sub_cos_pos_of_theta_range ⟨hθpos, hmax.1.2⟩
  have hfact := container_radius_eq_factored R a θmax hR ha hclear hsingle hmax
  have h1 : R * Real.sin θmax ≠ 0 := mul_ne_zero hR.ne' hsinpos.ne'
  have h2 : 1 - Real.cos θmax ≠ 0 := hcospos.ne'
  rw [power_ratio_eq_sin I R a θmax hI hR ha hclear hsingle hmax, hfact]
  rw [div_eq_div_iff (mul_ne_zero h1 h2) h2]
  ring

/-! ## T2-B3: imposing the power condition `P = 5 P₀` -/

/-- The bare-cylinder power is positive: `P₀/L = 2 a I > 0` for `0 < a`,
`0 < I`.  Needed to turn `P = 5 P₀` into the ratio equation `P/P₀ = 5`.
Proof route: unfold `powerWithoutMirrorPerLength`; `positivity`. -/
theorem powerWithoutMirrorPerLength_pos (I a : ℝ) (hI : 0 < I) (ha : 0 < a) :
    0 < powerWithoutMirrorPerLength I a := by
  unfold powerWithoutMirrorPerLength
  positivity

/-- **Cosine of the required maximum angle**: imposing `P = 5 P₀` on the T2-B2
ratio forces `cos θ_max = 4/5`.
Proof route: `power_ratio` gives `P/P₀ = 1/(1 − cos θ_max)`; from `hP` and
`powerWithoutMirrorPerLength_pos` (`P₀ ≠ 0`) the same ratio equals `5`; hence
`1/(1 − cos θ_max) = 5`.  Since `0 < θ_max ≤ π/2` (`thetaMax_pos`, `hmax.1`)
gives `1 − cos θ_max > 0` (`one_sub_cos_pos_of_theta_range`), `field_simp`
yields `1 − cos θ_max = 1/5`, i.e. `cos θ_max = 4/5`. -/
theorem cos_thetaMax_of_power_five (I R a θmax : ℝ) (hI : 0 < I) (hR : 0 < R)
    (ha : 0 < a) (hclear : ContainerClearOfMirror R a)
    (hsingle : SingleReflectionRegime R a) (hmax : IsMaxIncidenceAngle R a θmax)
    (hP : powerWithMirrorPerLength I R a = 5 * powerWithoutMirrorPerLength I a) :
    Real.cos θmax = 4 / 5 := by
  have hratio := power_ratio I R a θmax hI hR ha hclear hsingle hmax
  have hP0ne : powerWithoutMirrorPerLength I a ≠ 0 :=
    (powerWithoutMirrorPerLength_pos I a hI ha).ne'
  have hratio5 : powerWithMirrorPerLength I R a / powerWithoutMirrorPerLength I a = 5 := by
    rw [hP]
    field_simp
  have hθpos := thetaMax_pos R a θmax hR ha hclear hmax
  have hcosne : 1 - Real.cos θmax ≠ 0 :=
    (one_sub_cos_pos_of_theta_range ⟨hθpos, hmax.1.2⟩).ne'
  rw [hratio] at hratio5
  field_simp at hratio5
  linarith

/-- **Sine of the required maximum angle** (positive branch selected by
`0 < θ_max ≤ π/2`, not by the answer): `sin θ_max = 3/5`.
Proof route: `Real.sin_sq_add_cos_sq θmax` and `cos_thetaMax_of_power_five`
give `sin² θ_max = 1 − (4/5)² = 9/25 = (3/5)²`; `sin_pos_of_theta_range`
(with `thetaMax_pos` and `hmax.1`) gives `0 < sin θ_max`, so the positive root
is forced: `sin θ_max = 3/5` (`sq_eq_sq'` / `abs` case split). -/
theorem sin_thetaMax_of_power_five (I R a θmax : ℝ) (hI : 0 < I) (hR : 0 < R)
    (ha : 0 < a) (hclear : ContainerClearOfMirror R a)
    (hsingle : SingleReflectionRegime R a) (hmax : IsMaxIncidenceAngle R a θmax)
    (hP : powerWithMirrorPerLength I R a = 5 * powerWithoutMirrorPerLength I a) :
    Real.sin θmax = 3 / 5 := by
  have hcos := cos_thetaMax_of_power_five I R a θmax hI hR ha hclear hsingle hmax hP
  have hθpos := thetaMax_pos R a θmax hR ha hclear hmax
  have hsinpos : 0 < Real.sin θmax := sin_pos_of_theta_range ⟨hθpos, hmax.1.2⟩
  have hsq : Real.sin θmax ^ 2 = (3 / 5 : ℝ) ^ 2 := by
    have h := Real.sin_sq_add_cos_sq θmax
    rw [hcos] at h
    have h2 : Real.sin θmax ^ 2 = 1 - (4 / 5 : ℝ) ^ 2 := by linarith
    rw [h2]
    norm_num
  exact (sq_eq_sq₀ hsinpos.le (by norm_num)).mp hsq

/-- **Double angle at the required maximum angle**: `sin (2 θ_max) = 24/25`.
Proof route: `Real.sin_two_mul` with `sin_thetaMax_of_power_five` and
`cos_thetaMax_of_power_five`: `2 · (3/5) · (4/5) = 24/25`. -/
theorem sin_two_thetaMax_of_power_five (I R a θmax : ℝ) (hI : 0 < I) (hR : 0 < R)
    (ha : 0 < a) (hclear : ContainerClearOfMirror R a)
    (hsingle : SingleReflectionRegime R a) (hmax : IsMaxIncidenceAngle R a θmax)
    (hP : powerWithMirrorPerLength I R a = 5 * powerWithoutMirrorPerLength I a) :
    Real.sin (2 * θmax) = 24 / 25 := by
  rw [Real.sin_two_mul,
    sin_thetaMax_of_power_five I R a θmax hI hR ha hclear hsingle hmax hP,
    cos_thetaMax_of_power_five I R a θmax hI hR ha hclear hsingle hmax hP]
  norm_num

/-- **Uniqueness of the required angle**: on `[0, π/2]` the cosine determines
the angle, so at most one `θ_max` (and hence, via `container_radius_eq_factored`,
at most one `a`) satisfies the power condition — "the value of `a`" asked for by
T2-B3 is well-defined.  Proof route: `Real.strictAntiOn_cos` is strictly
antitone on `[0, π] ⊇ [0, π/2]`; apply `StrictAntiOn.injOn` (`Set.InjOn`). -/
theorem thetaMax_unique_of_cos_eq {θ θ' : ℝ}
    (hθ : θ ∈ Set.Icc 0 (Real.pi / 2)) (hθ' : θ' ∈ Set.Icc 0 (Real.pi / 2))
    (h : Real.cos θ = Real.cos θ') : θ = θ' := by
  have hpi : Real.pi / 2 ≤ Real.pi := by linarith [Real.pi_pos]
  exact Real.strictAntiOn_cos.injOn ⟨hθ.1, le_trans hθ.2 hpi⟩ ⟨hθ'.1, le_trans hθ'.2 hpi⟩ h

/-- **The container radius for `P = 5 P₀`** (raw end-to-end quantity, metres):
under the problem's regime hypotheses and the power condition,

```
a = R·sin θ_max·(1 − cos θ_max) = R·(3/5)·(1/5) = 3R/25.
```

Proof route: `container_radius_eq_factored` (the T2-B1 relation) at the
required angle, substituting `cos_thetaMax_of_power_five` and
`sin_thetaMax_of_power_five`; ring-normalize.  (Equivalently: substitute
`sin_two_thetaMax_of_power_five` into `container_radius_eq`,
`a = R·(3/5) − (R/2)·(24/25) = 3R/25`.) -/
theorem container_radius_of_power_five (I R a θmax : ℝ) (hI : 0 < I) (hR : 0 < R)
    (ha : 0 < a) (hclear : ContainerClearOfMirror R a)
    (hsingle : SingleReflectionRegime R a) (hmax : IsMaxIncidenceAngle R a θmax)
    (hP : powerWithMirrorPerLength I R a = 5 * powerWithoutMirrorPerLength I a) :
    a = 3 * R / 25 := by
  have hfact := container_radius_eq_factored R a θmax hR ha hclear hsingle hmax
  have hcos := cos_thetaMax_of_power_five I R a θmax hI hR ha hclear hsingle hmax hP
  have hsin := sin_thetaMax_of_power_five I R a θmax hI hR ha hclear hsingle hmax hP
  rw [hfact, hsin, hcos]
  ring

/-- Feasibility of the derived radius: `3R/25` lies in the admissible range
`0 < a < R/2` of the model (cf. `container_radius_lt_half`), so the candidate
is realizable inside the bowl in the single-reflection regime.  Pure algebra:
`0 < 3R/25` and `3R/25 < R/2` both follow from `0 < R` by `linarith`. -/
theorem candidate_radius_mem_range (R : ℝ) (hR : 0 < R) :
    0 < 3 * R / 25 ∧ 3 * R / 25 < R / 2 := by
  exact ⟨by linarith, by linarith⟩

/-! ## Unit conversion and the main target -/

/-- **Source-derived reporting rule**: T2-B3 fixes `R = 1.0 m`, so all lengths
in the model are measured in metres, and asks for the answer in centimetres;
`mToCm l = 100 · l` is the exact SI conversion of the raw metre value to
centimetres.  (The derived value is exactly `12`, so no numerical rounding
beyond this unit conversion is applied.) -/
noncomputable def mToCm (l : ℝ) : ℝ := 100 * l

/-- **T2-B3 main target** (blueprint `thm:physics:ipho_2026_t2_b3:target`).
With the mirror radius fixed at `R = 1.0 m` (`hR1 : R = 1`, lengths measured in
metres) and under the problem's regime hypotheses — positive uniform intensity
`0 < I`, positive container radius `0 < a`, the container strictly inside the
bowl (`ContainerClearOfMirror`, Fig. 2f), the single-reflection regime
(`SingleReflectionRegime`, the problem's "at most once" assumption), `θ_max`
the problem's maximum incidence angle (`IsMaxIncidenceAngle`) — any
configuration meeting the power condition `P = 5 P₀` has container radius

```
a = 3/25 m,   i.e. exactly 12 cm   (mToCm a = 12).
```

Proof route: `container_radius_of_power_five` gives `a = 3R/25`; with
`hR1 : R = 1`, `mToCm a = 100 · (3/25) = 12` by `mToCm` and `norm_num`.  The
answer value `12` appears only here, on the conclusion side. -/
theorem t2_b3_container_radius_cm (I R a θmax : ℝ) (hI : 0 < I) (hR : 0 < R)
    (ha : 0 < a) (hclear : ContainerClearOfMirror R a)
    (hsingle : SingleReflectionRegime R a) (hmax : IsMaxIncidenceAngle R a θmax)
    (hR1 : R = 1)
    (hP : powerWithMirrorPerLength I R a = 5 * powerWithoutMirrorPerLength I a) :
    mToCm a = 12 := by
  have ha' := container_radius_of_power_five I R a θmax hI hR ha hclear hsingle hmax hP
  rw [hR1] at ha'
  rw [mToCm, ha']
  norm_num

end IPhO2026.T2B3
