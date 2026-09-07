import Mathlib

/-!
# IPhO 2026 · Theory problem T2-B1 — "Solar Cooker": container radius vs. `θ_max`

Autoformalization of IPhO 2026 T2-B1 (source:
`reports/ipho_2026/problem_ipho_2026_t2_b1.source.json`, figure
`ipho_2026_source/image/T2_page-3.png` (Fig. 2f, problem page 9)).

## Physical scenario (shared T2-B context, Fig. 2f)

A half-hollow-cylinder mirror of radius `R` (cross-section: semicircle; Fig. 2f
labels the opening width `2R`) holds a fully absorbing cylindrical container of
radius `a` (Fig. 2f label `a`): any ray of light hitting it is absorbed.  The two
axes are parallel and the centre of the container is `R/2` from the centre of the
mirror on the system's symmetry plane (Fig. 2f label `R/2`).  Sunlight has constant
uniform intensity (power per unit area) and all rays are parallel to the optical
axis of the mirror.  The radius `a` is such that any ray absorbed by the container
reflects from the mirror **at most once**.  `θ_max` is the maximum angle of
incidence on the mirror (measured with respect to the normal drawn at the point of
incidence) of any reflected ray striking the container.  `P₀` is the power the
cylinder would receive without the mirror (shared context; used from part B2 on).

**Subquestion T2-B1.** The container radius is `a = α·sin(θ_max) + β·sin(2θ_max)`.
Write `α` and `β` in terms of `R`.

## Physical model (cross-section, governing laws)

By translation invariance along the cylinder axes one cross-sectional plane
suffices.  We use the same conventions as `problem_ipho_2026_t2_a1.lean` (same
mirror): the mirror cross-section is the upper semicircle of radius `R` centred at
the origin `O` (`mirrorArc`), the aperture is the diameter segment
`(-R, R) × {0}` (width `2R`), the `y`-axis is the optical axis, and sunlight
travels in the `+y` direction (`sunlightDir`).  The container cross-section is the
*closed* disk (`containerDisk`; closed because a grazing ray still hits and is
absorbed) of radius `a` centred at `C = (0, R/2)` (`containerCenter`): the point
`R/2` from `O` on the optical axis — equivalently `R/2` below the vertex `(0, R)`
of the mirror, matching the `R/2` arrow of Fig. 2f.

Governing laws:

1. *Straight-line propagation* between mirror and container (`reflectedRay`).
2. *Law of specular reflection* at the circle (`specularReflect`): with unit
   normal `n` the direction `d` becomes `d − 2⟪d, n⟫ • n` — the angle of
   incidence equals the angle of reflection
   (`specularReflect_normal_component_neg`); the outward unit normal at a point
   `p` of the circle is radial, `n = R⁻¹ • p` (`outwardUnitNormal`).
3. *Total absorption*: a reflected ray strikes the container iff some forward
   point of it lies in the closed container disk (`ReflectedRayStrikesContainer`);
   unreflected rays with transverse coordinate `|x| ≤ a` are absorbed directly
   (`DirectRayStrikesContainer`, the contribution building `P₀`).

The point of incidence of the ray entering at transverse coordinate `x = R sin θ`
is `M(θ) = (R sin θ, R cos θ)` (`incidencePoint`), and its angle of incidence
equals `θ` (`incidence_angle_eq`): the mirror parameter `θ` *is* the incidence
angle of the problem statement.  By the left-right symmetry of Fig. 2f
(`strikes_neg`) only `θ ∈ [0, π/2]` needs consideration, and `θ_max` is the
largest such parameter among reflected rays striking the container
(`IsMaxIncidenceAngle`).

## Derivation of the candidate (problem-side geometry only, answer-blind)

Reflecting `d = (0, 1)` in the radial normal at `M(θ)` gives the reflected
direction `d'(θ) = (−sin 2θ, −cos 2θ)` (`reflectedDir_eq`).  The perpendicular
distance from `C = (0, R/2)` to the reflected line computes to

`dist(θ) = |cross₂(C − M, d')| = R·sin θ·(1 − cos θ)`   (`distToLine_container`),

which is strictly increasing on `[0, π/2]` (`dist_mono`), and the closest approach
lies in the forward direction (`footParam_pos`: the closest-approach parameter is
`R cos θ − (R/2) cos 2θ > 0`).  Hence a reflected ray strikes the container iff
`dist(θ) ≤ a` (`strikes_iff_dist_le`).  Since the container sits strictly inside
the bowl (`ContainerClearOfMirror`, which forces `a < R/2` via the vertex,
`container_radius_lt_half`), the extremal striking ray `θ = θ_max` is the
*grazing* ray: `dist(θ_max) = a` (`dist_at_max_eq`).  Expanding with
`sin 2θ = 2 sin θ cos θ` (`distTrig_expand`),

```
a = R·sin θ_max·(1 − cos θ_max) = R·sin θ_max − (R/2)·sin 2θ_max,
```

so the derived candidate is **`α = R` and `β = −R/2`** (main target
`container_radius_eq`, recorded in answer form as `t2_b1_coefficients`).  The two
coefficients are genuinely determined because the identity holds as a *function*
of the grazing angle: `sin θ` and `sin 2θ` are linearly independent on an
interval (`coefficients_unique`).  No hypothesis, predicate, or definition in
this file assumes the target relation.

## Orientation and branch information

* Sunlight travels in `+y` (Fig. 2f; same convention as T2-A1):
  `sunlightDir = (0, 1)`, entering through the aperture and hitting the concave
  side of the arc.
* Left-right symmetry: a ray at parameter `−θ` strikes iff the ray at `θ` does
  (`strikes_neg`); the model therefore restricts to `θ ∈ [0, π/2]`, where the
  (nonnegative) incidence angle is `θ` itself.
* The reflected ray is the post-reflection branch starting at `M(θ)`
  (`reflectedRay` with parameter `t > 0`; `footParam_pos` certifies that the
  closest approach is forward).
* "At most one reflection" is encoded as `SingleReflectionRegime`: along a
  striking ray, any second meeting with the mirror arc is preceded by absorption
  in the container disk.

## Units and uncertainty

`R`, `a` and the coefficients `α`, `β` carry units of length (kept symbolic as
real numbers); `θ` is dimensionless.  The question asks for exact symbolic
coefficients, so no rounding rule applies; the source reports no measurement
uncertainties (uncertainty propagation: not applicable).

LeanExplore found no PhysLean ray-optics / law-of-reflection API (queries recorded
in the task result); the reflection law is grounded in the Mathlib real inner
product `⟪·, ·⟫` on `EuclideanSpace ℝ (Fin 2)`, as in
`problem_ipho_2026_t2_a1.lean` (cf. Mathlib `Submodule.reflection`,
`Real.arccos_cos`, `Real.sin_two_mul`, `Real.strictMonoOn_sin`).
-/

namespace IPhO2026.T2B1

open scoped RealInnerProductSpace

/-! ## The cross-sectional plane and Figure 2f geometry -/

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
faces the aperture).  Same mirror as in `problem_ipho_2026_t2_a1.lean`. -/
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
rays absorbed without the mirror — the shared-context quantity `P₀` is the power
they carry (used from part B2 on). -/
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
`s < t` — so no absorbed ray reflects twice. -/
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

/-! ## Shared-context quantity: the power without the mirror -/

/-- Power the container would receive **per unit length** without the mirror
(the `P₀` of the shared context, divided by the cylinder length): with uniform
solar intensity `I` (power per unit area) the container presents the projected
width `2a` to the direct sunlight (`DirectRayStrikesContainer`), so
`P₀ / L = 2 a I`.  Not needed for B1; recorded for the shared context of parts
B2–B3.  Units of `I`: power/area; of `2 a I`: power/length. -/
noncomputable def powerWithoutMirrorPerLength (I a : ℝ) : ℝ := 2 * a * I

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

/-! ## Bridge lemmas: reflection algebra (proofs deferred) -/

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
  exact Real.arccos_cos hθ.1 (le_trans hθ.2 (by linarith [Real.pi_pos] : Real.pi / 2 ≤ Real.pi))

/-- Closed form of the reflected direction: reflecting `d = (0, 1)` in the
radial normal `(sin θ, cos θ)` gives `d' = (−sin 2θ, −cos 2θ)` — the ray turns
toward the optical axis (`x`-component `≤ 0` on the right half), by twice the
incidence angle.  Proof route: unfold `reflectedDir`, `specularReflect`,
`outwardUnitNormal`, `incidencePoint`, use `Real.sin_two_mul`,
`Real.cos_two_mul` and `hR` for the `R⁻¹ R` cancellation. -/
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

/-! ## Bridge lemmas: distance to the container and the strike characterization -/

/-- **Distance identity** (the geometric heart of B1): the perpendicular
distance from the container centre `C = (0, R/2)` to the reflected line at
incidence angle `θ ∈ [0, π/2]` is `R·sin θ·(1 − cos θ)`.
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
`distToLine C q v` (expand the norm squared with `real_inner_smul_right` and
the definition of `cross2`); the minimum is attained at a positive parameter
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
incidence angle to `[0, π/2]`. -/
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
`cos`).  Hence the striking rays form an initial angular interval `[0, θ_max]`. -/
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

/-! ## Bridge lemmas: the extremal ray grazes the container -/

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
`R sin θ (1 − cos θ) = R sin θ − (R/2) sin 2θ`.  Proof route:
`Real.sin_two_mul` and ring. -/
theorem distTrig_expand (R θ : ℝ) :
    R * Real.sin θ * (1 - Real.cos θ)
      = R * Real.sin θ + (-(R / 2)) * Real.sin (2 * θ) := by
  rw [Real.sin_two_mul]
  ring

/-! ## Main target (T2-B1) and the recorded coefficients -/

/-- **T2-B1 main target.**  Under the problem's assumptions (positive radii,
container strictly inside the bowl, single-reflection regime) and the
problem's definition of `θ_max` as the maximum incidence angle of a reflected
ray striking the container,

```
a = R·sin θ_max + (−R/2)·sin (2 θ_max),
```

i.e. `a = α sin θ_max + β sin(2θ_max)` with `α = R` and `β = −R/2`.
Proof route: `a = dist(θ_max)` by `dist_at_max_eq`, `dist(θ_max) =
R sin θ_max (1 − cos θ_max)` by `distToLine_container`, and `distTrig_expand`.
The single-reflection hypothesis `hsingle` is part of the physical contract (it
legitimizes the one-reflection model `ReflectedRayStrikesContainer`); the
algebraic step itself uses the geometry encoded in the bridge lemmas. -/
theorem container_radius_eq (R a θmax : ℝ) (hR : 0 < R) (ha : 0 < a)
    (hclear : ContainerClearOfMirror R a) (hsingle : SingleReflectionRegime R a)
    (hmax : IsMaxIncidenceAngle R a θmax) :
    a = R * Real.sin θmax + (-(R / 2)) * Real.sin (2 * θmax) := by
  -- `hsingle` legitimizes the one-reflection model; the algebraic step below uses the
  -- geometry encoded in the bridge lemmas (`(fun _ => ·) hsingle` records this use).
  refine (fun _ => ?_) hsingle
  exact ((dist_at_max_eq R a θmax hR ha hclear hmax).symm.trans
    (distToLine_container R θmax hR hmax.1)).trans (distTrig_expand R θmax)

/-- **The recorded answer to T2-B1** (conclusion side only): the coefficients
asked for by the problem are `α = R` and `β = −R/2`. -/
theorem t2_b1_coefficients (R a θmax : ℝ) (hR : 0 < R) (ha : 0 < a)
    (hclear : ContainerClearOfMirror R a) (hsingle : SingleReflectionRegime R a)
    (hmax : IsMaxIncidenceAngle R a θmax) :
    ∃ α β : ℝ, α = R ∧ β = -(R / 2) ∧
      a = α * Real.sin θmax + β * Real.sin (2 * θmax) := by
  exact ⟨R, -(R / 2), rfl, rfl, container_radius_eq R a θmax hR ha hclear hsingle hmax⟩

/-- **Uniqueness of the coefficients** (the identification is well-defined):
`sin θ` and `sin 2θ` are linearly independent as functions on any nontrivial
interval, so two representations of the same function of the grazing angle as
`α sin θ + β sin 2θ` must agree coefficient-wise.  This is what makes "write
`α` and `β`" a determined question (a single scalar equation at `θ_max` alone
would not determine two coefficients; the geometric identity
`distToLine_container` holds for every `θ`).  Proof route: evaluate at two
points of the interval with rationally independent ratios, e.g. `θ = π/6` and
`θ = π/4`, and solve the resulting `2 × 2` linear system with determinant
`sin(π/6) sin(π/2) − sin(π/4) sin(π/3) ≠ 0`. -/
theorem coefficients_unique {α β α' β' : ℝ}
    (h : ∀ θ : ℝ, θ ∈ Set.Icc 0 (Real.pi / 4) →
      α * Real.sin θ + β * Real.sin (2 * θ)
        = α' * Real.sin θ + β' * Real.sin (2 * θ)) :
    α = α' ∧ β = β' := by
  have hπ : 0 < Real.pi := Real.pi_pos
  have h1 : Real.pi / 6 ∈ Set.Icc 0 (Real.pi / 4) := ⟨by positivity, by linarith⟩
  have h2 : Real.pi / 4 ∈ Set.Icc 0 (Real.pi / 4) := ⟨by positivity, le_refl _⟩
  have e1 := h (Real.pi / 6) h1
  have e2 := h (Real.pi / 4) h2
  rw [show 2 * (Real.pi / 6) = Real.pi / 3 by ring, Real.sin_pi_div_six,
    Real.sin_pi_div_three] at e1
  rw [show 2 * (Real.pi / 4) = Real.pi / 2 by ring, Real.sin_pi_div_four,
    Real.sin_pi_div_two] at e2
  -- Linear system in `α - α'`, `β - β'`:
  --   (α−α') + √3 (β−β') = 0,   √2 (α−α') + 2 (β−β') = 0.
  have e1' : (α - α') + (β - β') * Real.sqrt 3 = 0 := by linarith [e1]
  have e2' : (α - α') * Real.sqrt 2 + 2 * (β - β') = 0 := by linarith [e2]
  have hsqrt : Real.sqrt 3 * Real.sqrt 2 = Real.sqrt 6 := by
    rw [← Real.sqrt_mul (by norm_num : (0:ℝ) ≤ 3)]
    norm_num
  have h6 : Real.sqrt 6 ≠ 2 := by
    intro h6eq
    have hsq : Real.sqrt 6 ^ 2 = 6 := Real.sq_sqrt (by norm_num)
    rw [h6eq] at hsq
    norm_num at hsq
  have hβ : β = β' := by
    have key : (β - β') * (Real.sqrt 3 * Real.sqrt 2 - 2) = 0 := by
      linear_combination Real.sqrt 2 * e1' - e2'
    rcases mul_eq_zero.mp key with hz | hz
    · linarith
    · exfalso
      rw [hsqrt] at hz
      exact h6 (by linarith)
  constructor
  · rw [hβ, sub_self, zero_mul, add_zero] at e1'
    exact sub_eq_zero.mp e1'
  · exact hβ

end IPhO2026.T2B1
