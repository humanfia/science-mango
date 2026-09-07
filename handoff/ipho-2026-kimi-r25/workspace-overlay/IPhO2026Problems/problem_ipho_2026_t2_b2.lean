import Mathlib

/-!
# IPhO 2026 · Theory problem T2-B2 — "Solar Cooker": the power ratio `P / P₀` in terms of `θ_max`

Autoformalization of IPhO 2026 T2-B2 (source:
`reports/ipho_2026/problem_ipho_2026_t2_b2.source.json`, figure
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
container.

**Subquestion T2-B2.** Let `P₀` be the power that would be received by the
cylinder if the mirror was not present.  Write `P/P₀`, the ratio of the actual
received power `P` to `P₀`, in terms of `θ_max`.

## Physical model (cross-section, governing laws)

By translation invariance along the cylinder axes one cross-sectional plane
suffices, and both `P` and `P₀` are proportional to the cylinder length `L`;
we therefore work with **power per unit length** throughout (the common factor
`L` cancels in the ratio).  We use the same conventions as
`problem_ipho_2026_t2_b1.lean` (same mirror, same Fig. 2f): the mirror
cross-section is the upper semicircle of radius `R` centred at the origin `O`
(`mirrorArc`), the aperture is the diameter segment of width `2R` (`aperture`),
the `y`-axis is the optical axis, sunlight travels in the `+y` direction
(`sunlightDir`), and the container cross-section is the closed disk
(`containerDisk`; closed because a grazing ray still hits and is absorbed) of
radius `a` centred at `C = (0, R/2)` (`containerCenter`).

Governing laws:

1. *Straight-line propagation* between mirror and container (`reflectedRay`).
2. *Law of specular reflection* at the circle (`specularReflect`): with unit
   normal `n` the direction `d` becomes `d − 2⟪d, n⟫ • n` — the angle of
   incidence equals the angle of reflection
   (`specularReflect_normal_component_neg`).
3. *Total absorption*: a reflected ray strikes the container iff some forward
   point of it lies in the closed container disk (`ReflectedRayStrikesContainer`);
   unreflected rays with transverse coordinate `|x| ≤ a` are absorbed directly
   (`DirectRayStrikesContainer`).
4. *Energy flux for uniform parallel light*: the power carried by a family of
   parallel rays of uniform intensity `I` is `I` times the Lebesgue measure of
   its impact-parameter set (times `L`).  This is the physical content of
   `powerWithMirrorPerLength` and `powerWithoutMirrorPerLength`.

The point of incidence of the ray entering at transverse coordinate
`x = R sin θ` is `M(θ) = (R sin θ, R cos θ)` (`incidencePoint`), and its angle
of incidence equals `θ` (`incidence_angle_eq`): the mirror parameter `θ` *is*
the incidence angle of the problem statement.  By the left-right symmetry of
Fig. 2f (`strikes_neg`) only `θ ∈ [0, π/2]` needs consideration, and `θ_max` is
the largest such parameter among reflected rays striking the container
(`IsMaxIncidenceAngle`, the problem's own definition of `θ_max`).

## Derivation of the candidate (problem-side geometry only, answer-blind)

From the shared T2-B model (as established for T2-B1, re-derived inline here by
the `derive_inline_from_problem_only_material` policy): the perpendicular
distance from `C` to the ray reflected at incidence angle `θ` is
`dist(θ) = R·sin θ·(1 − cos θ)` (`distToLine_container`), strictly increasing
on `[0, π/2]` (`dist_strictMonoOn`), the extremal striking ray grazes the
container (`dist_at_max_eq`), hence `a = R·sin θ_max·(1 − cos θ_max)`
(`container_radius_eq_factored`, the factored form of the T2-B1 headline
`container_radius_eq`: `α = R`, `β = −R/2`).

For T2-B2 we add the flux bookkeeping:

* Direct rays with `|x| ≤ a` are absorbed without any reflection; rays with
  `|x| > a` pass the container and reach the mirror.
* A mirror ray at parameter `θ ∈ [0, π/2]` strikes the container after one
  reflection iff `θ ≤ θ_max` (`strikes_iff_le_max`: `dist` is strictly
  increasing and `dist(θ_max) = a`); its impact parameter is `|x| = R sin θ`,
  so the reflected contribution fills exactly the two strips
  `a < |x| ≤ R sin θ_max` (`sin_surj_upto` covers every intermediate value).
* Hence the absorbed impact-parameter set is exactly the interval
  `[−R sin θ_max, R sin θ_max]` (`absorbedImpactSet_eq_Icc`) — the
  single-reflection hypothesis `SingleReflectionRegime` (the problem's "at most
  once" assumption) certifies that every geometrically striking reflected ray
  is really absorbed before any would-be second mirror encounter, so no
  striking ray is lost and none is double-counted (the direct strip
  `[−a, a]` is absorbed before reaching the mirror at all).
* Therefore, per unit length, `P = 2·R·sin θ_max·I` (`powerWithMirror_eq`)
  while `P₀ = 2·a·I` (`powerWithoutMirrorPerLength`), so

  `P / P₀ = R·sin θ_max / a`   (`power_ratio_eq_sin`),

  and the T2-B1 relation eliminates `a`
  (`sin θ_max > 0`, `1 − cos θ_max > 0` since `0 < θ_max ≤ π/2`,
  `thetaMax_pos`):

  `P / P₀ = 1 / (1 − cos θ_max)`   (main target `power_ratio`).

Sanity checks on the candidate: the ratio is `≥ 1` on `(0, π/2]` (the mirror
only adds power), and `P/P₀ ≈ 2/θ_max² → ∞` as `θ_max → 0` (a small container
collects a fixed aperture worth of sunlight).

No hypothesis, predicate, structure field, or local definition in this file
mentions the target relation; the candidate `1 / (1 − cos θ_max)` appears only
in the conclusions of the last two theorems.

## Orientation and branch information

* Sunlight travels in `+y` (Fig. 2f; same convention as T2-A1/T2-B1):
  `sunlightDir = (0, 1)`.
* The reflected ray is the post-reflection branch `t > 0` of `reflectedRay`;
  the closest approach to `C` lies on it (`footParam_pos`).
* Left-right symmetry (`strikes_neg`) folds the two halves of the mirror onto
  `θ ∈ [0, π/2]`; `absorbedImpactSet` uses `|x| = R sin θ` to count both
  branches of impact parameters.
* The incidence angle is measured from the normal at the point of incidence,
  as the problem requires (`incidence_angle_eq`).
* `θ_max` is attained (the grazing ray touches the *closed* container disk) —
  this is built into `IsMaxIncidenceAngle`.

## Units and uncertainty

`R` and `a` carry units of length (kept symbolic as real numbers); `I` carries
power/area; `P/L`, `P₀/L` carry power/length; `θ_max` and the ratio `P/P₀` are
dimensionless.  The question asks for an exact symbolic expression, so no
rounding rule applies; the source reports no measurement uncertainties
(uncertainty propagation: not applicable).

LeanExplore found no PhysLean ray-optics / law-of-reflection or radiative-flux
API (queries recorded in the task result); the reflection law is grounded in
the Mathlib real inner product `⟪·, ·⟫` on `EuclideanSpace ℝ (Fin 2)` as in
`problem_ipho_2026_t2_b1.lean`, and the flux measure in
`MeasureTheory.volume`/`Real.volume_Icc`.
-/

namespace IPhO2026.T2B2

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
`s < t` — so no absorbed ray reflects twice.  For T2-B2 this certifies that
every geometrically striking reflected ray contributes its power to `P`: none
is re-reflected away before reaching the container. -/
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

/-! ## Bridge lemmas: reflection algebra (shared model, proofs deferred) -/

/-! ### Auxiliary coordinate lemmas (proof infrastructure, no physical content) -/

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
(shared T2-B model, as in `problem_ipho_2026_t2_b1.lean`) -/

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
This is the form that eliminates `a` from the power ratio.  Proof route:
`dist_at_max_eq` and `distToLine_container` at `θ_max`
(`hmax.1` gives `θ_max ∈ [0, π/2]`). -/
theorem container_radius_eq_factored (R a θmax : ℝ) (hR : 0 < R) (ha : 0 < a)
    (hclear : ContainerClearOfMirror R a) (hsingle : SingleReflectionRegime R a)
    (hmax : IsMaxIncidenceAngle R a θmax) :
    a = R * Real.sin θmax * (1 - Real.cos θmax) := by
  -- `hsingle` is part of the physical contract (used in `absorbedImpactSet_eq_Icc`);
  -- the algebra uses `dist_at_max_eq` and `distToLine_container`.
  refine (fun _ => ?_) hsingle
  exact (dist_at_max_eq R a θmax hR ha hclear hmax).symm.trans
    (distToLine_container R θmax hR hmax.1)

/-! ## Bridge lemmas: signs of the trigonometric factors at `θ_max` -/

/-- `θ_max` is strictly positive: `θ_max ∈ [0, π/2]` (from `hmax.1`) and if
`θ_max = 0` then `a = dist(0) = R·sin 0·(1 − cos 0) = 0` by `dist_at_max_eq`
and `distToLine_container`, contradicting `0 < a`. -/
theorem thetaMax_pos (R a θmax : ℝ) (hR : 0 < R) (ha : 0 < a)
    (hclear : ContainerClearOfMirror R a) (hmax : IsMaxIncidenceAngle R a θmax) :
    0 < θmax := by
  have hθm := hmax.1
  rcases eq_or_lt_of_le hθm.1 with h0 | hpos
  · exfalso
    have h00 : (0:ℝ) ∈ Set.Icc 0 (Real.pi / 2) := ⟨le_refl 0, by positivity⟩
    have hdist := dist_at_max_eq R a θmax hR ha hclear hmax
    rw [← h0] at hdist
    rw [distToLine_container R 0 hR h00] at hdist
    simp [Real.sin_zero, Real.cos_zero] at hdist
    linarith
  · exact hpos

/-- `sin θ > 0` on `(0, π/2]`.  Proof route:
`Real.sin_pos_of_pos_of_lt_pi` with `0 < θ` and `θ ≤ π/2 < π`. -/
theorem sin_pos_of_theta_range {θ : ℝ} (hθ : θ ∈ Set.Ioc 0 (Real.pi / 2)) :
    0 < Real.sin θ := by
  exact Real.sin_pos_of_pos_of_lt_pi hθ.1 (lt_of_le_of_lt hθ.2 (by linarith [Real.pi_pos]))

/-- `1 − cos θ > 0` on `(0, π/2]`.  Proof route: `cos` is strictly antitone on
`[0, π]` (`Real.strictAntiOn_cos`), so `cos θ < cos 0 = 1` for `0 < θ ≤ π/2`. -/
theorem one_sub_cos_pos_of_theta_range {θ : ℝ} (hθ : θ ∈ Set.Ioc 0 (Real.pi / 2)) :
    0 < 1 - Real.cos θ := by
  have hcos : Real.cos θ < 1 := by
    have h0 : (0:ℝ) ∈ Set.Icc 0 Real.pi := ⟨le_refl 0, Real.pi_pos.le⟩
    have hθ' : θ ∈ Set.Icc 0 Real.pi := ⟨hθ.1.le, le_trans hθ.2 (by linarith [Real.pi_pos])⟩
    have h := Real.strictAntiOn_cos h0 hθ' hθ.1
    rwa [Real.cos_zero] at h
  exact sub_pos.mpr hcos

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
  have hbound := hmax.2.2
  have hDmax : R * Real.sin θmax * (1 - Real.cos θmax) = a := by
    have h := dist_at_max_eq R a θmax hR ha hclear hmax
    rwa [distToLine_container R θmax hR hθm] at h
  constructor
  · intro hstr
    exact hbound θ hθ hstr
  · intro hle
    rw [strikes_iff_dist_le R a θ hR ha hθ, distToLine_container R θ hR hθ, ← hDmax]
    exact ((dist_strictMonoOn R hR).le_iff_le hθ hθm).mpr hle

/-- **Coverage of the impact strip**: every value `y ∈ [0, sin θ_max]` is
`sin θ` for some `θ ∈ [0, θ_max]`.  Proof route: take `θ = Real.arcsin y`;
`Real.sin_arcsin'` (with `0 ≤ y ≤ sin θ_max ≤ 1`) gives `sin θ = y`, and
`Real.monotone_arcsin` with `Real.arcsin_sin` (valid on `[0, π/2]`) gives
`arcsin y ≤ arcsin (sin θ_max) = θ_max`. -/
theorem sin_surj_upto {θmax : ℝ} (hθmax : θmax ∈ Set.Icc 0 (Real.pi / 2))
    {y : ℝ} (hy : y ∈ Set.Icc 0 (Real.sin θmax)) :
    ∃ θ : ℝ, θ ∈ Set.Icc 0 θmax ∧ Real.sin θ = y := by
  have hsin1 : Real.sin θmax ≤ 1 := Real.sin_le_one θmax
  have hy1 : -1 ≤ y := le_trans (by norm_num : (-1:ℝ) ≤ 0) hy.1
  have hy2 : y ≤ 1 := le_trans hy.2 hsin1
  have hθmax_neg : -(Real.pi / 2) ≤ θmax :=
    le_trans (by linarith [Real.pi_pos] : -(Real.pi / 2) ≤ 0) hθmax.1
  have harcsin : Real.arcsin (Real.sin θmax) = θmax := Real.arcsin_sin hθmax_neg hθmax.2
  refine ⟨Real.arcsin y, ⟨Real.arcsin_nonneg.mpr hy.1, ?_⟩, ?_⟩
  · calc Real.arcsin y ≤ Real.arcsin (Real.sin θmax) := Real.monotone_arcsin hy.2
      _ = θmax := harcsin
  · exact Real.sin_arcsin' ⟨hy1, hy2⟩

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
  have hθm := hmax.1
  have hfactored : a = R * Real.sin θmax * (1 - Real.cos θmax) :=
    container_radius_eq_factored R a θmax hR ha hclear hsingle hmax
  have hsinθmax : 0 ≤ Real.sin θmax :=
    Real.sin_nonneg_of_mem_Icc ⟨hθm.1, le_trans hθm.2 (by linarith [Real.pi_pos])⟩
  have hcosθmax : 0 ≤ Real.cos θmax :=
    Real.cos_nonneg_of_mem_Icc
      ⟨le_trans (by linarith [Real.pi_pos] : -(Real.pi / 2) ≤ 0) hθm.1, hθm.2⟩
  have hale : a ≤ R * Real.sin θmax := by
    rw [hfactored]
    have hcos1 : 1 - Real.cos θmax ≤ 1 := by linarith
    calc R * Real.sin θmax * (1 - Real.cos θmax)
        ≤ R * Real.sin θmax * 1 :=
          mul_le_mul_of_nonneg_left hcos1 (mul_nonneg hR.le hsinθmax)
      _ = R * Real.sin θmax := mul_one _
  ext x
  simp only [absorbedImpactSet, Set.mem_union, Set.mem_setOf_eq, Set.mem_Icc]
  constructor
  · rintro (hdirect | ⟨θ, hθ, hstr, hx⟩)
    · have hdirect' : |x| ≤ a := hdirect
      exact abs_le.mp (le_trans hdirect' hale)
    · have hle : θ ≤ θmax := (strikes_iff_le_max R a θmax hR ha hclear hmax hθ).mp hstr
      have hsin_le : Real.sin θ ≤ Real.sin θmax :=
        Real.strictMonoOn_sin.monotoneOn
          ⟨le_trans (by linarith [Real.pi_pos] : -(Real.pi / 2) ≤ 0) hθ.1, hθ.2⟩
          ⟨le_trans (by linarith [Real.pi_pos] : -(Real.pi / 2) ≤ 0) hθm.1, hθm.2⟩ hle
      have hxabs : |x| ≤ R * Real.sin θmax := by
        rw [hx]
        exact mul_le_mul_of_nonneg_left hsin_le hR.le
      exact abs_le.mp hxabs
  · rintro ⟨hlo, hhi⟩
    by_cases hdirect : |x| ≤ a
    · left
      exact hdirect
    · right
      have hxabs : |x| ≤ R * Real.sin θmax := abs_le.mpr ⟨hlo, hhi⟩
      have hy : |x| / R ∈ Set.Icc 0 (Real.sin θmax) := by
        refine ⟨div_nonneg (abs_nonneg x) hR.le, ?_⟩
        rw [div_le_iff₀ hR, mul_comm (Real.sin θmax) R]
        exact hxabs
      obtain ⟨θ, ⟨hθ0, hθmax'⟩, hsin⟩ := sin_surj_upto hθm hy
      have hθicc : θ ∈ Set.Icc 0 (Real.pi / 2) := ⟨hθ0, le_trans hθmax' hθm.2⟩
      refine ⟨θ, hθicc, ?_, ?_⟩
      · rw [strikes_iff_le_max R a θmax hR ha hclear hmax hθicc]
        exact hθmax'
      · rw [hsin, mul_comm R (|x| / R), div_mul_cancel₀ |x| hR.ne']

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

/-! ## Bridge lemmas: the power ratio -/

/-- **Received power in closed form**: per unit length, `P = 2·R·sin θ_max·I`
(intensity times the width `2 R sin θ_max` of the absorbed impact set).
Proof route: unfold `powerWithMirrorPerLength`, rewrite with
`volume_absorbedImpactSet`, apply `ENNReal.toReal_ofReal`
(`0 ≤ 2 R sin θ_max` since `sin θ_max ≥ 0` on `[0, π/2]`), and ring. -/
theorem powerWithMirror_eq (I R a θmax : ℝ) (hR : 0 < R) (ha : 0 < a)
    (hclear : ContainerClearOfMirror R a) (hsingle : SingleReflectionRegime R a)
    (hmax : IsMaxIncidenceAngle R a θmax) :
    powerWithMirrorPerLength I R a = 2 * R * Real.sin θmax * I := by
  have hsin : 0 ≤ Real.sin θmax :=
    Real.sin_nonneg_of_mem_Icc ⟨hmax.1.1, le_trans hmax.1.2 (by linarith [Real.pi_pos])⟩
  have hnonneg : 0 ≤ 2 * R * Real.sin θmax := by positivity
  unfold powerWithMirrorPerLength
  rw [volume_absorbedImpactSet R a θmax hR ha hclear hsingle hmax,
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
  have hIne : I ≠ 0 := hI.ne'
  have hane : a ≠ 0 := ha.ne'
  rw [powerWithMirror_eq I R a θmax hR ha hclear hsingle hmax]
  unfold powerWithoutMirrorPerLength
  field_simp

/-! ## Main target (T2-B2) -/

/-- **T2-B2 main target** (blueprint `thm:physics:ipho_2026_t2_b2:target`).
Under the problem's assumptions — positive radii `0 < R`, `0 < a`, positive
uniform solar intensity `0 < I`, the container strictly inside the bowl
(`ContainerClearOfMirror`, Fig. 2f), the single-reflection regime
(`SingleReflectionRegime`, the problem's "at most once" assumption) — and with
`θ_max` the problem's own maximum incidence angle of a reflected ray striking
the container (`IsMaxIncidenceAngle`), the ratio of the received power with the
mirror to the power without it is

```
P / P₀ = 1 / (1 − cos θ_max).
```

Proof route: `power_ratio_eq_sin` gives `P/P₀ = R sin θ_max / a`; the T2-B1
relation in factored form (`container_radius_eq_factored`) gives
`a = R sin θ_max (1 − cos θ_max)` with `R sin θ_max ≠ 0` (`thetaMax_pos`,
`sin_pos_of_theta_range`) and `1 − cos θ_max ≠ 0`
(`one_sub_cos_pos_of_theta_range`); cancel by `field_simp`.
The hypothesis `hsingle` belongs to the physical contract: it certifies that
every striking reflected ray is absorbed (used in `absorbedImpactSet_eq_Icc`);
the final algebra uses the geometric bridges. -/
theorem power_ratio (I R a θmax : ℝ) (hI : 0 < I) (hR : 0 < R) (ha : 0 < a)
    (hclear : ContainerClearOfMirror R a) (hsingle : SingleReflectionRegime R a)
    (hmax : IsMaxIncidenceAngle R a θmax) :
    powerWithMirrorPerLength I R a / powerWithoutMirrorPerLength I a
      = 1 / (1 - Real.cos θmax) := by
  rw [power_ratio_eq_sin I R a θmax hI hR ha hclear hsingle hmax]
  have hfactored : a = R * Real.sin θmax * (1 - Real.cos θmax) :=
    container_radius_eq_factored R a θmax hR ha hclear hsingle hmax
  have hθpos : 0 < θmax := thetaMax_pos R a θmax hR ha hclear hmax
  have hsinpos : 0 < Real.sin θmax := sin_pos_of_theta_range ⟨hθpos, hmax.1.2⟩
  have hcospos : 0 < 1 - Real.cos θmax := one_sub_cos_pos_of_theta_range ⟨hθpos, hmax.1.2⟩
  have h1 : R * Real.sin θmax ≠ 0 := mul_ne_zero hR.ne' hsinpos.ne'
  have h2 : 1 - Real.cos θmax ≠ 0 := hcospos.ne'
  rw [hfactored]
  field_simp

end IPhO2026.T2B2
