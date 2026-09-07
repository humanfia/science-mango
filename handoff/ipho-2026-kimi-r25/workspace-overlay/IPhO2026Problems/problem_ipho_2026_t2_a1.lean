import Mathlib

/-!
# IPhO 2026 · Theory problem T2-A1 — "Cooking with sunlight?" (multiple reflections)

Autoformalization of IPhO 2026 T2-A1 (source: `reports/ipho_2026/problem_ipho_2026_t2_a1.source.json`,
figures `ipho_2026_source/image/T2_page-1.png` (Fig. 2c), `T2_page-2.png` (Figs. 2d, 2e)).

## Physical scenario

A half-cylindrical mirror of radius `R` (Fig. 2c: a cylindrical trough of opening
width `2R`) is illuminated by rays from a distant external source, all parallel to the
mirror's optical axis.  By the translation symmetry along the cylinder axis it is
sufficient to study one cross-sectional plane (problem text, page 7), the plane of
Fig. 2d: the mirror cross-section is the upper semicircle of radius `R` centred at the
origin `O`, the `x`-axis runs along the diameter (the open aperture stretches from
`-R` to `R`), and the `y`-axis is the optical axis.  Incident rays travel in the `+y`
direction (orange arrows of Fig. 2d), enter through the aperture, and hit the
*inside* (concave side) of the arc at the point `(x, √(R² − x²))`, where `x ∈ (-R, R)`
is the transverse coordinate of the ray.

The ray then undergoes repeated **specular reflection** on the arc until a would-be
impact lands off the arc (`y ≤ 0`), i.e. the chord from the last impact crosses the
aperture and the ray leaves the cavity.  `N(x)` denotes the number of reflections.
Fig. 2e plots `N` against `x ∈ (-R, R)`: a staircase with steps at
`-x₃, -x₂, -x₁, x₁, x₂, x₃`, closed dots at `(±x_N, N)` and open dots at
`(±x_N, N+1)` — at `|x| = x_N` exactly the ray still counts `N` reflections (the
grazing hit on the rim `y = 0` is *not* a reflection).  The problem defines `x_N`,
the *positive threshold*, as the largest distance from the optical axis for which a
ray undergoes at most `N` reflections.

**Subquestion T2-A1.** Find the general expression for `x_N` in the infinite
sequence `x₁, x₂, x₃, …`, in terms of `R` and the positive integer `N`.

## Physical model (governing laws)

1. *Straight-line propagation* (`nextImpact`): between reflections a ray travels
   straight; from an impact point `p` on the circle (`‖p‖ = R`) with unit direction
   `d`, the line `p + t • d` meets the circle again at the nonzero root
   `t = −2⟪p, d⟫` of `‖p + t • d‖² = R²`.
2. *Law of specular reflection* (`specularReflect`): at an impact point with outward
   unit normal `n` the direction becomes `d − 2⟪d, n⟫ • n` — the tangential component
   is kept and the normal component flips, i.e. the angle of incidence equals the
   angle of reflection (`specularReflect_normal_component_neg`).  On the circle the
   outward unit normal is radial, `n = R⁻¹ • p` (`outwardUnitNormal`).
3. *Rim convention* (Fig. 2e closed/open dots): the `k`-th reflection happens iff the
   `k`-th impact point lies on the *open* arc `y > 0` (`IsReflectedAt`); a hit at
   `y = 0` (the rim `(±R, 0)`) or below ends the trajectory without a reflection.

The bounce map (`bounceStep`) iterates "propagate to next circle intersection, then
reflect", producing the (mathematically total) sequence of impact points
`impactPoint R x k`; the physical trajectory uses the initial segment up to the first
impact off the arc, which always exists (`eventually_not_reflected`).

## Derivation of the candidate (problem-side geometry only, answer-blind)

Let `φ₀ := arccos (x / R) ∈ (0, π/2)` be the polar angle (from the `+x` direction) of
the first impact `(x, √(R²−x²))`.  The incoming direction is vertical, so the angle
of incidence at the first impact is `α = π/2 − φ₀`.  Reflection on a circle preserves
the incidence angle, hence (inscribed-angle theorem on the isosceles triangle formed
by two consecutive impacts and the centre) every chord between consecutive impacts
subtends the same central angle `π − 2α = 2φ₀`: the polar angle of the `k`-th impact
is `(2k+1)·φ₀` (`rayStateAfter_polar`).  Reflection `k` therefore happens iff
`sin((2k+1)φ₀) > 0`, i.e. iff `(2k+1)φ₀ < π` (the first odd multiple reaching `π`
lands in `[π, 2π)` because the step `2φ₀ < π`).  Consequently

```
N(x) ≤ N  ⟺  (2N+1)·φ₀ ≥ π  ⟺  φ₀ ≥ π/(2N+1)  ⟺  x ≤ R·cos(π/(2N+1)),
```

with equality attained (rim hit at `(2N+1)φ₀ = π` does not count).  The candidate
threshold is therefore `x_N = R·cos(π/(2N+1))` (`candidateThreshold`), strictly
increasing in `N` with `x₁ = R/2`, `x₂ = R·cos(π/5) ≈ 0.809 R`, `x₃ = R·cos(π/7)
≈ 0.901 R`, `x_N < R` and `x_N → R` — the staircase shape of Fig. 2e.  That this
candidate equals `threshold R N` is the content of the main theorem `threshold_eq`
(proof deferred to the prover stage); nothing in the definitions assumes it.

## Orientation and branch information

* Incoming rays point in `+y` (Fig. 2d arrows); the model fixes `incomingDir = (0, 1)`.
* The staircase is symmetric, `N(−x) = N(x)` (`hasAtMostNReflections_neg`), so the
  positive axis `x > 0` used for `threshold` represents the *distance* from the
  optical axis.
* The closed-dot branch of Fig. 2e (rim hits do not count) is carried by the strict
  inequality `0 < yCoord p` in `mirrorArc` and confirmed by
  `hasExactly_at_threshold`: at `x = x_N` the count is exactly `N`.
* The `mod 2π` branch in the counting argument is fixed by the first-crossing bound
  recorded in the docstring of `hasAtMostNReflections_iff`.

## Units and uncertainty

`R` and `x` carry units of length (the problem leaves the scale symbolic); all
lengths are real numbers with the roles kept explicit.  The question asks for an
exact symbolic expression, so no numerical rounding rule applies, and the source
reports no experimental uncertainties (uncertainty propagation: not applicable).

LeanExplore found no PhysLean ray-optics / law-of-reflection API; the reflection law
is grounded against the Euclidean inner product `⟪·, ·⟫` on `EuclideanSpace ℝ (Fin 2)`
(Mathlib), cf. `Submodule.reflection` (hyperplane reflection) — see the task result
for the grounding record.
-/

namespace IPhO2026.T2A1

open scoped RealInnerProductSpace

/-! ## The cross-sectional plane and figure geometry (Figs. 2c, 2d) -/

/-- The cross-sectional plane of Fig. 2d (perpendicular to the cylinder axis):
the Euclidean plane with coordinates `(x, y)`, `x` along the aperture diameter and
`y` along the optical axis. -/
abbrev Plane := EuclideanSpace ℝ (Fin 2)

/-- Transverse coordinate of a point: the signed distance from the optical axis
(the `x` of Fig. 2d).  Units: length. -/
noncomputable def xCoord (p : Plane) : ℝ := p 0

/-- Height coordinate of a point along the optical axis (the `y` of Fig. 2d).
Units: length. -/
noncomputable def yCoord (p : Plane) : ℝ := p 1

/-- The circular cross-section of the half-cylinder: the circle of radius `R`
centred at the origin `O` of Fig. 2d.  Units of `R`: length. -/
noncomputable def mirrorCircle (R : ℝ) : Set Plane := {p | ‖p‖ = R}

/-- The reflecting surface: the open upper semicircle `y > 0` of Fig. 2d (the
concave side faces the aperture).  The rim points `(±R, 0)` are excluded — by the
closed/open dot convention of Fig. 2e a hit exactly on the rim does not count as a
reflection. -/
noncomputable def mirrorArc (R : ℝ) : Set Plane := {p | p ∈ mirrorCircle R ∧ 0 < yCoord p}

/-- The open aperture of the half-cylinder: the diameter segment
`{y = 0, |x| < R}` of Fig. 2d, of width `2R` (the `2R` label of Fig. 2c).  Rays
enter and leave the cavity through it; there is no mirror here. -/
noncomputable def aperture (R : ℝ) : Set Plane := {p | yCoord p = 0 ∧ |xCoord p| < R}

/-! ## Governing laws: straight-line propagation and specular reflection -/

/-- The outward unit normal to the circle of radius `R` at a point `p` on it:
the radial direction `R⁻¹ • p`.  Unit length is certified by
`outwardUnitNormal_norm`. -/
noncomputable def outwardUnitNormal (R : ℝ) (p : Plane) : Plane := R⁻¹ • p

/-- **Law of specular reflection** (governing law), vector form: a ray with
direction `d` reflecting at a point with unit normal `n` acquires the direction
`d − 2⟪d, n⟫ • n`; the tangential component is preserved and the normal component
changes sign, which is exactly "angle of incidence equals angle of reflection"
(see `specularReflect_normal_component_neg`).  Grounded in the Mathlib inner
product; this is the explicit form of the hyperplane reflection
`Submodule.reflection (ℝ ∙ n)ᗮ`. -/
noncomputable def specularReflect (n d : Plane) : Plane := d - (2 * ⟪d, n⟫) • n

/-- **Straight-line propagation** (governing law): between reflections the ray
travels straight through the homogeneous air in the cavity.  From an impact point
`p` on the circle (`‖p‖ = R`) with unit direction `d`, the line `p + t • d` meets
the circle at `t = 0` (the point `p` itself) and at `t = −2⟪p, d⟫`; `nextImpact`
is this second intersection, certified by `nextImpact_mem_circle` and
`nextImpact_ne_self`. -/
noncomputable def nextImpact (p d : Plane) : Plane := p - (2 * ⟪p, d⟫) • d

/-! ## The ray dynamics: states, bounce map, impact sequence -/

/-- The state of the bouncing ray: the current impact point on the mirror circle
together with the unit direction of travel immediately *after* reflection there. -/
structure RayState where
  /-- Current impact point on the mirror circle. -/
  point : Plane
  /-- Unit direction of travel immediately after reflection at `point`. -/
  dir : Plane

/-- Direction of the incident rays: `+y`, parallel to the optical axis, pointing
into the cavity (Fig. 2d arrows; the source is distant, so all rays share it). -/
noncomputable def incomingDir : Plane := !₂[(0 : ℝ), 1]

/-- First impact of the ray with transverse coordinate `x`: it enters through the
aperture at `(x, 0)` travelling along `+y` and meets the arc at
`(x, √(R² − x²))` (Fig. 2d).  Units of `x`, `R`: length. -/
noncomputable def firstImpactPoint (R x : ℝ) : Plane := !₂[x, Real.sqrt (R ^ 2 - x ^ 2)]

/-- One full reflection cycle: propagate straight from the current impact to the
next circle intersection, then apply the law of reflection with the radial outward
normal there.  (The map is total; physically the trajectory stops at the first
impact that lands off the arc, cf. `IsReflectedAt`.) -/
noncomputable def bounceStep (R : ℝ) (s : RayState) : RayState :=
  ⟨nextImpact s.point s.dir,
   specularReflect (outwardUnitNormal R (nextImpact s.point s.dir)) s.dir⟩

/-- Initial ray state at the first reflection: the first impact point together
with the direction obtained by reflecting the incident direction `incomingDir`
in the radial normal there (the first reflection always happens for `|x| < R`,
see `firstImpactPoint_mem_arc`). -/
noncomputable def initialState (R x : ℝ) : RayState :=
  ⟨firstImpactPoint R x,
   specularReflect (outwardUnitNormal R (firstImpactPoint R x)) incomingDir⟩

/-- The ray state at the `k`-th impact (0-indexed): iterate of the bounce map. -/
noncomputable def rayStateAfter (R x : ℝ) (k : ℕ) : RayState :=
  (bounceStep R)^[k] (initialState R x)

/-- The `k`-th impact point (0-indexed) of the ray with transverse coordinate `x`. -/
noncomputable def impactPoint (R x : ℝ) (k : ℕ) : Plane := (rayStateAfter R x k).point

/-! ## Reflection counting (Fig. 2e) -/

/-- The `k`-th reflection physically happens iff the `k`-th impact point lies on
the reflecting arc (`y > 0`).  Impacts at `y ≤ 0` are on the missing lower half of
the cylinder or exactly on the rim: the chord from the previous impact has crossed
the aperture and the ray has left the cavity (rim convention of Fig. 2e). -/
def IsReflectedAt (R x : ℝ) (k : ℕ) : Prop :=
  impactPoint R x k ∈ mirrorArc R

/-- The ray undergoes at least `n` reflections: its first `n` impacts all lie on
the reflecting arc. -/
def HasAtLeastNReflections (R x : ℝ) (n : ℕ) : Prop :=
  ∀ k : ℕ, k < n → IsReflectedAt R x k

/-- The ray undergoes at most `N` reflections: some impact among the first `N + 1`
lands off the arc, so the physical trajectory stops no later than the `N`-th
reflection.  By `hasAtMost_iff_not_atLeast_succ` this is exactly
`¬ HasAtLeastNReflections R x (N + 1)`. -/
def HasAtMostNReflections (R x : ℝ) (N : ℕ) : Prop :=
  ∃ k : ℕ, k ≤ N ∧ ¬ IsReflectedAt R x k

/-- The ray undergoes exactly `n` reflections (the step height of the Fig. 2e
staircase): its first `n` impacts lie on the arc and the `(n+1)`-th does not. -/
def HasExactlyNReflections (R x : ℝ) (n : ℕ) : Prop :=
  HasAtLeastNReflections R x n ∧ ¬ HasAtLeastNReflections R x (n + 1)

/-! ## The threshold `x_N` and the derived candidate expression -/

/-- The threshold `x_N` of the problem: the largest distance from the optical axis
allowing at most `N` reflections.  By the left-right symmetry of Fig. 2e
(`hasAtMostNReflections_neg`) the distances are the positive transverse
coordinates, so `x_N` is the supremum of the positive coordinates `x < R` whose
ray reflects at most `N` times. -/
noncomputable def threshold (R : ℝ) (N : ℕ) : ℝ :=
  sSup {x : ℝ | 0 < x ∧ x < R ∧ HasAtMostNReflections R x N}

/-- The derived candidate expression for `x_N`, obtained from the problem-side
geometry alone (law of reflection + circle, see the module docstring):
`x_N = R·cos(π/(2N+1))`.  This definition only *records* the candidate for the
answer-blind pipeline; that it equals the threshold is proved as
`threshold_eq_candidate` (currently `sorry`, like every proof in this file). -/
noncomputable def candidateThreshold (R : ℝ) (N : ℕ) : ℝ :=
  R * Real.cos (Real.pi / (2 * (N : ℝ) + 1))

/-! ## Bridge lemmas: law-of-reflection algebra (proofs deferred) -/

/-- The radial normal at a point of the circle is a unit vector. -/
theorem outwardUnitNormal_norm (hR : 0 < R) {p : Plane} (hp : p ∈ mirrorCircle R) :
    ‖outwardUnitNormal R p‖ = 1 := by
  sorry

/-- Reflection in a unit normal preserves unit vectors (directions stay
normalized along the whole trajectory). -/
theorem specularReflect_norm {n d : Plane} (hn : ‖n‖ = 1) (hd : ‖d‖ = 1) :
    ‖specularReflect n d‖ = 1 := by
  sorry

/-- Angle form of the law of reflection: the normal component of the direction
flips sign at a reflection, i.e. the angle of incidence equals the angle of
reflection with respect to the radial normal. -/
theorem specularReflect_normal_component_neg (hR : 0 < R) {p d : Plane}
    (hp : p ∈ mirrorCircle R) :
    ⟪specularReflect (outwardUnitNormal R p) d, outwardUnitNormal R p⟫
      = -⟪d, outwardUnitNormal R p⟫ := by
  sorry

/-- After reflection the ray points into the disk with the opposite radial
component: `⟪p, d'⟫ = −⟪p, d⟫`.  In particular a ray arriving at the arc from
inside (`⟪p, d⟫ > 0` for the upward-moving incident ray) leaves the impact
point inward (`⟪p, d'⟫ < 0`), so `nextImpact` is reached in the forward
direction. -/
theorem inner_point_specularReflect (hR : 0 < R) {p d : Plane} (hp : p ∈ mirrorCircle R) :
    ⟪p, specularReflect (outwardUnitNormal R p) d⟫ = -⟪p, d⟫ := by
  sorry

/-- Straight-line propagation lands back on the circle: `nextImpact p d` is again
a point of the mirror circle. -/
theorem nextImpact_mem_circle {R : ℝ} {p d : Plane} (hp : p ∈ mirrorCircle R)
    (hd : ‖d‖ = 1) :
    nextImpact p d ∈ mirrorCircle R := by
  sorry

/-- The next impact differs from the current one whenever the direction is not
tangent to the circle (`⟪p, d⟫ ≠ 0`); along the physical trajectory
`⟪p, d⟫ = −R·sin φ₀ < 0` (see `rayStateAfter_polar`). -/
theorem nextImpact_ne_self {p d : Plane} (h : ⟪p, d⟫ ≠ 0) :
    nextImpact p d ≠ p := by
  sorry

/-- The incident direction is a unit vector. -/
theorem incomingDir_norm : ‖incomingDir‖ = 1 := by
  sorry

/-- Every ray entering through the aperture (`|x| < R`) hits the reflecting arc:
the first impact lies on the mirror arc, so every ray reflects at least once
(Fig. 2e: `N ≥ 1` on all of `(-R, R)`). -/
theorem firstImpactPoint_mem_arc (hR : 0 < R) {x : ℝ} (hx : x ∈ Set.Ioo (-R) R) :
    firstImpactPoint R x ∈ mirrorArc R := by
  sorry

/-- State invariant: every impact point lies on the mirror circle and every
leg direction is a unit vector (induction over `bounceStep` using
`nextImpact_mem_circle`, `specularReflect_norm`, `outwardUnitNormal_norm`,
`firstImpactPoint_mem_arc`, `incomingDir_norm`). -/
theorem rayStateAfter_invariant (hR : 0 < R) {x : ℝ} (hx : x ∈ Set.Ioo (-R) R) (k : ℕ) :
    (rayStateAfter R x k).point ∈ mirrorCircle R ∧ ‖(rayStateAfter R x k).dir‖ = 1 := by
  sorry

/-! ## Bridge lemmas: constant angular step and the impact closed form -/

/-- **Constant angular step** (the geometric heart of the problem): with
`φ₀ := arccos (x / R)` the polar angle of the first impact, the `k`-th impact has
polar angle `(2k+1)·φ₀` and the `k`-th post-reflection direction is the unit
vector tangent to the chord at polar angle `(2k+2)·φ₀`.

Proof route for the prover stage: induction on `k`.  The incidence angle is
preserved by `specularReflect`, so by the inscribed-angle theorem (the triangle
formed by two consecutive impacts and the centre is isosceles) every chord
subtends the central angle `π − 2α = 2φ₀`, where `α = π/2 − φ₀` is the incidence
angle of the vertical incident ray; the algebra is carried by
`inner_point_specularReflect`, `nextImpact_mem_circle` and the trigonometric
identities for `(2k+3)φ₀ = (2k+1)φ₀ + 2φ₀`. -/
theorem rayStateAfter_polar (hR : 0 < R) {x : ℝ} (hx : x ∈ Set.Ioo (-R) R) (k : ℕ) :
    rayStateAfter R x k =
      ⟨!₂[R * Real.cos ((2 * (k : ℝ) + 1) * Real.arccos (x / R)),
          R * Real.sin ((2 * (k : ℝ) + 1) * Real.arccos (x / R))],
       !₂[-Real.sin ((2 * (k : ℝ) + 2) * Real.arccos (x / R)),
          Real.cos ((2 * (k : ℝ) + 2) * Real.arccos (x / R))]⟩ := by
  sorry

/-- The `k`-th reflection happens iff `sin((2k+1)·φ₀) > 0`, the impact lying on
the open upper arc. -/
theorem isReflectedAt_iff_sin_pos (hR : 0 < R) {x : ℝ} (hx : x ∈ Set.Ioo (-R) R) (k : ℕ) :
    IsReflectedAt R x k ↔ 0 < Real.sin ((2 * (k : ℝ) + 1) * Real.arccos (x / R)) := by
  sorry

/-- Every ray entering through the aperture reflects at least once. -/
theorem hasAtLeast_one (hR : 0 < R) {x : ℝ} (hx : x ∈ Set.Ioo (-R) R) :
    HasAtLeastNReflections R x 1 := by
  sorry

/-- Finiteness of the reflection count: every ray eventually exits through the
aperture — some impact lands off the arc.  (With `φ₀ > 0` the odd multiples
`(2k+1)·φ₀` are unbounded, and the first one reaching `π` lands in `[π, 2π)`
because the step `2φ₀ < π`.) -/
theorem eventually_not_reflected (hR : 0 < R) {x : ℝ} (hx : x ∈ Set.Ioo (-R) R) :
    ∃ k : ℕ, ¬ IsReflectedAt R x k := by
  sorry

/-- "At most `N`" is the negation of "at least `N + 1`": the reflections that
physically occur form an initial segment of the impact sequence. -/
theorem hasAtMost_iff_not_atLeast_succ (R x : ℝ) (N : ℕ) :
    HasAtMostNReflections R x N ↔ ¬ HasAtLeastNReflections R x (N + 1) := by
  sorry

/-! ## Bridge lemmas: the counting characterization and the threshold -/

/-- **Counting characterization** (main bridge from the model to the threshold):
for a ray entering at `0 < x < R`, at most `N` reflections is equivalent to
`x ≤ R·cos(π/(2N+1))`.

Proof route: by `isReflectedAt_iff_sin_pos`, `HasAtMostNReflections R x N` means
`sin((2k+1)φ₀) ≤ 0` for some `k ≤ N`.  The first odd multiple of `φ₀` reaching
`π` lands in `[π, 2π)` (step `2φ₀ < π`), so such a `k` exists iff
`(2N+1)·φ₀ ≥ π`, i.e. `φ₀ ≥ π/(2N+1)`; since `arccos` is antitone on
`[-1, 1]` and `x/R ∈ (0, 1)`, this is `x ≤ R·cos(π/(2N+1))`.  The branch choice
(`sin θ ≤ 0 ⟺ θ ∈ [π, 2π]` *within the first crossing*) is pinned by the
first-crossing bound. -/
theorem hasAtMostNReflections_iff (hR : 0 < R) {x : ℝ} (hx0 : 0 < x) (hxR : x < R)
    (N : ℕ) :
    HasAtMostNReflections R x N ↔ x ≤ candidateThreshold R N := by
  sorry

/-- Left-right symmetry of the staircase (Fig. 2e): reflection across the optical
axis conjugates the dynamics, so the reflection count at `-x` equals that at
`x`.  This legitimizes defining the threshold (a *distance* from the optical
axis) on the positive axis only. -/
theorem hasAtMostNReflections_neg (R : ℝ) (x : ℝ) (N : ℕ) :
    HasAtMostNReflections R (-x) N ↔ HasAtMostNReflections R x N := by
  sorry

/-- The threshold set is the half-open interval `(0, R·cos(π/(2N+1))]`: for
`N ≥ 1` the endpoint lies in `(0, R)`, absorbs the constraint `x < R`, and
belongs to the set (closed dots of Fig. 2e: the maximum is attained). -/
theorem threshold_set_eq (hR : 0 < R) (N : ℕ) (hN : 1 ≤ N) :
    {x : ℝ | 0 < x ∧ x < R ∧ HasAtMostNReflections R x N}
      = Set.Ioc 0 (candidateThreshold R N) := by
  sorry

/-- **T2-A1 main target.**  The general expression for the threshold sequence:
`x_N = R·cos(π/(2N+1))` for every positive integer `N`.  Proof route:
`threshold_set_eq` identifies the threshold set with `Set.Ioc 0 (R·cos(π/(2N+1)))`
(the endpoint is positive since `π/(2N+1) ≤ π/3 < π/2` for `N ≥ 1`), and
`csSup_Ioc` evaluates the supremum. -/
theorem threshold_eq (hR : 0 < R) (N : ℕ) (hN : 1 ≤ N) :
    threshold R N = R * Real.cos (Real.pi / (2 * (N : ℝ) + 1)) := by
  sorry

/-- The recorded candidate is the threshold (answer-blind record, conclusion
side only). -/
theorem threshold_eq_candidate (hR : 0 < R) (N : ℕ) (hN : 1 ≤ N) :
    threshold R N = candidateThreshold R N := by
  sorry

/-- The Fig. 2e staircase: on the positive axis the ray undergoes exactly `n`
reflections precisely on `(x_{n-1}, x_n]` (with `x₀ := R·cos π = -R` the
convention `candidateThreshold R 0`, so for `n = 1` the interval is
`(-R, R/2] ∩ (0, R)`). -/
theorem hasExactlyNReflections_iff (hR : 0 < R) {x : ℝ} (hx0 : 0 < x) (hxR : x < R)
    (n : ℕ) (hn : 1 ≤ n) :
    HasExactlyNReflections R x n ↔
      x ∈ Set.Ioc (candidateThreshold R (n - 1)) (candidateThreshold R n) := by
  sorry

/-- Closed dots of Fig. 2e: at the threshold itself the ray undergoes exactly
`N` reflections (the `(N+1)`-th impact is the rim hit `(2N+1)φ₀ = π`, which does
not count), so the "maximum distance" of the problem statement is attained. -/
theorem hasExactly_at_threshold (hR : 0 < R) (N : ℕ) (hN : 1 ≤ N) :
    HasExactlyNReflections R (threshold R N) N := by
  sorry

/-- The threshold is positive (`x_N ≥ R·cos(π/3) = R/2 > 0`). -/
theorem threshold_pos (hR : 0 < R) (N : ℕ) (hN : 1 ≤ N) :
    0 < threshold R N := by
  sorry

/-- The threshold is strictly inside the aperture (`x_N < R`: rays sufficiently
close to the rim reflect arbitrarily often). -/
theorem threshold_lt_radius (hR : 0 < R) (N : ℕ) (hN : 1 ≤ N) :
    threshold R N < R := by
  sorry

/-- The thresholds are strictly increasing (Fig. 2e: `x₁ < x₂ < x₃ < …`). -/
theorem threshold_strict_mono (hR : 0 < R) {M N : ℕ} (hM : 1 ≤ M) (hMN : M < N) :
    threshold R M < threshold R N := by
  sorry

/-- The thresholds accumulate at the rim: `x_N → R` as `N → ∞` (near-grazing
rays bounce arbitrarily many times before leaving). -/
theorem tendsto_threshold_atTop (hR : 0 < R) :
    Filter.Tendsto (fun N : ℕ => threshold R (N + 1)) Filter.atTop (nhds R) := by
  sorry

end IPhO2026.T2A1
