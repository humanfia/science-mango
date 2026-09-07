import Mathlib

/-!
# IPhO 2026 · Theory problem T2-C3 — "Caustics and Cusp": the limiting
intersection `(X_c, Y_c)` of two neighboring reflected rays

Autoformalization of IPhO 2026 T2-C3 (source:
`reports/ipho_2026/problem_ipho_2026_t2_c3.source.json`, figure
`ipho_2026_source/image/T2_page-4.png` — Fig. 2g, problem page 10).

## Physical scenario (shared T2-C context, Fig. 2g)

Same half-cylindrical mirror as in T2-C1 (`problem_ipho_2026_t2_c1.lean`):
the cross-section is the upper semicircle of radius `R` centred at the origin
`O`; the aperture is the diameter from `(−R, 0)` to `(R, 0)` (the `-R` and `R`
labels on the `x`-axis of Fig. 2g); the `y`-axis is the optical axis.  Ray A
travels in `+y` (upward arrows of Fig. 2g) from its base point
`A = (R sin θ, 0)` on the `x`-axis (the `A` label of Fig. 2g) and strikes the
concave side of the mirror at `M(θ) = (R sin θ, R cos θ)`; the marked angle `θ`
between the dashed radius `O M(θ)` and the vertical incoming ray is the angle
of incidence (`incidence_angle_eq`).  The reflected ray is the line
`y = m_A x + b_A` labelled in Fig. 2g.  Ray B is **parallel to A** (same
incoming direction `(0, 1)`, see `rayB_parallel_to_rayA`) and strikes the
surface at incidence angle `θ + Δθ` with `Δθ ≪ θ`
(`incidence_angle_rayB_eq`); its reflected line is `y = m_B x + b_B`.  The
envelope of the reflected rays — the limit of the intersection point of the
reflected rays of A and B as `Δθ → 0` — is the **caustic**.

**Subquestion T2-C3.**  Find the coordinates of the point of intersection
`(X_c, Y_c)` between the reflected rays of A and B, in terms of `R` and `θ`.
Since the answer must not involve `Δθ`, this is the *limiting* intersection as
`Δθ → 0` (blueprint chapter: "limiting intersection coordinates").

## Assumption/target split

*Governing laws (assumptions).*  (1) Straight-line propagation before and
after the reflection (`incomingRayA`, `reflectedRayA`, `incomingRayB`,
`reflectedRayB`).  (2) Vector law of specular reflection `d ↦ d − 2⟪d, n⟫ • n`
in the radial unit normal (`specularReflect`, `outwardUnitNormal`); the normal
component flips sign (`specularReflect_normal_component_neg`), i.e. the angle
of incidence equals the angle of reflection.  (3) Line readouts: `m_A, b_A`
(resp. `m_B, b_B`) are *any* reals such that `y = m x + b` holds at every point
of the reflected line of A (resp. B) — the predicates
`IsLineEquationOfReflectedRayA` / `IsLineEquationOfReflectedRayB`.  (4) `P(Δθ)`
is *any* point lying simultaneously on both reflected lines — the predicate
`IsIntersectionPoint`.  None of (1)–(4) mentions the answer.

*Previous-part results (derived inline per
`derive_inline_from_problem_only_material`).*  T2-C1: `m_A = cot(2θ)`,
`b_A = R/(2 cos θ)` — re-derived here from the reflection law with full proofs
(`slope_intercept_of_reflected_ray_A`, no `sorry`).  T2-C2: the exact ray-B
parameters `m_B = cot(2(θ+Δθ))`, `b_B = R/(2 cos(θ+Δθ))`
(`slope_intercept_of_reflected_ray_B`, proved by the angle shift) and their
first-order expansions in `Δθ`, carried rigorously by
`hasDerivAt_reflectedSlope`, `hasDerivAt_reflectedIntercept` and the little-o
forms `reflectedSlope_first_order`, `reflectedSlope_first_order_Δ`,
`reflectedIntercept_first_order`, `reflectedIntercept_first_order_Δ`.

*Figure/data readouts.*  `O = (0, 0)`; rim points `(±R, 0)`; base point
`A = (R sin θ, 0)`; impact points on the right half-arc
(`θ, θ + Δθ ∈ (0, π/2)`); incoming rays point in `+y`.

*Current target (conclusion side only).*  `X_c = R sin³θ` and
`Y_c = R cos θ (1 + 2 sin²θ)/2` appear only inside the definitions `causticX`,
`causticY`, `causticPoint` and in theorem *conclusions*
(`tendsto_reflectedRaysIntersection`, `limiting_intersection_of_reflected_rays`,
`limiting_intersection_coordinates`).  No hypothesis, predicate, structure
field, or local definition makes the main theorem true by unfolding: the
conclusion is a `Filter.Tendsto` statement about an *arbitrary* family `P` of
intersection points characterized only by `IsIntersectionPoint`.

## Derivation of the candidate (problem-side geometry only, answer-blind)

Intersecting `y = m_A x + b_A` with `y = m_B x + b_B` gives
`x(Δθ) = (b_B − b_A)/(m_A − m_B)`, `y(Δθ) = m_A x(Δθ) + b_A`
(`lineIntersection`, `lineIntersection_isIntersectionPoint`).  With the
previous-part functions `m(φ) = cot 2φ`, `b(φ) = R/(2 cos φ)`, the difference
quotients converge to the derivatives (`hasDerivAt_reflectedSlope`,
`hasDerivAt_reflectedIntercept`): `m'(θ) = −2/sin²(2θ)`,
`b'(θ) = R sin θ/(2 cos²θ)`.  Hence
`X_c = −b'(θ)/m'(θ) = R sin θ sin²(2θ)/(4 cos²θ) = R sin³θ`
(using `sin 2θ = 2 sin θ cos θ`) and
`Y_c = m_A X_c + b_A = R (1 + cos 2θ sin²θ)/(2 cos θ)
= R cos θ (1 + 2 sin²θ)/2`
(using `cos 2θ = 2cos²θ − 1` and `sin²θ + cos²θ = 1`).  Equivalent nephroid
parametrization (`causticPoint_trig_form`):
`(X_c, Y_c) = (R/4)(3 sin θ − sin 3θ, 3 cos θ − cos 3θ)` — the catacaustic of
the circle for a beam of parallel rays.  Sanity check at `θ = π/6`:
`X_c = R/8`, `Y_c = 3√3 R/8`, which lies on the forward reflected ray of A at
parameter `t = √3 R/4 > 0`.

## Orientation and branch information

* Rays travel in `+y` before reflection (`rayADir`, `rayBDir`); the "parallel"
  clause of T2-C2 is `rayBDir = rayADir`.
* Impact points lie on the right half of the arc (`θ, θ + Δθ ∈ (0, π/2)`),
  matching Fig. 2g.
* The limit is taken as `Δθ → 0` with `Δθ ≠ 0` (the punctured-neighborhood
  filter `𝓝[≠] 0`, two-sided: ray B may sit on either side of ray A); the
  informal `Δθ ≪ θ` is superseded by this limit.
* For `Δθ ≠ 0` the two reflected lines are not parallel
  (`reflected_rays_ne_parallel`, via `reflectedSlope_ne_of_ne`), so the
  intersection exists and is unique (`exists_intersectionPoint_of_reflected_rays`,
  `IsIntersectionPoint.unique`): the hypotheses of the main theorem are
  satisfiable, and any `P` satisfying them converges to the caustic point.

## Units and uncertainty

`R`, `b_A`, `b_B`, `X_c`, `Y_c` and all point coordinates carry units of
length (kept symbolic as real numbers); `m_A`, `m_B`, `θ`, `Δθ` are
dimensionless.  The question asks for exact symbolic expressions, so no
rounding rule applies; the source reports no measurement uncertainties
(uncertainty propagation: not applicable).

## Grounding

LeanExplore found no PhysLean ray-optics / law-of-reflection / caustic /
envelope API (queries recorded in the task result); as in
`problem_ipho_2026_t2_c1.lean`, the reflection law is grounded in the Mathlib
real inner product on `EuclideanSpace ℝ (Fin 2)` (cf. `Submodule.reflection`).
New Mathlib grounding for this file: `Filter.Tendsto`, `Topology.nhdsNE`
(notation `𝓝[≠]`), `HasDerivAt`, `hasDerivAt_iff_isLittleO`,
`Asymptotics.IsLittleO.comp_tendsto`, `PiLp.continuous_apply`,
`Real.sin_three_mul`, `Real.cos_three_mul`, `Fin.forall_fin_two`, and
`Real.sin_eq_zero_iff` for the non-parallelism route.  Near miss: there is no
`Real.hasDerivAt_cot`; the derivative of `cot` must be derived from
`Real.hasDerivAt_cos` / `Real.hasDerivAt_sin` via `HasDerivAt.div` (proof
deferred to the prover stage).
-/

namespace IPhO2026.T2C3

open scoped RealInnerProductSpace Topology

/-! ## The cross-sectional plane and Figure 2g geometry (shared with T2-C1) -/

/-- The cross-sectional plane of Fig. 2g (perpendicular to the cylinder axis):
the Euclidean plane with coordinates `(x, y)`, `x` along the aperture diameter
and `y` along the optical axis. -/
abbrev Plane := EuclideanSpace ℝ (Fin 2)

/-- Transverse coordinate of a point: the `x` of Fig. 2g.  Units: length. -/
noncomputable def xCoord (p : Plane) : ℝ := p 0

/-- Coordinate along the optical axis: the `y` of Fig. 2g.  Units: length. -/
noncomputable def yCoord (p : Plane) : ℝ := p 1

/-- The circular cross-section of the half-cylindrical mirror: the circle of
radius `R` centred at the origin `O` of Fig. 2g.  Units of `R`: length. -/
noncomputable def mirrorCircle (R : ℝ) : Set Plane := {p | ‖p‖ = R}

/-- The reflecting surface of Fig. 2g: the open upper semicircle `y > 0`, whose
concave side faces the aperture; the rim points are `(±R, 0)` (the `-R` and `R`
labels on the `x`-axis of Fig. 2g).  Same mirror as in
`problem_ipho_2026_t2_c1.lean`. -/
noncomputable def mirrorArc (R : ℝ) : Set Plane :=
  {p | p ∈ mirrorCircle R ∧ 0 < yCoord p}

/-- The outward unit normal to the circle of radius `R` at a point `p` on it:
the radial direction `R⁻¹ • p`.  Unit length is certified by
`outwardUnitNormal_norm`. -/
noncomputable def outwardUnitNormal (R : ℝ) (p : Plane) : Plane := R⁻¹ • p

/-- **Law of specular reflection** (governing law), vector form: a ray with
direction `d` reflecting at a point with unit normal `n` acquires the
direction `d − 2⟪d, n⟫ • n`; the tangential component is preserved and the
normal component changes sign, i.e. the angle of incidence equals the angle of
reflection (`specularReflect_normal_component_neg`). -/
noncomputable def specularReflect (n d : Plane) : Plane := d - (2 * ⟪d, n⟫) • n

/-! ## Ray A (incidence angle θ): the T2-C1 geometry, derived inline -/

/-- Direction of ray A before reflection: `+y`, parallel to the optical axis
(the upward arrows of Fig. 2g). -/
noncomputable def rayADir : Plane := !₂[(0 : ℝ), 1]

/-- Base point `A` of ray A on the `x`-axis (the `A` label of Fig. 2g):
`(R sin θ, 0)`, the foot of the vertical incoming ray.  Units: length. -/
noncomputable def rayABase (R θ : ℝ) : Plane := !₂[R * Real.sin θ, (0 : ℝ)]

/-- Impact point of ray A on the mirror: `M(θ) = (R sin θ, R cos θ)`.  The
radius `O M(θ)` (dashed in Fig. 2g) makes the angle `θ` with the vertical
incoming ray, so the marked angle of Fig. 2g is the angle of incidence
(`incidence_angle_eq`). -/
noncomputable def incidencePoint (R θ : ℝ) : Plane := !₂[R * Real.sin θ, R * Real.cos θ]

/-- Ray A before reflection (straight-line propagation): the vertical straight
line through its base point `A`; it reaches the mirror at `t = R cos θ`
(`incomingRayA_reaches_mirror`). -/
noncomputable def incomingRayA (R θ t : ℝ) : Plane := rayABase R θ + t • rayADir

/-- Direction of ray A after its reflection at `M(θ)`: the law of specular
reflection applied to `rayADir` in the radial normal there. -/
noncomputable def reflectedDirA (R θ : ℝ) : Plane :=
  specularReflect (outwardUnitNormal R (incidencePoint R θ)) rayADir

/-- The reflected line of ray A (straight-line propagation after the
reflection): the line through `M(θ)` along `reflectedDirA R θ`.  The physical
reflected ray is the forward branch `t > 0`; the equation `y = m_A x + b_A` of
the problem describes the whole affine line. -/
noncomputable def reflectedRayA (R θ t : ℝ) : Plane :=
  incidencePoint R θ + t • reflectedDirA R θ

/-- **`m_A`, `b_A` as defined by the problem** (the equation label of Fig. 2g):
the slope and `y`-intercept of the reflected line of ray A — every point of the
reflected line satisfies `y = m_A x + b_A`.  `m_A` is dimensionless; `b_A` has
units of length. -/
def IsLineEquationOfReflectedRayA (R θ m b : ℝ) : Prop :=
  ∀ t : ℝ, yCoord (reflectedRayA R θ t) = m * xCoord (reflectedRayA R θ t) + b

/-! ## Ray B (parallel to A, incidence angle θ + Δθ) -/

/-- Direction of ray B before reflection: equal to `rayADir` — this **is** the
"ray B, parallel to A" clause of T2-C2 (`rayB_parallel_to_rayA`). -/
noncomputable def rayBDir : Plane := rayADir

/-- Base point of ray B on the `x`-axis: `(R sin(θ + Δθ), 0)`, the foot of the
vertical incoming ray B.  Units: length. -/
noncomputable def rayBBase (R θ Δθ : ℝ) : Plane := !₂[R * Real.sin (θ + Δθ), (0 : ℝ)]

/-- Impact point of ray B on the mirror: `M(θ + Δθ)
= (R sin(θ + Δθ), R cos(θ + Δθ))`; ray B strikes the surface at the angle
`θ + Δθ` (`incidence_angle_rayB_eq`). -/
noncomputable def incidencePointB (R θ Δθ : ℝ) : Plane :=
  !₂[R * Real.sin (θ + Δθ), R * Real.cos (θ + Δθ)]

/-- Ray B before reflection (straight-line propagation): the vertical straight
line through its base point. -/
noncomputable def incomingRayB (R θ Δθ t : ℝ) : Plane := rayBBase R θ Δθ + t • rayBDir

/-- Direction of ray B after its reflection at `M(θ + Δθ)`: the law of
specular reflection applied to `rayBDir` in the radial normal there. -/
noncomputable def reflectedDirB (R θ Δθ : ℝ) : Plane :=
  specularReflect (outwardUnitNormal R (incidencePointB R θ Δθ)) rayBDir

/-- The reflected line of ray B (straight-line propagation after the
reflection): the line through `M(θ + Δθ)` along `reflectedDirB R θ Δθ`.  Its
equation is `y = m_B x + b_B`. -/
noncomputable def reflectedRayB (R θ Δθ t : ℝ) : Plane :=
  incidencePointB R θ Δθ + t • reflectedDirB R θ Δθ

/-- **`m_B`, `b_B` as defined by the problem**: the slope and `y`-intercept of
the reflected line of ray B — every point of that line satisfies
`y = m_B x + b_B`. -/
def IsLineEquationOfReflectedRayB (R θ Δθ m b : ℝ) : Prop :=
  ∀ t : ℝ, yCoord (reflectedRayB R θ Δθ t) = m * xCoord (reflectedRayB R θ Δθ t) + b

/-! ## Reflection-law and T2-C1 bridge lemmas (proved inline, full proofs) -/

/-- The incoming direction of ray A is a unit vector. -/
theorem rayADir_norm : ‖rayADir‖ = 1 := by
  have norm_coords : ∀ p : Plane, ‖p‖ = Real.sqrt (p 0 ^ 2 + p 1 ^ 2) := by
    intro p
    rw [EuclideanSpace.norm_eq, Fin.sum_univ_two]
    simp [Real.norm_eq_abs, sq_abs]
  rw [rayADir, norm_coords]
  simp

/-- The radial normal at a point of the circle is a unit vector. -/
theorem outwardUnitNormal_norm (R : ℝ) (hR : 0 < R) {p : Plane}
    (hp : p ∈ mirrorCircle R) :
    ‖outwardUnitNormal R p‖ = 1 := by
  have hp' : ‖p‖ = R := hp
  simp only [outwardUnitNormal, norm_smul, Real.norm_of_nonneg (inv_nonneg.mpr hR.le), hp',
    inv_mul_cancel₀ hR.ne']

/-- Angle form of the law of reflection: the normal component of the direction
flips sign at a reflection, i.e. the angle of incidence equals the angle of
reflection with respect to the normal. -/
theorem specularReflect_normal_component_neg {n d : Plane} (hn : ‖n‖ = 1) :
    ⟪specularReflect n d, n⟫ = -⟪d, n⟫ := by
  have hnn : ⟪n, n⟫ = 1 := by rw [real_inner_self_eq_norm_sq, hn]; norm_num
  simp only [specularReflect, inner_sub_left, real_inner_smul_left, hnn]
  ring

/-- The impact point of ray A lies on the reflecting arc of Fig. 2g (on the
right half for `0 < θ < π/2`, as drawn). -/
theorem incidencePoint_mem_arc (R θ : ℝ) (hR : 0 < R)
    (hθ : θ ∈ Set.Ioo 0 (Real.pi / 2)) :
    incidencePoint R θ ∈ mirrorArc R := by
  obtain ⟨hθ0, hθ1⟩ := hθ
  have norm_coords : ∀ p : Plane, ‖p‖ = Real.sqrt (p 0 ^ 2 + p 1 ^ 2) := by
    intro p
    rw [EuclideanSpace.norm_eq, Fin.sum_univ_two]
    simp [Real.norm_eq_abs, sq_abs]
  refine ⟨?_, ?_⟩
  · show ‖incidencePoint R θ‖ = R
    rw [incidencePoint, norm_coords]
    have hsq : (!₂[R * Real.sin θ, R * Real.cos θ] : Plane) 0 ^ 2
        + (!₂[R * Real.sin θ, R * Real.cos θ] : Plane) 1 ^ 2 = R ^ 2 := by
      simp only [Matrix.cons_val_zero, Matrix.cons_val_one]
      rw [mul_pow, mul_pow, ← mul_add, Real.sin_sq_add_cos_sq, mul_one]
    rw [hsq, Real.sqrt_sq hR.le]
  · show 0 < yCoord (incidencePoint R θ)
    simp only [yCoord, incidencePoint, Matrix.cons_val_one]
    exact mul_pos hR (Real.cos_pos_of_mem_Ioo ⟨by linarith [Real.pi_pos], hθ1⟩)

/-- Ray A strikes the mirror at `M(θ)`: travelling straight up from its base
point `A`, it reaches `M(θ)` after covering the height `R cos θ`. -/
theorem incomingRayA_reaches_mirror (R θ : ℝ) :
    incomingRayA R θ (R * Real.cos θ) = incidencePoint R θ := by
  ext i
  fin_cases i <;>
    simp only [incomingRayA, rayABase, rayADir, incidencePoint, PiLp.add_apply,
      PiLp.smul_apply, smul_eq_mul, Matrix.cons_val_zero, Matrix.cons_val_one,
      Fin.reduceFinMk] <;>
    ring

/-- **The parameter `θ` is the angle of incidence**: the angle between the
incident direction and the normal at `M(θ)`, measured with respect to the
normal, is `arccos (cos θ) = θ` on `[0, π/2]`. -/
theorem incidence_angle_eq (R θ : ℝ) (hR : 0 < R)
    (hθ : θ ∈ Set.Icc 0 (Real.pi / 2)) :
    Real.arccos ⟪rayADir, outwardUnitNormal R (incidencePoint R θ)⟫ = θ := by
  have inner_coords : ∀ u v : Plane, ⟪u, v⟫ = u 0 * v 0 + u 1 * v 1 := by
    intro u v
    rw [PiLp.inner_apply, Fin.sum_univ_two]
    simp [RCLike.inner_apply]
    ring
  have hinner : ⟪rayADir, outwardUnitNormal R (incidencePoint R θ)⟫ = Real.cos θ := by
    simp only [inner_coords, rayADir, outwardUnitNormal, incidencePoint, PiLp.smul_apply,
      smul_eq_mul, Matrix.cons_val_zero, Matrix.cons_val_one]
    rw [zero_mul, one_mul, zero_add, ← mul_assoc, inv_mul_cancel₀ hR.ne', one_mul]
  rw [hinner]
  exact Real.arccos_cos hθ.1 (le_trans hθ.2 (by linarith [Real.pi_pos] : Real.pi / 2 ≤ Real.pi))

/-- Closed form of the reflected direction of ray A: reflecting `d = (0, 1)` in
the radial normal `(sin θ, cos θ)` at `M(θ)` gives `d' = (−sin 2θ, −cos 2θ)` —
the ray turns back toward the aperture and toward the optical axis, deflected
by twice the incidence angle. -/
theorem reflectedDirA_eq (R θ : ℝ) (hR : 0 < R) :
    reflectedDirA R θ = !₂[-Real.sin (2 * θ), -Real.cos (2 * θ)] := by
  have inner_coords : ∀ u v : Plane, ⟪u, v⟫ = u 0 * v 0 + u 1 * v 1 := by
    intro u v
    rw [PiLp.inner_apply, Fin.sum_univ_two]
    simp [RCLike.inner_apply]
    ring
  have hinner : ⟪rayADir, outwardUnitNormal R (incidencePoint R θ)⟫ = Real.cos θ := by
    simp only [inner_coords, rayADir, outwardUnitNormal, incidencePoint, PiLp.smul_apply,
      smul_eq_mul, Matrix.cons_val_zero, Matrix.cons_val_one]
    rw [zero_mul, one_mul, zero_add, ← mul_assoc, inv_mul_cancel₀ hR.ne', one_mul]
  ext i
  simp only [reflectedDirA, specularReflect]
  rw [hinner]
  fin_cases i <;>
    simp only [PiLp.sub_apply, PiLp.smul_apply, smul_eq_mul, outwardUnitNormal,
      incidencePoint, rayADir, Matrix.cons_val_zero, Matrix.cons_val_one, Fin.reduceFinMk]
  · rw [Real.sin_two_mul]
    field_simp
    ring
  · rw [Real.cos_two_mul]
    field_simp
    ring

/-- Coordinate form of the reflected line of ray A:
`(x(t), y(t)) = (R sin θ − t sin 2θ, R cos θ − t cos 2θ)`. -/
theorem reflectedRayA_coords (R θ : ℝ) (hR : 0 < R) (t : ℝ) :
    reflectedRayA R θ t =
      !₂[R * Real.sin θ - t * Real.sin (2 * θ),
        R * Real.cos θ - t * Real.cos (2 * θ)] := by
  rw [reflectedRayA, reflectedDirA_eq R θ hR]
  ext i
  fin_cases i <;>
    simp only [incidencePoint, PiLp.add_apply, PiLp.smul_apply, smul_eq_mul,
      Matrix.cons_val_zero, Matrix.cons_val_one, Fin.reduceFinMk] <;>
    ring

/-- The reflected line of ray A is non-vertical for `0 < θ < π/2`, so it is
indeed the graph of an affine function `x ↦ m x + b`: the equation
`y = m_A x + b_A` of the problem exists. -/
theorem reflected_ray_A_has_line_equation (R θ : ℝ) (hR : 0 < R)
    (hθ : θ ∈ Set.Ioo 0 (Real.pi / 2)) :
    ∃ m b : ℝ, IsLineEquationOfReflectedRayA R θ m b := by
  obtain ⟨hθ0, hθ1⟩ := hθ
  have hs : Real.sin (2 * θ) ≠ 0 :=
    (Real.sin_pos_of_pos_of_lt_pi (by linarith) (by linarith)).ne'
  refine ⟨Real.cos (2 * θ) / Real.sin (2 * θ),
    R * Real.cos θ - (Real.cos (2 * θ) / Real.sin (2 * θ)) * (R * Real.sin θ), ?_⟩
  intro t
  rw [reflectedRayA_coords R θ hR t]
  simp only [xCoord, yCoord, Matrix.cons_val_zero, Matrix.cons_val_one]
  field_simp
  ring

/-- **T2-C1 re-derived inline (previous-part result).**  The slope and
`y`-intercept of the reflected ray A of Fig. 2g are `m_A = cot(2θ)` and
`b_A = R / (2 cos θ)`.  Since the reflected line is non-vertical on
`0 < θ < π/2`, a pair `(m, b)` satisfying `IsLineEquationOfReflectedRayA` is
uniquely determined, so this also records the characterization of the T2-C1
answer. -/
theorem slope_intercept_of_reflected_ray_A (R θ m b : ℝ) (hR : 0 < R)
    (hθ : θ ∈ Set.Ioo 0 (Real.pi / 2))
    (hline : IsLineEquationOfReflectedRayA R θ m b) :
    m = Real.cot (2 * θ) ∧ b = R / (2 * Real.cos θ) := by
  obtain ⟨hθ0, hθ1⟩ := hθ
  have hs : Real.sin (2 * θ) ≠ 0 :=
    (Real.sin_pos_of_pos_of_lt_pi (by linarith) (by linarith)).ne'
  have hsθ : Real.sin θ ≠ 0 :=
    (Real.sin_pos_of_pos_of_lt_pi hθ0 (by linarith [Real.pi_pos])).ne'
  have hc : Real.cos θ ≠ 0 :=
    (Real.cos_pos_of_mem_Ioo ⟨by linarith [Real.pi_pos], hθ1⟩).ne'
  have h0 := hline 0
  have h1 := hline 1
  rw [reflectedRayA_coords R θ hR 0] at h0
  rw [reflectedRayA_coords R θ hR 1] at h1
  simp only [xCoord, yCoord, Matrix.cons_val_zero, Matrix.cons_val_one] at h0 h1
  have h0' : R * Real.cos θ = m * (R * Real.sin θ) + b := by linear_combination h0
  have h1' : R * Real.cos θ - Real.cos (2 * θ)
      = m * (R * Real.sin θ - Real.sin (2 * θ)) + b := by linear_combination h1
  have hsub : m * Real.sin (2 * θ) = Real.cos (2 * θ) := by
    linear_combination h1' - h0'
  have hm : m = Real.cot (2 * θ) := by
    rw [Real.cot_eq_cos_div_sin, eq_div_iff hs]
    exact hsub
  have hb0 : b = R * Real.cos θ - m * (R * Real.sin θ) := by linear_combination -h0'
  have htrig : Real.sin (2 * θ) * Real.cos θ - Real.cos (2 * θ) * Real.sin θ
      = Real.sin θ := by
    rw [← Real.sin_sub (2 * θ) θ, show 2 * θ - θ = θ by ring]
  have hb1 : b = R * Real.sin θ / Real.sin (2 * θ) := by
    rw [eq_div_iff hs]
    linear_combination Real.sin (2 * θ) * hb0 - (R * Real.sin θ) * hsub + R * htrig
  have hb : b = R / (2 * Real.cos θ) := by
    rw [hb1, Real.sin_two_mul,
      div_eq_div_iff (mul_ne_zero (mul_ne_zero two_ne_zero hsθ) hc)
        (mul_ne_zero two_ne_zero hc)]
    ring
  exact ⟨hm, hb⟩

/-! ## Ray B bridges: everything is ray A evaluated at the shifted angle -/

/-- **Ray B is parallel to ray A** (the T2-C2 clause): the incoming directions
coincide. -/
theorem rayB_parallel_to_rayA : rayBDir = rayADir := rfl

/-- Ray B's reflected line is ray A's reflected line at the shifted incidence
angle `θ + Δθ` — the two rays share the same incoming direction and differ only
in where they strike the mirror. -/
theorem reflectedRayB_eq_reflectedRayA_shift (R θ Δθ t : ℝ) :
    reflectedRayB R θ Δθ t = reflectedRayA R (θ + Δθ) t := rfl

/-- Ray B strikes the mirror at `M(θ + Δθ)`: travelling straight up from its
base point, it reaches the impact point after covering the height
`R cos(θ + Δθ)`.  This is the "strikes the surface" clause of T2-C2. -/
theorem incomingRayB_reaches_mirror (R θ Δθ : ℝ) :
    incomingRayB R θ Δθ (R * Real.cos (θ + Δθ)) = incidencePointB R θ Δθ :=
  incomingRayA_reaches_mirror R (θ + Δθ)

/-- The impact point of ray B lies on the reflecting arc of Fig. 2g for
`θ + Δθ ∈ (0, π/2)`. -/
theorem incidencePointB_mem_arc (R θ Δθ : ℝ) (hR : 0 < R)
    (h : θ + Δθ ∈ Set.Ioo 0 (Real.pi / 2)) :
    incidencePointB R θ Δθ ∈ mirrorArc R :=
  incidencePoint_mem_arc R (θ + Δθ) hR h

/-- **Ray B strikes the surface at the angle `θ + Δθ`** (the T2-C2 clause):
the angle between the incoming direction and the normal at `M(θ + Δθ)` is
`θ + Δθ`. -/
theorem incidence_angle_rayB_eq (R θ Δθ : ℝ) (hR : 0 < R)
    (h : θ + Δθ ∈ Set.Icc 0 (Real.pi / 2)) :
    Real.arccos ⟪rayBDir, outwardUnitNormal R (incidencePointB R θ Δθ)⟫ = θ + Δθ :=
  incidence_angle_eq R (θ + Δθ) hR h

/-- The reflected line of ray B is non-vertical for `0 < θ + Δθ < π/2`, so its
equation `y = m_B x + b_B` exists. -/
theorem reflected_ray_B_has_line_equation (R θ Δθ : ℝ) (hR : 0 < R)
    (h : θ + Δθ ∈ Set.Ioo 0 (Real.pi / 2)) :
    ∃ m b : ℝ, IsLineEquationOfReflectedRayB R θ Δθ m b :=
  reflected_ray_A_has_line_equation R (θ + Δθ) hR h

/-- **Exact ray-B parameters (T2-C1 applied at `θ + Δθ`).**  The slope and
`y`-intercept of the reflected ray B are `m_B = cot(2(θ + Δθ))` and
`b_B = R / (2 cos(θ + Δθ))`.  This is the exact (unexpanded) form whose
first-order expansion in `Δθ` is the content of T2-C2. -/
theorem slope_intercept_of_reflected_ray_B (R θ Δθ m b : ℝ) (hR : 0 < R)
    (h : θ + Δθ ∈ Set.Ioo 0 (Real.pi / 2))
    (hline : IsLineEquationOfReflectedRayB R θ Δθ m b) :
    m = Real.cot (2 * (θ + Δθ)) ∧ b = R / (2 * Real.cos (θ + Δθ)) :=
  slope_intercept_of_reflected_ray_A R (θ + Δθ) m b hR h hline

/-! ## Slope and intercept as functions of the incidence angle; the T2-C2
first-order expansion in `Δθ` -/

/-- The reflected slope as a function of the incidence angle `φ`: the T2-C1
value `m_A = cot(2φ)`.  Dimensionless. -/
noncomputable def reflectedSlope (θ : ℝ) : ℝ := Real.cot (2 * θ)

/-- The reflected `y`-intercept as a function of the incidence angle `φ`: the
T2-C1 value `b_A = R / (2 cos φ)`.  Units: length. -/
noncomputable def reflectedIntercept (R θ : ℝ) : ℝ := R / (2 * Real.cos θ)

/-- **Derivative of the reflected slope** (the rigorous carrier of the T2-C2
first-order expansion of `m_B`): `d/dφ cot(2φ) = −2/sin²(2φ)`.  Proof route:
`Real.cot_eq_cos_div_sin`, then `HasDerivAt.div` of the chain-rule derivatives
(`Real.hasDerivAt_cos`/`Real.hasDerivAt_sin` composed with `2 * ·`), using
`Real.sin_sq_add_cos_sq` to simplify
`(−2 sin²(2θ) − 2 cos²(2θ))/sin²(2θ) = −2/sin²(2θ)`. -/
theorem hasDerivAt_reflectedSlope (θ : ℝ) (h : Real.sin (2 * θ) ≠ 0) :
    HasDerivAt reflectedSlope (-2 / Real.sin (2 * θ) ^ 2) θ := by
  have h1 : HasDerivAt (fun φ : ℝ => 2 * φ) 2 θ := by
    simpa using (hasDerivAt_id θ).const_mul (2 : ℝ)
  have hs : HasDerivAt (fun φ : ℝ => Real.sin (2 * φ)) (Real.cos (2 * θ) * 2) θ :=
    (Real.hasDerivAt_sin (2 * θ)).comp θ h1
  have hc : HasDerivAt (fun φ : ℝ => Real.cos (2 * φ)) (-Real.sin (2 * θ) * 2) θ :=
    (Real.hasDerivAt_cos (2 * θ)).comp θ h1
  have hfun : reflectedSlope = fun φ : ℝ => Real.cos (2 * φ) / Real.sin (2 * φ) := by
    funext φ
    exact Real.cot_eq_cos_div_sin (2 * φ)
  rw [hfun]
  have hdiv : HasDerivAt (fun φ : ℝ => Real.cos (2 * φ) / Real.sin (2 * φ))
      (((-Real.sin (2 * θ) * 2) * Real.sin (2 * θ)
        - Real.cos (2 * θ) * (Real.cos (2 * θ) * 2)) / Real.sin (2 * θ) ^ 2) θ :=
    hc.div hs h
  have hnum : (-Real.sin (2 * θ) * 2) * Real.sin (2 * θ)
      - Real.cos (2 * θ) * (Real.cos (2 * θ) * 2) = -2 := by
    have hsc := Real.sin_sq_add_cos_sq (2 * θ)
    linear_combination (-2 : ℝ) * hsc
  rw [hnum] at hdiv
  exact hdiv

/-- **Derivative of the reflected intercept** (the rigorous carrier of the
T2-C2 first-order expansion of `b_B`):
`d/dφ [R/(2 cos φ)] = R sin φ/(2 cos²φ)`.  Proof route:
`reflectedIntercept R = (R/2) • (Real.cos)⁻¹`, `HasDerivAt.inv` with
`Real.hasDerivAt_cos`, then `HasDerivAt.const_mul`. -/
theorem hasDerivAt_reflectedIntercept (R θ : ℝ) (h : Real.cos θ ≠ 0) :
    HasDerivAt (reflectedIntercept R) (R * Real.sin θ / (2 * Real.cos θ ^ 2)) θ := by
  have hfun : reflectedIntercept R = fun φ : ℝ => (R / 2) * (Real.cos φ)⁻¹ := by
    funext φ
    show R / (2 * Real.cos φ) = (R / 2) * (Real.cos φ)⁻¹
    rw [div_eq_mul_inv, div_eq_mul_inv, mul_inv, mul_assoc]
  have hc : HasDerivAt (fun φ : ℝ => (Real.cos φ)⁻¹) (-(-Real.sin θ) / Real.cos θ ^ 2) θ :=
    (Real.hasDerivAt_cos θ).inv h
  have hmul : HasDerivAt (fun φ : ℝ => (R / 2) * (Real.cos φ)⁻¹)
      ((R / 2) * (-(-Real.sin θ) / Real.cos θ ^ 2)) θ := hc.const_mul (R / 2)
  have hderiv : (R / 2) * (-(-Real.sin θ) / Real.cos θ ^ 2)
      = R * Real.sin θ / (2 * Real.cos θ ^ 2) := by
    rw [neg_neg, div_mul_div_comm]
  rw [hfun]
  rw [hderiv] at hmul
  exact hmul

/-- **T2-C2, first-order expansion of `m_B`** (little-o form):
`m(φ) = m(θ) + m'(θ)(φ − θ) + o(φ − θ)` with `m'(θ) = −2/sin²(2θ)`. -/
theorem reflectedSlope_first_order (θ : ℝ) (h : Real.sin (2 * θ) ≠ 0) :
    (fun φ => reflectedSlope φ - reflectedSlope θ
        - (φ - θ) • (-2 / Real.sin (2 * θ) ^ 2)) =o[𝓝 θ] fun φ => φ - θ :=
  hasDerivAt_iff_isLittleO.mp (hasDerivAt_reflectedSlope θ h)

/-- **T2-C2, first-order expansion of `b_B`** (little-o form):
`b(φ) = b(θ) + b'(θ)(φ − θ) + o(φ − θ)` with
`b'(θ) = R sin θ/(2 cos²θ)`. -/
theorem reflectedIntercept_first_order (R θ : ℝ) (h : Real.cos θ ≠ 0) :
    (fun φ => reflectedIntercept R φ - reflectedIntercept R θ
        - (φ - θ) • (R * Real.sin θ / (2 * Real.cos θ ^ 2))) =o[𝓝 θ] fun φ => φ - θ :=
  hasDerivAt_iff_isLittleO.mp (hasDerivAt_reflectedIntercept R θ h)

/-- **T2-C2 in the `Δθ` variable**: `m_B = m_A − (2/sin²(2θ)) Δθ + o(Δθ)`. -/
theorem reflectedSlope_first_order_Δ (θ : ℝ) (h : Real.sin (2 * θ) ≠ 0) :
    (fun Δθ => reflectedSlope (θ + Δθ) - reflectedSlope θ
        - Δθ • (-2 / Real.sin (2 * θ) ^ 2)) =o[𝓝 0] fun Δθ => Δθ := by
  have hg : Filter.Tendsto (fun Δθ : ℝ => θ + Δθ) (𝓝 0) (𝓝 θ) := by
    have h1 : Filter.Tendsto (fun _ : ℝ => θ) (𝓝 (0 : ℝ)) (𝓝 θ) := tendsto_const_nhds
    have h2 : Filter.Tendsto (fun Δθ : ℝ => Δθ) (𝓝 (0 : ℝ)) (𝓝 0) := Filter.tendsto_id
    simpa using h1.add h2
  have hcomp := (reflectedSlope_first_order θ h).comp_tendsto hg
  have eL : (fun Δθ : ℝ => reflectedSlope (θ + Δθ) - reflectedSlope θ
        - Δθ • (-2 / Real.sin (2 * θ) ^ 2))
      = (fun φ => reflectedSlope φ - reflectedSlope θ
          - (φ - θ) • (-2 / Real.sin (2 * θ) ^ 2)) ∘ (fun Δθ => θ + Δθ) := by
    funext Δθ
    simp only [Function.comp_apply, add_sub_cancel_left]
  have eR : (fun Δθ : ℝ => Δθ) = (fun φ : ℝ => φ - θ) ∘ (fun Δθ => θ + Δθ) := by
    funext Δθ
    simp only [Function.comp_apply, add_sub_cancel_left]
  rw [eL, eR]
  exact hcomp

/-- **T2-C2 in the `Δθ` variable**:
`b_B = b_A + (R sin θ/(2 cos²θ)) Δθ + o(Δθ)`. -/
theorem reflectedIntercept_first_order_Δ (R θ : ℝ) (h : Real.cos θ ≠ 0) :
    (fun Δθ => reflectedIntercept R (θ + Δθ) - reflectedIntercept R θ
        - Δθ • (R * Real.sin θ / (2 * Real.cos θ ^ 2))) =o[𝓝 0] fun Δθ => Δθ := by
  have hg : Filter.Tendsto (fun Δθ : ℝ => θ + Δθ) (𝓝 0) (𝓝 θ) := by
    have h1 : Filter.Tendsto (fun _ : ℝ => θ) (𝓝 (0 : ℝ)) (𝓝 θ) := tendsto_const_nhds
    have h2 : Filter.Tendsto (fun Δθ : ℝ => Δθ) (𝓝 (0 : ℝ)) (𝓝 0) := Filter.tendsto_id
    simpa using h1.add h2
  have hcomp := (reflectedIntercept_first_order R θ h).comp_tendsto hg
  have eL : (fun Δθ : ℝ => reflectedIntercept R (θ + Δθ) - reflectedIntercept R θ
        - Δθ • (R * Real.sin θ / (2 * Real.cos θ ^ 2)))
      = (fun φ => reflectedIntercept R φ - reflectedIntercept R θ
          - (φ - θ) • (R * Real.sin θ / (2 * Real.cos θ ^ 2))) ∘ (fun Δθ => θ + Δθ) := by
    funext Δθ
    simp only [Function.comp_apply, add_sub_cancel_left]
  have eR : (fun Δθ : ℝ => Δθ) = (fun φ : ℝ => φ - θ) ∘ (fun Δθ => θ + Δθ) := by
    funext Δθ
    simp only [Function.comp_apply, add_sub_cancel_left]
  rw [eL, eR]
  exact hcomp

/-! ## Intersection of the two reflected lines -/

/-- **The intersection condition**: a point `p` lies on both reflected lines
`y = m₁ x + b₁` (ray A) and `y = m₂ x + b₂` (ray B).  This is the "point of
intersection between the reflected rays of A and B" of the problem; the two
equations pin the coordinates without fixing any value. -/
def IsIntersectionPoint (m₁ b₁ m₂ b₂ : ℝ) (p : Plane) : Prop :=
  yCoord p = m₁ * xCoord p + b₁ ∧ yCoord p = m₂ * xCoord p + b₂

/-- The explicit intersection point of two non-parallel affine lines
`y = m₁ x + b₁` and `y = m₂ x + b₂`: solving the two equations gives
`x = (b₂ − b₁)/(m₁ − m₂)` and `y = (m₁ b₂ − m₂ b₁)/(m₁ − m₂)`. -/
noncomputable def lineIntersection (m₁ b₁ m₂ b₂ : ℝ) : Plane :=
  !₂[(b₂ - b₁) / (m₁ - m₂), (m₁ * b₂ - m₂ * b₁) / (m₁ - m₂)]

/-- The explicit intersection of two non-parallel lines lies on both lines. -/
theorem lineIntersection_isIntersectionPoint {m₁ b₁ m₂ b₂ : ℝ} (hm : m₁ ≠ m₂) :
    IsIntersectionPoint m₁ b₁ m₂ b₂ (lineIntersection m₁ b₁ m₂ b₂) := by
  have hm' : m₁ - m₂ ≠ 0 := sub_ne_zero.mpr hm
  constructor <;>
    simp only [xCoord, yCoord, lineIntersection, Matrix.cons_val_zero, Matrix.cons_val_one] <;>
    field_simp <;>
    ring

/-- The intersection point of two non-parallel lines is unique: from
`y = m₁ x + b₁ = m₂ x + b₂` at both points, `(m₁ − m₂)(x_p − x_q) = 0` forces
the `x`-coordinates (and then the `y`-coordinates) to agree. -/
theorem IsIntersectionPoint.unique {m₁ b₁ m₂ b₂ : ℝ} (hm : m₁ ≠ m₂) {p q : Plane}
    (hp : IsIntersectionPoint m₁ b₁ m₂ b₂ p) (hq : IsIntersectionPoint m₁ b₁ m₂ b₂ q) :
    p = q := by
  have hm' : m₁ - m₂ ≠ 0 := sub_ne_zero.mpr hm
  have hxp : (m₁ - m₂) * xCoord p = b₂ - b₁ := by linarith [hp.1, hp.2]
  have hxq : (m₁ - m₂) * xCoord q = b₂ - b₁ := by linarith [hq.1, hq.2]
  have hx : xCoord p = xCoord q := mul_left_cancel₀ hm' (by rw [hxp, hxq])
  have hy : yCoord p = yCoord q := by rw [hp.1, hq.1, hx]
  have hx' : p 0 = q 0 := hx
  have hy' : p 1 = q 1 := hy
  exact PiLp.ext (Fin.forall_fin_two.mpr ⟨hx', hy'⟩)

/-- **The two reflected rays are not parallel for `Δθ ≠ 0`**: their slopes
`cot(2θ)` and `cot(2(θ + Δθ))` differ.  Proof route: with
`u = 2θ`, `v = 2(θ + Δθ)`, both in `(0, π)`,
`cot u − cot v = sin(v − u)/(sin u sin v) = sin(2Δθ)/(sin u sin v)` from
`Real.cot_eq_cos_div_sin` and `Real.sin_sub`; the denominator is nonzero by
`Real.sin_pos_of_pos_of_lt_pi`, and `sin(2Δθ) ≠ 0` because `0 < |2Δθ| < π`
(from the `Ioo` hypotheses and `Real.sin_eq_zero_iff`). -/
theorem reflectedSlope_ne_of_ne (θ Δθ : ℝ) (hθ : θ ∈ Set.Ioo 0 (Real.pi / 2))
    (hΔ : θ + Δθ ∈ Set.Ioo 0 (Real.pi / 2)) (hΔ0 : Δθ ≠ 0) :
    reflectedSlope θ ≠ reflectedSlope (θ + Δθ) := by
  obtain ⟨hθ0, hθ1⟩ := hθ
  obtain ⟨hΔl, hΔu⟩ := hΔ
  intro heq
  have hsin1 : Real.sin (2 * θ) ≠ 0 :=
    (Real.sin_pos_of_pos_of_lt_pi (by linarith) (by linarith)).ne'
  have hsin2 : Real.sin (2 * (θ + Δθ)) ≠ 0 :=
    (Real.sin_pos_of_pos_of_lt_pi (by linarith) (by linarith)).ne'
  have heq' : Real.cot (2 * θ) = Real.cot (2 * (θ + Δθ)) := heq
  rw [Real.cot_eq_cos_div_sin, Real.cot_eq_cos_div_sin] at heq'
  have heq2 : Real.cos (2 * θ) * Real.sin (2 * (θ + Δθ))
      = Real.cos (2 * (θ + Δθ)) * Real.sin (2 * θ) := by
    rwa [div_eq_div_iff hsin1 hsin2] at heq'
  have hsin_diff : Real.sin (2 * (θ + Δθ) - 2 * θ) = 0 := by
    rw [Real.sin_sub]
    linarith [heq2]
  have h2 : 2 * (θ + Δθ) - 2 * θ = 2 * Δθ := by ring
  rw [h2] at hsin_diff
  have hbnd1 : -Real.pi < 2 * Δθ := by linarith [Real.pi_pos]
  have hbnd2 : 2 * Δθ < Real.pi := by linarith [Real.pi_pos]
  have hz : 2 * Δθ = 0 := (Real.sin_eq_zero_iff_of_lt_of_lt hbnd1 hbnd2).mp hsin_diff
  exact hΔ0 (by linarith)

/-- The reflected rays of A and B are not parallel for `Δθ ≠ 0`: any line
parameters `(m_A, b_A)`, `(m_B, b_B)` characterized by the line-equation
predicates have `m_A ≠ m_B`. -/
theorem reflected_rays_ne_parallel (R θ Δθ : ℝ) (hR : 0 < R)
    (hθ : θ ∈ Set.Ioo 0 (Real.pi / 2)) (hΔ : θ + Δθ ∈ Set.Ioo 0 (Real.pi / 2))
    (hΔ0 : Δθ ≠ 0) {mA bA mB bB : ℝ}
    (hA : IsLineEquationOfReflectedRayA R θ mA bA)
    (hB : IsLineEquationOfReflectedRayB R θ Δθ mB bB) : mA ≠ mB := by
  obtain ⟨hmA, -⟩ := slope_intercept_of_reflected_ray_A R θ mA bA hR hθ hA
  obtain ⟨hmB, -⟩ := slope_intercept_of_reflected_ray_B R θ Δθ mB bB hR hΔ hB
  rw [hmA, hmB]
  exact reflectedSlope_ne_of_ne θ Δθ hθ hΔ hΔ0

/-- **The intersection of the reflected rays exists** for `Δθ ≠ 0` (with both
impact points on the arc): the explicit `lineIntersection` serves as a witness.
This certifies that the hypotheses of the main theorem are satisfiable. -/
theorem exists_intersectionPoint_of_reflected_rays (R θ Δθ : ℝ) (hR : 0 < R)
    (hθ : θ ∈ Set.Ioo 0 (Real.pi / 2)) (hΔ : θ + Δθ ∈ Set.Ioo 0 (Real.pi / 2))
    (hΔ0 : Δθ ≠ 0) {mA bA mB bB : ℝ}
    (hA : IsLineEquationOfReflectedRayA R θ mA bA)
    (hB : IsLineEquationOfReflectedRayB R θ Δθ mB bB) :
    ∃ p : Plane, IsIntersectionPoint mA bA mB bB p :=
  ⟨lineIntersection mA bA mB bB,
    lineIntersection_isIntersectionPoint
      (reflected_rays_ne_parallel R θ Δθ hR hθ hΔ hΔ0 hA hB)⟩

/-! ## The caustic point: the T2-C3 target -/

/-- **The `x`-coordinate of the caustic point (the T2-C3 candidate)**:
`X_c = R sin³θ`, derived inline (module docstring) as
`−b'(θ)/m'(θ) = R sin θ sin²(2θ)/(4 cos²θ)`.  Units: length.  Appears only in
conclusions. -/
noncomputable def causticX (R θ : ℝ) : ℝ := R * Real.sin θ ^ 3

/-- **The `y`-coordinate of the caustic point (the T2-C3 candidate)**:
`Y_c = R cos θ (1 + 2 sin²θ)/2`, derived inline (module docstring) as
`m_A X_c + b_A`.  Units: length.  Appears only in conclusions. -/
noncomputable def causticY (R θ : ℝ) : ℝ := R * Real.cos θ * (1 + 2 * Real.sin θ ^ 2) / 2

/-- **The caustic point `(X_c, Y_c)`** in the coordinate system of Fig. 2g. -/
noncomputable def causticPoint (R θ : ℝ) : Plane := !₂[causticX R θ, causticY R θ]

/-- The intersection point of the two reflected lines as an explicit function
of `Δθ` (the raw end-to-end quantity of the problem): the `lineIntersection`
of the previous-part line parameters of rays A and B.  At `Δθ = 0` the two
lines coincide and this is `0/0`-indeterminate, which is why the limit is
taken over the punctured neighborhood `𝓝[≠] 0`. -/
noncomputable def reflectedRaysIntersection (R θ Δθ : ℝ) : Plane :=
  lineIntersection (reflectedSlope θ) (reflectedIntercept R θ)
    (reflectedSlope (θ + Δθ)) (reflectedIntercept R (θ + Δθ))

/-- **The computational core of T2-C3**: the explicit intersection of the
reflected lines converges, as `Δθ → 0` with `Δθ ≠ 0`, to the caustic point
`(R sin³θ, R cos θ (1 + 2 sin²θ)/2)`.  Proof route: the `x`-coordinate is
`(b(θ+Δθ) − b(θ))/(m(θ) − m(θ+Δθ))`, a ratio of difference quotients; by
`hasDerivAt_reflectedSlope`/`hasDerivAt_reflectedIntercept` (via
`hasDerivAt_iff_tendsto_slope`-style rewrite) it converges to
`−b'(θ)/m'(θ) = R sin θ sin²(2θ)/(4 cos²θ) = R sin³θ`
(`Real.sin_two_mul`); the `y`-coordinate `m(θ) x(Δθ) + b(θ)` then converges by
continuity to `cot(2θ) · R sin³θ + R/(2 cos θ) = R cos θ (1 + 2 sin²θ)/2`
(`Real.cot_eq_cos_div_sin`, `Real.cos_two_mul`, `Real.sin_sq_add_cos_sq`);
the two coordinate limits assemble by `tendsto_pi_nhds`. -/
theorem tendsto_reflectedRaysIntersection (R θ : ℝ) (hR : 0 < R)
    (hθ : θ ∈ Set.Ioo 0 (Real.pi / 2)) :
    Filter.Tendsto (reflectedRaysIntersection R θ) (𝓝[≠] 0) (𝓝 (causticPoint R θ)) := by
  obtain ⟨hθ0, hθ1⟩ := hθ
  have hsθ : Real.sin θ ≠ 0 :=
    (Real.sin_pos_of_pos_of_lt_pi hθ0 (by linarith [Real.pi_pos])).ne'
  have hs2 : Real.sin (2 * θ) ≠ 0 :=
    (Real.sin_pos_of_pos_of_lt_pi (by linarith) (by linarith)).ne'
  have hcθ : Real.cos θ ≠ 0 :=
    (Real.cos_pos_of_mem_Ioo ⟨by linarith [Real.pi_pos], hθ1⟩).ne'
  have hm := hasDerivAt_reflectedSlope θ hs2
  have hb := hasDerivAt_reflectedIntercept R θ hcθ
  have hm'ne : (-2 / Real.sin (2 * θ) ^ 2) ≠ 0 :=
    div_ne_zero (by norm_num) (pow_ne_zero 2 hs2)
  -- the shift `Δθ ↦ θ + Δθ` maps the punctured filter to the punctured filter
  have hg : Filter.Tendsto (fun Δθ : ℝ => θ + Δθ) (𝓝[≠] (0 : ℝ)) (𝓝[≠] θ) := by
    apply tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within
    · have h1 : Filter.Tendsto (fun Δθ : ℝ => θ + Δθ) (𝓝 (0 : ℝ)) (𝓝 (θ + 0)) :=
        tendsto_const_nhds.add Filter.tendsto_id
      rw [add_zero] at h1
      exact h1.mono_left nhdsWithin_le_nhds
    · filter_upwards [self_mem_nhdsWithin] with Δθ hΔ
      have hΔ0 : Δθ ≠ 0 := hΔ
      show θ + Δθ ≠ θ
      intro h
      exact hΔ0 (by linarith)
  -- difference quotients of slope and intercept converge to the derivatives
  have hmq : Filter.Tendsto
      (fun Δθ : ℝ => (reflectedSlope (θ + Δθ) - reflectedSlope θ) / Δθ)
      (𝓝[≠] 0) (𝓝 (-2 / Real.sin (2 * θ) ^ 2)) := by
    have h := (hasDerivAt_iff_tendsto_slope.mp hm).comp hg
    have hfun : (slope reflectedSlope θ) ∘ (fun Δθ : ℝ => θ + Δθ)
        = fun Δθ : ℝ => (reflectedSlope (θ + Δθ) - reflectedSlope θ) / Δθ := by
      funext Δθ
      simp only [Function.comp_apply, slope_def_field, add_sub_cancel_left]
    rw [hfun] at h
    exact h
  have hbq : Filter.Tendsto
      (fun Δθ : ℝ => (reflectedIntercept R (θ + Δθ) - reflectedIntercept R θ) / Δθ)
      (𝓝[≠] 0) (𝓝 (R * Real.sin θ / (2 * Real.cos θ ^ 2))) := by
    have h := (hasDerivAt_iff_tendsto_slope.mp hb).comp hg
    have hfun : (slope (reflectedIntercept R) θ) ∘ (fun Δθ : ℝ => θ + Δθ)
        = fun Δθ : ℝ => (reflectedIntercept R (θ + Δθ) - reflectedIntercept R θ) / Δθ := by
      funext Δθ
      simp only [Function.comp_apply, slope_def_field, add_sub_cancel_left]
    rw [hfun] at h
    exact h
  -- x-coordinate: ratio of difference quotients tends to `−b'(θ)/m'(θ)`
  have hXratio : Filter.Tendsto
      (fun Δθ : ℝ => ((reflectedIntercept R (θ + Δθ) - reflectedIntercept R θ) / Δθ) /
        (-((reflectedSlope (θ + Δθ) - reflectedSlope θ) / Δθ)))
      (𝓝[≠] 0)
      (𝓝 ((R * Real.sin θ / (2 * Real.cos θ ^ 2)) / (-(-2 / Real.sin (2 * θ) ^ 2)))) :=
    hbq.div hmq.neg (neg_ne_zero.mpr hm'ne)
  have hXeq : (fun Δθ : ℝ => ((reflectedIntercept R (θ + Δθ) - reflectedIntercept R θ) / Δθ) /
        (-((reflectedSlope (θ + Δθ) - reflectedSlope θ) / Δθ)))
      =ᶠ[𝓝[≠] 0] fun Δθ : ℝ => (reflectedIntercept R (θ + Δθ) - reflectedIntercept R θ) /
        (reflectedSlope θ - reflectedSlope (θ + Δθ)) := by
    filter_upwards [self_mem_nhdsWithin] with Δθ hΔ
    have hΔ0 : Δθ ≠ 0 := hΔ
    rw [div_neg, div_div_div_cancel_right₀ hΔ0, ← div_neg, neg_sub]
  have hX' : Filter.Tendsto
      (fun Δθ : ℝ => (reflectedIntercept R (θ + Δθ) - reflectedIntercept R θ) /
        (reflectedSlope θ - reflectedSlope (θ + Δθ)))
      (𝓝[≠] 0) (𝓝 (causticX R θ)) := by
    have hXval : (R * Real.sin θ / (2 * Real.cos θ ^ 2)) / (-(-2 / Real.sin (2 * θ) ^ 2))
        = causticX R θ := by
      show (R * Real.sin θ / (2 * Real.cos θ ^ 2)) / (-(-2 / Real.sin (2 * θ) ^ 2))
          = R * Real.sin θ ^ 3
      rw [neg_div, neg_neg, Real.sin_two_mul]
      field_simp
    have h := hXratio.congr' hXeq
    rwa [hXval] at h
  -- the denominator is nonzero eventually (slopes differ for `Δθ ≠ 0`)
  have hne_ev : ∀ᶠ Δθ in 𝓝[≠] (0 : ℝ), reflectedSlope θ ≠ reflectedSlope (θ + Δθ) := by
    have hIoo : Set.Ioo 0 (Real.pi / 2) ∈ 𝓝 θ := Ioo_mem_nhds hθ0 hθ1
    have ht : Filter.Tendsto (fun Δθ : ℝ => θ + Δθ) (𝓝 (0 : ℝ)) (𝓝 (θ + 0)) :=
      (continuous_const.add continuous_id).tendsto 0
    rw [add_zero] at ht
    have hIoo_ev : ∀ᶠ Δθ in 𝓝 (0 : ℝ), θ + Δθ ∈ Set.Ioo 0 (Real.pi / 2) :=
      ht.eventually hIoo
    filter_upwards [hIoo_ev.filter_mono nhdsWithin_le_nhds, self_mem_nhdsWithin]
      with Δθ hI h0
    have hΔ0 : Δθ ≠ 0 := h0
    exact reflectedSlope_ne_of_ne θ Δθ ⟨hθ0, hθ1⟩ hI hΔ0
  -- y-coordinate: `Y(Δθ) = m(θ) X(Δθ) + b(θ)` whenever the slopes differ
  have hYeq : (fun Δθ : ℝ => reflectedSlope θ *
          ((reflectedIntercept R (θ + Δθ) - reflectedIntercept R θ) /
            (reflectedSlope θ - reflectedSlope (θ + Δθ))) + reflectedIntercept R θ)
      =ᶠ[𝓝[≠] 0] fun Δθ : ℝ => (reflectedSlope θ * reflectedIntercept R (θ + Δθ) -
          reflectedSlope (θ + Δθ) * reflectedIntercept R θ) /
        (reflectedSlope θ - reflectedSlope (θ + Δθ)) := by
    filter_upwards [hne_ev] with Δθ hΔ
    have hne : reflectedSlope θ - reflectedSlope (θ + Δθ) ≠ 0 := sub_ne_zero.mpr hΔ
    field_simp
    ring
  have hYlim0 : Filter.Tendsto
      (fun Δθ : ℝ => reflectedSlope θ *
          ((reflectedIntercept R (θ + Δθ) - reflectedIntercept R θ) /
            (reflectedSlope θ - reflectedSlope (θ + Δθ))) + reflectedIntercept R θ)
      (𝓝[≠] 0) (𝓝 (reflectedSlope θ * causticX R θ + reflectedIntercept R θ)) :=
    (tendsto_const_nhds.mul hX').add tendsto_const_nhds
  have hY' : Filter.Tendsto
      (fun Δθ : ℝ => (reflectedSlope θ * reflectedIntercept R (θ + Δθ) -
          reflectedSlope (θ + Δθ) * reflectedIntercept R θ) /
        (reflectedSlope θ - reflectedSlope (θ + Δθ)))
      (𝓝[≠] 0) (𝓝 (causticY R θ)) := by
    have h2c : (2 : ℝ) * Real.cos θ ≠ 0 := mul_ne_zero two_ne_zero hcθ
    have h2sc : 2 * Real.sin θ * Real.cos θ ≠ 0 :=
      mul_ne_zero (mul_ne_zero two_ne_zero hsθ) hcθ
    have stepA : Real.cot (2 * θ) * (R * Real.sin θ ^ 3)
        = Real.cos (2 * θ) * (R * Real.sin θ ^ 2) / (2 * Real.cos θ) := by
      rw [Real.cot_eq_cos_div_sin, Real.sin_two_mul, div_mul_eq_mul_div,
        div_eq_div_iff h2sc h2c]
      ring
    have stepB : Real.cos (2 * θ) * (R * Real.sin θ ^ 2) / (2 * Real.cos θ)
        + R / (2 * Real.cos θ)
        = (Real.cos (2 * θ) * (R * Real.sin θ ^ 2) + R) / (2 * Real.cos θ) :=
      (add_div _ _ _).symm
    have stepC : (Real.cos (2 * θ) * (R * Real.sin θ ^ 2) + R) / (2 * Real.cos θ)
        = R * Real.cos θ * (1 + 2 * Real.sin θ ^ 2) / 2 := by
      rw [div_eq_div_iff h2c two_ne_zero, Real.cos_two_mul]
      linear_combination (-2 * R) * Real.sin_sq_add_cos_sq θ
    have hYval : reflectedSlope θ * causticX R θ + reflectedIntercept R θ
        = causticY R θ := by
      show Real.cot (2 * θ) * (R * Real.sin θ ^ 3) + R / (2 * Real.cos θ)
          = R * Real.cos θ * (1 + 2 * Real.sin θ ^ 2) / 2
      rw [stepA, stepB, stepC]
    have h := hYlim0.congr' hYeq
    rwa [hYval] at h
  -- assemble the two coordinate limits
  have hpi : Filter.Tendsto
      (fun Δθ : ℝ => ![(reflectedIntercept R (θ + Δθ) - reflectedIntercept R θ) /
            (reflectedSlope θ - reflectedSlope (θ + Δθ)),
          (reflectedSlope θ * reflectedIntercept R (θ + Δθ) -
            reflectedSlope (θ + Δθ) * reflectedIntercept R θ) /
            (reflectedSlope θ - reflectedSlope (θ + Δθ))])
      (𝓝[≠] 0) (𝓝 ![causticX R θ, causticY R θ]) := by
    rw [tendsto_pi_nhds]
    intro i
    fin_cases i
    · simpa only [Matrix.cons_val_zero, Matrix.cons_val_one, Fin.reduceFinMk] using hX'
    · simpa only [Matrix.cons_val_zero, Matrix.cons_val_one, Fin.reduceFinMk] using hY'
  have hcont : Continuous (WithLp.toLp 2 : (Fin 2 → ℝ) → Plane) :=
    PiLp.continuous_toLp 2 (fun _ : Fin 2 => ℝ)
  have h2 := (hcont.tendsto ![causticX R θ, causticY R θ]).comp hpi
  refine h2.congr fun Δθ => ?_
  rfl

/-- **Main target (T2-C3).**  Let ray A reflect with line `y = m_A x + b_A`
(any parameters satisfying the line-equation predicate), and for each
neighboring parallel ray B at incidence angle `θ + Δθ` let its reflected line
be `y = m_B(Δθ) x + b_B(Δθ)`.  If `P(Δθ)` is any point where the two reflected
lines meet (such points exist and are unique for `Δθ ≠ 0` by
`exists_intersectionPoint_of_reflected_rays` and `IsIntersectionPoint.unique`),
then as `Δθ → 0` the intersection converges to the caustic point
`(X_c, Y_c) = (R sin³θ, R cos θ (1 + 2 sin²θ)/2)`.

Proof route: the set `{Δθ | θ + Δθ ∈ (0, π/2)}` is a neighborhood of `0`
(preimage of `Ioo 0 (π/2) ∈ 𝓝 θ` under the continuous map `Δθ ↦ θ + Δθ`), and
on its punctured part `P(Δθ)` is forced to equal
`reflectedRaysIntersection R θ Δθ`: the line parameters are pinned by
`slope_intercept_of_reflected_ray_A` / `slope_intercept_of_reflected_ray_B`,
the lines are non-parallel by `reflected_rays_ne_parallel`, and the
intersection is unique by `IsIntersectionPoint.unique`.  Hence `P` is
eventually equal to `reflectedRaysIntersection R θ` on `𝓝[≠] 0`, and
`Filter.Tendsto.congr'` transfers `tendsto_reflectedRaysIntersection`. -/
theorem limiting_intersection_of_reflected_rays
    (R θ : ℝ) (hR : 0 < R) (hθ : θ ∈ Set.Ioo 0 (Real.pi / 2))
    (mA bA : ℝ) (hA : IsLineEquationOfReflectedRayA R θ mA bA)
    (mB bB : ℝ → ℝ)
    (hB : ∀ Δθ : ℝ, θ + Δθ ∈ Set.Ioo 0 (Real.pi / 2) →
      IsLineEquationOfReflectedRayB R θ Δθ (mB Δθ) (bB Δθ))
    (P : ℝ → Plane)
    (hP : ∀ Δθ : ℝ, θ + Δθ ∈ Set.Ioo 0 (Real.pi / 2) → Δθ ≠ 0 →
      IsIntersectionPoint mA bA (mB Δθ) (bB Δθ) (P Δθ)) :
    Filter.Tendsto P (𝓝[≠] 0) (𝓝 (causticPoint R θ)) := by
  have hθ0 : 0 < θ := hθ.1
  have hθ1 : θ < Real.pi / 2 := hθ.2
  obtain ⟨hmA, hbA⟩ := slope_intercept_of_reflected_ray_A R θ mA bA hR hθ hA
  have hIoo : Set.Ioo 0 (Real.pi / 2) ∈ 𝓝 θ := Ioo_mem_nhds hθ0 hθ1
  have ht : Filter.Tendsto (fun Δθ : ℝ => θ + Δθ) (𝓝 (0 : ℝ)) (𝓝 (θ + 0)) :=
    (continuous_const.add continuous_id).tendsto 0
  rw [add_zero] at ht
  have hIoo_ev : ∀ᶠ Δθ in 𝓝[≠] (0 : ℝ), θ + Δθ ∈ Set.Ioo 0 (Real.pi / 2) :=
    (ht.eventually hIoo).filter_mono nhdsWithin_le_nhds
  have hEq : reflectedRaysIntersection R θ =ᶠ[𝓝[≠] (0 : ℝ)] P := by
    filter_upwards [hIoo_ev, self_mem_nhdsWithin] with Δθ hI h0
    have hΔ0 : Δθ ≠ 0 := h0
    obtain ⟨hmB, hbB⟩ :=
      slope_intercept_of_reflected_ray_B R θ Δθ (mB Δθ) (bB Δθ) hR hI (hB Δθ hI)
    have hne : reflectedSlope θ ≠ reflectedSlope (θ + Δθ) :=
      reflectedSlope_ne_of_ne θ Δθ ⟨hθ0, hθ1⟩ hI hΔ0
    have hP' : IsIntersectionPoint (reflectedSlope θ) (reflectedIntercept R θ)
        (reflectedSlope (θ + Δθ)) (reflectedIntercept R (θ + Δθ)) (P Δθ) := by
      have h := hP Δθ hI hΔ0
      rw [hmA, hbA, hmB, hbB] at h
      exact h
    exact IsIntersectionPoint.unique hne (lineIntersection_isIntersectionPoint hne) hP'
  exact (tendsto_reflectedRaysIntersection R θ hR hθ).congr' hEq

/-- **Answer form (T2-C3), coordinatewise**: the limiting intersection
coordinates are `X_c = R sin³θ` and `Y_c = R cos θ (1 + 2 sin²θ)/2`, in terms
of `R` and `θ` as the problem requests.  Derived from
`limiting_intersection_of_reflected_rays` by continuity of the coordinate
projections (`PiLp.continuous_apply`). -/
theorem limiting_intersection_coordinates
    (R θ : ℝ) (hR : 0 < R) (hθ : θ ∈ Set.Ioo 0 (Real.pi / 2))
    (mA bA : ℝ) (hA : IsLineEquationOfReflectedRayA R θ mA bA)
    (mB bB : ℝ → ℝ)
    (hB : ∀ Δθ : ℝ, θ + Δθ ∈ Set.Ioo 0 (Real.pi / 2) →
      IsLineEquationOfReflectedRayB R θ Δθ (mB Δθ) (bB Δθ))
    (P : ℝ → Plane)
    (hP : ∀ Δθ : ℝ, θ + Δθ ∈ Set.Ioo 0 (Real.pi / 2) → Δθ ≠ 0 →
      IsIntersectionPoint mA bA (mB Δθ) (bB Δθ) (P Δθ)) :
    Filter.Tendsto (fun Δθ => xCoord (P Δθ)) (𝓝[≠] 0) (𝓝 (causticX R θ)) ∧
      Filter.Tendsto (fun Δθ => yCoord (P Δθ)) (𝓝[≠] 0) (𝓝 (causticY R θ)) := by
  have hmain := limiting_intersection_of_reflected_rays R θ hR hθ mA bA hA mB bB hB P hP
  have hc0 : Continuous fun p : Plane => p 0 :=
    PiLp.continuous_apply (ι := Fin 2) (p := 2) (β := fun _ : Fin 2 => ℝ) 0
  have hc1 : Continuous fun p : Plane => p 1 :=
    PiLp.continuous_apply (ι := Fin 2) (p := 2) (β := fun _ : Fin 2 => ℝ) 1
  constructor
  · have h := (hc0.tendsto (causticPoint R θ)).comp hmain
    simpa only [Function.comp_def, xCoord, causticPoint, Matrix.cons_val_zero,
      Matrix.cons_val_one, Fin.reduceFinMk] using h
  · have h := (hc1.tendsto (causticPoint R θ)).comp hmain
    simpa only [Function.comp_def, yCoord, causticPoint, Matrix.cons_val_zero,
      Matrix.cons_val_one, Fin.reduceFinMk] using h

/-- **Envelope content**: the limiting intersection point lies on the
reflected line of ray A itself — `Y_c = m_A X_c + b_A` — certifying that the
caustic point is the envelope contact point of the ray family.  Proof route:
rewrite `m`, `b` via `slope_intercept_of_reflected_ray_A`, unfold `causticX`,
`causticY`, then with `Real.cot_eq_cos_div_sin` and `field_simp`
(`sin 2θ ≠ 0`, `cos θ ≠ 0`) the identity reduces to
`R cos θ (1 + 2 sin²θ)/2 = R cos(2θ) sin²θ/(2 cos θ) + R/(2 cos θ)`, i.e.
`cos²θ (1 + 2 sin²θ) = 1 + cos(2θ) sin²θ`, which follows from
`Real.cos_two_mul`, `Real.sin_sq_add_cos_sq` and `ring`. -/
theorem causticPoint_mem_reflectedRayA_line (R θ m b : ℝ) (hR : 0 < R)
    (hθ : θ ∈ Set.Ioo 0 (Real.pi / 2)) (hA : IsLineEquationOfReflectedRayA R θ m b) :
    yCoord (causticPoint R θ) = m * xCoord (causticPoint R θ) + b := by
  have hθ0 : 0 < θ := hθ.1
  have hθ1 : θ < Real.pi / 2 := hθ.2
  obtain ⟨hm, hb⟩ := slope_intercept_of_reflected_ray_A R θ m b hR hθ hA
  have hsθ : Real.sin θ ≠ 0 :=
    (Real.sin_pos_of_pos_of_lt_pi hθ0 (by linarith [Real.pi_pos])).ne'
  have hcθ : Real.cos θ ≠ 0 :=
    (Real.cos_pos_of_mem_Ioo ⟨by linarith [Real.pi_pos], hθ1⟩).ne'
  have h2c : (2 : ℝ) * Real.cos θ ≠ 0 := mul_ne_zero two_ne_zero hcθ
  have h2sc : 2 * Real.sin θ * Real.cos θ ≠ 0 :=
    mul_ne_zero (mul_ne_zero two_ne_zero hsθ) hcθ
  have stepA : Real.cot (2 * θ) * (R * Real.sin θ ^ 3)
      = Real.cos (2 * θ) * (R * Real.sin θ ^ 2) / (2 * Real.cos θ) := by
    rw [Real.cot_eq_cos_div_sin, Real.sin_two_mul, div_mul_eq_mul_div,
      div_eq_div_iff h2sc h2c]
    ring
  have stepB : Real.cos (2 * θ) * (R * Real.sin θ ^ 2) / (2 * Real.cos θ)
      + R / (2 * Real.cos θ)
      = (Real.cos (2 * θ) * (R * Real.sin θ ^ 2) + R) / (2 * Real.cos θ) :=
    (add_div _ _ _).symm
  have stepC : (Real.cos (2 * θ) * (R * Real.sin θ ^ 2) + R) / (2 * Real.cos θ)
      = R * Real.cos θ * (1 + 2 * Real.sin θ ^ 2) / 2 := by
    rw [div_eq_div_iff h2c two_ne_zero, Real.cos_two_mul]
    linear_combination (-2 * R) * Real.sin_sq_add_cos_sq θ
  have hx : xCoord (causticPoint R θ) = causticX R θ := by
    simp only [xCoord, causticPoint, Matrix.cons_val_zero]
  have hy : yCoord (causticPoint R θ) = causticY R θ := by
    simp only [yCoord, causticPoint, Matrix.cons_val_zero, Matrix.cons_val_one]
  rw [hx, hy, hm, hb]
  show causticY R θ = Real.cot (2 * θ) * causticX R θ + R / (2 * Real.cos θ)
  show R * Real.cos θ * (1 + 2 * Real.sin θ ^ 2) / 2
      = Real.cot (2 * θ) * (R * Real.sin θ ^ 3) + R / (2 * Real.cos θ)
  rw [stepA, stepB, stepC]

/-- **Nephroid form of the caustic point** (equivalent parametrization):
`X_c = (R/4)(3 sin θ − sin 3θ)` and `Y_c = (R/4)(3 cos θ − cos 3θ)` — the
catacaustic of the circle for parallel rays is the 2-cusped epicycloid
(nephroid) of Fig. 2g's setting. -/
theorem causticPoint_trig_form (R θ : ℝ) :
    causticX R θ = R / 4 * (3 * Real.sin θ - Real.sin (3 * θ)) ∧
      causticY R θ = R / 4 * (3 * Real.cos θ - Real.cos (3 * θ)) := by
  constructor
  · rw [causticX, Real.sin_three_mul]
    ring
  · rw [causticY, Real.cos_three_mul]
    linear_combination R * Real.cos θ * Real.sin_sq_add_cos_sq θ

/-- The caustic curve of the half-cylindrical mirror for vertical parallel
rays: the curve traced by the limiting intersection point `(X_c, Y_c)` as the
incidence angle ranges over `(0, π/2)` — the envelope of the reflected rays
mentioned in the shared problem context. -/
noncomputable def causticCurve (R : ℝ) : Set Plane :=
  causticPoint R '' Set.Ioo 0 (Real.pi / 2)

/-- The caustic point of the ray at incidence angle `θ` lies on the caustic
curve. -/
theorem causticPoint_mem_causticCurve (R θ : ℝ) (hθ : θ ∈ Set.Ioo 0 (Real.pi / 2)) :
    causticPoint R θ ∈ causticCurve R :=
  ⟨θ, hθ, rfl⟩

end IPhO2026.T2C3
