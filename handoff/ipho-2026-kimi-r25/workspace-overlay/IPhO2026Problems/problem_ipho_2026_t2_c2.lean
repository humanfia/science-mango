import Mathlib

/-!
# IPhO 2026 · Theory problem T2-C2 — "Caustics and Cusp": reflected ray B to first order in `Δθ`

Autoformalization of IPhO 2026 T2-C2 (source:
`reports/ipho_2026/problem_ipho_2026_t2_c2.source.json`, figure
`ipho_2026_source/image/T2_page-4.png` (Fig. 2g, problem page 10)).

## Physical scenario (shared T2-C context, Fig. 2g)

Same half-cylindrical mirror and coordinate convention as T2-C1
(`problem_ipho_2026_t2_c1.lean`): the cross-section is the upper semicircle of
radius `R` centred at the origin `O`; the aperture is the diameter segment from
`(-R, 0)` to `(R, 0)` (the `-R` and `R` labels on the `x`-axis of Fig. 2g); the
`y`-axis is the optical axis.  Incoming rays are parallel to the optical axis
and travel in `+y`.  Ray A strikes at incidence angle `θ` and its reflected
line is `y = m_A x + b_A` (part T2-C1).

**Subquestion T2-C2.**  A ray B, parallel to ray A (hence with the same
incoming direction `rayBDir = (0, 1)`), strikes the surface at incidence angle
`θ + Δθ` with `Δθ ≪ θ`.  Its reflected line is `y = m_B x + b_B`.  Write `m_B`
and `b_B` in terms of `θ`, `Δθ`, `R`, approximating to first order in `Δθ`.
(The envelope/intersection of neighboring reflected rays — the caustic
mentioned in the shared context — is the subject of T2-C3/C4 and is not
formalized here; this part supplies the first-order expansions those parts
consume.)

## Physical model (governing laws)

1. *Straight-line propagation* (`incomingRayB`, `reflectedRayB`): before and
   after reflection ray B travels along straight lines.
2. *Law of specular reflection* at the circle (`specularReflect` with the
   radial outward unit normal `outwardUnitNormal`): the tangential direction
   component is preserved and the normal component flips sign
   (`specularReflect_normal_component_neg`).
3. *Line-equation readout*: `m_B`, `b_B` are characterized by
   `IsLineEquationOfReflectedRayB` — every point of the reflected line
   satisfies `y = m_B x + b_B`; the pair is unique because the reflected
   direction has nonzero `x`-component `−sin 2(θ + Δθ) ≠ 0` for
   `θ + Δθ ∈ (0, π/2)`.
4. *Previous-part result* (T2-C1, dependency policy
   `derive_inline_from_problem_only_material`): the reflected line of a ray
   parallel to the optical axis striking at incidence angle `φ` has slope
   `cot(2φ)` and intercept `R/(2 cos φ)`.  It is re-derived inline for
   `φ = θ + Δθ` as the bridge theorem
   `slope_intercept_of_reflected_ray_B_exact` (conclusion side, proved from
   laws 1–3, not assumed).
5. *"First order in `Δθ`"* is the asymptotic statement that the error of the
   affine-in-`Δθ` truncation is `o(Δθ)` as `Δθ → 0`
   (`Asymptotics.IsLittleO` over the filter `𝓝 0`), equivalently a
   `HasDerivAt` statement (Mathlib `hasDerivAt_iff_isLittleO`).  The physical
   hypothesis `Δθ ≪ θ` is the regime in which the truncation is useful and is
   represented by that limit filter.

## Derivation of the candidate (problem-side geometry + calculus only, answer-blind)

With `m(φ) = cot(2φ)` and `b(φ) = R/(2 cos φ)` from the T2-C1-level geometry
(laws 1–3), differentiation gives

* `dm/dφ = −2/sin²(2φ)` (from `cot = cos/sin` by the quotient rule and
  `sin² + cos² = 1`), hence `m_B = cot(2θ) − (2/sin²(2θ))·Δθ + o(Δθ)`;
* `db/dφ = R sin φ/(2 cos²φ)`, hence
  `b_B = R/(2 cos θ) + (R sin θ/(2 cos²θ))·Δθ + o(Δθ)`.

The candidate truncations are recorded as `slopeBFirstOrder` /
`interceptBFirstOrder`.  That these affine-in-`Δθ` expressions really are the
first-order expansions of the physically determined `m_B`, `b_B` is the
content of the main theorem `slope_intercept_of_reflected_ray_B_first_order`
(conclusion side only; no hypothesis, predicate field, or definition in this
file makes it true by unfolding).  Their zeroth-order terms are exactly `m_A`,
`b_A` of T2-C1, as consistency requires — ray B at `Δθ = 0` is ray A
(`incidencePointB_zero`, `slopeBFirstOrder_zero`, `interceptBFirstOrder_zero`).

## Orientation and branch information

* Ray B travels in `+y` before reflection (parallel to A; the upward arrows of
  Fig. 2g): `rayBDir = (0, 1)`.
* The impact point stays on the right half of the arc, as drawn, for
  `θ + Δθ ∈ (0, π/2)` (`incidencePointB_mem_arc`); the parametrization
  `M(θ + Δθ) = (R sin(θ + Δθ), R cos(θ + Δθ))` makes the marked incidence
  angle equal to `θ + Δθ` (`incidence_angle_B_eq`).
* The physical reflected ray is the forward branch `t > 0` of `reflectedRayB`;
  the equation `y = m_B x + b_B` of the problem describes the whole affine
  line, so `IsLineEquationOfReflectedRayB` quantifies over all `t : ℝ`.
* `Δθ` may have either sign (ray B on either side of A); the asymptotic
  statement is two-sided (`𝓝 0`), matching the limit `Δθ → 0` used later for
  the caustic in T2-C3.

## Units and uncertainty

`R`, `b_B`, `interceptBFirstOrder` and all point coordinates carry units of
length; `m_B`, `slopeBFirstOrder`, `θ`, `Δθ` and the expansion coefficient
`2/sin²(2θ)` are dimensionless; `R sin θ/(2 cos²θ)` has units of length.
The question asks for exact symbolic expressions, so no rounding rule applies;
the source reports no measurement uncertainties (uncertainty propagation: not
applicable — the `o(Δθ)` remainder is the truncation error of the mathematical
approximation, not a measurement uncertainty).

LeanExplore found no PhysLean ray-optics / law-of-reflection / caustic API
(queries recorded in the T2-C1 task result); as in T2-C1 the reflection law is
grounded in the Mathlib real inner product on `EuclideanSpace ℝ (Fin 2)`, and
the first-order expansion is grounded in Mathlib `HasDerivAt`,
`hasDerivAt_iff_isLittleO`, `Asymptotics.IsLittleO`, `Real.cot_eq_cos_div_sin`.
-/

namespace IPhO2026.T2C2

open scoped RealInnerProductSpace
open scoped Topology
open Asymptotics

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
concave side faces the aperture; the rim points are `(±R, 0)`. -/
noncomputable def mirrorArc (R : ℝ) : Set Plane :=
  {p | p ∈ mirrorCircle R ∧ 0 < yCoord p}

/-- The outward unit normal to the circle of radius `R` at a point `p` on it:
the radial direction `R⁻¹ • p`.  Unit length is certified by
`outwardUnitNormal_norm`. -/
noncomputable def outwardUnitNormal (R : ℝ) (p : Plane) : Plane := R⁻¹ • p

/-- **Law of specular reflection** (governing law 2), vector form: a ray with
direction `d` reflecting at a point with unit normal `n` acquires the direction
`d − 2⟪d, n⟫ • n`; the tangential component is preserved and the normal
component changes sign, i.e. the angle of incidence equals the angle of
reflection (`specularReflect_normal_component_neg`). -/
noncomputable def specularReflect (n d : Plane) : Plane := d - (2 * ⟪d, n⟫) • n

/-! ## Ray B: parallel to A, striking at incidence angle `θ + Δθ` -/

/-- Direction of ray B before reflection: `+y`, parallel to the optical axis —
ray B is parallel to ray A (the upward arrows of Fig. 2g). -/
noncomputable def rayBDir : Plane := !₂[(0 : ℝ), 1]

/-- Base point of ray B on the `x`-axis: `(R sin(θ + Δθ), 0)`, the foot of the
vertical incoming ray, directly below its impact point (the analogue for ray B
of the `A` label of Fig. 2g).  Units: length. -/
noncomputable def rayBBase (R θ Δθ : ℝ) : Plane := !₂[R * Real.sin (θ + Δθ), (0 : ℝ)]

/-- Impact point of ray B on the mirror: `M(θ + Δθ) = (R sin(θ + Δθ), R cos(θ + Δθ))`.
The radius `O M(θ + Δθ)` makes the angle `θ + Δθ` with the vertical incoming
ray, so the parametrized incidence angle is `θ + Δθ` as the problem states
(`incidence_angle_B_eq`). -/
noncomputable def incidencePointB (R θ Δθ : ℝ) : Plane :=
  !₂[R * Real.sin (θ + Δθ), R * Real.cos (θ + Δθ)]

/-- Ray B before reflection (governing law 1, straight-line propagation): the
vertical straight line through its base point, parametrized by the height; it
reaches the mirror at `t = R cos(θ + Δθ)` (`incomingRayB_reaches_mirror`). -/
noncomputable def incomingRayB (R θ Δθ t : ℝ) : Plane := rayBBase R θ Δθ + t • rayBDir

/-- Direction of ray B after its reflection at `M(θ + Δθ)`: the law of specular
reflection applied to `rayBDir` in the radial normal there. -/
noncomputable def reflectedDirB (R θ Δθ : ℝ) : Plane :=
  specularReflect (outwardUnitNormal R (incidencePointB R θ Δθ)) rayBDir

/-- The reflected line of ray B (governing law 1, straight-line propagation
after the reflection): the line through the impact point along
`reflectedDirB R θ Δθ`, parametrized by arc length `t`.  The physical reflected
ray is the forward branch `t > 0`; the equation `y = m_B x + b_B` of the
problem describes the whole affine line. -/
noncomputable def reflectedRayB (R θ Δθ t : ℝ) : Plane :=
  incidencePointB R θ Δθ + t • reflectedDirB R θ Δθ

/-! ## The equation `y = m_B x + b_B` of the reflected ray -/

/-- **`m_B`, `b_B` as defined by the problem**: the slope and `y`-intercept of
the reflected line of ray B — every point of the reflected line satisfies
`y = m_B x + b_B`.  `m_B` is dimensionless; `b_B` has units of length. -/
def IsLineEquationOfReflectedRayB (R θ Δθ m b : ℝ) : Prop :=
  ∀ t : ℝ, yCoord (reflectedRayB R θ Δθ t) = m * xCoord (reflectedRayB R θ Δθ t) + b

/-! ## Bridge lemmas: ray-B geometry (proofs deferred to the prover stage) -/

/-- The incoming direction of ray B is a unit vector. -/
theorem rayBDir_norm : ‖rayBDir‖ = 1 := by
  have norm_coords : ∀ p : Plane, ‖p‖ = Real.sqrt (p 0 ^ 2 + p 1 ^ 2) := by
    intro p
    rw [EuclideanSpace.norm_eq, Fin.sum_univ_two]
    simp [Real.norm_eq_abs, sq_abs]
  rw [rayBDir, norm_coords]
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

/-- The impact point of ray B lies on the reflecting arc of Fig. 2g (on the
right half for `0 < θ + Δθ < π/2`, as drawn). -/
theorem incidencePointB_mem_arc (R θ Δθ : ℝ) (hR : 0 < R)
    (hΔ : θ + Δθ ∈ Set.Ioo 0 (Real.pi / 2)) :
    incidencePointB R θ Δθ ∈ mirrorArc R := by
  obtain ⟨hΔ0, hΔ1⟩ := hΔ
  have norm_coords : ∀ p : Plane, ‖p‖ = Real.sqrt (p 0 ^ 2 + p 1 ^ 2) := by
    intro p
    rw [EuclideanSpace.norm_eq, Fin.sum_univ_two]
    simp [Real.norm_eq_abs, sq_abs]
  refine ⟨?_, ?_⟩
  · show ‖incidencePointB R θ Δθ‖ = R
    rw [incidencePointB, norm_coords]
    have hsq : (!₂[R * Real.sin (θ + Δθ), R * Real.cos (θ + Δθ)] : Plane) 0 ^ 2
        + (!₂[R * Real.sin (θ + Δθ), R * Real.cos (θ + Δθ)] : Plane) 1 ^ 2 = R ^ 2 := by
      simp only [Matrix.cons_val_zero, Matrix.cons_val_one]
      rw [mul_pow, mul_pow, ← mul_add, Real.sin_sq_add_cos_sq, mul_one]
    rw [hsq, Real.sqrt_sq hR.le]
  · show 0 < yCoord (incidencePointB R θ Δθ)
    simp only [yCoord, incidencePointB, Matrix.cons_val_one]
    exact mul_pos hR (Real.cos_pos_of_mem_Ioo ⟨by linarith [Real.pi_pos], hΔ1⟩)

/-- Ray B strikes the mirror at `M(θ + Δθ)`: travelling straight up from its
base point, it reaches `M(θ + Δθ)` after covering the height `R cos(θ + Δθ)`. -/
theorem incomingRayB_reaches_mirror (R θ Δθ : ℝ) :
    incomingRayB R θ Δθ (R * Real.cos (θ + Δθ)) = incidencePointB R θ Δθ := by
  ext i
  fin_cases i <;>
    simp only [incomingRayB, rayBBase, rayBDir, incidencePointB, PiLp.add_apply,
      PiLp.smul_apply, smul_eq_mul, Matrix.cons_val_zero, Matrix.cons_val_one,
      Fin.reduceFinMk] <;>
    ring

/-- **The parameter `θ + Δθ` is the angle of incidence of ray B** (the bridge
between the mirror parametrization and the problem's "strikes the surface at
an angle `θ + Δθ`"): the angle between the incident direction and the normal
at `M(θ + Δθ)`, measured with respect to the normal, is
`arccos (cos(θ + Δθ)) = θ + Δθ` on `[0, π/2]`. -/
theorem incidence_angle_B_eq (R θ Δθ : ℝ) (hR : 0 < R)
    (hΔ : θ + Δθ ∈ Set.Icc 0 (Real.pi / 2)) :
    Real.arccos ⟪rayBDir, outwardUnitNormal R (incidencePointB R θ Δθ)⟫ = θ + Δθ := by
  have inner_coords : ∀ u v : Plane, ⟪u, v⟫ = u 0 * v 0 + u 1 * v 1 := by
    intro u v
    rw [PiLp.inner_apply, Fin.sum_univ_two]
    simp [RCLike.inner_apply]
    ring
  have hinner : ⟪rayBDir, outwardUnitNormal R (incidencePointB R θ Δθ)⟫
      = Real.cos (θ + Δθ) := by
    simp only [inner_coords, rayBDir, outwardUnitNormal, incidencePointB, PiLp.smul_apply,
      smul_eq_mul, Matrix.cons_val_zero, Matrix.cons_val_one]
    rw [zero_mul, one_mul, zero_add, ← mul_assoc, inv_mul_cancel₀ hR.ne', one_mul]
  rw [hinner]
  exact Real.arccos_cos hΔ.1 (le_trans hΔ.2 (by linarith [Real.pi_pos] : Real.pi / 2 ≤ Real.pi))

/-- Closed form of the reflected direction of ray B: reflecting `d = (0, 1)` in
the radial normal `(sin(θ + Δθ), cos(θ + Δθ))` at `M(θ + Δθ)` gives
`d' = (−sin 2(θ + Δθ), −cos 2(θ + Δθ))` — the ray is deflected by twice the
incidence angle, toward the aperture and the optical axis. -/
theorem reflectedDirB_eq (R θ Δθ : ℝ) (hR : 0 < R) :
    reflectedDirB R θ Δθ =
      !₂[-Real.sin (2 * (θ + Δθ)), -Real.cos (2 * (θ + Δθ))] := by
  have inner_coords : ∀ u v : Plane, ⟪u, v⟫ = u 0 * v 0 + u 1 * v 1 := by
    intro u v
    rw [PiLp.inner_apply, Fin.sum_univ_two]
    simp [RCLike.inner_apply]
    ring
  have hinner : ⟪rayBDir, outwardUnitNormal R (incidencePointB R θ Δθ)⟫
      = Real.cos (θ + Δθ) := by
    simp only [inner_coords, rayBDir, outwardUnitNormal, incidencePointB, PiLp.smul_apply,
      smul_eq_mul, Matrix.cons_val_zero, Matrix.cons_val_one]
    rw [zero_mul, one_mul, zero_add, ← mul_assoc, inv_mul_cancel₀ hR.ne', one_mul]
  ext i
  simp only [reflectedDirB, specularReflect]
  rw [hinner]
  fin_cases i <;>
    simp only [PiLp.sub_apply, PiLp.smul_apply, smul_eq_mul, outwardUnitNormal,
      incidencePointB, rayBDir, Matrix.cons_val_zero, Matrix.cons_val_one, Fin.reduceFinMk]
  · rw [Real.sin_two_mul]
    field_simp
    ring
  · rw [Real.cos_two_mul]
    field_simp
    ring

/-- Coordinate form of the reflected line of ray B:
`(x(t), y(t)) = (R sin(θ + Δθ) − t sin 2(θ + Δθ), R cos(θ + Δθ) − t cos 2(θ + Δθ))`.
Direct carrier of the slope/intercept computation. -/
theorem reflectedRayB_coords (R θ Δθ : ℝ) (hR : 0 < R) (t : ℝ) :
    reflectedRayB R θ Δθ t =
      !₂[R * Real.sin (θ + Δθ) - t * Real.sin (2 * (θ + Δθ)),
        R * Real.cos (θ + Δθ) - t * Real.cos (2 * (θ + Δθ))] := by
  rw [reflectedRayB, reflectedDirB_eq R θ Δθ hR]
  ext i
  fin_cases i <;>
    simp only [incidencePointB, PiLp.add_apply, PiLp.smul_apply, smul_eq_mul,
      Matrix.cons_val_zero, Matrix.cons_val_one, Fin.reduceFinMk] <;>
    ring

/-- The reflected line of ray B is non-vertical for `0 < θ + Δθ < π/2` (its
horizontal direction component is `−sin 2(θ + Δθ) ≠ 0`), so it is the graph of
an affine function: the equation `y = m_B x + b_B` of the problem exists. -/
theorem reflected_ray_B_has_line_equation (R θ Δθ : ℝ) (hR : 0 < R)
    (hΔ : θ + Δθ ∈ Set.Ioo 0 (Real.pi / 2)) :
    ∃ m b : ℝ, IsLineEquationOfReflectedRayB R θ Δθ m b := by
  obtain ⟨hΔ0, hΔ1⟩ := hΔ
  have hs : Real.sin (2 * (θ + Δθ)) ≠ 0 :=
    (Real.sin_pos_of_pos_of_lt_pi (by linarith) (by linarith)).ne'
  refine ⟨Real.cos (2 * (θ + Δθ)) / Real.sin (2 * (θ + Δθ)),
    R * Real.cos (θ + Δθ)
      - (Real.cos (2 * (θ + Δθ)) / Real.sin (2 * (θ + Δθ))) * (R * Real.sin (θ + Δθ)), ?_⟩
  intro t
  rw [reflectedRayB_coords R θ Δθ hR t]
  simp only [xCoord, yCoord, Matrix.cons_val_zero, Matrix.cons_val_one]
  have key : ∀ (X₀ Y₀ c s : ℝ), s ≠ 0 →
      Y₀ - t * c = c / s * (X₀ - t * s) + (Y₀ - c / s * X₀) := by
    intro X₀ Y₀ c s hs0
    field_simp
    ring
  exact key _ _ _ _ hs

/-- At `Δθ = 0` ray B coincides with ray A: the impact point reduces to
`M(θ) = (R sin θ, R cos θ)` (the T2-C1 configuration).  Definitional sanity
check of the parametrization. -/
theorem incidencePointB_zero (R θ : ℝ) :
    incidencePointB R θ 0 = !₂[R * Real.sin θ, R * Real.cos θ] := by
  simp [incidencePointB]

/-! ## Previous-part bridge (T2-C1 applied to ray B): exact slope and intercept -/

/-- **Exact slope and intercept of ray B** (previous-part result of T2-C1
re-derived inline at incidence angle `θ + Δθ`, per the dependency policy
`derive_inline_from_problem_only_material`): any pair `(m, b)` satisfying
`IsLineEquationOfReflectedRayB R θ Δθ` obeys `m = cot(2(θ + Δθ))` and
`b = R/(2 cos(θ + Δθ))`; the pair is unique because the reflected line is
non-vertical.  Proof route: mirror of T2-C1's
`slope_intercept_of_reflected_ray_A` with `θ` replaced by `θ + Δθ` —
instantiate the line equation at `t = 0, 1`, subtract, and use
`Real.cot_eq_cos_div_sin`, `Real.sin_two_mul`. -/
theorem slope_intercept_of_reflected_ray_B_exact (R θ Δθ m b : ℝ) (hR : 0 < R)
    (hΔ : θ + Δθ ∈ Set.Ioo 0 (Real.pi / 2))
    (hline : IsLineEquationOfReflectedRayB R θ Δθ m b) :
    m = Real.cot (2 * (θ + Δθ)) ∧ b = R / (2 * Real.cos (θ + Δθ)) := by
  obtain ⟨hΔ0, hΔ1⟩ := hΔ
  have hs : Real.sin (2 * (θ + Δθ)) ≠ 0 :=
    (Real.sin_pos_of_pos_of_lt_pi (by linarith) (by linarith)).ne'
  have hsθ : Real.sin (θ + Δθ) ≠ 0 :=
    (Real.sin_pos_of_pos_of_lt_pi hΔ0 (by linarith [Real.pi_pos])).ne'
  have hc : Real.cos (θ + Δθ) ≠ 0 :=
    (Real.cos_pos_of_mem_Ioo ⟨by linarith [Real.pi_pos], hΔ1⟩).ne'
  have h0 := hline 0
  have h1 := hline 1
  rw [reflectedRayB_coords R θ Δθ hR 0] at h0
  rw [reflectedRayB_coords R θ Δθ hR 1] at h1
  simp only [xCoord, yCoord, Matrix.cons_val_zero, Matrix.cons_val_one] at h0 h1
  have h0' : R * Real.cos (θ + Δθ) = m * (R * Real.sin (θ + Δθ)) + b := by
    linear_combination h0
  have h1' : R * Real.cos (θ + Δθ) - Real.cos (2 * (θ + Δθ))
      = m * (R * Real.sin (θ + Δθ) - Real.sin (2 * (θ + Δθ))) + b := by
    linear_combination h1
  have hsub : m * Real.sin (2 * (θ + Δθ)) = Real.cos (2 * (θ + Δθ)) := by
    linear_combination h1' - h0'
  have hm : m = Real.cot (2 * (θ + Δθ)) := by
    rw [Real.cot_eq_cos_div_sin, eq_div_iff hs]
    exact hsub
  have hb0 : b = R * Real.cos (θ + Δθ) - m * (R * Real.sin (θ + Δθ)) := by
    linear_combination -h0'
  have htrig : Real.sin (2 * (θ + Δθ)) * Real.cos (θ + Δθ)
      - Real.cos (2 * (θ + Δθ)) * Real.sin (θ + Δθ) = Real.sin (θ + Δθ) := by
    rw [← Real.sin_sub (2 * (θ + Δθ)) (θ + Δθ), show 2 * (θ + Δθ) - (θ + Δθ) = θ + Δθ by ring]
  have hb1 : b = R * Real.sin (θ + Δθ) / Real.sin (2 * (θ + Δθ)) := by
    rw [eq_div_iff hs]
    linear_combination Real.sin (2 * (θ + Δθ)) * hb0 - (R * Real.sin (θ + Δθ)) * hsub
      + R * htrig
  have hb : b = R / (2 * Real.cos (θ + Δθ)) := by
    rw [hb1, Real.sin_two_mul,
      div_eq_div_iff (mul_ne_zero (mul_ne_zero two_ne_zero hsθ) hc)
        (mul_ne_zero two_ne_zero hc)]
    ring
  exact ⟨hm, hb⟩

/-! ## Candidate first-order expansions in `Δθ` (the answer to be justified) -/

/-- **Candidate first-order expansion of `m_B`** (derived answer-blind by
differentiating the exact T2-C1 slope `m(φ) = cot(2φ)`:
`dm/dφ = −2/sin²(2φ)` at `φ = θ`).  Dimensionless.  That this affine-in-`Δθ`
expression is the correct first-order truncation of the physical `m_B` is the
content of `slope_intercept_of_reflected_ray_B_first_order`, not of this
definition. -/
noncomputable def slopeBFirstOrder (θ Δθ : ℝ) : ℝ :=
  Real.cot (2 * θ) - (2 / (Real.sin (2 * θ)) ^ 2) * Δθ

/-- **Candidate first-order expansion of `b_B`** (derived answer-blind by
differentiating the exact T2-C1 intercept `b(φ) = R/(2 cos φ)`:
`db/dφ = R sin φ/(2 cos²φ)` at `φ = θ`).  Units: length.  That this
affine-in-`Δθ` expression is the correct first-order truncation of the
physical `b_B` is the content of
`slope_intercept_of_reflected_ray_B_first_order`, not of this definition. -/
noncomputable def interceptBFirstOrder (R θ Δθ : ℝ) : ℝ :=
  R / (2 * Real.cos θ) + (R * Real.sin θ / (2 * (Real.cos θ) ^ 2)) * Δθ

/-- Zeroth-order consistency: at `Δθ = 0` the candidate slope expansion reduces
to `m_A = cot(2θ)` of T2-C1 (ray B at `Δθ = 0` is ray A). -/
theorem slopeBFirstOrder_zero (θ : ℝ) :
    slopeBFirstOrder θ 0 = Real.cot (2 * θ) := by
  simp [slopeBFirstOrder]

/-- Zeroth-order consistency: at `Δθ = 0` the candidate intercept expansion
reduces to `b_A = R/(2 cos θ)` of T2-C1 (ray B at `Δθ = 0` is ray A). -/
theorem interceptBFirstOrder_zero (R θ : ℝ) :
    interceptBFirstOrder R θ 0 = R / (2 * Real.cos θ) := by
  simp [interceptBFirstOrder]

/-! ## Calculus carriers of the first-order expansion -/

/-- The slope of the reflected line, as a function `φ ↦ cot(2φ)` of the
incidence angle, has derivative `−2/sin²(2θ)` at `φ = θ`.  This is the
calculus content of the first-order expansion of `m_B` (via Mathlib
`hasDerivAt_iff_isLittleO`).  Proof route: `Real.cot_eq_cos_div_sin`, then the
quotient rule (`HasDerivAt.div` of `hasDerivAt_cos`/`hasDerivAt_sin` composed
with `2 * ·`), using `sin(2θ) ≠ 0` for `θ ∈ (0, π/2)`, and
`Real.sin_sq_add_cos_sq` to simplify the numerator. -/
theorem slope_B_hasDerivAt (θ : ℝ) (hθ : θ ∈ Set.Ioo 0 (Real.pi / 2)) :
    HasDerivAt (fun φ => Real.cot (2 * φ)) (-2 / (Real.sin (2 * θ)) ^ 2) θ := by
  obtain ⟨hθ0, hθ1⟩ := hθ
  have hs : Real.sin (2 * θ) ≠ 0 :=
    (Real.sin_pos_of_pos_of_lt_pi (by linarith) (by linarith)).ne'
  have h2 : HasDerivAt (fun φ : ℝ => 2 * φ) 2 θ := by
    simpa using (hasDerivAt_id θ).const_mul (2 : ℝ)
  have hcos : HasDerivAt (fun φ : ℝ => Real.cos (2 * φ)) (-Real.sin (2 * θ) * 2) θ :=
    (Real.hasDerivAt_cos (2 * θ)).comp θ h2
  have hsin : HasDerivAt (fun φ : ℝ => Real.sin (2 * φ)) (Real.cos (2 * θ) * 2) θ :=
    (Real.hasDerivAt_sin (2 * θ)).comp θ h2
  have hnum : -Real.sin (2 * θ) * 2 * Real.sin (2 * θ)
      - Real.cos (2 * θ) * (Real.cos (2 * θ) * 2) = -2 := by
    linear_combination -2 * Real.sin_sq_add_cos_sq (2 * θ)
  have hdiv : HasDerivAt (fun φ : ℝ => Real.cos (2 * φ) / Real.sin (2 * φ))
      ((-Real.sin (2 * θ) * 2 * Real.sin (2 * θ)
        - Real.cos (2 * θ) * (Real.cos (2 * θ) * 2)) / (Real.sin (2 * θ)) ^ 2) θ :=
    hcos.fun_div hsin hs
  rw [hnum] at hdiv
  simpa only [Real.cot_eq_cos_div_sin] using hdiv

/-- The intercept of the reflected line, as a function `φ ↦ R/(2 cos φ)` of
the incidence angle, has derivative `R sin θ/(2 cos²θ)` at `φ = θ`.  This is
the calculus content of the first-order expansion of `b_B`.  Proof route:
`HasDerivAt.div`/`HasDerivAt.const_mul` with `hasDerivAt_cos`, using
`cos θ ≠ 0` for `θ ∈ (0, π/2)`. -/
theorem intercept_B_hasDerivAt (R θ : ℝ) (hθ : θ ∈ Set.Ioo 0 (Real.pi / 2)) :
    HasDerivAt (fun φ => R / (2 * Real.cos φ))
      (R * Real.sin θ / (2 * (Real.cos θ) ^ 2)) θ := by
  obtain ⟨hθ0, hθ1⟩ := hθ
  have hc : Real.cos θ ≠ 0 :=
    (Real.cos_pos_of_mem_Ioo ⟨by linarith [Real.pi_pos], hθ1⟩).ne'
  have h2c : (2 : ℝ) * Real.cos θ ≠ 0 := mul_ne_zero two_ne_zero hc
  have hdiv : HasDerivAt (fun φ : ℝ => R / (2 * Real.cos φ))
      ((0 * (2 * Real.cos θ) - R * (2 * -Real.sin θ)) / (2 * Real.cos θ) ^ 2) θ :=
    (hasDerivAt_const (c := R) (x := θ)).fun_div
      ((Real.hasDerivAt_cos θ).const_mul 2) h2c
  have heq : (0 * (2 * Real.cos θ) - R * (2 * -Real.sin θ)) / (2 * Real.cos θ) ^ 2
      = R * Real.sin θ / (2 * (Real.cos θ) ^ 2) := by
    rw [div_eq_div_iff (pow_ne_zero 2 h2c) (mul_ne_zero two_ne_zero (pow_ne_zero 2 hc))]
    ring
  rw [heq] at hdiv
  exact hdiv

/-! ## Main target (T2-C2) -/

/-- **Main target (T2-C2).**  Let `mB δ`, `bB δ` be the slope and `y`-intercept
of the reflected line of ray B striking at incidence angle `θ + δ` (any
functions pinned by `IsLineEquationOfReflectedRayB` wherever ray B hits the
right half of the arc).  Then, to first order in `Δθ`,

* `m_B = cot(2θ) − (2/sin²(2θ))·Δθ` and
* `b_B = R/(2 cos θ) + (R sin θ/(2 cos²θ))·Δθ`,

in the precise sense that the errors of these affine truncations are `o(Δθ)`
as `Δθ → 0` (both signs of `Δθ`; the physical hypothesis `Δθ ≪ θ` is the
regime where the truncation is useful).  Proof route: on a neighborhood of
`δ = 0` one has `θ + δ ∈ (0, π/2)` (since `θ ∈ (0, π/2)` is open), so
`slope_intercept_of_reflected_ray_B_exact` identifies `mB δ = cot(2(θ + δ))`
and `bB δ = R/(2 cos(θ + δ))` eventually; then `slope_B_hasDerivAt` /
`intercept_B_hasDerivAt` and `hasDerivAt_iff_isLittleO` give the two
little-o statements (transported along `δ ↦ θ + δ`,
e.g. via `Asymptotics.IsLittleO.comp_tendsto`). -/
theorem slope_intercept_of_reflected_ray_B_first_order
    (R θ : ℝ) (hR : 0 < R) (hθ : θ ∈ Set.Ioo 0 (Real.pi / 2))
    (mB bB : ℝ → ℝ)
    (hline : ∀ δ : ℝ, θ + δ ∈ Set.Ioo 0 (Real.pi / 2) →
      IsLineEquationOfReflectedRayB R θ δ (mB δ) (bB δ)) :
    (fun δ : ℝ => mB δ - slopeBFirstOrder θ δ) =o[𝓝 (0 : ℝ)] (fun δ => δ) ∧
      (fun δ : ℝ => bB δ - interceptBFirstOrder R θ δ) =o[𝓝 (0 : ℝ)] (fun δ => δ) := by
  have hcont : Filter.Tendsto (fun δ : ℝ => θ + δ) (𝓝 (0 : ℝ)) (𝓝 θ) := by
    have hc : Continuous (fun δ : ℝ => θ + δ) := continuous_const.add continuous_id
    simpa using hc.tendsto (0 : ℝ)
  have hpre : ∀ᶠ δ in 𝓝 (0 : ℝ), θ + δ ∈ Set.Ioo 0 (Real.pi / 2) :=
    hcont.eventually (isOpen_Ioo.mem_nhds hθ)
  constructor
  · have h := hasDerivAt_iff_isLittleO_nhds_zero.mp (slope_B_hasDerivAt θ hθ)
    refine h.congr' ?_ (Filter.Eventually.of_forall fun _ => rfl)
    filter_upwards [hpre] with δ hδ
    obtain ⟨hm, -⟩ := slope_intercept_of_reflected_ray_B_exact R θ δ (mB δ) (bB δ) hR hδ
      (hline δ hδ)
    rw [hm]
    simp only [slopeBFirstOrder, smul_eq_mul]
    ring
  · have h := hasDerivAt_iff_isLittleO_nhds_zero.mp (intercept_B_hasDerivAt R θ hθ)
    refine h.congr' ?_ (Filter.Eventually.of_forall fun _ => rfl)
    filter_upwards [hpre] with δ hδ
    obtain ⟨-, hb⟩ := slope_intercept_of_reflected_ray_B_exact R θ δ (mB δ) (bB δ) hR hδ
      (hline δ hδ)
    rw [hb]
    simp only [interceptBFirstOrder, smul_eq_mul]
    ring

end IPhO2026.T2C2
