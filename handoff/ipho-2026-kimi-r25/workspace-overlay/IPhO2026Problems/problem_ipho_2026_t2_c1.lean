import Mathlib

/-!
# IPhO 2026 · Theory problem T2-C1 — "Caustics and Cusp": equation of reflected ray A

Autoformalization of IPhO 2026 T2-C1 (source:
`reports/ipho_2026/problem_ipho_2026_t2_c1.source.json`, figure
`ipho_2026_source/image/T2_page-4.png` (Fig. 2g, problem page 10)).

## Physical scenario (shared T2-C context, Fig. 2g)

Same half-cylindrical mirror as in T2-A/T2-B (`problem_ipho_2026_t2_a1.lean`,
`problem_ipho_2026_t2_b1.lean`): the cross-section is the upper semicircle of
radius `R` centred at the origin `O`; the aperture is the diameter segment from
`(-R, 0)` to `(R, 0)` (the `-R` and `R` labels on the `x`-axis of Fig. 2g); the
`y`-axis is the optical axis.  Ray A is parallel to the optical axis and travels
in the `+y` direction (upward arrows of Fig. 2g) from its base point
`A = (R sin θ, 0)` on the `x`-axis (the `A` label of Fig. 2g) and strikes the
concave side of the mirror at `M(θ) = (R sin θ, R cos θ)`.  The angle `θ` marked
in Fig. 2g is the angle between the radius `O M(θ)` (dashed; the normal at the
impact point) and the vertical incoming ray — i.e. the angle of incidence
(`incidence_angle_eq`).  The reflected ray is described, in the coordinate
system of Fig. 2g, by the equation `y = m_A x + b_A` (the label on the reflected
line in Fig. 2g).  The shared context also mentions a neighboring parallel ray B
striking at `θ + Δθ` with `Δθ ≪ θ`, whose intersection with ray A builds the
caustic; ray B and `Δθ` belong to parts T2-C2–C4 and are formalized there, not
here.

**Subquestion T2-C1.** Write `m_A` and `b_A` in terms of `θ` and `R`.  Hint
(problem statement): the expected form is `m_A = K₁ cot(K₂ θ)` and
`b_A = R K₃ / cos(K₄ θ)` with `Kᵢ` numerical constants.

## Physical model (governing laws)

1. *Straight-line propagation* (`incomingRayA`, `reflectedRayA`): before and
   after the reflection the ray travels along straight lines.
2. *Law of specular reflection* at the circle (`specularReflect`): with unit
   normal `n` the direction `d` becomes `d − 2⟪d, n⟫ • n` — the tangential
   component is preserved and the normal component flips sign, i.e. the angle of
   incidence equals the angle of reflection
   (`specularReflect_normal_component_neg`); the outward unit normal at a point
   `p` of the circle is radial, `n = R⁻¹ • p` (`outwardUnitNormal`).
3. *Line-equation readout*: `m_A`, `b_A` are characterized by the reflected
   line satisfying `y = m_A x + b_A` at every one of its points
   (`IsLineEquationOfReflectedRayA`).  The pair is unique because the reflected
   direction has nonzero `x`-component `−sin 2θ ≠ 0` for `θ ∈ (0, π/2)`.

## Derivation of the candidate (problem-side geometry only, answer-blind)

Reflecting `d = (0, 1)` in the radial normal `(sin θ, cos θ)` at `M(θ)` gives
the reflected direction `d'(θ) = (−sin 2θ, −cos 2θ)` (`reflectedDirA_eq`), so
the reflected line is `(x(t), y(t)) = (R sin θ − t sin 2θ, R cos θ − t cos 2θ)`
(`reflectedRayA_coords`).  Its slope is
`Δy/Δx = (−cos 2θ)/(−sin 2θ) = cot 2θ`, and its `y`-intercept computes to
`b = R cos θ − cot 2θ · R sin θ = R sin θ / sin 2θ = R / (2 cos θ)`.  The
candidate is therefore **`m_A = cot(2θ)` and `b_A = R / (2 cos θ)`** — in the
hint's form, `K₁ = 1`, `K₂ = 2`, `K₃ = 1/2`, `K₄ = 1` (main target
`slope_intercept_of_reflected_ray_A`, recorded in answer form as
`slope_intercept_of_reflected_ray_A_hint_form`).  No hypothesis, predicate, or
definition in this file assumes the target relation: `m`, `b` enter only as
universally quantified variables constrained by `IsLineEquationOfReflectedRayA`,
and the closed forms appear only in theorem conclusions.

## Orientation and branch information

* Ray A travels in `+y` before reflection (Fig. 2g arrows): `rayADir = (0, 1)`.
* The impact point is on the right half of the arc (`θ ∈ (0, π/2)`;
  `incidencePoint_mem_arc`), matching Fig. 2g where `A` lies between `O` and
  `R`.
* The physical reflected ray is the forward branch `t > 0` of `reflectedRayA`;
  the equation `y = m_A x + b_A` of the problem is a statement about the whole
  affine line, so `IsLineEquationOfReflectedRayA` quantifies over all `t : ℝ`.
  No sign/branch choice is made in the conclusions: the direction of travel is
  fixed by `rayADir` and the reflection law, not selected by the answer.

## Units and uncertainty

`R`, `b_A` and all point coordinates carry units of length (kept symbolic as
real numbers); `m_A`, the `Kᵢ` and `θ` are dimensionless.  The question asks for
exact symbolic expressions, so no rounding rule applies; the source reports no
measurement uncertainties (uncertainty propagation: not applicable).

LeanExplore found no PhysLean ray-optics / law-of-reflection / caustic API
(queries recorded in the task result); the reflection law is grounded in the
Mathlib real inner product `⟪·, ·⟫` on `EuclideanSpace ℝ (Fin 2)`, following
`problem_ipho_2026_t2_a1.lean` / `problem_ipho_2026_t2_b1.lean` (cf. Mathlib
`Submodule.reflection`, `Real.cot_eq_cos_div_sin`, `Real.sin_two_mul`,
`Real.arccos_cos`).
-/

namespace IPhO2026.T2C1

open scoped RealInnerProductSpace

/-! ## The cross-sectional plane and Figure 2g geometry -/

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
`problem_ipho_2026_t2_a1.lean` and `problem_ipho_2026_t2_b1.lean`. -/
noncomputable def mirrorArc (R : ℝ) : Set Plane :=
  {p | p ∈ mirrorCircle R ∧ 0 < yCoord p}

/-- Base point `A` of ray A on the `x`-axis (the `A` label of Fig. 2g):
`(R sin θ, 0)`, the foot of the vertical incoming ray, directly below the
impact point.  Units: length. -/
noncomputable def rayABase (R θ : ℝ) : Plane := !₂[R * Real.sin θ, (0 : ℝ)]

/-- Impact point of ray A on the mirror: `M(θ) = (R sin θ, R cos θ)`.  The
radius `O M(θ)` (dashed in Fig. 2g) makes the angle `θ` with the vertical
incoming ray, so the marked angle of Fig. 2g is the angle of incidence
(`incidence_angle_eq`). -/
noncomputable def incidencePoint (R θ : ℝ) : Plane := !₂[R * Real.sin θ, R * Real.cos θ]

/-- The outward unit normal to the circle of radius `R` at a point `p` on it:
the radial direction `R⁻¹ • p`.  Unit length is certified by
`outwardUnitNormal_norm`. -/
noncomputable def outwardUnitNormal (R : ℝ) (p : Plane) : Plane := R⁻¹ • p

/-- Direction of ray A before reflection: `+y`, parallel to the optical axis
(the upward arrows of Fig. 2g). -/
noncomputable def rayADir : Plane := !₂[(0 : ℝ), 1]

/-- Ray A before reflection (governing law 1, straight-line propagation): the
vertical straight line through its base point `A`, parametrized by the height;
it reaches the mirror at `t = R cos θ` (`incomingRayA_reaches_mirror`). -/
noncomputable def incomingRayA (R θ t : ℝ) : Plane := rayABase R θ + t • rayADir

/-! ## Governing law: specular reflection at the circle -/

/-- **Law of specular reflection** (governing law 2), vector form: a ray with
direction `d` reflecting at a point with unit normal `n` acquires the direction
`d − 2⟪d, n⟫ • n`; the tangential component is preserved and the normal
component changes sign, i.e. the angle of incidence equals the angle of
reflection (`specularReflect_normal_component_neg`).  Grounded in the Mathlib
inner product; this is the explicit form of the hyperplane reflection
`Submodule.reflection (ℝ ∙ n)ᗮ`. -/
noncomputable def specularReflect (n d : Plane) : Plane := d - (2 * ⟪d, n⟫) • n

/-- Direction of ray A after its reflection at `M(θ)`: the law of specular
reflection applied to `rayADir` in the radial normal there. -/
noncomputable def reflectedDirA (R θ : ℝ) : Plane :=
  specularReflect (outwardUnitNormal R (incidencePoint R θ)) rayADir

/-- The reflected line of ray A (governing law 1, straight-line propagation
after the reflection): the line through the impact point `M(θ)` along
`reflectedDirA R θ`, parametrized by arc length `t`.  The physical reflected
ray is the forward branch `t > 0`; the equation `y = m_A x + b_A` of the
problem describes the whole affine line. -/
noncomputable def reflectedRayA (R θ t : ℝ) : Plane :=
  incidencePoint R θ + t • reflectedDirA R θ

/-! ## The equation `y = m_A x + b_A` of the reflected ray -/

/-- **`m_A`, `b_A` as defined by the problem** (the equation label of Fig. 2g):
the slope and `y`-intercept of the reflected line of ray A — every point of the
reflected line satisfies `y = m_A x + b_A`.  `m_A` is dimensionless; `b_A` has
units of length. -/
def IsLineEquationOfReflectedRayA (R θ m b : ℝ) : Prop :=
  ∀ t : ℝ, yCoord (reflectedRayA R θ t) = m * xCoord (reflectedRayA R θ t) + b

/-! ## Bridge lemmas (proofs deferred to the prover stage) -/

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
point `A`, it reaches `M(θ)` after covering the height `R cos θ`.  Together
with `incidencePoint_mem_arc` this is the "strikes the mirror" clause of the
problem statement. -/
theorem incomingRayA_reaches_mirror (R θ : ℝ) :
    incomingRayA R θ (R * Real.cos θ) = incidencePoint R θ := by
  ext i
  fin_cases i <;>
    simp only [incomingRayA, rayABase, rayADir, incidencePoint, PiLp.add_apply,
      PiLp.smul_apply, smul_eq_mul, Matrix.cons_val_zero, Matrix.cons_val_one,
      Fin.reduceFinMk] <;>
    ring

/-- **The parameter `θ` is the angle of incidence** (the bridge between the
mirror parametrization and the marked angle of Fig. 2g): the angle between the
incident direction and the normal at `M(θ)`, measured with respect to the
normal as the problem requires, is `arccos (cos θ) = θ` on `[0, π/2]`.
Proof route: `⟪rayADir, outwardUnitNormal R (M θ)⟫ = cos θ` by direct
computation, then `Real.arccos_cos`. -/
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
by twice the incidence angle.  Proof route: unfold `reflectedDirA`,
`specularReflect`, `outwardUnitNormal`, `incidencePoint`; use
`Real.sin_two_mul`, `Real.cos_two_mul` and `hR` for the `R⁻¹ R` cancellation. -/
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
`(x(t), y(t)) = (R sin θ − t sin 2θ, R cos θ − t cos 2θ)`.  Direct carrier of
the slope/intercept computation; follows from `reflectedDirA_eq`. -/
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

/-- The reflected line of ray A is non-vertical for `0 < θ < π/2` (its
horizontal direction component is `−sin 2θ ≠ 0`), so it is indeed the graph of
an affine function `x ↦ m x + b`: the equation `y = m_A x + b_A` of the problem
exists.  Proof route: `reflectedRayA_coords`, then
`m := Real.cos (2*θ) / Real.sin (2*θ)`, `b := y(0) − m·x(0)`; the required
identity holds by `field_simp` with `Real.sin_pos_of_pos_of_lt_pi` and `ring`. -/
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

/-! ## Main target (T2-C1) -/

/-- **Main target (T2-C1).**  The slope and `y`-intercept of the reflected ray
A of Fig. 2g are `m_A = cot(2θ)` and `b_A = R / (2 cos θ)`.  Since the
reflected line has nonzero horizontal direction (`−sin 2θ ≠ 0` on
`0 < θ < π/2`), a pair `(m, b)` satisfying `IsLineEquationOfReflectedRayA` is
uniquely determined, so this theorem also records the characterization of the
answer.  Proof route: instantiate `hline` at `t = 0` and `t = 1`, subtract to
obtain `m = (−cos 2θ)/(−sin 2θ) = cot 2θ` (`Real.cot_eq_cos_div_sin`), then
`b = y(0) − m·x(0) = R cos θ − cot 2θ · R sin θ = R sin θ / sin 2θ
= R / (2 cos θ)` (`Real.sin_two_mul`). -/
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

/-- **Answer form (T2-C1 hint).**  In the format requested by the problem
statement, `m_A = K₁ cot(K₂ θ)` and `b_A = R K₃ / cos(K₄ θ)`, the numerical
constants are `K₁ = 1`, `K₂ = 2`, `K₃ = 1/2`, `K₄ = 1`.  Restatement of
`slope_intercept_of_reflected_ray_A` (multiply by `1`, `1/2`). -/
theorem slope_intercept_of_reflected_ray_A_hint_form (R θ m b : ℝ) (hR : 0 < R)
    (hθ : θ ∈ Set.Ioo 0 (Real.pi / 2))
    (hline : IsLineEquationOfReflectedRayA R θ m b) :
    m = (1 : ℝ) * Real.cot ((2 : ℝ) * θ) ∧
      b = R * (1 / 2 : ℝ) / Real.cos ((1 : ℝ) * θ) := by
  obtain ⟨hm, hb⟩ := slope_intercept_of_reflected_ray_A R θ m b hR hθ hline
  obtain ⟨hθ0, hθ1⟩ := hθ
  have hc : Real.cos θ ≠ 0 :=
    (Real.cos_pos_of_mem_Ioo ⟨by linarith [Real.pi_pos], hθ1⟩).ne'
  refine ⟨?_, ?_⟩
  · rw [hm, one_mul]
  · rw [hb, one_mul, div_eq_div_iff (mul_ne_zero two_ne_zero hc) hc]
    ring

end IPhO2026.T2C1
