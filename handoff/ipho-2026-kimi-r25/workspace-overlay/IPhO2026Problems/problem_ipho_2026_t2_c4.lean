import Mathlib

/-!
# IPhO 2026 · Theory problem T2-C4 — "Caustics and Cusp": small-`θ` cusp form of the caustic

Autoformalization of IPhO 2026 T2-C4 (source:
`reports/ipho_2026/problem_ipho_2026_t2_c4.source.json`, figure
`ipho_2026_source/image/T2_page-4.png` (Fig. 2g, problem page 10)).

## Physical scenario (shared T2-C context, Fig. 2g)

Same half-cylindrical mirror and coordinate convention as T2-C1–T2-C3
(`problem_ipho_2026_t2_c1.lean`, `problem_ipho_2026_t2_c2.lean`): the
cross-section is the upper semicircle of radius `R` centred at the origin `O`;
the aperture is the diameter segment from `(-R, 0)` to `(R, 0)`; the `y`-axis is
the optical axis.  Incoming rays are parallel to the optical axis and travel in
`+y`.  Ray A strikes at incidence angle `θ` and its reflected line is
`y = m_A x + b_A`; a neighboring parallel ray B strikes at `θ + Δθ`
(`Δθ ≪ θ`) with reflected line `y = m_B x + b_B`.  The envelope — equivalently
the limiting intersection point of the reflected lines of A and B as `Δθ → 0` —
is the caustic point `(X_c, Y_c)` (part T2-C3).

**Subquestion T2-C4.** For `θ ≪ 1` the caustic has the cusp form
`Y_c = v · |X_c|^(p/q) + u`.  Write `v` and `u` in terms of `R` and find the
integers `p` and `q` (equivalently, the rational number `p/q`).

## Physical model (governing laws)

1. *Straight-line propagation* (`reflectedRay`): before and after reflection
   each ray travels along a straight line.
2. *Law of specular reflection* at the circle (`specularReflect` with the
   radial outward unit normal `outwardUnitNormal`): the tangential direction
   component is preserved and the normal component flips sign
   (`specularReflect_normal_component_neg`).
3. *Line-equation readout*: the slope `m(φ)` and intercept `b(φ)` of the ray
   striking at incidence parameter `φ` are characterized by
   `IsLineEquationOfReflectedRay` — every point of the reflected line satisfies
   `y = m x + b`.
4. *Caustic as limiting intersection* (shared context, "The envelope/
   intersection of neighboring rays forms the caustic"): `IsCausticPoint` says
   the intersection point `(raysIntersectX m b θ Δθ, raysIntersectY m b θ Δθ)`
   of the reflected lines at `θ` and `θ + Δθ` converges to `P` as `Δθ → 0`
   (punctured filter `𝓝[≠] 0`; `Δθ` may have either sign).
5. *"For `θ ≪ 1`"* is the asymptotic regime `θ → 0` on the punctured
   two-sided filter `𝓝[≠] 0`: the equation `Y_c = v|X_c|^(p/q) + u` of the
   problem is the statement that the error of this cusp law is
   `o(|X_c|^(p/q))` as `θ → 0` (the `IsLittleO` conjunct of the main theorems),
   equivalently `(Y_c − u)/|X_c|^(p/q) → v` (the `Tendsto` conjunct; the two
   are linked by Mathlib `Asymptotics.isLittleO_iff_tendsto'`).

## Previous-part bridges (dependency policy `derive_inline_from_problem_only_material`)

* **T2-C1, re-derived inline** (`slope_intercept_of_reflected_ray`, conclusion
  side, proved from laws 1–3): the reflected line at incidence parameter `φ`
  has `m(φ) = cot(2φ)` and `b(φ) = R/(2 cos φ)`.
* **T2-C3, re-derived inline** (`causticPoint_eq`, conclusion side): the
  limiting intersection of the reflected lines at `θ` and `θ + Δθ` is
  `X_c(θ) = R sin³θ`, `Y_c(θ) = (R/2) cos θ (1 + 2 sin²θ)`
  (`causticX`, `causticY`).  Sketch: the intersection abscissa is
  `(b(θ+Δθ) − b(θ))/(m(θ) − m(θ+Δθ)) → −b'(θ)/m'(θ)` with
  `m'(θ) = −2/sin²(2θ)`, `b'(θ) = R sin θ/(2 cos²θ)`, giving
  `X_c = R sin θ sin²(2θ)/(4 cos²θ) = R sin³θ` and
  `Y_c = m X_c + b = R(1 + cos 2θ sin²θ)/(2 cos θ) = (R/2) cos θ (1 + 2 sin²θ)`
  (using `1 + cos 2θ sin²θ = cos²θ (1 + 2 sin²θ)`).

## Derivation of the candidate (problem-side calculus only, answer-blind)

From the T2-C3 parametrization, with `sin θ/θ → 1` (Mathlib `Real.continuous_sinc`,
`Real.sinc_of_ne_zero`) and `(cos θ − 1)/θ² → −1/2`
(from `cos θ − 1 = −2 sin²(θ/2)` and the same sinc limit):

* `|X_c|^(2/3) = R^(2/3) sin²θ = R^(2/3) θ² (1 + o(1))`
  (`abs_causticX_rpow`, `tendsto_abs_causticX_rpow_div_sq`);
* `Y_c − R/2 = (R/2)(cos θ (1 + 2 sin²θ) − 1)
   = (R/2)((cos θ − 1) + 2 cos θ sin²θ) = (R/2)(−θ²/2 + 2θ² + o(θ²))
   = (3R/4) θ² + o(θ²)` (`causticY_sub_cuspU_eq`,
  `tendsto_causticY_sub_cuspU_div_sq`).

Hence `(Y_c − R/2)/|X_c|^(2/3) → (3R/4)/R^(2/3) = (3/4) R^(1/3)`, so the cusp
law holds with the candidate constants **`u = R/2`, `v = (3/4)·R^(1/3)`
(`= ³√(27R/64)`), `p = 2`, `q = 3`**, recorded as `cuspU`, `cuspV`, `cuspP`,
`cuspQ` (values exposed by `cusp_constants`, assembled into the cusp curve
`cuspForm R X = v·|X|^(p/q) + u`).  No hypothesis, predicate field, or local
definition makes the cusp law true by unfolding: `cuspForm` enters the main
theorems only on the conclusion side, and the caustic functions `Xc`, `Yc` of
`caustic_cusp_law` are universally quantified, pinned only by the physical
hypotheses `hmb` (laws 1–3) and `hc` (law 4).

## Orientation and branch information

* Rays travel in `+y` before reflection (Fig. 2g arrows): `rayDir = (0, 1)`;
  the physical reflected ray is the forward branch `t > 0` of `reflectedRay`,
  while the problem's line equation describes the whole affine line, so
  `IsLineEquationOfReflectedRay` quantifies over all `t : ℝ`.
* Signed branch: `θ ∈ (−π/2, π/2) ∖ {0}` parametrizes both halves of the arc —
  `θ > 0` is the right half drawn in Fig. 2g, `θ < 0` the mirror-image left
  half.  `X_c` is odd (`causticX_neg`) and `Y_c` is even (`causticY_neg`), so
  the cusp law with `|X_c|` and the two-sided punctured filter `𝓝[≠] 0` covers
  both branches of the caustic, exactly as the problem's `|X_c|` indicates.
* The cusp point is `(X_c, Y_c) → (0, R/2)` as `θ → 0`
  (`causticX_zero`, `causticY_zero`); `u = R/2` is its height.

## Units and uncertainty

`R`, `b(φ)`, `u`, `v` (dimension: length^(1/3) · (length)^(2/3) = length in the
law) and all coordinates carry units of length (kept symbolic as reals);
`m(φ)`, `θ`, `Δθ`, `p`, `q` are dimensionless.  The question asks for exact
symbolic constants, so no rounding rule applies; the source reports no
measurement uncertainties (uncertainty propagation: not applicable — the
`o(|X_c|^(2/3))` remainder is the mathematical truncation error of the
small-`θ` expansion, not a measurement uncertainty).

LeanExplore found no PhysLean ray-optics / law-of-reflection / caustic /
envelope API (queries recorded in the T2-C1 task result and re-checked here);
as in T2-C1/T2-C2 the reflection law is grounded in the Mathlib real inner
product on `EuclideanSpace ℝ (Fin 2)`, and the asymptotics are grounded in
Mathlib `Tendsto`, `Asymptotics.IsLittleO`,
`Asymptotics.isLittleO_iff_tendsto'`, `Real.continuous_sinc`,
`Real.rpow_natCast` / `Real.rpow_mul`, `Real.cot_eq_cos_div_sin`.
-/

namespace IPhO2026.T2C4

open scoped RealInnerProductSpace Topology
open Asymptotics Filter

/-! ## The cross-sectional plane and Figure 2g geometry (shared T2-C model) -/

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

/-- Common incoming direction of rays A and B: `+y`, parallel to the optical
axis (the upward arrows of Fig. 2g; "a ray B, parallel to A"). -/
noncomputable def rayDir : Plane := !₂[(0 : ℝ), 1]

/-- Impact point on the mirror of the ray striking at (signed) incidence
parameter `θ`: `M(θ) = (R sin θ, R cos θ)`.  The radius `O M(θ)` (dashed in
Fig. 2g; the normal at the impact point) makes the angle `θ` with the vertical
incoming ray, so the parametrized incidence angle is `θ` as the problem states.
`θ > 0` is the right half of the arc (as drawn); `θ < 0` the left half. -/
noncomputable def incidencePoint (R θ : ℝ) : Plane := !₂[R * Real.sin θ, R * Real.cos θ]

/-- Direction after reflection at `M(θ)`: the law of specular reflection applied
to `rayDir` in the radial normal there.  Equals `(−sin 2θ, −cos 2θ)`
(`reflectedDir_eq`). -/
noncomputable def reflectedDir (R θ : ℝ) : Plane :=
  specularReflect (outwardUnitNormal R (incidencePoint R θ)) rayDir

/-- The reflected line of the ray striking at `θ` (governing law 1,
straight-line propagation after reflection): the line through the impact point
along `reflectedDir R θ`, parametrized by `t`.  The physical reflected ray is
the forward branch `t > 0`; the equation `y = m x + b` of the problem describes
the whole affine line. -/
noncomputable def reflectedRay (R θ t : ℝ) : Plane := incidencePoint R θ + t • reflectedDir R θ

/-- **Slope and intercept as defined by the problem**: `m`, `b` are the slope
and `y`-intercept of the reflected line of the ray striking at `θ` — every
point of the reflected line satisfies `y = m x + b`.  `m` is dimensionless;
`b` has units of length.  The pair is unique because the reflected direction
has nonzero `x`-component `−sin 2θ ≠ 0` for `θ ∈ (−π/2, π/2) ∖ {0}`. -/
def IsLineEquationOfReflectedRay (R θ m b : ℝ) : Prop :=
  ∀ t : ℝ, yCoord (reflectedRay R θ t) = m * xCoord (reflectedRay R θ t) + b

/-! ## Bridge lemmas: mirror geometry and the reflection law (proofs deferred) -/

/-- The incoming direction is a unit vector. -/
theorem rayDir_norm : ‖rayDir‖ = 1 := by
  have norm_coords : ∀ p : Plane, ‖p‖ = Real.sqrt (p 0 ^ 2 + p 1 ^ 2) := by
    intro p
    rw [EuclideanSpace.norm_eq, Fin.sum_univ_two]
    simp [Real.norm_eq_abs, sq_abs]
  rw [rayDir, norm_coords]
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

/-- Closed form of the reflected direction: reflecting `d = (0, 1)` in the
radial normal `(sin θ, cos θ)` at `M(θ)` gives `d' = (−sin 2θ, −cos 2θ)` — the
ray is deflected by twice the incidence angle, toward the aperture and the
optical axis. -/
theorem reflectedDir_eq (R θ : ℝ) (hR : 0 < R) :
    reflectedDir R θ = !₂[-Real.sin (2 * θ), -Real.cos (2 * θ)] := by
  have inner_coords : ∀ u v : Plane, ⟪u, v⟫ = u 0 * v 0 + u 1 * v 1 := by
    intro u v
    rw [PiLp.inner_apply, Fin.sum_univ_two]
    simp [RCLike.inner_apply]
    ring
  have hinner : ⟪rayDir, outwardUnitNormal R (incidencePoint R θ)⟫ = Real.cos θ := by
    simp only [inner_coords, rayDir, outwardUnitNormal, incidencePoint, PiLp.smul_apply,
      smul_eq_mul, Matrix.cons_val_zero, Matrix.cons_val_one]
    rw [zero_mul, one_mul, zero_add, ← mul_assoc, inv_mul_cancel₀ hR.ne', one_mul]
  ext i
  simp only [reflectedDir, specularReflect]
  rw [hinner]
  fin_cases i <;>
    simp only [PiLp.sub_apply, PiLp.smul_apply, smul_eq_mul, outwardUnitNormal,
      incidencePoint, rayDir, Matrix.cons_val_zero, Matrix.cons_val_one, Fin.reduceFinMk]
  · rw [Real.sin_two_mul]
    field_simp
    ring
  · rw [Real.cos_two_mul]
    field_simp
    ring

/-- The impact point lies on the reflecting arc of Fig. 2g for every signed
incidence parameter `θ ∈ (−π/2, π/2)` (both halves of the arc). -/
theorem incidencePoint_mem_arc (R θ : ℝ) (hR : 0 < R)
    (hθ : θ ∈ Set.Ioo (-(Real.pi / 2)) (Real.pi / 2)) :
    incidencePoint R θ ∈ mirrorArc R := by
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
    exact mul_pos hR (Real.cos_pos_of_mem_Ioo hθ)

/-- The reflected line is non-vertical for `θ ∈ (−π/2, π/2) ∖ {0}` (its
horizontal direction component is `−sin 2θ ≠ 0`), so it is the graph of an
affine function: the equation `y = m x + b` of the problem exists. -/
theorem reflected_ray_has_line_equation (R θ : ℝ) (hR : 0 < R)
    (hθ : θ ∈ Set.Ioo (-(Real.pi / 2)) (Real.pi / 2)) (hθ0 : θ ≠ 0) :
    ∃ m b : ℝ, IsLineEquationOfReflectedRay R θ m b := by
  obtain ⟨hθl, hθu⟩ := hθ
  have hs : Real.sin (2 * θ) ≠ 0 := by
    have h2θ : 2 * θ ≠ 0 := mul_ne_zero two_ne_zero hθ0
    exact fun h => h2θ ((Real.sin_eq_zero_iff_of_lt_of_lt
      (by linarith [Real.pi_pos]) (by linarith [Real.pi_pos])).mp h)
  have hcoords : ∀ t : ℝ, reflectedRay R θ t =
      !₂[R * Real.sin θ - t * Real.sin (2 * θ),
        R * Real.cos θ - t * Real.cos (2 * θ)] := by
    intro t
    rw [reflectedRay, reflectedDir_eq R θ hR]
    ext i
    fin_cases i <;>
      simp only [incidencePoint, PiLp.add_apply, PiLp.smul_apply, smul_eq_mul,
        Matrix.cons_val_zero, Matrix.cons_val_one, Fin.reduceFinMk] <;>
      ring
  refine ⟨Real.cos (2 * θ) / Real.sin (2 * θ),
    R * Real.cos θ - (Real.cos (2 * θ) / Real.sin (2 * θ)) * (R * Real.sin θ), ?_⟩
  intro t
  rw [hcoords t]
  simp only [xCoord, yCoord, Matrix.cons_val_zero, Matrix.cons_val_one]
  field_simp
  ring

/-! ## Previous-part bridge (T2-C1, re-derived inline): exact slope and intercept -/

/-- **Exact slope and intercept of the reflected line** (previous-part result
of T2-C1 re-derived inline, per the dependency policy
`derive_inline_from_problem_only_material`): any pair `(m, b)` satisfying
`IsLineEquationOfReflectedRay R θ` obeys `m = cot(2θ)` and
`b = R/(2 cos θ)`; the pair is unique because the reflected line is
non-vertical.  Proof route: mirror of T2-C1's
`slope_intercept_of_reflected_ray_A` — use `reflectedDir_eq`, instantiate the
line equation at two parameter values, subtract, and simplify with
`Real.cot_eq_cos_div_sin`, `Real.sin_two_mul`. -/
theorem slope_intercept_of_reflected_ray (R θ m b : ℝ) (hR : 0 < R)
    (hθ : θ ∈ Set.Ioo (-(Real.pi / 2)) (Real.pi / 2)) (hθ0 : θ ≠ 0)
    (hline : IsLineEquationOfReflectedRay R θ m b) :
    m = Real.cot (2 * θ) ∧ b = R / (2 * Real.cos θ) := by
  obtain ⟨hθl, hθu⟩ := hθ
  have hs : Real.sin (2 * θ) ≠ 0 := by
    have h2θ : 2 * θ ≠ 0 := mul_ne_zero two_ne_zero hθ0
    exact fun h => h2θ ((Real.sin_eq_zero_iff_of_lt_of_lt
      (by linarith [Real.pi_pos]) (by linarith [Real.pi_pos])).mp h)
  have hsθ : Real.sin θ ≠ 0 :=
    fun h => hθ0 ((Real.sin_eq_zero_iff_of_lt_of_lt
      (by linarith [Real.pi_pos]) (by linarith [Real.pi_pos])).mp h)
  have hc : Real.cos θ ≠ 0 := (Real.cos_pos_of_mem_Ioo ⟨hθl, hθu⟩).ne'
  have hcoords : ∀ t : ℝ, reflectedRay R θ t =
      !₂[R * Real.sin θ - t * Real.sin (2 * θ),
        R * Real.cos θ - t * Real.cos (2 * θ)] := by
    intro t
    rw [reflectedRay, reflectedDir_eq R θ hR]
    ext i
    fin_cases i <;>
      simp only [incidencePoint, PiLp.add_apply, PiLp.smul_apply, smul_eq_mul,
        Matrix.cons_val_zero, Matrix.cons_val_one, Fin.reduceFinMk] <;>
      ring
  have h0 := hline 0
  have h1 := hline 1
  rw [hcoords 0] at h0
  rw [hcoords 1] at h1
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

/-! ## The two-ray intersection and the caustic (T2-C3 objects) -/

/-- `x`-coordinate of the intersection of the reflected lines at parameters
`θ` (ray A) and `θ + Δθ` (ray B): solving
`m(θ) x + b(θ) = m(θ+Δθ) x + b(θ+Δθ)`.  Units: length. -/
noncomputable def raysIntersectX (m b : ℝ → ℝ) (θ Δθ : ℝ) : ℝ :=
  (b (θ + Δθ) - b θ) / (m θ - m (θ + Δθ))

/-- `y`-coordinate of the intersection of the reflected lines at `θ` and
`θ + Δθ`, read from ray A's line.  Units: length. -/
noncomputable def raysIntersectY (m b : ℝ → ℝ) (θ Δθ : ℝ) : ℝ :=
  m θ * raysIntersectX m b θ Δθ + b θ

/-- The intersection abscissa really lies on both reflected lines (when they
are not parallel).  This is the defining property of `raysIntersectX` —
solving the two line equations — and constrains the definition. -/
theorem raysIntersectX_mem_both_lines (m b : ℝ → ℝ) (θ Δθ : ℝ)
    (h : m θ ≠ m (θ + Δθ)) :
    m θ * raysIntersectX m b θ Δθ + b θ =
      m (θ + Δθ) * raysIntersectX m b θ Δθ + b (θ + Δθ) := by
  have hD : m θ - m (θ + Δθ) ≠ 0 := sub_ne_zero.mpr h
  unfold raysIntersectX
  field_simp
  ring

/-- The intersection point read from ray A's line. -/
theorem raysIntersectY_mem_first_line (m b : ℝ → ℝ) (θ Δθ : ℝ) :
    raysIntersectY m b θ Δθ = m θ * raysIntersectX m b θ Δθ + b θ :=
  rfl

/-- The intersection point also lies on ray B's line (when the lines are not
parallel). -/
theorem raysIntersectY_mem_second_line (m b : ℝ → ℝ) (θ Δθ : ℝ)
    (h : m θ ≠ m (θ + Δθ)) :
    raysIntersectY m b θ Δθ = m (θ + Δθ) * raysIntersectX m b θ Δθ + b (θ + Δθ) := by
  rw [raysIntersectY_mem_first_line, raysIntersectX_mem_both_lines m b θ Δθ h]

/-- **The caustic point at parameter `θ`** (governing law 4 of the shared
context: "The envelope/intersection of neighboring rays forms the caustic";
the object whose coordinates T2-C3 asks for): the intersection point of the
reflected lines at `θ` and `θ + Δθ` converges to `P` as `Δθ → 0`.  The
punctured two-sided filter `𝓝[≠] 0` allows `Δθ` of either sign (ray B on
either side of ray A). -/
def IsCausticPoint (m b : ℝ → ℝ) (θ : ℝ) (P : Plane) : Prop :=
  Tendsto (fun Δθ => !₂[raysIntersectX m b θ Δθ, raysIntersectY m b θ Δθ])
    (𝓝[≠] (0 : ℝ)) (𝓝 P)

/-- The caustic point at a given parameter is unique when it exists (limits in
the Hausdorff plane are unique; `𝓝[≠] (0 : ℝ)` is nontrivial). -/
theorem IsCausticPoint.unique {m b : ℝ → ℝ} {θ : ℝ} {P Q : Plane}
    (hP : IsCausticPoint m b θ P) (hQ : IsCausticPoint m b θ Q) :
    P = Q :=
  tendsto_nhds_unique hP hQ

/-- **The caustic curve, `x`-coordinate** (the `X_c` of T2-C3/T2-C4):
`X_c(θ) = R sin³θ`.  Units: length.  That this explicit function is the
limiting intersection of neighboring reflected rays is the content of
`causticPoint_eq` (T2-C3 re-derived inline), not of this definition. -/
noncomputable def causticX (R θ : ℝ) : ℝ := R * Real.sin θ ^ 3

/-- **The caustic curve, `y`-coordinate** (the `Y_c` of T2-C3/T2-C4):
`Y_c(θ) = (R/2) cos θ (1 + 2 sin²θ)`.  Units: length.  Equivalent forms:
`R(1 + cos 2θ sin²θ)/(2 cos θ)` (direct from the intersection limit) and
`(R/2)(3 cos θ − 2 cos³θ)` (`causticY_eq_three_cos`).  That this explicit
function is the limiting intersection of neighboring reflected rays is the
content of `causticPoint_eq` (T2-C3 re-derived inline), not of this
definition. -/
noncomputable def causticY (R θ : ℝ) : ℝ := R / 2 * Real.cos θ * (1 + 2 * Real.sin θ ^ 2)

/-- **T2-C3 result, re-derived inline** (dependency policy
`derive_inline_from_problem_only_material`): the limiting intersection of the
reflected lines at `θ` and `θ + Δθ` as `Δθ → 0` is
`(X_c(θ), Y_c(θ)) = (R sin³θ, (R/2) cos θ (1 + 2 sin²θ))`.  Proof route:
`slope_intercept_of_reflected_ray` identifies `m(φ) = cot(2φ)`,
`b(φ) = R/(2 cos φ)` for all `φ` near `θ`; the difference quotient
`(b(θ+Δθ) − b(θ))/(m(θ) − m(θ+Δθ))` converges to `−b'(θ)/m'(θ)`
(`HasDerivAt.tendsto_slope`-type lemmas) with `m'(θ) = −2/sin²(2θ)` and
`b'(θ) = R sin θ/(2 cos²θ)`, giving `X_c = R sin³θ`; then
`Y_c = m(θ) X_c + b(θ)` by continuity. -/
theorem causticPoint_eq (R θ : ℝ) (hR : 0 < R)
    (hθ : θ ∈ Set.Ioo (-(Real.pi / 2)) (Real.pi / 2)) (hθ0 : θ ≠ 0)
    (m b : ℝ → ℝ)
    (hmb : ∀ φ ∈ Set.Ioo (-(Real.pi / 2)) (Real.pi / 2), φ ≠ 0 →
      IsLineEquationOfReflectedRay R φ (m φ) (b φ)) :
    IsCausticPoint m b θ !₂[causticX R θ, causticY R θ] := by
  obtain ⟨hθl, hθu⟩ := hθ
  -- nonzero quantities from the two-sided range and `θ ≠ 0`
  have hsθ : Real.sin θ ≠ 0 :=
    fun h => hθ0 ((Real.sin_eq_zero_iff_of_lt_of_lt
      (by linarith [Real.pi_pos]) (by linarith [Real.pi_pos])).mp h)
  have hs2 : Real.sin (2 * θ) ≠ 0 := by
    have h2θ : 2 * θ ≠ 0 := mul_ne_zero two_ne_zero hθ0
    exact fun h => h2θ ((Real.sin_eq_zero_iff_of_lt_of_lt
      (by linarith [Real.pi_pos]) (by linarith [Real.pi_pos])).mp h)
  have hcθ : Real.cos θ ≠ 0 := (Real.cos_pos_of_mem_Ioo ⟨hθl, hθu⟩).ne'
  -- the line parameters at `θ` are pinned by the T2-C1 bridge
  obtain ⟨hmθ, hbθ⟩ :=
    slope_intercept_of_reflected_ray R θ (m θ) (b θ) hR ⟨hθl, hθu⟩ hθ0
      (hmb θ ⟨hθl, hθu⟩ hθ0)
  -- derivative of the explicit slope function `φ ↦ cot(2φ)`
  have hdm : HasDerivAt (fun φ : ℝ => Real.cot (2 * φ)) (-2 / Real.sin (2 * θ) ^ 2) θ := by
    have h1 : HasDerivAt (fun φ : ℝ => 2 * φ) 2 θ := by
      simpa using (hasDerivAt_id θ).const_mul (2 : ℝ)
    have hs : HasDerivAt (fun φ : ℝ => Real.sin (2 * φ)) (Real.cos (2 * θ) * 2) θ :=
      (Real.hasDerivAt_sin (2 * θ)).comp θ h1
    have hc : HasDerivAt (fun φ : ℝ => Real.cos (2 * φ)) (-Real.sin (2 * θ) * 2) θ :=
      (Real.hasDerivAt_cos (2 * θ)).comp θ h1
    have hfun : (fun φ : ℝ => Real.cot (2 * φ))
        = fun φ : ℝ => Real.cos (2 * φ) / Real.sin (2 * φ) := by
      funext φ
      exact Real.cot_eq_cos_div_sin (2 * φ)
    rw [hfun]
    have hdiv : HasDerivAt (fun φ : ℝ => Real.cos (2 * φ) / Real.sin (2 * φ))
        (((-Real.sin (2 * θ) * 2) * Real.sin (2 * θ)
          - Real.cos (2 * θ) * (Real.cos (2 * θ) * 2)) / Real.sin (2 * θ) ^ 2) θ :=
      hc.div hs hs2
    have hnum : (-Real.sin (2 * θ) * 2) * Real.sin (2 * θ)
        - Real.cos (2 * θ) * (Real.cos (2 * θ) * 2) = -2 := by
      have hsc := Real.sin_sq_add_cos_sq (2 * θ)
      linear_combination (-2 : ℝ) * hsc
    rw [hnum] at hdiv
    exact hdiv
  -- derivative of the explicit intercept function `φ ↦ R/(2 cos φ)`
  have hdb : HasDerivAt (fun φ : ℝ => R / (2 * Real.cos φ))
      (R * Real.sin θ / (2 * Real.cos θ ^ 2)) θ := by
    have hfun : (fun φ : ℝ => R / (2 * Real.cos φ))
        = fun φ : ℝ => (R / 2) * (Real.cos φ)⁻¹ := by
      funext φ
      show R / (2 * Real.cos φ) = (R / 2) * (Real.cos φ)⁻¹
      rw [div_eq_mul_inv, div_eq_mul_inv, mul_inv, mul_assoc]
    have hc : HasDerivAt (fun φ : ℝ => (Real.cos φ)⁻¹)
        (-(-Real.sin θ) / Real.cos θ ^ 2) θ := (Real.hasDerivAt_cos θ).inv hcθ
    have hmul : HasDerivAt (fun φ : ℝ => (R / 2) * (Real.cos φ)⁻¹)
        ((R / 2) * (-(-Real.sin θ) / Real.cos θ ^ 2)) θ := hc.const_mul (R / 2)
    have hderiv : (R / 2) * (-(-Real.sin θ) / Real.cos θ ^ 2)
        = R * Real.sin θ / (2 * Real.cos θ ^ 2) := by
      rw [neg_neg, div_mul_div_comm]
    rw [hfun]
    rw [hderiv] at hmul
    exact hmul
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
  -- difference quotients converge to the derivatives
  have hmq : Filter.Tendsto
      (fun Δθ : ℝ => (Real.cot (2 * (θ + Δθ)) - Real.cot (2 * θ)) / Δθ)
      (𝓝[≠] 0) (𝓝 (-2 / Real.sin (2 * θ) ^ 2)) := by
    have h := (hasDerivAt_iff_tendsto_slope.mp hdm).comp hg
    have hfun : (slope (fun φ : ℝ => Real.cot (2 * φ)) θ) ∘ (fun Δθ : ℝ => θ + Δθ)
        = fun Δθ : ℝ => (Real.cot (2 * (θ + Δθ)) - Real.cot (2 * θ)) / Δθ := by
      funext Δθ
      simp only [Function.comp_apply, slope_def_field, add_sub_cancel_left]
    rw [hfun] at h
    exact h
  have hbq : Filter.Tendsto
      (fun Δθ : ℝ => (R / (2 * Real.cos (θ + Δθ)) - R / (2 * Real.cos θ)) / Δθ)
      (𝓝[≠] 0) (𝓝 (R * Real.sin θ / (2 * Real.cos θ ^ 2))) := by
    have h := (hasDerivAt_iff_tendsto_slope.mp hdb).comp hg
    have hfun : (slope (fun φ : ℝ => R / (2 * Real.cos φ)) θ) ∘ (fun Δθ : ℝ => θ + Δθ)
        = fun Δθ : ℝ => (R / (2 * Real.cos (θ + Δθ)) - R / (2 * Real.cos θ)) / Δθ := by
      funext Δθ
      simp only [Function.comp_apply, slope_def_field, add_sub_cancel_left]
    rw [hfun] at h
    exact h
  -- x-coordinate: ratio of difference quotients tends to `−b'(θ)/m'(θ)`
  have hm'ne : (-2 / Real.sin (2 * θ) ^ 2) ≠ 0 :=
    div_ne_zero (by norm_num) (pow_ne_zero 2 hs2)
  have hXratio : Filter.Tendsto
      (fun Δθ : ℝ => ((R / (2 * Real.cos (θ + Δθ)) - R / (2 * Real.cos θ)) / Δθ) /
        (-((Real.cot (2 * (θ + Δθ)) - Real.cot (2 * θ)) / Δθ)))
      (𝓝[≠] 0)
      (𝓝 ((R * Real.sin θ / (2 * Real.cos θ ^ 2)) / (-(-2 / Real.sin (2 * θ) ^ 2)))) :=
    hbq.div hmq.neg (neg_ne_zero.mpr hm'ne)
  have hXeq : (fun Δθ : ℝ => ((R / (2 * Real.cos (θ + Δθ)) - R / (2 * Real.cos θ)) / Δθ) /
        (-((Real.cot (2 * (θ + Δθ)) - Real.cot (2 * θ)) / Δθ)))
      =ᶠ[𝓝[≠] 0] fun Δθ : ℝ => (R / (2 * Real.cos (θ + Δθ)) - R / (2 * Real.cos θ)) /
        (Real.cot (2 * θ) - Real.cot (2 * (θ + Δθ))) := by
    filter_upwards [self_mem_nhdsWithin] with Δθ hΔ
    have hΔ0 : Δθ ≠ 0 := hΔ
    rw [div_neg, div_div_div_cancel_right₀ hΔ0, ← div_neg, neg_sub]
  have hXval : (R * Real.sin θ / (2 * Real.cos θ ^ 2)) / (-(-2 / Real.sin (2 * θ) ^ 2))
      = causticX R θ := by
    show (R * Real.sin θ / (2 * Real.cos θ ^ 2)) / (-(-2 / Real.sin (2 * θ) ^ 2))
        = R * Real.sin θ ^ 3
    rw [neg_div, neg_neg, Real.sin_two_mul]
    field_simp
  have hX' : Filter.Tendsto
      (fun Δθ : ℝ => (R / (2 * Real.cos (θ + Δθ)) - R / (2 * Real.cos θ)) /
        (Real.cot (2 * θ) - Real.cot (2 * (θ + Δθ))))
      (𝓝[≠] 0) (𝓝 (causticX R θ)) := by
    have h := hXratio.congr' hXeq
    rwa [hXval] at h
  -- y-coordinate: `Y(Δθ) = m(θ) X(Δθ) + b(θ)`, limit by continuity
  have hYlim : Filter.Tendsto
      (fun Δθ : ℝ => Real.cot (2 * θ) *
          ((R / (2 * Real.cos (θ + Δθ)) - R / (2 * Real.cos θ)) /
            (Real.cot (2 * θ) - Real.cot (2 * (θ + Δθ)))) + R / (2 * Real.cos θ))
      (𝓝[≠] 0) (𝓝 (Real.cot (2 * θ) * causticX R θ + R / (2 * Real.cos θ))) :=
    (tendsto_const_nhds.mul hX').add tendsto_const_nhds
  have hYval : Real.cot (2 * θ) * causticX R θ + R / (2 * Real.cos θ)
      = causticY R θ := by
    have h2c : (2 : ℝ) * Real.cos θ ≠ 0 := mul_ne_zero two_ne_zero hcθ
    have h2sc : 2 * Real.sin θ * Real.cos θ ≠ 0 :=
      mul_ne_zero (mul_ne_zero two_ne_zero hsθ) hcθ
    have stepA : Real.cot (2 * θ) * (R * Real.sin θ ^ 3)
        = Real.cos (2 * θ) * (R * Real.sin θ ^ 2) / (2 * Real.cos θ) := by
      rw [Real.cot_eq_cos_div_sin, Real.sin_two_mul, div_mul_eq_mul_div,
        div_eq_div_iff h2sc h2c]
      ring
    show Real.cot (2 * θ) * (R * Real.sin θ ^ 3) + R / (2 * Real.cos θ)
        = R / 2 * Real.cos θ * (1 + 2 * Real.sin θ ^ 2)
    rw [stepA, ← add_div, div_eq_iff h2c, Real.cos_two_mul]
    linear_combination (-R) * Real.sin_sq_add_cos_sq θ
  have hY' : Filter.Tendsto
      (fun Δθ : ℝ => Real.cot (2 * θ) *
          ((R / (2 * Real.cos (θ + Δθ)) - R / (2 * Real.cos θ)) /
            (Real.cot (2 * θ) - Real.cot (2 * (θ + Δθ)))) + R / (2 * Real.cos θ))
      (𝓝[≠] 0) (𝓝 (causticY R θ)) := by
    rwa [hYval] at hYlim
  -- the line parameters at `θ + Δθ` are pinned eventually on the punctured filter
  have hIoo : Set.Ioo (-(Real.pi / 2)) (Real.pi / 2) ∈ 𝓝 θ := Ioo_mem_nhds hθl hθu
  have ht : Filter.Tendsto (fun Δθ : ℝ => θ + Δθ) (𝓝 (0 : ℝ)) (𝓝 (θ + 0)) :=
    (continuous_const.add continuous_id).tendsto 0
  rw [add_zero] at ht
  have hIoo_ev : ∀ᶠ Δθ in 𝓝[≠] (0 : ℝ), θ + Δθ ∈ Set.Ioo (-(Real.pi / 2)) (Real.pi / 2) :=
    (ht.eventually hIoo).filter_mono nhdsWithin_le_nhds
  have hne_ev : ∀ᶠ Δθ in 𝓝[≠] (0 : ℝ), θ + Δθ ≠ 0 := by
    have h1 : ({0}ᶜ : Set ℝ) ∈ 𝓝 θ :=
      isOpen_compl_singleton.mem_nhds (by simpa using hθ0)
    have h2 : ∀ᶠ x in 𝓝 θ, x ≠ 0 :=
      Filter.eventually_of_mem h1 (fun x hx => by simpa using hx)
    exact (ht.eventually h2).filter_mono nhdsWithin_le_nhds
  have hmb_ev : ∀ᶠ Δθ in 𝓝[≠] (0 : ℝ),
      m (θ + Δθ) = Real.cot (2 * (θ + Δθ)) ∧ b (θ + Δθ) = R / (2 * Real.cos (θ + Δθ)) := by
    filter_upwards [hIoo_ev, hne_ev] with Δθ hI hN
    exact slope_intercept_of_reflected_ray R (θ + Δθ) (m (θ + Δθ)) (b (θ + Δθ)) hR hI hN
      (hmb (θ + Δθ) hI hN)
  -- transfer the explicit limits to the pinned line family `m b`
  have hX_ev : (fun Δθ => (R / (2 * Real.cos (θ + Δθ)) - R / (2 * Real.cos θ)) /
        (Real.cot (2 * θ) - Real.cot (2 * (θ + Δθ))))
      =ᶠ[𝓝[≠] 0] fun Δθ => raysIntersectX m b θ Δθ := by
    filter_upwards [hmb_ev] with Δθ hΔ
    obtain ⟨hm, hb⟩ := hΔ
    unfold raysIntersectX
    rw [hm, hb, hmθ, hbθ]
  have hY_ev : (fun Δθ => Real.cot (2 * θ) *
          ((R / (2 * Real.cos (θ + Δθ)) - R / (2 * Real.cos θ)) /
            (Real.cot (2 * θ) - Real.cot (2 * (θ + Δθ)))) + R / (2 * Real.cos θ))
      =ᶠ[𝓝[≠] 0] fun Δθ => raysIntersectY m b θ Δθ := by
    filter_upwards [hX_ev] with Δθ hΔ
    unfold raysIntersectY
    rw [← hΔ, hmθ, hbθ]
  have hXm : Filter.Tendsto (fun Δθ => raysIntersectX m b θ Δθ)
      (𝓝[≠] 0) (𝓝 (causticX R θ)) := hX'.congr' hX_ev
  have hYm : Filter.Tendsto (fun Δθ => raysIntersectY m b θ Δθ)
      (𝓝[≠] 0) (𝓝 (causticY R θ)) := hY'.congr' hY_ev
  -- assemble the two coordinate limits
  have hpi : Filter.Tendsto
      (fun Δθ => ![raysIntersectX m b θ Δθ, raysIntersectY m b θ Δθ])
      (𝓝[≠] 0) (𝓝 ![causticX R θ, causticY R θ]) := by
    rw [tendsto_pi_nhds]
    intro i
    fin_cases i
    · simpa only [Matrix.cons_val_zero, Matrix.cons_val_one, Fin.reduceFinMk] using hXm
    · simpa only [Matrix.cons_val_zero, Matrix.cons_val_one, Fin.reduceFinMk] using hYm
  have hcont : Continuous (WithLp.toLp 2 : (Fin 2 → ℝ) → Plane) :=
    PiLp.continuous_toLp 2 (fun _ : Fin 2 => ℝ)
  have h2 := (hcont.tendsto ![causticX R θ, causticY R θ]).comp hpi
  exact h2.congr fun Δθ => rfl

/-- The cusp is approached as `θ → 0`: `X_c(0) = 0`. -/
@[simp]
theorem causticX_zero (R : ℝ) : causticX R 0 = 0 := by
  simp [causticX]

/-- The cusp point has height `R/2`: `Y_c(0) = R/2` (this is the value of `u`,
here only as the continuous extension of the caustic parametrization). -/
@[simp]
theorem causticY_zero (R : ℝ) : causticY R 0 = R / 2 := by
  simp [causticY]

/-- Branch structure of the caustic: `X_c` is odd in `θ` (the two halves of
the mirror give the two arms `X_c ≷ 0` of the cusp; the problem's `|X_c|`
quotes the unsigned abscissa). -/
theorem causticX_neg (R θ : ℝ) : causticX R (-θ) = -causticX R θ := by
  simp only [causticX, Real.sin_neg]
  ring

/-- Branch structure of the caustic: `Y_c` is even in `θ` (both arms lie at
the same height). -/
theorem causticY_neg (R θ : ℝ) : causticY R (-θ) = causticY R θ := by
  simp [causticY, Real.cos_neg, Real.sin_neg]

/-- Equivalent expanded form of the caustic height:
`Y_c(θ) = (R/2)(3 cos θ − 2 cos³θ)`. -/
theorem causticY_eq_three_cos (R θ : ℝ) :
    causticY R θ = R / 2 * (3 * Real.cos θ - 2 * Real.cos θ ^ 3) := by
  simp only [causticY, Real.sin_sq]
  ring

/-! ## Candidate cusp coefficients (the T2-C4 answer, derived answer-blind) -/

/-- **Candidate numerator `p`** of the cusp exponent (derived answer-blind from
the caustic parametrization: `X_c ∝ θ³` while `Y_c − R/2 ∝ θ²`, so
`Y_c − u ∝ |X_c|^(2/3)`).  Dimensionless integer. -/
def cuspP : ℤ := 2

/-- **Candidate denominator `q`** of the cusp exponent.  Dimensionless
integer. -/
def cuspQ : ℤ := 3

/-- **Candidate cusp exponent** `p/q = 2/3` as a real number (the exponent of
`|X_c|` in the cusp law). -/
noncomputable def cuspExponent : ℝ := (cuspP : ℝ) / (cuspQ : ℝ)

/-- **Candidate offset `u`** (derived answer-blind: the height of the cusp
point, `Y_c → R/2` as `θ → 0`).  Units: length. -/
noncomputable def cuspU (R : ℝ) : ℝ := R / 2

/-- **Candidate amplitude `v`** (derived answer-blind:
`(Y_c − R/2)/|X_c|^(2/3) → (3/4)·R^(1/3)`, equivalently `v = ³√(27R/64)`).
Units: length^(1/3), so that `v·|X_c|^(2/3)` has units of length. -/
noncomputable def cuspV (R : ℝ) : ℝ := 3 / 4 * R ^ ((1 : ℝ) / 3)

/-- **The cusp curve** `X ↦ v·|X|^(p/q) + u` with the candidate constants:
the right-hand side of the T2-C4 relation `Y_c = v|X_c|^(p/q) + u`. -/
noncomputable def cuspForm (R X : ℝ) : ℝ := cuspV R * |X| ^ cuspExponent + cuspU R

/-- The determined constants in explicit form (T2-C4 answer record):
`p = 2`, `q = 3`, `p/q = 2/3`, `u = R/2`, `v = (3/4)·R^(1/3)`.
Naming-expansion lemmas only — the physical claim that the caustic obeys the
cusp law with these constants is the main theorem `caustic_cusp_law`. -/
theorem cusp_constants (R : ℝ) :
    cuspP = 2 ∧ cuspQ = 3 ∧ cuspU R = R / 2 ∧ cuspV R = 3 / 4 * R ^ ((1 : ℝ) / 3) :=
  ⟨rfl, rfl, rfl, rfl⟩

/-- The cusp exponent is `2/3`. -/
theorem cuspExponent_eq : cuspExponent = (2 : ℝ) / 3 := by
  norm_num [cuspExponent, cuspP, cuspQ]

/-- The cusp form with explicit constants:
`cuspForm R X = (3/4) R^(1/3) · |X|^(2/3) + R/2`. -/
theorem cuspForm_eq (R X : ℝ) :
    cuspForm R X = 3 / 4 * R ^ ((1 : ℝ) / 3) * |X| ^ ((2 : ℝ) / 3) + R / 2 := by
  unfold cuspForm cuspV cuspU cuspExponent cuspP cuspQ
  norm_num

/-! ## Analytic bridges toward the cusp law (proofs deferred) -/

/-- Algebraic core of the cusp limit: the height deficit splits as
`Y_c(θ) − u = (R/2)((cos θ − 1) + 2 cos θ sin²θ)`. -/
theorem causticY_sub_cuspU_eq (R θ : ℝ) :
    causticY R θ - cuspU R = R / 2 * ((Real.cos θ - 1) + 2 * Real.cos θ * Real.sin θ ^ 2) := by
  simp only [causticY, cuspU]
  ring

/-- The caustic abscissa is nonzero at every nonzero incidence parameter in
`(−π/2, π/2)` (`sin θ ≠ 0` there); in particular `|X_c|^(p/q) ≠ 0` on the
punctured neighborhoods used below, so ratios by `|X_c|^(2/3)` are
well-defined. -/
theorem causticX_ne_zero (R θ : ℝ) (hR : 0 < R)
    (hθ : θ ∈ Set.Ioo (-(Real.pi / 2)) (Real.pi / 2)) (hθ0 : θ ≠ 0) :
    causticX R θ ≠ 0 := by
  obtain ⟨hθl, hθu⟩ := hθ
  have hsθ : Real.sin θ ≠ 0 :=
    fun h => hθ0 ((Real.sin_eq_zero_iff_of_lt_of_lt
      (by linarith [Real.pi_pos]) (by linarith [Real.pi_pos])).mp h)
  exact mul_ne_zero hR.ne' (pow_ne_zero 3 hsθ)

/-- Exact `2/3`-power law of the caustic abscissa:
`|X_c(θ)|^(2/3) = R^(2/3) sin²θ`.  Proof route: `|R sin³θ| = R·|sin θ|³`,
`Real.mul_rpow`, `Real.rpow_natCast`, `Real.rpow_mul` giving
`(|sin θ|³)^(2/3) = |sin θ|²`, and `sq_abs`. -/
theorem abs_causticX_rpow (R θ : ℝ) (hR : 0 ≤ R) :
    |causticX R θ| ^ ((2 : ℝ) / 3) = R ^ ((2 : ℝ) / 3) * Real.sin θ ^ 2 := by
  have h1 : |causticX R θ| = R * |Real.sin θ| ^ 3 := by
    show |R * Real.sin θ ^ 3| = R * |Real.sin θ| ^ 3
    rw [abs_mul, abs_of_nonneg hR, abs_pow]
  rw [h1, Real.mul_rpow hR (pow_nonneg (abs_nonneg _) 3)]
  congr 1
  have hnn : (0 : ℝ) ≤ |Real.sin θ| := abs_nonneg _
  calc (|Real.sin θ| ^ 3) ^ ((2 : ℝ) / 3)
      = (|Real.sin θ| ^ ((3 : ℕ) : ℝ)) ^ ((2 : ℝ) / 3) := by rw [Real.rpow_natCast]
    _ = |Real.sin θ| ^ (((3 : ℕ) : ℝ) * (2 / 3)) := by rw [← Real.rpow_mul hnn]
    _ = |Real.sin θ| ^ ((2 : ℕ) : ℝ) := by
        rw [show (((3 : ℕ) : ℝ) * (2 / 3)) = ((2 : ℕ) : ℝ) by norm_num]
    _ = Real.sin θ ^ 2 := by rw [Real.rpow_natCast, sq_abs]

/-- Second-order normalization of the caustic height at the cusp:
`(Y_c(θ) − R/2)/θ² → 3R/4` as `θ → 0`.  Proof route: `causticY_sub_cuspU_eq`
splits the numerator into `(R/2)((cos θ − 1) + 2 cos θ sin²θ)`; then
`(cos θ − 1)/θ² → −1/2` (from `cos θ − 1 = −2 sin²(θ/2)` and
`sin x/x → 1`, carried by Mathlib `Real.continuous_sinc` with
`Real.sinc_of_ne_zero`) and `(sin θ/θ)² → 1`, `cos θ → 1`. -/
theorem tendsto_causticY_sub_cuspU_div_sq (R : ℝ) :
    Tendsto (fun θ => (causticY R θ - cuspU R) / θ ^ 2) (𝓝[≠] (0 : ℝ))
      (𝓝 (3 * R / 4)) := by
  -- `sin x / x → 1` on the punctured filter, via continuity of `sinc`
  have hsinc : Tendsto (fun θ : ℝ => Real.sin θ / θ) (𝓝[≠] (0 : ℝ)) (𝓝 1) := by
    have h : Tendsto Real.sinc (𝓝[≠] (0 : ℝ)) (𝓝 (Real.sinc 0)) :=
      (Real.continuous_sinc.tendsto 0).mono_left
        (nhdsWithin_le_nhds (s := {0}ᶜ) (a := (0 : ℝ)))
    rw [Real.sinc_zero] at h
    apply h.congr'
    filter_upwards [self_mem_nhdsWithin] with θ hθ
    exact Real.sinc_of_ne_zero hθ
  -- `(cos θ − 1)/θ² → −1/2`, via `cos θ − 1 = −2 sin²(θ/2)` and sinc at `θ/2`
  have hcos : Tendsto (fun θ : ℝ => (Real.cos θ - 1) / θ ^ 2) (𝓝[≠] (0 : ℝ))
      (𝓝 (-1 / 2 : ℝ)) := by
    have hhalf : Tendsto (fun θ : ℝ => θ / 2) (𝓝[≠] (0 : ℝ)) (𝓝[≠] (0 : ℝ)) := by
      apply tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within
      · have h : Tendsto (fun θ : ℝ => θ / 2) (𝓝 (0 : ℝ)) (𝓝 (0 / 2)) :=
          Filter.tendsto_id.div_const (2 : ℝ)
        rw [zero_div] at h
        exact h.mono_left (nhdsWithin_le_nhds (s := {0}ᶜ) (a := (0 : ℝ)))
      · filter_upwards [self_mem_nhdsWithin] with θ hθ
        exact div_ne_zero hθ two_ne_zero
    have hsin2 : Tendsto (fun θ : ℝ => (Real.sin (θ / 2) / (θ / 2)) ^ 2) (𝓝[≠] (0 : ℝ))
        (𝓝 (1 : ℝ)) := by
      have h := hsinc.comp hhalf
      have h2 := h.mul h
      simpa only [Function.comp_apply, pow_two, mul_one] using h2
    have hform : (fun θ : ℝ => (Real.cos θ - 1) / θ ^ 2) =ᶠ[𝓝[≠] (0 : ℝ)]
        fun θ => (-1 / 2 : ℝ) * (Real.sin (θ / 2) / (θ / 2)) ^ 2 := by
      filter_upwards [self_mem_nhdsWithin] with θ hθ
      have hθ0 : θ ≠ 0 := hθ
      have h1 : Real.cos θ - 1 = -2 * Real.sin (θ / 2) ^ 2 := by
        have h2 := Real.cos_two_mul' (θ / 2)
        rw [show 2 * (θ / 2) = θ by ring] at h2
        have hsc := Real.sin_sq_add_cos_sq (θ / 2)
        linarith [h2]
      rw [h1]
      field_simp
    have hlim : Tendsto (fun θ : ℝ => (-1 / 2 : ℝ) * (Real.sin (θ / 2) / (θ / 2)) ^ 2)
        (𝓝[≠] (0 : ℝ)) (𝓝 ((-1 / 2 : ℝ) * 1)) := tendsto_const_nhds.mul hsin2
    rw [show (-1 / 2 : ℝ) * 1 = -1 / 2 by norm_num] at hlim
    exact hlim.congr' hform.symm
  -- `(sin θ/θ)² → 1` and `cos θ → 1`
  have hsinsq : Tendsto (fun θ : ℝ => (Real.sin θ / θ) ^ 2) (𝓝[≠] (0 : ℝ)) (𝓝 1) := by
    simpa only [pow_two, mul_one] using hsinc.mul hsinc
  have hcos1 : Tendsto (fun θ : ℝ => Real.cos θ) (𝓝[≠] (0 : ℝ)) (𝓝 1) := by
    have h : Tendsto Real.cos (𝓝[≠] (0 : ℝ)) (𝓝 (Real.cos 0)) :=
      (Real.continuous_cos.tendsto 0).mono_left
        (nhdsWithin_le_nhds (s := {0}ᶜ) (a := (0 : ℝ)))
    rwa [Real.cos_zero] at h
  -- combine: `(Y_c − u)/θ² = (R/2)((cos θ − 1)/θ² + 2 cos θ (sin θ/θ)²) → (R/2)(−1/2 + 2)`
  have h2 : Tendsto (fun θ : ℝ => (2 : ℝ) * Real.cos θ * (Real.sin θ / θ) ^ 2)
      (𝓝[≠] (0 : ℝ)) (𝓝 ((2 : ℝ) * 1 * 1)) :=
    (tendsto_const_nhds.mul hcos1).mul hsinsq
  have hsum : Tendsto
      (fun θ : ℝ => (Real.cos θ - 1) / θ ^ 2 + (2 : ℝ) * Real.cos θ * (Real.sin θ / θ) ^ 2)
      (𝓝[≠] (0 : ℝ)) (𝓝 (-1 / 2 + (2 : ℝ) * 1 * 1)) := hcos.add h2
  have hcomb : Tendsto
      (fun θ : ℝ => R / 2 *
        ((Real.cos θ - 1) / θ ^ 2 + (2 : ℝ) * Real.cos θ * (Real.sin θ / θ) ^ 2))
      (𝓝[≠] (0 : ℝ)) (𝓝 (R / 2 * (-1 / 2 + (2 : ℝ) * 1 * 1))) := hsum.const_mul (R / 2)
  have hval : R / 2 * (-1 / 2 + (2 : ℝ) * 1 * 1) = 3 * R / 4 := by ring
  rw [hval] at hcomb
  apply hcomb.congr'
  filter_upwards [self_mem_nhdsWithin] with θ hθ
  have hθ0 : θ ≠ 0 := hθ
  rw [causticY_sub_cuspU_eq]
  field_simp

/-- Normalization of the caustic horizontal scale:
`|X_c(θ)|^(2/3)/θ² → R^(2/3)` as `θ → 0`.  Proof route: `abs_causticX_rpow`
reduces the ratio to `R^(2/3)·(sin θ/θ)²`, and `sin θ/θ → 1`
(`Real.continuous_sinc`, `Real.sinc_of_ne_zero`). -/
theorem tendsto_abs_causticX_rpow_div_sq (R : ℝ) (hR : 0 < R) :
    Tendsto (fun θ => |causticX R θ| ^ ((2 : ℝ) / 3) / θ ^ 2) (𝓝[≠] (0 : ℝ))
      (𝓝 (R ^ ((2 : ℝ) / 3))) := by
  have hsinc : Tendsto (fun θ : ℝ => Real.sin θ / θ) (𝓝[≠] (0 : ℝ)) (𝓝 1) := by
    have h : Tendsto Real.sinc (𝓝[≠] (0 : ℝ)) (𝓝 (Real.sinc 0)) :=
      (Real.continuous_sinc.tendsto 0).mono_left
        (nhdsWithin_le_nhds (s := {0}ᶜ) (a := (0 : ℝ)))
    rw [Real.sinc_zero] at h
    apply h.congr'
    filter_upwards [self_mem_nhdsWithin] with θ hθ
    exact Real.sinc_of_ne_zero hθ
  have hsinsq : Tendsto (fun θ : ℝ => (Real.sin θ / θ) ^ 2) (𝓝[≠] (0 : ℝ)) (𝓝 1) := by
    simpa only [pow_two, mul_one] using hsinc.mul hsinc
  have hlim : Tendsto (fun θ : ℝ => R ^ ((2 : ℝ) / 3) * (Real.sin θ / θ) ^ 2)
      (𝓝[≠] (0 : ℝ)) (𝓝 (R ^ ((2 : ℝ) / 3) * 1)) := tendsto_const_nhds.mul hsinsq
  rw [mul_one] at hlim
  apply hlim.congr'
  filter_upwards [self_mem_nhdsWithin] with θ hθ
  have hθ0 : θ ≠ 0 := hθ
  rw [abs_causticX_rpow R θ hR.le]
  field_simp

/-! ## Main target (T2-C4) -/

/-- **Main target, explicit caustic (T2-C4).**  The caustic curve
`(X_c(θ), Y_c(θ)) = (R sin³θ, (R/2) cos θ (1 + 2 sin²θ))` of T2-C3 obeys the
cusp law `Y_c = v·|X_c|^(p/q) + u` for `θ ≪ 1` with the determined constants
`u = R/2`, `v = (3/4)·R^(1/3)`, `p = 2`, `q = 3`, in the precise asymptotic
senses

* `(Y_c(θ) − u)/|X_c(θ)|^(p/q) → v` as `θ → 0` (both signs of `θ`;
  the two arms of the cusp), and
* `Y_c(θ) − (v·|X_c(θ)|^(p/q) + u) = o(|X_c(θ)|^(p/q))`.

Proof route: write the ratio as
`[(Y_c − u)/θ²] / [|X_c|^(2/3)/θ²]` and apply
`tendsto_causticY_sub_cuspU_div_sq` and `tendsto_abs_causticX_rpow_div_sq`;
the limit `(3R/4)/R^(2/3) = (3/4)·R^(1/3)` follows from `Real.rpow_sub`.  The
`IsLittleO` form follows via `Asymptotics.isLittleO_iff_tendsto'` (side
condition vacuous by `causticX_ne_zero`). -/
theorem caustic_cusp_law_explicit (R : ℝ) (hR : 0 < R) :
    Tendsto (fun θ => (causticY R θ - cuspU R) / |causticX R θ| ^ cuspExponent)
        (𝓝[≠] (0 : ℝ)) (𝓝 (cuspV R)) ∧
      (fun θ => causticY R θ - cuspForm R (causticX R θ))
        =o[𝓝[≠] (0 : ℝ)] (fun θ => |causticX R θ| ^ cuspExponent) := by
  have hY := tendsto_causticY_sub_cuspU_div_sq R
  have hX := tendsto_abs_causticX_rpow_div_sq R hR
  have hRp : R ^ ((2 : ℝ) / 3) ≠ 0 := (Real.rpow_pos_of_pos hR _).ne'
  -- on the punctured arc near `0` the caustic abscissa (and its `2/3` power) is nonzero
  have hIoo_ev : ∀ᶠ θ in 𝓝[≠] (0 : ℝ), θ ∈ Set.Ioo (-(Real.pi / 2)) (Real.pi / 2) :=
    nhdsWithin_le_nhds
      (Ioo_mem_nhds (by linarith [Real.pi_pos]) (by linarith [Real.pi_pos]))
  have hXne : ∀ᶠ θ in 𝓝[≠] (0 : ℝ), causticX R θ ≠ 0 := by
    filter_upwards [hIoo_ev, self_mem_nhdsWithin] with θ hI h0
    exact causticX_ne_zero R θ hR hI h0
  have hXpow : ∀ᶠ θ in 𝓝[≠] (0 : ℝ), |causticX R θ| ^ ((2 : ℝ) / 3) ≠ 0 := by
    filter_upwards [hXne] with θ hθ
    exact (Real.rpow_pos_of_pos (abs_pos.mpr hθ) _).ne'
  -- first conjunct: the ratio tends to `v`, as a quotient of the two `/θ²` limits
  have hratio : Tendsto (fun θ => (causticY R θ - cuspU R) / |causticX R θ| ^ cuspExponent)
      (𝓝[≠] 0) (𝓝 ((3 * R / 4) / R ^ ((2 : ℝ) / 3))) := by
    have hdiv := hY.div hX hRp
    apply hdiv.congr'
    filter_upwards [self_mem_nhdsWithin] with θ hθ
    have hθ0 : θ ≠ 0 := hθ
    rw [cuspExponent_eq]
    simp only [Pi.div_apply]
    rw [div_div_div_cancel_right₀ (pow_ne_zero 2 hθ0)]
  have hval : (3 * R / 4) / R ^ ((2 : ℝ) / 3) = cuspV R := by
    show (3 * R / 4) / R ^ ((2 : ℝ) / 3) = 3 / 4 * R ^ ((1 : ℝ) / 3)
    have h1 : R ^ ((1 : ℝ) / 3) = R / R ^ ((2 : ℝ) / 3) := by
      rw [show (1 : ℝ) / 3 = 1 - 2 / 3 by norm_num, Real.rpow_sub hR, Real.rpow_one]
    rw [h1]
    field_simp
  rw [hval] at hratio
  refine ⟨hratio, ?_⟩
  -- second conjunct, via `isLittleO_iff_tendsto'`
  have hside : ∀ᶠ θ in 𝓝[≠] (0 : ℝ),
      |causticX R θ| ^ cuspExponent = 0 → causticY R θ - cuspForm R (causticX R θ) = 0 := by
    filter_upwards [hXpow] with θ hθ hzero
    rw [cuspExponent_eq] at hzero
    exact absurd hzero hθ
  rw [Asymptotics.isLittleO_iff_tendsto' hside]
  have hlim : Tendsto (fun θ => (causticY R θ - cuspForm R (causticX R θ)) /
      |causticX R θ| ^ cuspExponent) (𝓝[≠] 0) (𝓝 (cuspV R - cuspV R)) := by
    have hsub := hratio.sub (tendsto_const_nhds (x := cuspV R))
    apply hsub.congr'
    filter_upwards [hXpow] with θ hθ
    have hne : |causticX R θ| ^ cuspExponent ≠ 0 := by
      rw [cuspExponent_eq]
      exact hθ
    simp only [cuspForm]
    field_simp
    ring
  rw [sub_self] at hlim
  exact hlim

/-- **Main target (T2-C4).**  Let `m φ`, `b φ` be the slope and `y`-intercept
of the reflected line of the ray striking at incidence parameter `φ` (any
functions pinned by `IsLineEquationOfReflectedRay` on the punctured arc), and
let `(Xc θ, Yc θ)` be the limiting intersection point of the reflected lines
at `θ` and `θ + Δθ` (any functions pinned by `IsCausticPoint`).  Then for
`θ ≪ 1` the caustic obeys the cusp law

`Y_c = v·|X_c|^(p/q) + u`  with  `u = R/2`, `v = (3/4)·R^(1/3)`, `p = 2`,
`q = 3`,

in the precise asymptotic senses `(Yc θ − u)/|Xc θ|^(p/q) → v` and
`Yc θ − (v·|Xc θ|^(p/q) + u) = o(|Xc θ|^(p/q))` as `θ → 0` (two-sided,
covering both arms of the cusp through `|X_c|`).

Proof route: on the punctured arc, `slope_intercept_of_reflected_ray` (T2-C1
bridge) fixes `m`, `b` to the exact formulas, `causticPoint_eq` (T2-C3 bridge)
and `IsCausticPoint.unique` then identify `Xc θ = causticX R θ` and
`Yc θ = causticY R θ`; the punctured arc is a neighborhood of `0` within
`{0}ᶜ`, so `Filter.Tendsto.congr'`/`Asymptotics.IsLittleO.congr'` transport
`caustic_cusp_law_explicit` to `(Xc, Yc)`. -/
theorem caustic_cusp_law (R : ℝ) (hR : 0 < R)
    (m b : ℝ → ℝ)
    (hmb : ∀ φ ∈ Set.Ioo (-(Real.pi / 2)) (Real.pi / 2), φ ≠ 0 →
      IsLineEquationOfReflectedRay R φ (m φ) (b φ))
    (Xc Yc : ℝ → ℝ)
    (hc : ∀ θ ∈ Set.Ioo (-(Real.pi / 2)) (Real.pi / 2), θ ≠ 0 →
      IsCausticPoint m b θ !₂[Xc θ, Yc θ]) :
    Tendsto (fun θ => (Yc θ - cuspU R) / |Xc θ| ^ cuspExponent)
        (𝓝[≠] (0 : ℝ)) (𝓝 (cuspV R)) ∧
      (fun θ => Yc θ - cuspForm R (Xc θ))
        =o[𝓝[≠] (0 : ℝ)] (fun θ => |Xc θ| ^ cuspExponent) := by
  obtain ⟨h1, h2⟩ := caustic_cusp_law_explicit R hR
  -- near `0`, any caustic witness pinned by `hc` coincides with the explicit curve
  have hIoo_ev : ∀ᶠ θ in 𝓝[≠] (0 : ℝ), θ ∈ Set.Ioo (-(Real.pi / 2)) (Real.pi / 2) :=
    nhdsWithin_le_nhds
      (Ioo_mem_nhds (by linarith [Real.pi_pos]) (by linarith [Real.pi_pos]))
  have hXY : ∀ᶠ θ in 𝓝[≠] (0 : ℝ), Xc θ = causticX R θ ∧ Yc θ = causticY R θ := by
    filter_upwards [hIoo_ev, self_mem_nhdsWithin] with θ hI h0
    have hθ0 : θ ≠ 0 := h0
    have hU := (hc θ hI hθ0).unique (causticPoint_eq R θ hR hI hθ0 m b hmb)
    have hx := congrArg (fun p : Plane => p 0) hU
    have hy := congrArg (fun p : Plane => p 1) hU
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one] at hx hy
    exact ⟨hx, hy⟩
  refine ⟨h1.congr' ?_, h2.congr' ?_ ?_⟩
  · filter_upwards [hXY] with θ hθ
    rw [hθ.1, hθ.2]
  · filter_upwards [hXY] with θ hθ
    rw [hθ.1, hθ.2]
  · filter_upwards [hXY] with θ hθ
    rw [hθ.1]

end IPhO2026.T2C4
