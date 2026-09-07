import Mathlib

open Real Filter InnerProductGeometry
open scoped InnerProductSpace RealInnerProductSpace Topology

/-!
# IPhO 2026, Theory problem T1-B2 — the unbound electron–positron pair (`μ = 15/2`)

## Problem-side summary (source: T1 page 2, figure 1b)

A positron `e⁺` and an electron `e⁻`, each of mass `m`, with charges of equal
magnitude `e` and opposite sign, are at one instant separated by `100·a₀`. Their
velocities are antiparallel and perpendicular to the separation line (figure 1b:
`e⁺` above moving right, `e⁻` below moving left, separation vertical). Each
particle has angular momentum of magnitude `μ·ℏ` about the system's center of
mass, with `μ` a dimensionless factor. The system is isolated, classical,
non-relativistic, and interacts only electrostatically. The problem defines
`a₀ = 4πε₀ℏ²/(m e²)` (Bohr radius) and `k = 1/(4πε₀)` (Coulomb's constant), and
supplies two hints:

* **Hint 1.** the eccentricity of the conic trajectory is
  `ε = √(1 + 4L²E/(k²e⁴m))`, with `E` the total energy and `L` the magnitude of
  the total angular momentum;
* **Hint 2.** a conic in polar coordinates is `r = a/(1 − ε cos θ)`.

**Subquestion T1-B2.** For `μ = 15/2` the pair is unbound. With `u⃗∞` the velocity
of `e⁺` relative to `e⁻` as the separation tends to infinity, find the angle
between `u⃗∞` and the initial line of motion of `e⁺`, in degrees.

## Candidate derived from problem-side evidence only (answer-blind)

* Equal-magnitude angular momenta about the center of mass plus antiparallel
  velocities force `v⃗₋(0) = −v⃗₊(0)`; hence `u⃗(0) = 2v⃗₊(0)` is parallel to the
  initial line of motion of `e⁺`, and `m·(100a₀/2)·‖v⃗₊(0)‖ = μℏ`.
* With `k e² = ℏ²/(m a₀)`: the total energy evaluates to
  `E = ℏ²(μ² − 25)/(2500 m a₀²)` and the total angular momentum to `L = 2μℏ`.
* Hint 1 then gives `ε = √(1 + 16μ²(μ² − 25)/2500)`; at `μ = 15/2`,
  `ε = √(49/4) = 7/2` (and `E = ℏ²/(80 m a₀²) > 0`, consistent with unbound).
* The initial instant is an apsis (`r⃗(0) ⊥ u⃗(0)`); on the unbound orbit it is the
  periapsis, so Hint 2's axis is `e₀ = −r̂(0)` and `a = 100a₀·(1 + ε) = 450 a₀`.
* The outgoing asymptote satisfies `1 − ε⟨e₀, r̂∞⟩ = 0`, i.e. the undirected angle
  from `e₀` to `u⃗∞ ∥ r̂∞` is `arccos (2/7)`; since `v⃗₊(0) ⊥ e₀` and the outgoing
  branch keeps a positive component along `u⃗(0)`, the requested angle is
  `π/2 − arccos (2/7) = arcsin (2/7) ≈ 16.60°`.

## Declarations

* `Constants`, `Constants.coulombK`, `Constants.bohrRadius` — physical constants
  and the two defining relations of the problem statement.
* `PairMotion` and derived coordinates (`relPos`, `relVel`, `cmPos`, `cmVel`).
* `CoulombKeplerLaws` — governing-law package: Newton's second law with the
  Coulomb attraction, the conserved energy and angular momentum of the relative
  motion, the conic orbit and eccentricity exactly as given by Hints 1–2, and
  the unbound-escape facts of the subquestion (separation → ∞, `u⃗∞` exists).
* `InitialData` — the instant data of the problem and figure 1b.
* Bridge lemmas evaluating `E`, `L`, `ε`, the periapsis geometry, and the
  asymptote direction; main theorem `angle_uInfinity_initial_positron_motion`
  (blueprint label `thm:physics:ipho_2026_t1_b2:target`) with the degree form
  and certified decimal bounds.
-/

namespace IPhO2026.T1B2

/-- The orbital plane of the pair: central-force motion is planar, and all motion
takes place in the plane of figure 1b. -/
abbrev Plane : Type := EuclideanSpace ℝ (Fin 2)

/-- The out-of-plane scalar component of the planar wedge product,
`planeWedge x y = x₀ y₁ − x₁ y₀`. Masses times wedges of positions and velocities
are the signed angular momenta (about the origin/center of mass) used below. -/
def planeWedge (x y : Plane) : ℝ := x 0 * y 1 - x 1 * y 0

/-! ## Planar linear algebra: coordinates, rotation, and wedge identities -/

/-- The 90-degree rotation in the plane, `planeRot (x₀, x₁) = (−x₁, x₀)`. -/
noncomputable def planeRot (x : Plane) : Plane :=
  (-x 1) • EuclideanSpace.single (0 : Fin 2) (1 : ℝ)
    + (x 0) • EuclideanSpace.single (1 : Fin 2) (1 : ℝ)

lemma planeRot_zero (x : Plane) : planeRot x 0 = -x 1 := by simp [planeRot]

lemma planeRot_one (x : Plane) : planeRot x 1 = x 0 := by simp [planeRot]

lemma inner_eq_coords (x y : Plane) : ⟪x, y⟫_ℝ = x 0 * y 0 + x 1 * y 1 := by
  rw [PiLp.inner_apply, Fin.sum_univ_two]; simp [RCLike.inner_apply]; ring

lemma norm_sq_eq_coords (x : Plane) : ‖x‖ ^ 2 = (x 0) ^ 2 + (x 1) ^ 2 := by
  rw [EuclideanSpace.norm_eq, Real.sq_sqrt (by positivity), Fin.sum_univ_two]
  simp [sq_abs]

lemma inner_planeRot_left (x y : Plane) : ⟪planeRot x, y⟫_ℝ = planeWedge x y := by
  rw [inner_eq_coords, planeRot_zero, planeRot_one]; simp only [planeWedge]; ring

lemma inner_planeRot_right (x y : Plane) : ⟪x, planeRot y⟫_ℝ = -planeWedge x y := by
  rw [inner_eq_coords, planeRot_zero, planeRot_one]; simp only [planeWedge]; ring

lemma norm_planeRot (x : Plane) : ‖planeRot x‖ = ‖x‖ := by
  have h1 : ‖planeRot x‖ ^ 2 = ‖x‖ ^ 2 := by
    rw [norm_sq_eq_coords, norm_sq_eq_coords, planeRot_zero, planeRot_one]; ring
  have h2 : |‖planeRot x‖| = |‖x‖| := (sq_eq_sq_iff_abs_eq_abs _ _).mp h1
  rwa [abs_of_nonneg (norm_nonneg _), abs_of_nonneg (norm_nonneg _)] at h2

/-- The master identity of plane geometry: `(x ∧ y)² + ⟨x, y⟩² = ‖x‖²‖y‖²`. -/
lemma planeWedge_sq_add_inner_sq (x y : Plane) :
    planeWedge x y ^ 2 + ⟪x, y⟫_ℝ ^ 2 = ‖x‖ ^ 2 * ‖y‖ ^ 2 := by
  rw [inner_eq_coords, norm_sq_eq_coords, norm_sq_eq_coords]; simp only [planeWedge]; ring

/-- Binet–Cauchy in the plane: `⟨e,e⟩⟨x,y⟩ = ⟨e,x⟩⟨e,y⟩ + (e∧x)(e∧y)`. -/
lemma inner_mul_inner_planeWedge (e x y : Plane) :
    ⟪e, e⟫_ℝ * ⟪x, y⟫_ℝ = ⟪e, x⟫_ℝ * ⟪e, y⟫_ℝ + planeWedge e x * planeWedge e y := by
  rw [inner_eq_coords, inner_eq_coords, inner_eq_coords, inner_eq_coords]
  simp only [planeWedge]; ring

/-- With a unit vector `e`: `⟨x,y⟩ = ⟨e,x⟩⟨e,y⟩ + (e∧x)(e∧y)`. -/
lemma inner_eq_inner_axis (e x y : Plane) (he : ‖e‖ = 1) :
    ⟪x, y⟫_ℝ = ⟪e, x⟫_ℝ * ⟪e, y⟫_ℝ + planeWedge e x * planeWedge e y := by
  have h := inner_mul_inner_planeWedge e x y
  rw [real_inner_self_eq_norm_sq, he] at h; simpa using h

lemma planeWedge_smul_left (a : ℝ) (x y : Plane) :
    planeWedge (a • x) y = a * planeWedge x y := by
  simp only [planeWedge, PiLp.smul_apply, smul_eq_mul]; ring

lemma planeWedge_smul_right (a : ℝ) (x y : Plane) :
    planeWedge x (a • y) = a * planeWedge x y := by
  simp only [planeWedge, PiLp.smul_apply, smul_eq_mul]; ring

lemma planeWedge_neg_left (x y : Plane) : planeWedge (-x) y = -planeWedge x y := by
  have h := planeWedge_smul_left (-1) x y
  rwa [neg_one_smul, neg_one_mul] at h

lemma planeWedge_self (x : Plane) : planeWedge x x = 0 := by simp only [planeWedge]; ring

lemma planeWedge_comm (x y : Plane) : planeWedge x y = -planeWedge y x := by
  simp only [planeWedge]; ring

lemma planeWedge_add_left (x y z : Plane) :
    planeWedge (x + y) z = planeWedge x z + planeWedge y z := by
  simp only [planeWedge, PiLp.add_apply]; ring

lemma planeWedge_add_right (x y z : Plane) :
    planeWedge x (y + z) = planeWedge x y + planeWedge x z := by
  simp only [planeWedge, PiLp.add_apply]; ring

lemma planeWedge_sub_left (x y z : Plane) :
    planeWedge (x - y) z = planeWedge x z - planeWedge y z := by
  simp only [planeWedge, PiLp.sub_apply]; ring

lemma planeWedge_sub_right (x y z : Plane) :
    planeWedge x (y - z) = planeWedge x y - planeWedge x z := by
  simp only [planeWedge, PiLp.sub_apply]; ring

lemma planeWedge_planeRot_left_unit (e : Plane) (he : ‖e‖ = 1) :
    planeWedge e (planeRot e) = 1 := by
  have hee : (e 0) ^ 2 + (e 1) ^ 2 = 1 := by
    have h := norm_sq_eq_coords e; rw [he] at h; linarith [h]
  rw [← inner_planeRot_left, inner_eq_coords, planeRot_zero, planeRot_one]
  linear_combination hee

/-! ## Real-analysis helpers: slopes, Cesàro means, Taylor bounds for `sin` -/

/-- A function with strictly positive derivative at `a` is strictly increasing right
through `a`: `g a < g t` for all `t > a` sufficiently close to `a`. -/
theorem eventually_gt_of_hasDerivAt_pos {g : ℝ → ℝ} {a c : ℝ}
    (hg : HasDerivAt g c a) (hc : 0 < c) : ∀ᶠ t in 𝓝[>] a, g a < g t := by
  rw [hasDerivAt_iff_tendsto_slope] at hg
  have hmono : 𝓝[>] a ≤ 𝓝[≠] a := nhdsWithin_mono a (fun _ ht => ne_of_gt ht)
  have hg' : Tendsto (slope g a) (𝓝[>] a) (𝓝 c) := hg.mono_left hmono
  have hev : ∀ᶠ t in 𝓝[>] a, c / 2 < slope g a t :=
    hg' (eventually_gt_nhds (half_lt_self_iff.mpr hc))
  filter_upwards [hev, self_mem_nhdsWithin] with t ht hta
  have hsub : t - a ≠ 0 := sub_ne_zero.mpr (ne_of_gt hta)
  have hpos : 0 < t - a := sub_pos.mpr hta
  have hmul : g t - g a = slope g a t * (t - a) := by
    rw [slope, smul_eq_mul, mul_comm ((t - a)⁻¹) _, ← div_eq_mul_inv,
      div_mul_cancel₀ _ hsub]
  have hmulpos : 0 < slope g a t * (t - a) := mul_pos (by linarith [ht]) hpos
  linarith [hmul, hmulpos]

/-- Cesàro mean of the derivative: if `f` is differentiable with continuous
derivative `f'` and `f' t → c`, then `t⁻¹ • (f t − f 0) → c`. -/
theorem tendsto_inv_smul_sub_of_tendsto_deriv {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [CompleteSpace E] {f : ℝ → E} {f' : ℝ → E} {c : E}
    (hder : ∀ t, HasDerivAt f (f' t) t) (hcont : Continuous f')
    (hlim : Tendsto f' atTop (𝓝 c)) :
    Tendsto (fun t => t⁻¹ • (f t - f 0)) atTop (𝓝 c) := by
  rw [Metric.tendsto_atTop] at hlim ⊢
  intro ε hε
  obtain ⟨T, hT⟩ := hlim (ε / 2) (half_pos hε)
  have hftc : ∀ b : ℝ, ∫ s in (0 : ℝ)..b, f' s = f b - f 0 := fun b =>
    intervalIntegral.integral_deriv_eq_sub' f (funext fun s => (hder s).deriv)
      (fun x _ => (hder x).differentiableAt) hcont.continuousOn
  set T₀ := max T 0 with hT₀def
  have hT₀T : T ≤ T₀ := le_max_left _ _
  have hT₀0 : (0 : ℝ) ≤ T₀ := le_max_right _ _
  set K := ‖∫ s in (0 : ℝ)..T₀, (f' s - c)‖ with hKdef
  have hK0 : 0 ≤ K := norm_nonneg _
  refine ⟨max T₀ (2 * K / ε + 1), fun t ht => ?_⟩
  have htT₀ : T₀ ≤ t := le_trans (le_max_left _ _) ht
  have ht1 : (1 : ℝ) ≤ t :=
    le_trans (le_add_of_nonneg_left (by positivity)) (le_trans (le_max_right _ _) ht)
  have ht0 : (0 : ℝ) < t := lt_of_lt_of_le one_pos ht1
  have ht0' : t ≠ 0 := ne_of_gt ht0
  have hε0 : (0 : ℝ) < ε := hε
  have key : t⁻¹ • (f t - f 0) - c = t⁻¹ • ∫ s in (0 : ℝ)..t, (f' s - c) := by
    have hi : IntervalIntegrable f' MeasureTheory.volume 0 t := hcont.intervalIntegrable 0 t
    rw [intervalIntegral.integral_sub hi intervalIntegrable_const, hftc,
      intervalIntegral.integral_const, sub_zero]
    conv_rhs => rw [smul_sub, smul_smul, inv_mul_cancel₀ ht0', one_smul]
  have hsplit : ∫ s in (0 : ℝ)..t, (f' s - c)
      = (∫ s in (0 : ℝ)..T₀, (f' s - c)) + ∫ s in T₀..t, (f' s - c) := by
    rw [← intervalIntegral.integral_add_adjacent_intervals
      ((hcont.sub continuous_const).intervalIntegrable _ _)
      ((hcont.sub continuous_const).intervalIntegrable _ _)]
  have htail : ‖∫ s in T₀..t, (f' s - c)‖ ≤ (ε / 2) * (t - T₀) := by
    have h1 := intervalIntegral.norm_integral_le_of_norm_le_const (a := T₀) (b := t)
      (C := ε / 2) (f := fun s => f' s - c) (by
        intro s hs
        rw [Set.uIoc_of_le htT₀] at hs
        have hsT : T ≤ s := le_trans hT₀T hs.1.le
        have hdist := hT s hsT
        rw [dist_eq_norm] at hdist
        exact hdist.le)
    rwa [abs_of_nonneg (sub_nonneg.mpr htT₀)] at h1
  have hmain : ‖t⁻¹ • (f t - f 0) - c‖ < ε := by
    rw [key, hsplit]
    have hn1 : ‖t⁻¹ • ((∫ s in (0 : ℝ)..T₀, (f' s - c)) + ∫ s in T₀..t, (f' s - c))‖
        = t⁻¹ * ‖(∫ s in (0 : ℝ)..T₀, (f' s - c)) + ∫ s in T₀..t, (f' s - c)‖ := by
      rw [norm_smul, Real.norm_of_nonneg (inv_nonneg.mpr ht0.le)]
    rw [hn1]
    have hle1 : ‖(∫ s in (0 : ℝ)..T₀, (f' s - c)) + ∫ s in T₀..t, (f' s - c)‖
        ≤ K + (ε / 2) * (t - T₀) := by
      have h2 := norm_add_le (∫ s in (0 : ℝ)..T₀, (f' s - c)) (∫ s in T₀..t, (f' s - c))
      rw [hKdef]
      linarith [h2, htail]
    have hlt2 : t⁻¹ * (K + (ε / 2) * (t - T₀)) < ε := by
      have htK : t⁻¹ * K < ε / 2 := by
        have h1 : 2 * K / ε < t :=
          lt_of_lt_of_le (by linarith) (le_trans (le_max_right _ _) ht)
        have h2 : 2 * K < t * ε := (div_lt_iff₀ hε0).mp h1
        have h3 : t⁻¹ * K = K / t := by rw [div_eq_mul_inv, mul_comm]
        rw [h3, div_lt_iff₀ ht0]
        linarith [h2]
      have hle3 : (ε / 2) * (t - T₀) ≤ (ε / 2) * t :=
        mul_le_mul_of_nonneg_left (by linarith) (le_of_lt (half_pos hε0))
      have hle4 : t⁻¹ * (K + (ε / 2) * (t - T₀)) ≤ t⁻¹ * (K + (ε / 2) * t) := by
        apply mul_le_mul_of_nonneg_left _ (inv_nonneg.mpr ht0.le)
        linarith [hle3]
      have heq : t⁻¹ * (K + (ε / 2) * t) = t⁻¹ * K + ε / 2 := by
        rw [mul_add, mul_comm (ε / 2) t, ← mul_assoc, inv_mul_cancel₀ ht0', one_mul]
      have h5 : t⁻¹ * (K + (ε / 2) * (t - T₀)) ≤ t⁻¹ * K + ε / 2 := by
        linarith [hle4, heq]
      linarith [h5, htK]
    calc t⁻¹ * ‖(∫ s in (0 : ℝ)..T₀, (f' s - c)) + ∫ s in T₀..t, (f' s - c)‖
        ≤ t⁻¹ * (K + (ε / 2) * (t - T₀)) :=
          mul_le_mul_of_nonneg_left hle1 (inv_nonneg.mpr ht0.le)
      _ < ε := hlt2
  rw [dist_eq_norm]
  exact hmain

/-- `∫₀ˣ (1 − t²/2) dt = x − x³/6`. -/
lemma int_one_sub_sq_div_two (x : ℝ) :
    ∫ t in (0 : ℝ)..x, (1 - t ^ 2 / 2) = x - x ^ 3 / 6 := by
  rw [intervalIntegral.integral_sub intervalIntegrable_const
      (((continuous_pow 2).div_const 2).intervalIntegrable _ _),
    intervalIntegral.integral_const, intervalIntegral.integral_div,
    intervalIntegral.integral_pow]
  simp only [smul_eq_mul, sub_zero]
  ring

/-- `∫₀ˣ (s − s³/6) ds = x²/2 − x⁴/24`. -/
lemma int_id_sub_cube_div_six (x : ℝ) :
    ∫ s in (0 : ℝ)..x, (s - s ^ 3 / 6) = x ^ 2 / 2 - x ^ 4 / 24 := by
  rw [intervalIntegral.integral_sub (continuous_id.intervalIntegrable _ _)
      (((continuous_pow 3).div_const 6).intervalIntegrable _ _),
    intervalIntegral.integral_div, intervalIntegral.integral_pow,
    intervalIntegral.integral_id]
  simp only [smul_eq_mul, sub_zero]
  ring

/-- The Taylor lower bound `x − x³/6 ≤ sin x` for `x ≥ 0`, from `1 − t²/2 ≤ cos t`. -/
lemma sin_lower (x : ℝ) (hx : 0 ≤ x) : x - x ^ 3 / 6 ≤ Real.sin x := by
  have h1 : ∫ t in (0 : ℝ)..x, (1 - t ^ 2 / 2) ≤ ∫ t in (0 : ℝ)..x, Real.cos t := by
    apply intervalIntegral.integral_mono_on hx
    · exact ((continuous_const.sub ((continuous_pow 2).div_const 2))).intervalIntegrable _ _
    · exact Real.continuous_cos.intervalIntegrable _ _
    · intro t _
      exact Real.one_sub_sq_div_two_le_cos
  rw [int_one_sub_sq_div_two, intervalIntegral.integral_cos, Real.sin_zero, sub_zero] at h1
  exact h1

/-- The Taylor upper bound `sin x ≤ x − x³/6 + x⁵/120` for `x ≥ 0`. -/
lemma sin_upper (x : ℝ) (hx : 0 ≤ x) : Real.sin x ≤ x - x ^ 3 / 6 + x ^ 5 / 120 := by
  have hcos : ∀ t : ℝ, 0 ≤ t → Real.cos t ≤ 1 - t ^ 2 / 2 + t ^ 4 / 24 := by
    intro t ht
    have h1 : ∫ s in (0 : ℝ)..t, (s - s ^ 3 / 6) ≤ ∫ s in (0 : ℝ)..t, Real.sin s := by
      apply intervalIntegral.integral_mono_on ht
      · exact ((continuous_id.sub ((continuous_pow 3).div_const 6))).intervalIntegrable _ _
      · exact Real.continuous_sin.intervalIntegrable _ _
      · intro s hs
        exact sin_lower s hs.1
    rw [intervalIntegral.integral_sin, Real.cos_zero] at h1
    rw [int_id_sub_cube_div_six] at h1
    linarith [h1]
  have h3 : ∫ t' in (0 : ℝ)..x, Real.cos t' ≤ ∫ t' in (0 : ℝ)..x, (1 - t' ^ 2 / 2 + t' ^ 4 / 24) := by
    apply intervalIntegral.integral_mono_on hx
    · exact Real.continuous_cos.intervalIntegrable _ _
    · exact (((continuous_const.sub ((continuous_pow 2).div_const 2)).add
        ((continuous_pow 4).div_const 24))).intervalIntegrable _ _
    · intro t ht
      exact hcos t ht.1
  rw [intervalIntegral.integral_cos, Real.sin_zero, sub_zero] at h3
  have h4 : ∫ t' in (0 : ℝ)..x, (1 - t' ^ 2 / 2 + t' ^ 4 / 24) = x - x ^ 3 / 6 + x ^ 5 / 120 := by
    rw [intervalIntegral.integral_add
      (((continuous_const.sub ((continuous_pow 2).div_const 2))).intervalIntegrable _ _)
      (((continuous_pow 4).div_const 24).intervalIntegrable _ _),
      int_one_sub_sq_div_two, intervalIntegral.integral_div, intervalIntegral.integral_pow]
    simp only [smul_eq_mul, sub_zero]
    ring
  rw [h4] at h3
  exact h3

/-- A continuous function negative at `s` but positive at `t₁ < s` attains a largest
zero on `[t₁, s]`. -/
lemma exists_max_zero_of_neg {g : ℝ → ℝ} (hg : Continuous g) {t₁ s : ℝ}
    (ht₁s : t₁ ≤ s) (hgt : 0 < g t₁) (hgs : g s < 0) :
    ∃ T ∈ g ⁻¹' {0} ∩ Set.Icc t₁ s, ∀ z ∈ g ⁻¹' {0} ∩ Set.Icc t₁ s, z ≤ T := by
  have hne : (g ⁻¹' {0} ∩ Set.Icc t₁ s).Nonempty := by
    have hsub := intermediate_value_Ioo' ht₁s hg.continuousOn (Set.mem_Ioo.mpr ⟨hgs, hgt⟩)
    obtain ⟨z, hz, hz0⟩ := hsub
    exact ⟨z, Set.mem_singleton_iff.mpr hz0, Set.mem_Icc.mpr ⟨hz.1.le, hz.2.le⟩⟩
  have hcomp : IsCompact (g ⁻¹' {0} ∩ Set.Icc t₁ s) :=
    isCompact_Icc.inter_left (isClosed_singleton.preimage hg)
  exact ⟨sSup _, hcomp.sSup_mem hne, fun z hz => le_csSup hcomp.bddAbove hz⟩

/-! ## Physical constants -/

/-- The physical constants of the problem: the common mass `m` of `e±`, the
elementary charge `e` (the magnitude of each charge), the reduced Planck
constant `ℏ`, and the vacuum permittivity `ε₀`. Coulomb's constant `k` and the
Bohr radius `a₀` are the derived constants `Constants.coulombK` and
`Constants.bohrRadius` defined by the relations given in the problem statement. -/
structure Constants where
  /-- the common mass `m` of the positron and the electron -/
  mass : ℝ
  /-- the elementary charge `e`; the particles carry `+e` and `-e` -/
  charge : ℝ
  /-- the reduced Planck constant `ℏ` -/
  hbar : ℝ
  /-- the vacuum permittivity `ε₀` -/
  permittivity : ℝ
  mass_pos : 0 < mass
  charge_pos : 0 < charge
  hbar_pos : 0 < hbar
  permittivity_pos : 0 < permittivity

namespace Constants

/-- Coulomb's constant `k = 1/(4πε₀)`, as defined in the problem statement. -/
noncomputable def coulombK (c : Constants) : ℝ := 1 / (4 * π * c.permittivity)

/-- The Bohr radius `a₀ = 4πε₀ℏ²/(m e²)`, as defined in the problem statement. -/
noncomputable def bohrRadius (c : Constants) : ℝ :=
  4 * π * c.permittivity * c.hbar ^ 2 / (c.mass * c.charge ^ 2)

lemma coulombK_pos (c : Constants) : 0 < c.coulombK := by
  have hε := c.permittivity_pos
  rw [coulombK]
  positivity

lemma bohrRadius_pos (c : Constants) : 0 < c.bohrRadius := by
  have hm := c.mass_pos
  have he := c.charge_pos
  have hh := c.hbar_pos
  have hε := c.permittivity_pos
  rw [bohrRadius]
  positivity

/-- The Bohr radius in terms of `k`: `a₀ = ℏ²/(k m e²)` (from `k = 1/(4πε₀)`). -/
lemma bohrRadius_eq (c : Constants) :
    c.bohrRadius = c.hbar ^ 2 / (c.coulombK * c.mass * c.charge ^ 2) := by
  have hm : c.mass ≠ 0 := ne_of_gt c.mass_pos
  have he : c.charge ≠ 0 := ne_of_gt c.charge_pos
  have hε : c.permittivity ≠ 0 := ne_of_gt c.permittivity_pos
  have hπ : (π : ℝ) ≠ 0 := pi_ne_zero
  rw [bohrRadius, coulombK]
  field_simp

/-- The working form of the Coulomb coupling, `k e² = ℏ²/(m a₀)`. -/
lemma coulombK_mul_charge_sq (c : Constants) :
    c.coulombK * c.charge ^ 2 = c.hbar ^ 2 / (c.mass * c.bohrRadius) := by
  have hm : c.mass ≠ 0 := ne_of_gt c.mass_pos
  have he : c.charge ≠ 0 := ne_of_gt c.charge_pos
  have hh : c.hbar ≠ 0 := ne_of_gt c.hbar_pos
  have hε : c.permittivity ≠ 0 := ne_of_gt c.permittivity_pos
  have hπ : (π : ℝ) ≠ 0 := pi_ne_zero
  rw [bohrRadius, coulombK]
  field_simp

end Constants

/-! ## The motion of the pair and the two-body coordinates -/

/-- A planar motion of the positron–electron pair: twice continuously
differentiable position functions of time `t`, where `t = 0` is the instant
described in the problem statement (figure 1b). -/
structure PairMotion where
  /-- position of the positron `e⁺` -/
  positron : ℝ → Plane
  /-- position of the electron `e⁻` -/
  electron : ℝ → Plane
  positron_smooth : ContDiff ℝ 2 positron
  electron_smooth : ContDiff ℝ 2 electron

namespace PairMotion

/-- The separation vector `r⃗(t) = r⃗₊(t) − r⃗₋(t)` (pointing from `e⁻` to `e⁺`). -/
def relPos (P : PairMotion) (t : ℝ) : Plane := P.positron t - P.electron t

/-- The relative velocity `u⃗(t) = v⃗₊(t) − v⃗₋(t)`: the velocity of `e⁺` relative
to `e⁻`. The `u⃗∞` of the problem is the limit of this function as `t → ∞`. -/
noncomputable def relVel (P : PairMotion) (t : ℝ) : Plane :=
  deriv P.positron t - deriv P.electron t

/-- The center-of-mass position `R⃗(t) = (r⃗₊(t) + r⃗₋(t))/2` (equal masses). -/
noncomputable def cmPos (P : PairMotion) (t : ℝ) : Plane := (1 / 2 : ℝ) • (P.positron t + P.electron t)

/-- The center-of-mass velocity `V⃗(t) = (v⃗₊(t) + v⃗₋(t))/2` (equal masses). -/
noncomputable def cmVel (P : PairMotion) (t : ℝ) : Plane :=
  (1 / 2 : ℝ) • (deriv P.positron t + deriv P.electron t)

end PairMotion

/-! ## Governing laws -/

/-- **Governing-law package** for the isolated, classical, non-relativistic
electron–positron system whose only interaction is the electrostatic (Coulomb)
attraction, together with the orbital facts supplied by the problem statement.

The package contains:

* Newton's second law for each particle with the Coulomb attraction
  `F = k e²/r²` (`newton_positron`, `newton_electron`) — the fundamental
  dynamics ("classical and non-relativistic … only interaction … electrostatic");
* the two first integrals of the relative motion `r⃗ = r⃗₊ − r⃗₋` (reduced mass
  `m/2`): the conserved energy `E` (`energy_eq`, equal to the total energy of the
  pair since the center of mass is at rest) and the conserved signed angular
  momentum `L` (`angMom_eq`, the total angular momentum about the center of mass);
* the orbit geometry given by the problem's hints: the trajectory is the conic
  `r = a/(1 − ε cos θ)` of Hint 2, written in the vector form
  `‖r⃗‖ = a + ε⟨e₀, r⃗⟩` with `a > 0` and a unit reference direction `e₀`
  (`conic_eq`, `semiLatus_pos`, `axis_unit`), and the eccentricity is given by
  Hint 1, `ε = √(1 + 4L²E/(k²e⁴m))` (`eccentricity_eq`);
* the unbound-escape facts of this subquestion: the separation tends to infinity
  (`escape`, "the system is unbound … as the separation distance between them
  tends to infinity") and the relative velocity has a limit `u⃗∞`
  (`uInfinity_tendsto`, the problem's "let `u⃗∞` be the velocity of `e⁺` relative
  to `e⁻` as the separation tends to infinity"). -/
structure CoulombKeplerLaws (c : Constants) (P : PairMotion) where
  /-- the conserved total energy `E` of the pair -/
  energy : ℝ
  /-- the conserved signed total angular momentum `L` about the center of mass
  (out-of-plane scalar; `|L|` is the magnitude entering Hint 1) -/
  angMom : ℝ
  /-- the semi-latus rectum `a` of the conic (Hint 2) -/
  semiLatus : ℝ
  /-- the eccentricity `ε` of the conic (Hint 1) -/
  eccentricity : ℝ
  /-- the unit reference direction of the conic's polar axis (`θ = 0` in Hint 2) -/
  axis : Plane
  /-- the asymptotic relative velocity `u⃗∞ = lim_{t → ∞} u⃗(t)` -/
  uInfinity : Plane
  /-- Newton's second law for the positron: `m a⃗₊ = −k e² r⃗/‖r⃗‖³` (attraction
  toward the electron). -/
  newton_positron : ∀ t, c.mass • deriv (deriv P.positron) t =
    (-(c.coulombK * c.charge ^ 2) / ‖P.relPos t‖ ^ 3) • P.relPos t
  /-- Newton's second law for the electron: `m a⃗₋ = +k e² r⃗/‖r⃗‖³` (attraction
  toward the positron). -/
  newton_electron : ∀ t, c.mass • deriv (deriv P.electron) t =
    ((c.coulombK * c.charge ^ 2) / ‖P.relPos t‖ ^ 3) • P.relPos t
  /-- the particles never collide on this orbit (so the force laws are regular) -/
  relPos_ne : ∀ t, P.relPos t ≠ 0
  /-- Conservation of energy: `(m/4)‖u⃗‖² − k e²/‖r⃗‖ = E` for all times. The
  relative-motion energy with reduced mass `m/2`; equals the total energy of the
  pair because the center of mass is at rest (`PairMotion.cmVel_zero`). -/
  energy_eq : ∀ t, (c.mass / 4) * ‖P.relVel t‖ ^ 2
    - c.coulombK * c.charge ^ 2 / ‖P.relPos t‖ = energy
  /-- Conservation of angular momentum: `(m/2)·(r⃗ × u⃗)_z = L` for all times; this
  is the total angular momentum of the pair about the center of mass. -/
  angMom_eq : ∀ t, (c.mass / 2) * planeWedge (P.relPos t) (P.relVel t) = angMom
  /-- the semi-latus rectum is positive -/
  semiLatus_pos : 0 < semiLatus
  /-- the conic's reference direction is a unit vector -/
  axis_unit : ‖axis‖ = 1
  /-- Hint 2 of the problem: the relative orbit is the conic
  `r = a/(1 − ε cos θ)`, equivalently `‖r⃗‖ = a + ε⟨e₀, r⃗⟩`. -/
  conic_eq : ∀ t, ‖P.relPos t‖ = semiLatus + eccentricity * ⟪axis, P.relPos t⟫_ℝ
  /-- Hint 1 of the problem: `ε = √(1 + 4L²E/(k²e⁴m))`. -/
  eccentricity_eq : eccentricity =
    Real.sqrt (1 + 4 * angMom ^ 2 * energy / (c.coulombK ^ 2 * c.charge ^ 4 * c.mass))
  /-- the pair is unbound (given for `μ = 15/2`): the separation tends to
  infinity in forward time -/
  escape : Tendsto (fun t => ‖P.relPos t‖) atTop atTop
  /-- the relative velocity has the limit `u⃗∞` as the separation tends to
  infinity (forward in time) -/
  uInfinity_tendsto : Tendsto P.relVel atTop (𝓝 uInfinity)

/-! ## The initial instant (problem data and figure 1b) -/

/-- The data of the initial instant `t = 0` (problem statement and figure 1b):
the separation is `100 a₀`, the velocities are antiparallel and perpendicular to
the separation line, nonzero, and each particle has angular momentum of
magnitude `μ·ℏ` with respect to the system's center of mass (the midpoint, the
masses being equal). -/
structure InitialData (c : Constants) (P : PairMotion) (mu : ℝ) : Prop where
  /-- initial separation `‖r⃗(0)‖ = 100 a₀` (figure 1b) -/
  separation : ‖P.relPos 0‖ = 100 * c.bohrRadius
  /-- the velocities are antiparallel: `v⃗₋(0) = −s·v⃗₊(0)` for some `s > 0` -/
  v_antiparallel : ∃ s : ℝ, 0 < s ∧ deriv P.electron 0 = (-s) • deriv P.positron 0
  /-- the velocities are perpendicular to the separation line (figure 1b);
  stated for the positron, the electron's perpendicularity follows from
  `v_antiparallel` -/
  v_perpendicular : ⟪deriv P.positron 0, P.relPos 0⟫_ℝ = 0
  /-- the positron is actually moving (figure 1b) -/
  v_positron_ne : deriv P.positron 0 ≠ 0
  /-- angular momentum of the positron about the center of mass:
  `|m ((r⃗₊ − R⃗) × v⃗₊)_z| = μℏ` with `r⃗₊ − R⃗ = r⃗/2` -/
  angMom_positron :
    |c.mass * planeWedge ((1 / 2 : ℝ) • P.relPos 0) (deriv P.positron 0)| = mu * c.hbar
  /-- angular momentum of the electron about the center of mass:
  `|m ((r⃗₋ − R⃗) × v⃗₋)_z| = μℏ` with `r⃗₋ − R⃗ = −r⃗/2` -/
  angMom_electron :
    |c.mass * planeWedge ((1 / 2 : ℝ) • (-P.relPos 0)) (deriv P.electron 0)| = mu * c.hbar

variable {c : Constants} {P : PairMotion}

/-- The relative position is differentiable with derivative `relVel`. -/
lemma hasDerivAt_relPos (P : PairMotion) (t : ℝ) :
    HasDerivAt P.relPos (P.relVel t) t := by
  have hp := ((P.positron_smooth.differentiable (by decide : (2 : ℕ∞) ≠ 0)) t).hasDerivAt
  have he := ((P.electron_smooth.differentiable (by decide : (2 : ℕ∞) ≠ 0)) t).hasDerivAt
  exact hp.sub he

/-- The relative velocity is continuous (the motions are `C²`). -/
lemma relVel_continuous (P : PairMotion) : Continuous P.relVel :=
  (P.positron_smooth.continuous_deriv (by decide : (1 : ℕ∞) ≤ 2)).sub
    (P.electron_smooth.continuous_deriv (by decide : (1 : ℕ∞) ≤ 2))

/-- Cesàro consequence of `uInfinity_tendsto`: the time-averaged relative
displacement converges to `u⃗∞`. -/
theorem tendsto_relPos_smul_inv (laws : CoulombKeplerLaws c P) :
    Tendsto (fun t => t⁻¹ • (P.relPos t - P.relPos 0)) atTop (𝓝 laws.uInfinity) :=
  tendsto_inv_smul_sub_of_tendsto_deriv (hasDerivAt_relPos P) (relVel_continuous P)
    laws.uInfinity_tendsto

/-! ## Bridge lemmas: initial kinematics -/

/-- From "velocities antiparallel" and "each particle has angular momentum `μℏ`
about the center of mass": the velocities are in fact opposite,
`v⃗₋(0) = −v⃗₊(0)`. (With `v⃗₋(0) = −s·v⃗₊(0)` one computes `|L₋| = s·|L₊|`, and
`|L₊| = |L₋| = μℏ ≠ 0` — nonzero because `v⃗₊(0) ≠ 0`, `r⃗(0) ≠ 0` and
`v⃗₊(0) ⊥ r⃗(0)` — forces `s = 1`.) -/
theorem electron_velocity_neg {mu : ℝ} (ic : InitialData c P mu) :
    deriv P.electron 0 = -deriv P.positron 0 := by
  obtain ⟨s, hs, hsv⟩ := ic.v_antiparallel
  have hm : (0:ℝ) < c.mass := c.mass_pos
  have ha : (0:ℝ) < c.bohrRadius := c.bohrRadius_pos
  have hr0n : ‖P.relPos 0‖ ≠ 0 := by
    rw [ic.separation]; positivity
  have hvpn : ‖deriv P.positron 0‖ ≠ 0 := norm_ne_zero_iff.mpr ic.v_positron_ne
  have hw : planeWedge (P.relPos 0) (deriv P.positron 0) ≠ 0 := by
    intro h
    have hmid := planeWedge_sq_add_inner_sq (P.relPos 0) (deriv P.positron 0)
    rw [h, real_inner_comm (P.relPos 0) (deriv P.positron 0), ic.v_perpendicular] at hmid
    simp only [ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow, add_zero] at hmid
    have hz : ‖P.relPos 0‖ ^ 2 * ‖deriv P.positron 0‖ ^ 2 = 0 := hmid.symm
    rcases mul_eq_zero.mp hz with h1 | h1
    · exact hr0n (pow_eq_zero_iff (by norm_num : (2:ℕ) ≠ 0) |>.mp h1)
    · exact hvpn (pow_eq_zero_iff (by norm_num : (2:ℕ) ≠ 0) |>.mp h1)
  have hX : c.mass * planeWedge ((1/2 : ℝ) • P.relPos 0) (deriv P.positron 0) ≠ 0 := by
    rw [planeWedge_smul_left]
    exact mul_ne_zero (ne_of_gt hm) (mul_ne_zero (by norm_num) hw)
  have hmu : mu * c.hbar ≠ 0 := by
    rw [← ic.angMom_positron]
    intro h
    exact hX (abs_eq_zero.mp h)
  have hme : c.mass * planeWedge ((1/2 : ℝ) • (-P.relPos 0)) (deriv P.electron 0)
      = s * (c.mass * planeWedge ((1/2 : ℝ) • P.relPos 0) (deriv P.positron 0)) := by
    rw [hsv, planeWedge_smul_right, planeWedge_smul_left, planeWedge_neg_left,
      planeWedge_smul_left]
    ring
  have habs : |s * (c.mass * planeWedge ((1/2 : ℝ) • P.relPos 0) (deriv P.positron 0))|
      = mu * c.hbar := by
    rw [← hme]
    exact ic.angMom_electron
  rw [abs_mul, abs_of_pos hs] at habs
  rw [← ic.angMom_positron] at habs
  have hXn : |c.mass * planeWedge ((1/2 : ℝ) • P.relPos 0) (deriv P.positron 0)| ≠ 0 :=
    abs_ne_zero.mpr hX
  have hs1 : s = 1 := by
    have h1 : s * |c.mass * planeWedge ((1/2:ℝ) • P.relPos 0) (deriv P.positron 0)|
        = 1 * |c.mass * planeWedge ((1/2:ℝ) • P.relPos 0) (deriv P.positron 0)| := by
      rw [one_mul]
      exact habs
    exact mul_right_cancel₀ hXn h1
  rw [hsv, hs1, neg_one_smul]

/-- The center of mass is initially at rest (equal masses, opposite velocities);
as the system is isolated it remains at rest, so the given frame is the
center-of-mass frame. -/
theorem cmVel_zero {mu : ℝ} (ic : InitialData c P mu) :
    P.cmVel 0 = 0 := by
  have h := electron_velocity_neg ic
  show (1/2 : ℝ) • (deriv P.positron 0 + deriv P.electron 0) = 0
  rw [h, add_neg_cancel, smul_zero]

/-- The initial relative velocity is twice the positron velocity,
`u⃗(0) = 2·v⃗₊(0)`; in particular it is parallel to the initial line of motion
of `e⁺`. -/
theorem relVel_zero {mu : ℝ} (ic : InitialData c P mu) :
    P.relVel 0 = 2 • deriv P.positron 0 := by
  have h := electron_velocity_neg ic
  show deriv P.positron 0 - deriv P.electron 0 = 2 • deriv P.positron 0
  rw [h, sub_neg_eq_add, two_smul]

/-- The initial relative velocity is perpendicular to the initial separation
(figure 1b): the initial instant is an apsis (extremum of `‖r⃗‖`) of the
relative orbit. -/
theorem relPos_relVel_orthogonal {mu : ℝ} (ic : InitialData c P mu) :
    ⟪P.relPos 0, P.relVel 0⟫_ℝ = 0 := by
  rw [relVel_zero ic, real_inner_smul_right,
    real_inner_comm (P.relPos 0) (deriv P.positron 0), ic.v_perpendicular, mul_zero]

/-- The initial speed of the positron from the angular-momentum datum:
`m·(100a₀/2)·‖v⃗₊(0)‖ = μℏ`, using `v⃗₊(0) ⊥ r⃗(0)` and
`|r⃗₊(0) − R⃗| = ‖r⃗(0)‖/2 = 50 a₀`. -/
theorem initial_speed {mu : ℝ} (ic : InitialData c P mu) :
    c.mass * (100 * c.bohrRadius / 2) * ‖deriv P.positron 0‖ = mu * c.hbar := by
  have hm : (0:ℝ) < c.mass := c.mass_pos
  have habsw : |planeWedge (P.relPos 0) (deriv P.positron 0)|
      = ‖P.relPos 0‖ * ‖deriv P.positron 0‖ := by
    have h := planeWedge_sq_add_inner_sq (P.relPos 0) (deriv P.positron 0)
    rw [real_inner_comm (P.relPos 0) (deriv P.positron 0), ic.v_perpendicular] at h
    simp only [ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow, add_zero] at h
    calc |planeWedge (P.relPos 0) (deriv P.positron 0)|
        = Real.sqrt (planeWedge (P.relPos 0) (deriv P.positron 0) ^ 2) := by
          rw [← sq_abs]
          exact (Real.sqrt_sq (abs_nonneg _)).symm
      _ = Real.sqrt (‖P.relPos 0‖^2 * ‖deriv P.positron 0‖^2) := by rw [h]
      _ = ‖P.relPos 0‖ * ‖deriv P.positron 0‖ := by
          rw [Real.sqrt_mul (sq_nonneg _), Real.sqrt_sq (norm_nonneg _),
            Real.sqrt_sq (norm_nonneg _)]
  have hmain := ic.angMom_positron
  rw [planeWedge_smul_left, abs_mul, abs_mul, abs_of_pos hm,
    abs_of_pos (show (0:ℝ) < 1/2 by norm_num), habsw, ic.separation] at hmain
  linarith [hmain]

/-! ## Bridge lemmas: the conserved quantities evaluated on the initial data -/

/-- The conserved total energy, evaluated at `t = 0`:
`E = m‖v⃗₊(0)‖² − k e²/(100a₀) = ℏ²(μ² − 25)/(2500 m a₀²)`,
using `u⃗(0) = 2v⃗₊(0)`, the angular-momentum datum, and `k e² = ℏ²/(m a₀)`. -/
theorem energy_value (laws : CoulombKeplerLaws c P) {mu : ℝ} (ic : InitialData c P mu) :
    laws.energy = c.hbar ^ 2 * (mu ^ 2 - 25) / (2500 * c.mass * c.bohrRadius ^ 2) := by
  have hm : c.mass ≠ 0 := ne_of_gt c.mass_pos
  have ha : c.bohrRadius ≠ 0 := ne_of_gt c.bohrRadius_pos
  have hm' : (0:ℝ) < c.mass := c.mass_pos
  have ha' : (0:ℝ) < c.bohrRadius := c.bohrRadius_pos
  have hE := laws.energy_eq 0
  rw [relVel_zero ic, norm_smul, mul_pow, ic.separation, c.coulombK_mul_charge_sq] at hE
  have h2 : ‖(2 : ℝ)‖ = 2 := by norm_num
  rw [h2] at hE
  have hspeed := initial_speed ic
  have hvp2 : ‖deriv P.positron 0‖ ^ 2
      = (mu * c.hbar) ^ 2 / (c.mass * (100 * c.bohrRadius / 2)) ^ 2 := by
    have h2' := congrArg (· ^ 2) hspeed
    rw [mul_pow] at h2'
    rw [eq_div_iff (by positivity)]
    linear_combination h2'
  rw [← hE, hvp2]
  field_simp
  ring

/-- The conserved total angular momentum is twice the single-particle angular
momentum, `L = 2 m ((r⃗(0)/2) × v⃗₊(0))_z`. -/
theorem angMom_value (laws : CoulombKeplerLaws c P) {mu : ℝ} (ic : InitialData c P mu) :
    laws.angMom =
      2 * (c.mass * planeWedge ((1 / 2 : ℝ) • P.relPos 0) (deriv P.positron 0)) := by
  have hL := laws.angMom_eq 0
  rw [relVel_zero ic, planeWedge_smul_right] at hL
  have hw : planeWedge ((1/2 : ℝ) • P.relPos 0) (deriv P.positron 0)
      = (1/2) * planeWedge (P.relPos 0) (deriv P.positron 0) := planeWedge_smul_left _ _ _
  rw [hw]
  linarith [hL]

/-- The squared total angular momentum, `L² = 4μ²ℏ²` (the combination entering
Hint 1). -/
theorem angMom_sq (laws : CoulombKeplerLaws c P) {mu : ℝ} (ic : InitialData c P mu) :
    laws.angMom ^ 2 = 4 * (mu * c.hbar) ^ 2 := by
  rw [angMom_value laws ic]
  have h2 := ic.angMom_positron
  have h3 : (c.mass * planeWedge ((1/2:ℝ) • P.relPos 0) (deriv P.positron 0))^2
      = (mu * c.hbar)^2 := by
    rw [← sq_abs, h2]
  linear_combination 4 * h3

/-! ## Bridge lemmas: the orbit for `μ = 15/2` -/

/-- For `μ = 15/2` the total energy is positive — `E = ℏ²/(80 m a₀²) > 0` —
consistent with the given fact that the pair is unbound. -/
theorem energy_pos (laws : CoulombKeplerLaws c P) (ic : InitialData c P (15/2)) :
    0 < laws.energy := by
  rw [energy_value laws ic]
  have hm : (0:ℝ) < c.mass := c.mass_pos
  have ha : (0:ℝ) < c.bohrRadius := c.bohrRadius_pos
  have hh : (0:ℝ) < c.hbar := c.hbar_pos
  have hmu : ((15:ℝ)/2)^2 - 25 = 125/4 := by norm_num
  rw [hmu]
  positivity

/-- The eccentricity from Hint 1 at `μ = 15/2`: with `L² = 4μ²ℏ²`,
`E = ℏ²(μ² − 25)/(2500 m a₀²)` and `k²e⁴m = ℏ⁴/(m a₀²)` one gets
`ε = √(1 + 16μ²(μ² − 25)/2500) = √(49/4) = 7/2`. -/
theorem eccentricity_value (laws : CoulombKeplerLaws c P) (ic : InitialData c P (15/2)) :
    laws.eccentricity = 7 / 2 := by
  have hm : c.mass ≠ 0 := ne_of_gt c.mass_pos
  have ha : c.bohrRadius ≠ 0 := ne_of_gt c.bohrRadius_pos
  rw [laws.eccentricity_eq, angMom_sq laws ic, energy_value laws ic,
    show c.coulombK ^ 2 * c.charge ^ 4 * c.mass = (c.coulombK * c.charge ^ 2) ^ 2 * c.mass
      from by ring,
    c.coulombK_mul_charge_sq]
  have h1 : 1 + 4 * (4 * ((15:ℝ)/2 * c.hbar) ^ 2) *
      (c.hbar ^ 2 * (((15:ℝ)/2) ^ 2 - 25) / (2500 * c.mass * c.bohrRadius ^ 2)) /
      ((c.hbar ^ 2 / (c.mass * c.bohrRadius)) ^ 2 * c.mass) = 49 / 4 := by
    field_simp
    ring
  rw [h1, show (49 : ℝ) / 4 = (7 / 2) ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]

/-- Differentiating Hint 2's identity `‖r⃗‖ = a + ε⟨e₀, r⃗⟩` at the apsis `t = 0`:
the conic's reference axis is perpendicular to the initial relative velocity. -/
theorem inner_axis_relVel0 (laws : CoulombKeplerLaws c P) (ic : InitialData c P (15/2)) :
    ⟪laws.axis, P.relVel 0⟫_ℝ = 0 := by
  have hFG : (fun t => ‖P.relPos t‖ ^ 2)
      = fun t => (laws.semiLatus + laws.eccentricity * ⟪laws.axis, P.relPos t⟫_ℝ) ^ 2 :=
    funext fun t => by rw [laws.conic_eq t]
  have hdl : HasDerivAt (fun t => ‖P.relPos t‖ ^ 2)
      (2 * ⟪P.relPos 0, P.relVel 0⟫_ℝ) 0 := by
    have h := (hasDerivAt_relPos P 0).norm_sq
    simpa using h
  have hinner : HasDerivAt (fun t => ⟪laws.axis, P.relPos t⟫_ℝ)
      ⟪laws.axis, P.relVel 0⟫_ℝ 0 := by
    have h := HasDerivAt.inner (𝕜 := ℝ) (hasDerivAt_const (0 : ℝ) laws.axis)
      (hasDerivAt_relPos P 0)
    simpa using h
  have hdr : HasDerivAt
      (fun t => (laws.semiLatus + laws.eccentricity * ⟪laws.axis, P.relPos t⟫_ℝ) ^ 2)
      (2 * (laws.semiLatus + laws.eccentricity * ⟪laws.axis, P.relPos 0⟫_ℝ) *
        (laws.eccentricity * ⟪laws.axis, P.relVel 0⟫_ℝ)) 0 := by
    have h := ((hasDerivAt_const (0 : ℝ) laws.semiLatus).add
      (hinner.const_mul laws.eccentricity)).pow 2
    simpa using h
  rw [hFG] at hdl
  have hdeq : (2 * ⟪P.relPos 0, P.relVel 0⟫_ℝ)
      = 2 * (laws.semiLatus + laws.eccentricity * ⟪laws.axis, P.relPos 0⟫_ℝ) *
          (laws.eccentricity * ⟪laws.axis, P.relVel 0⟫_ℝ) :=
    hdl.deriv.trans hdr.deriv.symm
  rw [relPos_relVel_orthogonal ic, mul_zero, ← laws.conic_eq 0] at hdeq
  have hr0n : ‖P.relPos 0‖ ≠ 0 := by
    rw [ic.separation]; positivity
  have hεn : laws.eccentricity ≠ 0 := by
    rw [eccentricity_value laws ic]; norm_num
  rcases mul_eq_zero.mp hdeq with h | h
  · exfalso
    exact hr0n (by linarith [h])
  · exact (mul_eq_zero.mp h).resolve_left hεn

/-- The initial instant is the *periapsis* of the hyperbola: the conic's
reference axis (`θ = 0` in Hint 2) points opposite to the initial separation,
`e₀ = −r̂(0)`. Indeed, differentiating Hint 2's `‖r⃗‖ = a + ε⟨e₀, r⃗⟩` at the
apsis `t = 0` gives `⟨e₀, u⃗(0)⟩ = 0`, so in the orbital plane `e₀ = ±r̂(0)`;
the `+` sign would force `a = 100a₀·(1 − ε) < 0` (since `ε = 7/2 > 1`),
contradicting `a > 0`. -/
theorem axis_eq_neg_relPos0 (laws : CoulombKeplerLaws c P)
    (ic : InitialData c P (15/2)) :
    laws.axis = (-(‖P.relPos 0‖)⁻¹) • P.relPos 0 := by
  have ha : (0:ℝ) < c.bohrRadius := c.bohrRadius_pos
  have hr0p : (0:ℝ) < ‖P.relPos 0‖ := by rw [ic.separation]; positivity
  have hr0n : ‖P.relPos 0‖ ≠ 0 := ne_of_gt hr0p
  have hε : laws.eccentricity = 7 / 2 := eccentricity_value laws ic
  have hu0 : P.relVel 0 ≠ 0 := by
    rw [relVel_zero ic]
    exact smul_ne_zero (by norm_num) ic.v_positron_ne
  have hu0n : ‖P.relVel 0‖ ≠ 0 := norm_ne_zero_iff.mpr hu0
  set û := (‖P.relVel 0‖)⁻¹ • P.relVel 0 with hû
  have hûn : ‖û‖ = 1 := by
    rw [hû, norm_smul, Real.norm_of_nonneg (inv_nonneg.mpr (norm_nonneg _)),
      inv_mul_cancel₀ hu0n]
  have heu : ⟪laws.axis, û⟫_ℝ = 0 := by
    rw [hû, real_inner_smul_right, inner_axis_relVel0 laws ic, mul_zero]
  have hur : ⟪û, P.relPos 0⟫_ℝ = 0 := by
    rw [hû, real_inner_smul_left, real_inner_comm (P.relVel 0) (P.relPos 0),
      relPos_relVel_orthogonal ic, mul_zero]
  have hpw1 : planeWedge û laws.axis ^ 2 = 1 := by
    have h := planeWedge_sq_add_inner_sq û laws.axis
    rw [real_inner_comm û laws.axis, heu, hûn, laws.axis_unit] at h
    linarith [h]
  have hpw2 : planeWedge û (P.relPos 0) ^ 2 = ‖P.relPos 0‖ ^ 2 := by
    have h := planeWedge_sq_add_inner_sq û (P.relPos 0)
    rw [hur, hûn] at h
    linarith [h]
  have hbc := inner_mul_inner_planeWedge û laws.axis (P.relPos 0)
  rw [real_inner_self_eq_norm_sq, hûn, real_inner_comm û laws.axis, heu, hur] at hbc
  have hsq : ⟪laws.axis, P.relPos 0⟫_ℝ ^ 2 = ‖P.relPos 0‖ ^ 2 := by
    have h2 : ⟪laws.axis, P.relPos 0⟫_ℝ
        = planeWedge û laws.axis * planeWedge û (P.relPos 0) := by
      linarith [hbc]
    rw [h2, mul_pow, hpw1, hpw2, one_mul]
  set r̂ := (‖P.relPos 0‖)⁻¹ • P.relPos 0 with hr̂
  have hr̂n : ‖r̂‖ = 1 := by
    rw [hr̂, norm_smul, Real.norm_of_nonneg (inv_nonneg.mpr (norm_nonneg _)),
      inv_mul_cancel₀ hr0n]
  have hin2 : ⟪laws.axis, r̂⟫_ℝ ^ 2 = 1 := by
    have h1 : (‖P.relPos 0‖⁻¹) ^ 2 * ‖P.relPos 0‖ ^ 2 = 1 := by
      rw [inv_pow, inv_mul_cancel₀ (pow_ne_zero 2 hr0n)]
    rw [hr̂, real_inner_smul_right, mul_pow, hsq]
    exact h1
  rcases (sq_eq_one_iff.mp hin2) with h1 | h1
  · have hin : ⟪laws.axis, P.relPos 0⟫_ℝ = ‖P.relPos 0‖ := by
      have hr0eq : P.relPos 0 = ‖P.relPos 0‖ • r̂ := by
        rw [hr̂, smul_smul, mul_inv_cancel₀ hr0n, one_smul]
      conv_lhs => rw [hr0eq]
      rw [real_inner_smul_right, h1, mul_one]
    have hc0 := laws.conic_eq 0
    rw [hε, hin] at hc0
    have hapos := laws.semiLatus_pos
    linarith [hc0, hapos, hr0p]
  · have hax : laws.axis = -r̂ := by
      have h1a : ⟪laws.axis, laws.axis⟫_ℝ = 1 := by
        rw [real_inner_self_eq_norm_sq, laws.axis_unit]; norm_num
      have h1b : ⟪r̂, r̂⟫_ℝ = 1 := by
        rw [real_inner_self_eq_norm_sq, hr̂n]; norm_num
      have h2 : ⟪laws.axis + r̂, laws.axis + r̂⟫_ℝ = 0 := by
        rw [inner_add_left, inner_add_right, inner_add_right]
        rw [real_inner_comm r̂ laws.axis]
        rw [h1a, h1b, h1]; norm_num
      have hsum : laws.axis + r̂ = 0 := inner_self_eq_zero.mp h2
      exact eq_neg_of_add_eq_zero_left hsum
    rw [hax, hr̂, ← neg_smul]

/-- The initial separation vector in terms of the conic axis:
`r⃗(0) = −‖r⃗(0)‖·e₀`. -/
theorem relPos0_eq_smul_axis (laws : CoulombKeplerLaws c P) (ic : InitialData c P (15/2)) :
    P.relPos 0 = (-‖P.relPos 0‖) • laws.axis := by
  have hr0n : ‖P.relPos 0‖ ≠ 0 := by
    rw [ic.separation]; positivity
  rw [axis_eq_neg_relPos0 laws ic, smul_smul, neg_mul_neg, mul_inv_cancel₀ hr0n, one_smul]

/-- The semi-latus rectum of the conic: evaluating Hint 2 at the periapsis,
`a = 100a₀·(1 + ε) = 450 a₀`. -/
theorem semiLatus_value (laws : CoulombKeplerLaws c P) (ic : InitialData c P (15/2)) :
    laws.semiLatus = 450 * c.bohrRadius := by
  have hr0n : ‖P.relPos 0‖ ≠ 0 := by
    rw [ic.separation]; positivity
  have hε : laws.eccentricity = 7 / 2 := eccentricity_value laws ic
  have hax := axis_eq_neg_relPos0 laws ic
  have hc0 := laws.conic_eq 0
  rw [hε, hax, real_inner_smul_left, real_inner_self_eq_norm_sq] at hc0
  have hsimp : (-(‖P.relPos 0‖)⁻¹) * ‖P.relPos 0‖ ^ 2 = -‖P.relPos 0‖ := by
    have h2 : ‖P.relPos 0‖⁻¹ * ‖P.relPos 0‖ ^ 2 = ‖P.relPos 0‖ := by
      rw [pow_two, ← mul_assoc, inv_mul_cancel₀ hr0n, one_mul]
    linear_combination -h2
  rw [hsimp, ic.separation] at hc0
  linarith [hc0]

/-! ## Bridge lemmas: the outgoing asymptote -/

/-- The asymptotic relative velocity is nonzero: by energy conservation
`(m/4)‖u⃗∞‖² = E > 0`, the potential energy dying out at infinite separation. -/
theorem uInfinity_ne (laws : CoulombKeplerLaws c P) (ic : InitialData c P (15/2)) :
    laws.uInfinity ≠ 0 := by
  have hE : (0:ℝ) < laws.energy := energy_pos laws ic
  have h1 : Tendsto (fun t => (c.mass / 4) * ‖P.relVel t‖ ^ 2) atTop
      (𝓝 ((c.mass / 4) * ‖laws.uInfinity‖ ^ 2)) :=
    (laws.uInfinity_tendsto.norm.pow 2).const_mul _
  have h2 : Tendsto (fun t => c.coulombK * c.charge ^ 2 / ‖P.relPos t‖) atTop (𝓝 0) := by
    have h3 : Tendsto (fun t => (‖P.relPos t‖)⁻¹) atTop (𝓝 0) :=
      laws.escape.inv_tendsto_atTop
    have h4 := h3.const_mul (c.coulombK * c.charge ^ 2)
    have h5 : (fun t => c.coulombK * c.charge ^ 2 / ‖P.relPos t‖)
        = fun t => c.coulombK * c.charge ^ 2 * (‖P.relPos t‖)⁻¹ :=
      funext fun t => by rw [div_eq_mul_inv]
    rw [h5]
    simpa using h4
  have hlim := h1.sub h2
  rw [funext laws.energy_eq] at hlim
  have heq := tendsto_nhds_unique hlim tendsto_const_nhds
  intro h
  rw [h] at heq
  simp only [norm_zero, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow,
    mul_zero, zero_sub] at heq
  linarith [hE, heq]

/-- The radial unit vector tends to the unit vector along `u⃗∞`:
`r̂(t) → û∞`. This makes precise "`u⃗∞` is parallel to the limiting direction
of `r⃗`": since `t⁻¹ r⃗(t) → u⃗∞` (Cesàro) and `‖t⁻¹ r⃗(t)‖ → ‖u⃗∞‖ ≠ 0`. -/
theorem tendsto_relPos_unit (laws : CoulombKeplerLaws c P)
    (ic : InitialData c P (15/2)) :
    Tendsto (fun t => (‖P.relPos t‖)⁻¹ • P.relPos t) atTop
      (𝓝 ((‖laws.uInfinity‖)⁻¹ • laws.uInfinity)) := by
  have hune : laws.uInfinity ≠ 0 := uInfinity_ne laws ic
  have h1 := tendsto_relPos_smul_inv laws
  have h2 : Tendsto (fun t => t⁻¹ • P.relPos 0) atTop (𝓝 0) := by
    have h := tendsto_inv_atTop_zero.smul tendsto_const_nhds
    simpa using h
  have h3 : Tendsto (fun t => t⁻¹ • P.relPos t) atTop (𝓝 laws.uInfinity) := by
    have hadd := h1.add h2
    have heq : (fun t => t⁻¹ • (P.relPos t - P.relPos 0) + t⁻¹ • P.relPos 0)
        = fun t => t⁻¹ • P.relPos t :=
      funext fun t => by rw [← smul_add, sub_add_cancel]
    rw [heq] at hadd
    simpa using hadd
  have hnorm : Tendsto (fun t => ‖t⁻¹ • P.relPos t‖) atTop (𝓝 ‖laws.uInfinity‖) := h3.norm
  have hinv : Tendsto (fun t => (‖t⁻¹ • P.relPos t‖)⁻¹) atTop (𝓝 (‖laws.uInfinity‖)⁻¹) :=
    hnorm.inv₀ (norm_ne_zero_iff.mpr hune)
  have h4 := hinv.smul h3
  have heq2 : (fun t => (‖P.relPos t‖)⁻¹ • P.relPos t)
      =ᶠ[atTop] fun t => (‖t⁻¹ • P.relPos t‖)⁻¹ • (t⁻¹ • P.relPos t) := by
    filter_upwards [eventually_gt_atTop (0 : ℝ)] with t ht
    rw [norm_smul, Real.norm_of_nonneg (inv_nonneg.mpr ht.le)]
    rw [mul_inv_rev, inv_inv, smul_smul]
    congr 1
    rw [mul_assoc, mul_inv_cancel₀ (ne_of_gt ht), mul_one]
  exact Tendsto.congr' heq2 h4

/-- Asymptote direction: as `‖r⃗‖ → ∞`, Hint 2's `1 = a/‖r⃗‖ + ε⟨e₀, r̂⟩` forces
`⟨e₀, r̂⟩ → 1/ε`, and `u⃗∞` is parallel to that limiting direction (the transverse
component `L/((m/2)‖r⃗‖)` of the velocity dies out while the radial component
tends to `√(4E/m) > 0`), hence `⟨e₀, u⃗∞⟩ = ‖u⃗∞‖/ε`. -/
theorem inner_axis_uInfinity (laws : CoulombKeplerLaws c P)
    (ic : InitialData c P (15/2)) :
    ⟪laws.axis, laws.uInfinity⟫_ℝ = (1 / laws.eccentricity) * ‖laws.uInfinity‖ := by
  have hune : laws.uInfinity ≠ 0 := uInfinity_ne laws ic
  have hε : laws.eccentricity = 7 / 2 := eccentricity_value laws ic
  have hεn : laws.eccentricity ≠ 0 := by rw [hε]; norm_num
  have hrn : ∀ t, ‖P.relPos t‖ ≠ 0 := fun t => norm_ne_zero_iff.mpr (laws.relPos_ne t)
  have hpt : ∀ t : ℝ, ‖P.relPos t‖ ≠ 0 → ⟪laws.axis, (‖P.relPos t‖)⁻¹ • P.relPos t⟫_ℝ
      = (1 - laws.semiLatus / ‖P.relPos t‖) / laws.eccentricity := by
    intro t hr0
    have hc := laws.conic_eq t
    have hx : laws.eccentricity * ⟪laws.axis, P.relPos t⟫_ℝ
        = ‖P.relPos t‖ - laws.semiLatus := by linarith [hc]
    have hfin : ⟪laws.axis, (‖P.relPos t‖)⁻¹ • P.relPos t⟫_ℝ * laws.eccentricity
        = 1 - laws.semiLatus / ‖P.relPos t‖ := by
      rw [real_inner_smul_right]
      calc (‖P.relPos t‖)⁻¹ * ⟪laws.axis, P.relPos t⟫_ℝ * laws.eccentricity
          = (‖P.relPos t‖)⁻¹ * (laws.eccentricity * ⟪laws.axis, P.relPos t⟫_ℝ) := by ring
        _ = (‖P.relPos t‖)⁻¹ * (‖P.relPos t‖ - laws.semiLatus) := by rw [hx]
        _ = 1 - laws.semiLatus / ‖P.relPos t‖ := by
            rw [mul_sub, inv_mul_cancel₀ hr0, div_eq_mul_inv, mul_comm]
    rw [eq_div_iff hεn]
    exact hfin
  have hlim1 : Tendsto (fun t => ⟪laws.axis, (‖P.relPos t‖)⁻¹ • P.relPos t⟫_ℝ) atTop
      (𝓝 ⟪laws.axis, (‖laws.uInfinity‖)⁻¹ • laws.uInfinity⟫_ℝ) :=
    tendsto_const_nhds.inner (tendsto_relPos_unit laws ic)
  have hz : Tendsto (fun t => laws.semiLatus / ‖P.relPos t‖) atTop (𝓝 0) := by
    have h3 : Tendsto (fun t => (‖P.relPos t‖)⁻¹) atTop (𝓝 0) :=
      laws.escape.inv_tendsto_atTop
    have h4 := h3.const_mul laws.semiLatus
    have h5 : (fun t => laws.semiLatus / ‖P.relPos t‖)
        = fun t => laws.semiLatus * (‖P.relPos t‖)⁻¹ :=
      funext fun t => by rw [div_eq_mul_inv]
    rw [h5]
    simpa using h4
  have hlim2 : Tendsto (fun t => (1 - laws.semiLatus / ‖P.relPos t‖) / laws.eccentricity)
      atTop (𝓝 ((1 - 0) / laws.eccentricity)) :=
    (tendsto_const_nhds.sub hz).div_const laws.eccentricity
  have hfun : (fun t => ⟪laws.axis, (‖P.relPos t‖)⁻¹ • P.relPos t⟫_ℝ)
      = fun t => (1 - laws.semiLatus / ‖P.relPos t‖) / laws.eccentricity :=
    funext fun t => hpt t (hrn t)
  rw [hfun] at hlim1
  have heq := tendsto_nhds_unique hlim1 hlim2
  rw [real_inner_smul_right] at heq
  have hunn : ‖laws.uInfinity‖ ≠ 0 := norm_ne_zero_iff.mpr hune
  have h3 : ⟪laws.axis, laws.uInfinity⟫_ℝ
      = ‖laws.uInfinity‖ * ((‖laws.uInfinity‖)⁻¹ * ⟪laws.axis, laws.uInfinity⟫_ℝ) := by
    rw [← mul_assoc, mul_inv_cancel₀ hunn, one_mul]
  rw [h3, heq, sub_zero]
  ring

/-- The transverse coordinate of the relative motion with respect to the conic's
axis: `y(t) = (e₀ ∧ r⃗(t))_z`. -/
noncomputable def transverseCoord (laws : CoulombKeplerLaws c P) (t : ℝ) : ℝ :=
  planeWedge laws.axis (P.relPos t)

/-- The scaled transverse coordinate `g(t) = u₂ · y(t)`, where
`u₂ = (e₀ ∧ u⃗(0))_z` is the (nonzero) transverse component of the initial
relative velocity. Since `y(0) = 0` (periapsis) and `y'(0) = u₂ ≠ 0`, the sign
of `g` near `0⁺` is positive, and a sign reversal would force a zero of `y`
with `y' > 0` — impossible because the zeros of `y` are apsides, where the
velocity is axial with the wrong magnitude sign (angular momentum conservation). -/
noncomputable def scaledTransverse (laws : CoulombKeplerLaws c P) (t : ℝ) : ℝ :=
  planeWedge laws.axis (P.relVel 0) * transverseCoord laws t

lemma hasDerivAt_transverseCoord (laws : CoulombKeplerLaws c P) (t : ℝ) :
    HasDerivAt (transverseCoord laws) (planeWedge laws.axis (P.relVel t)) t := by
  have h := HasDerivAt.inner (𝕜 := ℝ) (hasDerivAt_const t (planeRot laws.axis))
    (hasDerivAt_relPos P t)
  simp only [inner_zero_left, add_zero] at h
  have hfun : (fun x => ⟪planeRot laws.axis, P.relPos x⟫_ℝ)
      = fun x => planeWedge laws.axis (P.relPos x) :=
    funext fun x => inner_planeRot_left _ _
  rw [hfun, inner_planeRot_left] at h
  exact h

lemma continuous_transverseCoord (laws : CoulombKeplerLaws c P) :
    Continuous (transverseCoord laws) := by
  have hrc : Continuous P.relPos :=
    (P.positron_smooth.continuous).sub (P.electron_smooth.continuous)
  have h2 : Continuous (fun x => ⟪planeRot laws.axis, P.relPos x⟫_ℝ) :=
    continuous_const.inner hrc
  have hfun : (fun x => ⟪planeRot laws.axis, P.relPos x⟫_ℝ)
      = fun x => planeWedge laws.axis (P.relPos x) :=
    funext fun x => inner_planeRot_left _ _
  rw [hfun] at h2
  exact h2

lemma transverseCoord_zero (laws : CoulombKeplerLaws c P) (ic : InitialData c P (15/2)) :
    transverseCoord laws 0 = 0 := by
  show planeWedge laws.axis (P.relPos 0) = 0
  rw [relPos0_eq_smul_axis laws ic, planeWedge_smul_left, planeWedge_self, mul_zero]

lemma hasDerivAt_scaledTransverse (laws : CoulombKeplerLaws c P) (t : ℝ) :
    HasDerivAt (scaledTransverse laws)
      (planeWedge laws.axis (P.relVel 0) * planeWedge laws.axis (P.relVel t)) t :=
  (hasDerivAt_transverseCoord laws t).const_mul _

lemma scaledTransverse_zero (laws : CoulombKeplerLaws c P) (ic : InitialData c P (15/2)) :
    scaledTransverse laws 0 = 0 := by
  show planeWedge laws.axis (P.relVel 0) * transverseCoord laws 0 = 0
  rw [transverseCoord_zero laws ic, mul_zero]

lemma hasDerivAt_scaledTransverse_zero (laws : CoulombKeplerLaws c P)
    (ic : InitialData c P (15/2)) :
    HasDerivAt (scaledTransverse laws)
      (planeWedge laws.axis (P.relVel 0)) ^ 2 0 := by
  rw [pow_two]
  exact hasDerivAt_scaledTransverse laws 0

lemma continuous_scaledTransverse (laws : CoulombKeplerLaws c P) :
    Continuous (scaledTransverse laws) :=
  continuous_const.mul (continuous_transverseCoord laws)

/-- Outgoing-branch orientation: `u⃗∞` keeps a positive component along the
initial relative velocity `u⃗(0) = 2v⃗₊(0)`. The transverse motion never reverses,
because the conserved angular momentum is nonzero, so the polar angle sweeps
monotonically from the periapsis (`106.6°` before the asymptote) to the outgoing
asymptote; this selects the outgoing branch of the asymptote line. -/
theorem inner_uInfinity_relVel0_pos (laws : CoulombKeplerLaws c P)
    (ic : InitialData c P (15/2)) :
    0 < ⟪laws.uInfinity, P.relVel 0⟫_ℝ := by
  have hm : (0:ℝ) < c.mass := c.mass_pos
  have ha : (0:ℝ) < c.bohrRadius := c.bohrRadius_pos
  have hh : (0:ℝ) < c.hbar := c.hbar_pos
  have hr0p : (0:ℝ) < ‖P.relPos 0‖ := by rw [ic.separation]; positivity
  have hr0n : ‖P.relPos 0‖ ≠ 0 := ne_of_gt hr0p
  have hε : laws.eccentricity = 7 / 2 := eccentricity_value laws ic
  have hune : laws.uInfinity ≠ 0 := uInfinity_ne laws ic
  have hunn : ‖laws.uInfinity‖ ≠ 0 := norm_ne_zero_iff.mpr hune
  have hx0 : ⟪laws.axis, P.relPos 0⟫_ℝ = -‖P.relPos 0‖ := by
    conv_lhs => rw [relPos0_eq_smul_axis laws ic]
    rw [real_inner_smul_left, real_inner_self_eq_norm_sq, laws.axis_unit]
    simp
  have hL : laws.angMom ≠ 0 := by
    have h1 := angMom_value laws ic
    have h2 := ic.angMom_positron
    have hpos : (0:ℝ)
        < |c.mass * planeWedge ((1/2:ℝ) • P.relPos 0) (deriv P.positron 0)| := by
      rw [h2]; positivity
    have h3 : c.mass * planeWedge ((1/2:ℝ) • P.relPos 0) (deriv P.positron 0) ≠ 0 :=
      abs_pos.mp hpos
    rw [h1]
    exact mul_ne_zero (by norm_num) h3
  have hu2ne : planeWedge laws.axis (P.relVel 0) ≠ 0 := by
    intro h
    have hL0 := laws.angMom_eq 0
    rw [relPos0_eq_smul_axis laws ic, planeWedge_smul_left, h] at hL0
    simp only [mul_zero] at hL0
    exact hL hL0.symm
  -- the scaled transverse coordinate never becomes negative
  have hclaim : ∀ s : ℝ, 0 < s → 0 ≤ scaledTransverse laws s := by
    intro s hs
    by_contra hneg0
    push_neg at hneg0
    have hpos : ∀ᶠ t in 𝓝[>] (0:ℝ), scaledTransverse laws 0 < scaledTransverse laws t :=
      eventually_gt_of_hasDerivAt_pos (hasDerivAt_scaledTransverse_zero laws ic)
        (sq_pos_of_ne_zero hu2ne)
    rw [scaledTransverse_zero laws ic] at hpos
    obtain ⟨t₁, ht₁⟩ := (hpos.and (Ioo_mem_nhdsGT hs)).exists
    obtain ⟨T, hTmem, hTmax⟩ := exists_max_zero_of_neg (continuous_scaledTransverse laws)
      ht₁.2.1.le ht₁.1 hneg0
    have hT0 : scaledTransverse laws T = 0 := Set.mem_singleton_iff.mp hTmem.1
    have hTge : t₁ ≤ T := hTmem.2.1
    have hTle : T ≤ s := hTmem.2.2
    have hTlt : T < s := by
      rcases lt_or_eq_of_le hTle with h | h
      · exact h
      · exfalso
        rw [← h] at hT0
        linarith [hT0, hneg0]
    -- at the largest zero of the scaled transverse coordinate, the position is axial
    have hyT : planeWedge laws.axis (P.relPos T) = 0 := by
      have hT0' : planeWedge laws.axis (P.relVel 0) * planeWedge laws.axis (P.relPos T)
          = 0 := hT0
      exact (mul_eq_zero.mp hT0').resolve_left hu2ne
    have hrT : P.relPos T = ⟪laws.axis, P.relPos T⟫_ℝ • laws.axis := by
      set w := P.relPos T - ⟪laws.axis, P.relPos T⟫_ℝ • laws.axis with hw_def
      have he1 : ⟪laws.axis, w⟫_ℝ = 0 := by
        rw [hw_def, inner_sub_right, real_inner_smul_right, real_inner_self_eq_norm_sq,
          laws.axis_unit]
        simp
      have he2 : planeWedge laws.axis w = 0 := by
        rw [hw_def, planeWedge_sub_right, planeWedge_smul_right, planeWedge_self, hyT]
        simp
      have hbc := inner_mul_inner_planeWedge laws.axis (P.relPos T) w
      rw [real_inner_self_eq_norm_sq, laws.axis_unit, he1, he2] at hbc
      have hw0 : ⟪P.relPos T, w⟫_ℝ = 0 := by linarith [hbc]
      have h2 : ⟪w, P.relPos T⟫_ℝ = 0 := by rw [real_inner_comm]; exact hw0
      have h3 : ⟪w, laws.axis⟫_ℝ = 0 := by rw [real_inner_comm]; exact he1
      have h4 : ⟪w, w⟫_ℝ = ⟪w, P.relPos T⟫_ℝ - ⟪laws.axis, P.relPos T⟫_ℝ * ⟪w, laws.axis⟫_ℝ := by
        rw [hw_def, inner_sub_right, real_inner_smul_right]
      have hww : ⟪w, w⟫_ℝ = 0 := by rw [h4, h2, h3, mul_zero, sub_zero]
      have hwz : w = 0 := inner_self_eq_zero.mp hww
      rw [hw_def] at hwz
      exact sub_eq_zero.mp hwz
    have hnormT : ‖P.relPos T‖ = |⟪laws.axis, P.relPos T⟫_ℝ| := by
      conv_lhs => rw [hrT]
      rw [norm_smul, laws.axis_unit, mul_one, Real.norm_eq_abs]
    have hxT : ⟪laws.axis, P.relPos T⟫_ℝ = -‖P.relPos 0‖ := by
      have hconT := laws.conic_eq T
      have hcon0 := laws.conic_eq 0
      rw [hx0] at hcon0
      rw [hnormT, hε] at hconT
      rcases le_or_lt 0 ⟪laws.axis, P.relPos T⟫_ℝ with hxp | hxn
      · rw [abs_of_nonneg hxp] at hconT
        have hapos := laws.semiLatus_pos
        linarith [hconT, hapos, hxp]
      · rw [abs_of_neg hxn] at hconT
        rw [hε] at hcon0
        linarith [hconT, hcon0]
    have hpwT : planeWedge laws.axis (P.relVel T) = planeWedge laws.axis (P.relVel 0) := by
      have hLT := laws.angMom_eq T
      rw [hrT, planeWedge_smul_left, hxT] at hLT
      have hL0 := laws.angMom_eq 0
      rw [relPos0_eq_smul_axis laws ic, planeWedge_smul_left] at hL0
      have hcoef : (c.mass / 2) * (-‖P.relPos 0‖) ≠ 0 :=
        mul_ne_zero (div_ne_zero (ne_of_gt hm) (by norm_num)) (neg_ne_zero.mpr hr0n)
      have h4 : (c.mass / 2) * ((-‖P.relPos 0‖) * planeWedge laws.axis (P.relVel T))
          = (c.mass / 2) * ((-‖P.relPos 0‖) * planeWedge laws.axis (P.relVel 0)) := by
        rw [hLT, hL0]
      have h5 : ((c.mass / 2) * (-‖P.relPos 0‖)) * planeWedge laws.axis (P.relVel T)
          = ((c.mass / 2) * (-‖P.relPos 0‖)) * planeWedge laws.axis (P.relVel 0) := by
        linear_combination h4
      exact mul_left_cancel₀ hcoef h5
    -- the scaled transverse coordinate increases through T: a further zero exists
    have hgT : HasDerivAt (scaledTransverse laws)
        (planeWedge laws.axis (P.relVel 0)) ^ 2 T := by
      have h := hasDerivAt_scaledTransverse laws T
      rw [hpwT, ← pow_two] at h
      exact h
    obtain ⟨t₂, ht₂⟩ := ((eventually_gt_of_hasDerivAt_pos hgT
      (sq_pos_of_ne_zero hu2ne)).and (Ioo_mem_nhdsGT hTlt)).exists
    rw [hT0] at ht₂
    have hsub2 := intermediate_value_Ioo' ht₂.2.2.le
      (continuous_scaledTransverse laws).continuousOn
      (Set.mem_Ioo.mpr ⟨hneg0, ht₂.1⟩)
    obtain ⟨z, hz, hz0⟩ := hsub2
    have hzmem : z ∈ scaledTransverse laws ⁻¹' {0} ∩ Set.Icc t₁ s :=
      ⟨Set.mem_singleton_iff.mpr hz0,
        Set.mem_Icc.mpr ⟨le_trans hTge (le_trans ht₂.2.1.le hz.1.le), hz.2.le⟩⟩
    have hle := hTmax z hzmem
    linarith [ht₂.2.1, hz.1, hle]
  -- the transverse component of u⃗∞ keeps the sign of u₂
  have hylim : Tendsto (fun t => t⁻¹ * transverseCoord laws t) atTop
      (𝓝 (planeWedge laws.axis laws.uInfinity)) := by
    have hlim : Tendsto (fun t => planeWedge laws.axis (P.relVel t)) atTop
        (𝓝 (planeWedge laws.axis laws.uInfinity)) := by
      have h2 : Tendsto (fun t => ⟪planeRot laws.axis, P.relVel t⟫_ℝ) atTop
          (𝓝 ⟪planeRot laws.axis, laws.uInfinity⟫_ℝ) :=
        tendsto_const_nhds.inner laws.uInfinity_tendsto
      have hfun : (fun t => ⟪planeRot laws.axis, P.relVel t⟫_ℝ)
          = fun t => planeWedge laws.axis (P.relVel t) :=
        funext fun t => inner_planeRot_left _ _
      rw [hfun, inner_planeRot_left] at h2
      exact h2
    have h := tendsto_inv_smul_sub_of_tendsto_deriv (hasDerivAt_transverseCoord laws)
      (continuous_transverseCoord laws) hlim
    rw [transverseCoord_zero laws ic, sub_zero] at h
    have heq : (fun t => t⁻¹ • transverseCoord laws t)
        = fun t => t⁻¹ * transverseCoord laws t := funext fun t => smul_eq_mul
    rw [heq] at h
    exact h
  have hge : (0:ℝ)
      ≤ planeWedge laws.axis (P.relVel 0) * planeWedge laws.axis laws.uInfinity := by
    have h1 := hylim.const_mul (planeWedge laws.axis (P.relVel 0))
    have h2 : ∀ᶠ t in atTop,
        (0:ℝ) ≤ planeWedge laws.axis (P.relVel 0) * (t⁻¹ * transverseCoord laws t) := by
      filter_upwards [eventually_gt_atTop (0:ℝ)] with t ht
      rw [mul_left_comm]
      exact mul_nonneg (inv_nonneg.mpr ht.le) (hclaim t ht)
    exact ge_of_tendsto h1 h2
  -- the initial relative velocity is purely transverse to the axis
  have hu0eq : P.relVel 0 = planeWedge laws.axis (P.relVel 0) • planeRot laws.axis := by
    set w := P.relVel 0 - planeWedge laws.axis (P.relVel 0) • planeRot laws.axis with hw_def
    have he1 : ⟪laws.axis, w⟫_ℝ = 0 := by
      rw [hw_def, inner_sub_right, real_inner_smul_right, inner_planeRot_right,
        planeWedge_self, neg_zero, mul_zero]
      rw [inner_axis_relVel0 laws ic, sub_zero]
    have he2 : planeWedge laws.axis w = 0 := by
      rw [hw_def, planeWedge_sub_right, planeWedge_smul_right,
        planeWedge_planeRot_left_unit laws.axis laws.axis_unit, mul_one, sub_self]
    have hbc := inner_mul_inner_planeWedge laws.axis (P.relVel 0) w
    rw [real_inner_self_eq_norm_sq, laws.axis_unit, he1, he2] at hbc
    have hw0 : ⟪P.relVel 0, w⟫_ℝ = 0 := by linarith [hbc]
    have h2 : ⟪w, P.relVel 0⟫_ℝ = 0 := by rw [real_inner_comm]; exact hw0
    have h3 : ⟪w, planeRot laws.axis⟫_ℝ = 0 := by
      rw [inner_planeRot_right, planeWedge_comm]
      simp [he2]
    have h4 : ⟪w, w⟫_ℝ = ⟪w, P.relVel 0⟫_ℝ
        - planeWedge laws.axis (P.relVel 0) * ⟪w, planeRot laws.axis⟫_ℝ := by
      rw [hw_def, inner_sub_right, real_inner_smul_right]
    have hww : ⟪w, w⟫_ℝ = 0 := by rw [h4, h2, h3, mul_zero, sub_zero]
    have hwz : w = 0 := inner_self_eq_zero.mp hww
    rw [hw_def] at hwz
    exact sub_eq_zero.mp hwz
  have hid : ⟪laws.uInfinity, P.relVel 0⟫_ℝ
      = planeWedge laws.axis (P.relVel 0) * planeWedge laws.axis laws.uInfinity := by
    conv_lhs => rw [hu0eq]
    rw [real_inner_smul_right, ← real_inner_comm (planeRot laws.axis) laws.uInfinity,
      inner_planeRot_left]
  rw [hid]
  have hne : planeWedge laws.axis (P.relVel 0) * planeWedge laws.axis laws.uInfinity
      ≠ 0 := by
    intro hbad
    have hpw : planeWedge laws.axis laws.uInfinity = 0 :=
      (mul_eq_zero.mp hbad).resolve_left hu2ne
    have hmaster := planeWedge_sq_add_inner_sq laws.axis laws.uInfinity
    rw [hpw, laws.axis_unit] at hmaster
    have hin := inner_axis_uInfinity laws ic
    rw [hin, hε] at hmaster
    have hnorm_sq : (0:ℝ) < ‖laws.uInfinity‖ ^ 2 :=
      pow_pos (lt_of_le_of_ne (norm_nonneg _) (Ne.symm hunn)) 2
    have h71 : ((1:ℝ)/(7/2))^2 = 1 := by
      have h2 : ((1:ℝ)/(7/2) * ‖laws.uInfinity‖)^2 = ‖laws.uInfinity‖^2 := by
        linarith [hmaster]
      have h3 : ((1:ℝ)/(7/2))^2 * ‖laws.uInfinity‖^2 = 1 * ‖laws.uInfinity‖^2 := by
        linear_combination h2
      exact mul_right_cancel₀ (ne_of_gt hnorm_sq) h3
    norm_num at h71
  exact lt_of_le_of_ne hge hne.symm

/-- The undirected angle between `u⃗∞` and the conic's reference axis is
`arccos (1/ε) = arccos (2/7)`. -/
theorem angle_uInfinity_axis (laws : CoulombKeplerLaws c P)
    (ic : InitialData c P (15/2)) :
    angle laws.uInfinity laws.axis = Real.arccos (2 / 7) := by
  have hin := inner_axis_uInfinity laws ic
  have hε : laws.eccentricity = 7 / 2 := eccentricity_value laws ic
  have hune : laws.uInfinity ≠ 0 := uInfinity_ne laws ic
  have hunn : ‖laws.uInfinity‖ ≠ 0 := norm_ne_zero_iff.mpr hune
  have hcos : ⟪laws.uInfinity, laws.axis⟫_ℝ / (‖laws.uInfinity‖ * ‖laws.axis‖) = 2 / 7 := by
    rw [real_inner_comm laws.uInfinity laws.axis, hin, hε, laws.axis_unit, mul_one,
      mul_div_assoc, div_self hunn, mul_one]
    norm_num
  show Real.arccos (⟪laws.uInfinity, laws.axis⟫_ℝ / (‖laws.uInfinity‖ * ‖laws.axis‖))
    = Real.arccos (2 / 7)
  rw [hcos]

/-- The initial positron velocity is perpendicular to the conic's reference axis
(it is perpendicular to the separation, which is antiparallel to the axis). -/
theorem axis_inner_vPositron0 (laws : CoulombKeplerLaws c P)
    (ic : InitialData c P (15/2)) :
    ⟪laws.axis, deriv P.positron 0⟫_ℝ = 0 := by
  rw [axis_eq_neg_relPos0 laws ic, real_inner_smul_left,
    ← real_inner_comm (deriv P.positron 0) (P.relPos 0), ic.v_perpendicular, mul_zero]

/-! ## Main result -/

/-- **Main result (T1-B2)** — blueprint `thm:physics:ipho_2026_t1_b2:target`.
For `μ = 15/2` the angle between the asymptotic relative velocity `u⃗∞` (the
velocity of `e⁺` relative to `e⁻` as the separation tends to infinity) and the
initial line of motion of `e⁺` is `arcsin (2/7)` radians.

With `⟨e₀, û∞⟩ = 2/7` and `v⃗₊(0) ⊥ e₀` in the orbital plane, the component of
`û∞` along `v̂₊(0)` has magnitude `√(1 − (2/7)²) = 3√5/7`; the outgoing-branch
orientation (`inner_uInfinity_relVel0_pos`) makes this component positive, so
the undirected angle is `arccos (3√5/7) = arcsin (2/7)`. -/
theorem angle_uInfinity_initial_positron_motion (laws : CoulombKeplerLaws c P)
    (ic : InitialData c P (15/2)) :
    angle laws.uInfinity (deriv P.positron 0) = Real.arcsin (2 / 7) := by
  have hε : laws.eccentricity = 7 / 2 := eccentricity_value laws ic
  have hin := inner_axis_uInfinity laws ic
  have hort := axis_inner_vPositron0 laws ic
  have hune : laws.uInfinity ≠ 0 := uInfinity_ne laws ic
  have hvne : deriv P.positron 0 ≠ 0 := ic.v_positron_ne
  have hunn : ‖laws.uInfinity‖ ≠ 0 := norm_ne_zero_iff.mpr hune
  have hpos : (0:ℝ) < ⟪laws.uInfinity, deriv P.positron 0⟫_ℝ := by
    have h1 := inner_uInfinity_relVel0_pos laws ic
    rw [relVel_zero ic, real_inner_smul_right] at h1
    linarith [h1]
  have hbc := inner_eq_inner_axis laws.axis laws.uInfinity (deriv P.positron 0)
    laws.axis_unit
  rw [hort, mul_zero, zero_add] at hbc
  have h1' : planeWedge laws.axis laws.uInfinity ^ 2 = (45/49) * ‖laws.uInfinity‖ ^ 2 := by
    have h := planeWedge_sq_add_inner_sq laws.axis laws.uInfinity
    rw [laws.axis_unit, hin, hε] at h
    have hnorm : ((1:ℝ)/(7/2) * ‖laws.uInfinity‖)^2 = (4/49) * ‖laws.uInfinity‖^2 := by
      ring
    linarith [h, hnorm]
  have h2' : planeWedge laws.axis (deriv P.positron 0) ^ 2
      = ‖deriv P.positron 0‖ ^ 2 := by
    have h := planeWedge_sq_add_inner_sq laws.axis (deriv P.positron 0)
    rw [hort, laws.axis_unit] at h
    linarith [h]
  have hsq : ⟪laws.uInfinity, deriv P.positron 0⟫_ℝ ^ 2
      = (45/49) * (‖laws.uInfinity‖ ^ 2 * ‖deriv P.positron 0‖ ^ 2) := by
    rw [hbc, mul_pow, h1', h2']
    ring
  have h45 : Real.sqrt (45/49) = 3 * Real.sqrt 5 / 7 := by
    have h : (45:ℝ)/49 = (3 * Real.sqrt 5 / 7) ^ 2 := by
      rw [div_pow, mul_pow, Real.sq_sqrt (by norm_num : (0:ℝ) ≤ 5)]
      norm_num
    rw [h, Real.sqrt_sq (by positivity)]
  have hval : |⟪laws.uInfinity, deriv P.positron 0⟫_ℝ|
      = Real.sqrt (45/49) * (‖laws.uInfinity‖ * ‖deriv P.positron 0‖) := by
    calc |⟪laws.uInfinity, deriv P.positron 0⟫_ℝ|
        = Real.sqrt (⟪laws.uInfinity, deriv P.positron 0⟫_ℝ ^ 2) := by
          rw [← sq_abs]
          exact (Real.sqrt_sq (abs_nonneg _)).symm
      _ = Real.sqrt ((45/49) * (‖laws.uInfinity‖ ^ 2 * ‖deriv P.positron 0‖ ^ 2)) := by
          rw [hsq]
      _ = Real.sqrt (45/49)
            * Real.sqrt (‖laws.uInfinity‖ ^ 2 * ‖deriv P.positron 0‖ ^ 2) := by
          rw [Real.sqrt_mul (by norm_num : (0:ℝ) ≤ 45/49)]
      _ = Real.sqrt (45/49) * (‖laws.uInfinity‖ * ‖deriv P.positron 0‖) := by
          rw [Real.sqrt_mul (sq_nonneg _), Real.sqrt_sq (norm_nonneg laws.uInfinity),
            Real.sqrt_sq (norm_nonneg (deriv P.positron 0))]
  have hcos : ⟪laws.uInfinity, deriv P.positron 0⟫_ℝ
      = (3 * Real.sqrt 5 / 7) * (‖laws.uInfinity‖ * ‖deriv P.positron 0‖) := by
    have h1 : |⟪laws.uInfinity, deriv P.positron 0⟫_ℝ|
        = ⟪laws.uInfinity, deriv P.positron 0⟫_ℝ := abs_of_pos hpos
    rw [h1] at hval
    rw [hval, h45]
  have hdiv : ⟪laws.uInfinity, deriv P.positron 0⟫_ℝ
      / (‖laws.uInfinity‖ * ‖deriv P.positron 0‖) = 3 * Real.sqrt 5 / 7 := by
    rw [hcos, mul_div_assoc, div_self
      (mul_ne_zero hunn (norm_ne_zero_iff.mpr hvne)), mul_one]
  have hcos2 : Real.cos (Real.arcsin (2/7)) = 3 * Real.sqrt 5 / 7 := by
    rw [Real.cos_arcsin]
    have h : (1:ℝ) - (2/7)^2 = (45:ℝ)/49 := by norm_num
    rw [h, h45]
  show Real.arccos (⟪laws.uInfinity, deriv P.positron 0⟫_ℝ
      / (‖laws.uInfinity‖ * ‖deriv P.positron 0‖)) = Real.arcsin (2/7)
  rw [hdiv, ← hcos2]
  exact Real.arccos_cos (Real.arcsin_nonneg.mpr (by norm_num))
    (le_trans (Real.arcsin_le_pi_div_two _) (by linarith [Real.pi_pos]))

/-- The answer in degrees, as requested by the problem: the angle is
`(180/π)·arcsin(2/7)` degrees. -/
theorem angle_uInfinity_initial_positron_motion_degrees
    (laws : CoulombKeplerLaws c P) (ic : InitialData c P (15/2)) :
    angle laws.uInfinity (deriv P.positron 0) * (180 / π) =
      Real.arcsin (2 / 7) * (180 / π) := by
  rw [angle_uInfinity_initial_positron_motion laws ic]

/-- Decimal readout of the degree answer: approximately `16.60°`. The source
states no explicit rounding rule, so the exact closed form
`(180/π)·arcsin(2/7)` above is the derived candidate; these bounds certify its
leading decimals. -/
theorem angle_degrees_numeric_bounds :
    Real.arcsin (2 / 7) * (180 / π) ∈ Set.Ioo 16.60 16.61 := by
  have hπpos : (0:ℝ) < π := Real.pi_pos
  have hsin : Real.sin (Real.arcsin (2/7)) = 2/7 :=
    Real.sin_arcsin (by norm_num) (by norm_num)
  have hsm := Real.strictMonoOn_sin
  have hA1 : -(π/2) ≤ Real.arcsin (2/7) := Real.neg_pi_div_two_le_arcsin _
  have hA2 : Real.arcsin (2/7) ≤ π/2 := Real.arcsin_le_pi_div_two _
  have hA_mem : Real.arcsin (2/7) ∈ Set.Icc (-(π/2)) (π/2) := ⟨hA1, hA2⟩
  refine ⟨?_, ?_⟩
  · -- the lower bound: 16.60° is too small
    have hstep : (16.60:ℝ) * π / 180 < Real.arcsin (2/7) := by
      have hlo_mem : (16.60:ℝ) * π / 180 ∈ Set.Icc (-(π/2)) (π/2) := by
        refine ⟨by linarith [Real.pi_gt_d6], ?_⟩
        have h2 : (16.60:ℝ)*π/180 = (16.60/180)*π := by ring
        rw [h2]
        have h3 : (16.60:ℝ)/180 ≤ 1/2 := by norm_num
        have h4 : (16.60/180:ℝ)*π ≤ (1/2)*π :=
          mul_le_mul_of_nonneg_right h3 (le_of_lt hπpos)
        linarith [h4]
      have hsinlo : Real.sin ((16.60:ℝ) * π / 180) < 2/7 := by
        have hlo_gt : (16.60:ℝ)*3.141592/180 < (16.60:ℝ)*π/180 := by
          linarith [Real.pi_gt_d6]
        have hlo_lt : (16.60:ℝ)*π/180 < (16.60:ℝ)*3.141593/180 := by
          linarith [Real.pi_lt_d6]
        have hlo_pos : (0:ℝ) < (16.60:ℝ)*π/180 := by linarith [hlo_gt]
        have h1 := sin_upper ((16.60:ℝ) * π / 180) (le_of_lt hlo_pos)
        have hlo3 : ((16.60:ℝ)*3.141592/180)^3 ≤ ((16.60:ℝ)*π/180)^3 :=
          pow_le_pow_left (by norm_num) (le_of_lt hlo_gt) 3
        have hlo5 : ((16.60:ℝ)*π/180)^5 ≤ ((16.60:ℝ)*3.141593/180)^5 :=
          pow_le_pow_left (le_of_lt hlo_pos) (le_of_lt hlo_lt) 5
        have h2 : (16.60:ℝ)*π/180 - ((16.60:ℝ)*π/180)^3/6 + ((16.60:ℝ)*π/180)^5/120
            ≤ (16.60:ℝ)*3.141593/180 - ((16.60:ℝ)*3.141592/180)^3/6
              + ((16.60:ℝ)*3.141593/180)^5/120 := by linarith [hlo3, hlo5, hlo_lt]
        have h3 : (16.60:ℝ)*3.141593/180 - ((16.60:ℝ)*3.141592/180)^3/6
            + ((16.60:ℝ)*3.141593/180)^5/120 < 2/7 := by norm_num
        linarith [h1, h2, h3]
      rw [← hsin] at hsinlo
      exact (hsm.lt_iff_lt hlo_mem hA_mem).mp hsinlo
    have hconv : (16.60:ℝ) = ((16.60:ℝ) * π / 180) * (180/π) := by
      field_simp
      ring
    rw [hconv]
    exact mul_lt_mul_of_pos_right hstep (by positivity)
  · -- the upper bound: 16.61° is too large
    have hstep : Real.arcsin (2/7) < (16.61:ℝ) * π / 180 := by
      have hhi_mem : (16.61:ℝ) * π / 180 ∈ Set.Icc (-(π/2)) (π/2) := by
        refine ⟨by linarith [Real.pi_gt_d6], ?_⟩
        have h2 : (16.61:ℝ)*π/180 = (16.61/180)*π := by ring
        rw [h2]
        have h3 : (16.61:ℝ)/180 ≤ 1/2 := by norm_num
        have h4 : (16.61/180:ℝ)*π ≤ (1/2)*π :=
          mul_le_mul_of_nonneg_right h3 (le_of_lt hπpos)
        linarith [h4]
      have hsinhi : (2/7:ℝ) < Real.sin ((16.61:ℝ) * π / 180) := by
        have hhi_gt : (16.61:ℝ)*3.141592/180 < (16.61:ℝ)*π/180 := by
          linarith [Real.pi_gt_d6]
        have hhi_lt : (16.61:ℝ)*π/180 < (16.61:ℝ)*3.141593/180 := by
          linarith [Real.pi_lt_d6]
        have hhi_pos : (0:ℝ) < (16.61:ℝ)*π/180 := by linarith [hhi_gt]
        have h1 := sin_lower ((16.61:ℝ) * π / 180) (le_of_lt hhi_pos)
        have hhi3 : ((16.61:ℝ)*π/180)^3 ≤ ((16.61:ℝ)*3.141593/180)^3 :=
          pow_le_pow_left (le_of_lt hhi_pos) (le_of_lt hhi_lt) 3
        have h2 : (16.61:ℝ)*3.141592/180 - ((16.61:ℝ)*3.141593/180)^3/6
            ≤ (16.61:ℝ)*π/180 - ((16.61:ℝ)*π/180)^3/6 := by linarith [hhi3, hhi_gt]
        have h3 : (2/7:ℝ)
            < (16.61:ℝ)*3.141592/180 - ((16.61:ℝ)*3.141593/180)^3/6 := by norm_num
        linarith [h1, h2, h3]
      rw [← hsin] at hsinhi
      exact (hsm.lt_iff_lt hA_mem hhi_mem).mp hsinhi
    have hconv : (16.61:ℝ) = ((16.61:ℝ) * π / 180) * (180/π) := by
      field_simp
      ring
    rw [hconv]
    exact mul_lt_mul_of_pos_right hstep (by positivity)

end IPhO2026.T1B2
