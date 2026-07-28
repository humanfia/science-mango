import Mathlib

/-!
# IPhO 2026, Problem 2, Part A.1 — Threshold `x_N` for at most `N` reflections

Physical model (blueprint chapter
`blueprint/src/chapters/IPhO2026Problems_problem_IPhO_2026_2_A_1.tex`,
Figures 2c–2e on official source page `T2_page-2.png`):

* A half-cylindrical mirror of radius `R` (Figure 2d): the cross-section is
  the semicircle `x ^ 2 + y ^ 2 = R ^ 2`, `y ≥ 0`, with the optical axis as
  the `y`-axis; the diameter endpoints (the rim) are `(±R, 0)`. Figure 2c
  shows the 3D cooker: the cylindrical mirror concentrates sunlight on a
  collecting tube of diameter `2ℓ` along its focal axis.
* A family of rays parallel to the optical axis (the `y`-axis) strikes the
  inside of the mirror. An incident ray has transverse coordinate
  `x = R * cos α`, where `α` is the standard polar angle of its first impact
  point on the mirror (measured from the `+x` axis); the incidence angle at
  every impact is `π / 2 − α`.
* Law of reflection on a circular mirror (`angle of reflection = angle of
  incidence`): the incidence angle is the same at every impact of a given
  ray, so the central angle between consecutive impact points is the
  constant `2 α`; the successive impacts have standard polar angles
  `α, 3 α, 5 α, …, (2 k + 1) α, …`. The ray escapes through the open half
  `y < 0` as soon as a would-be impact lands strictly above `π` (off the
  physical semicircle); an impact landing exactly on the rim angle `π`
  (the point `(−R, 0)`) counts as a reflection (filled dots of Figure 2e).
* `N_refl x` is the number of reflections of the ray at coordinate `x`
  (Figure 2e: a right-continuous staircase in `|x|`, with plateaus at the
  levels `1, 2, 3, …` accumulating at the rim `±R`); `x_N` is the largest
  distance from the optical axis for which a ray undergoes at most `N`
  reflections — the `N`-th step edge of the staircase.

Current subquestion (A.1, the proof target):
  `x_N = R * cos (π / (2 N + 1))`, with the equivalent sine form
  `x_N = R * sin ((2 N − 1) * π / (4 N + 2))`.

The limiting ray is the one whose `N + 1`-st impact lands exactly on the
rim: its first impact angle is `α = π / (2 N + 1)`, its impacts are at
`π / (2 N + 1), 3 π / (2 N + 1), …, (2 N + 1) π / (2 N + 1) = π`, hence
`x_N = R * cos (π / (2 N + 1))`.
-/

open Real

namespace IPhO2026_2_A_1

/-- The physical setup of IPhO 2026 Problem 2, Part A.1: the
half-cylindrical mirror of radius `R`, the family of rays parallel to the
optical axis (Figure 2d), the reflection-count staircase of Figure 2e, and
its threshold sequence `x₁, x₂, x₃, …`. Coordinates are Cartesian in the
plane of Figure 2d, hence real scalars; `R`, `x`, and the thresholds `x_N`
carry the dimension of length; angles and the reflection count are
dimensionless. -/
structure HalfCylindricalMirror where
  /-- Radius `R` of the half-cylindrical mirror (a length), as labelled in
  Figures 2d and 2e (`2R` in Figure 2c is the cylinder diameter). -/
  R : ℝ
  /-- The mirror radius is positive. -/
  R_pos : 0 < R
  /-- Number `N_refl x` of reflections undergone by the incident ray with
  transverse coordinate `x` (the staircase variable `N` of Figure 2e;
  dimensionless). It is defined for all real `x`; the mirror only admits
  rays with `|x| < R`. -/
  N_refl : ℝ → ℕ
  /-- The general term `x_NAt n` of the threshold sequence `x₁, x₂, x₃, …`
  of T2-A1, indexed from `0` so that the recorded answer for the positive
  integer `N` is `x_NAt (N - 1)` (a length). -/
  x_NAt : ℕ → ℝ
  /-- The thresholds are positive (Figure 2e: the staircase is symmetric
  about the optical axis, with its edges at `±x₁, ±x₂, …`). -/
  x_NAt_pos : ∀ n : ℕ, 0 < x_NAt n
  /-- Each threshold lies inside the mirror opening `(−R, R)` (Figure 2e:
  every edge of the staircase lies strictly between the rim points `±R`). -/
  x_NAt_lt_R : ∀ n : ℕ, x_NAt n < R
  /-- Reflection-count symmetry (Figure 2d readout): the mirror is symmetric
  about the optical axis, so the number of reflections depends on `x` only
  through the distance `|x|` from the axis; the staircase of Figure 2e is
  symmetric in `x ↦ −x`. -/
  N_refl_abs : ∀ x : ℝ, N_refl (-x) = N_refl x
  /-- The axial ray (`x = 0`) is reflected exactly once, at the top of the
  mirror `(0, R)` (Figure 2d; the `N = 1` plateau of Figure 2e contains the
  origin). -/
  N_refl_zero : N_refl 0 = 1
  /-- Defining property of the threshold sequence (Figure 2e readout):
  `x_NAt n` is the largest distance from the optical axis for which a ray
  undergoes at most `n + 1` reflections: below it the count is at most
  `n + 1`, and from the edge onward (within the mirror opening) the count
  exceeds `n + 1`. The edge itself lies on the next plateau, per the
  right-continuous staircase of Figure 2e. -/
  x_NAt_is_threshold : ∀ n : ℕ,
    (∀ x : ℝ, |x| < x_NAt n → N_refl x ≤ n + 1) ∧
    (∀ x : ℝ, x_NAt n ≤ |x| → |x| < R → n + 1 < N_refl x)
  /-- Staircase edge value (Figure 2e readout, the filled dots): at the
  threshold `x_NAt n` the ray hits the rim `(±R, 0)` at its last impact,
  which counts as a reflection, so the count at the edge is exactly
  `n + 2`. -/
  x_NAt_edge_count : ∀ n : ℕ, N_refl (x_NAt n) = n + 2
  /-- Geometric reflection-count law (governing law). By the law of
  reflection (`angle of reflection = angle of incidence`) applied to the
  circular mirror, the incidence angle is the same at every impact of a
  given ray, the central angle between consecutive impact points is the
  constant `2 α`, and the impact points have standard polar angles
  `α, 3 α, 5 α, …, (2 k + 1) α, …`. For the right half of the mirror
  (`x ≥ 0`, entry polar angle `α ∈ (0, π / 2]`) the first would-be impact
  beyond `π` lands in the open lower half (the step `2 α` is at most `π`,
  so the sequence cannot jump over the lower half), and the ray escapes
  there; hence the reflection count is exactly the number of odd multiples
  of `α` not exceeding `π`, an impact exactly on the rim angle `π`
  included. The left-half count is fixed by the mirror symmetry
  `N_refl_abs`. -/
  reflection_count_law : ∀ α : ℝ, α ∈ Set.Ioc 0 (π / 2) →
    N_refl (R * cos α) = Set.ncard {k : ℕ | (2 * (k : ℝ) + 1) * α ≤ π}

namespace HalfCylindricalMirror

open Real

variable (s : HalfCylindricalMirror)

theorem limiting_ray_reflection_count (n : ℕ) :
    s.N_refl (s.R * cos (π / (2 * ((n : ℝ) + 1) + 1))) = n + 2 := by
  have hd_pos : (0:ℝ) < 2 * ((n : ℝ) + 1) + 1 := by positivity
  have hd_ne : (2 : ℝ) * ((n : ℝ) + 1) + 1 ≠ 0 := ne_of_gt hd_pos
  have htwo : (2:ℝ) ≤ 2 * ((n : ℝ) + 1) + 1 := by
    have : (0:ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n
    linarith
  have hα : π / (2 * ((n : ℝ) + 1) + 1) ∈ Set.Ioc 0 (π / 2) := by
    constructor
    · exact div_pos pi_pos hd_pos
    · rw [div_le_iff₀ hd_pos]
      calc π = π / 2 * 2 := by ring
      _ ≤ π / 2 * (2 * ((n : ℝ) + 1) + 1) :=
        mul_le_mul_of_nonneg_left htwo (by positivity)
  rw [s.reflection_count_law _ hα]
  have hour : ∀ k : ℕ,
      ((2 * (k : ℝ) + 1) * (π / (2 * ((n : ℝ) + 1) + 1)) ≤ π) ↔ k ≤ n + 1 := by
    intro k
    have hmd : (0:ℝ) < π / (2 * ((n : ℝ) + 1) + 1) := div_pos pi_pos hd_pos
    have hmd0 : (0:ℝ) ≤ π / (2 * ((n : ℝ) + 1) + 1) := le_of_lt hmd
    constructor
    · intro h
      by_contra hnot
      push_neg at hnot
      have hkn : ((n : ℝ) + 1) + 1 ≤ (k : ℝ) := by exact_mod_cast hnot
      have hlt : 2 * ((n : ℝ) + 1) + 1 < 2 * (k : ℝ) + 1 := by linarith
      have hstrict : (2 * ((n : ℝ) + 1) + 1) * (π / (2 * ((n : ℝ) + 1) + 1)) <
          (2 * (k : ℝ) + 1) * (π / (2 * ((n : ℝ) + 1) + 1)) :=
        mul_lt_mul_of_pos_right hlt hmd
      rw [mul_div_cancel₀ π hd_ne] at hstrict
      linarith
    · intro h
      have hkn : (k : ℝ) ≤ (n : ℝ) + 1 := by exact_mod_cast h
      have hmono : 2 * (k : ℝ) + 1 ≤ 2 * ((n : ℝ) + 1) + 1 := by linarith
      have hle : (2 * (k : ℝ) + 1) * (π / (2 * ((n : ℝ) + 1) + 1)) ≤
          (2 * ((n : ℝ) + 1) + 1) * (π / (2 * ((n : ℝ) + 1) + 1)) :=
        mul_le_mul_of_nonneg_right hmono hmd0
      rw [mul_div_cancel₀ π hd_ne] at hle
      exact hle
  have hset : {k : ℕ | (2 * (k : ℝ) + 1) * (π / (2 * ((n : ℝ) + 1) + 1)) ≤ π} =
      Finset.Iic (n + 1) := by
    ext k
    simp only [Set.mem_setOf_eq, Finset.mem_coe, Finset.mem_Iic]
    exact hour k
  rw [hset, Set.ncard_coe_finset, Nat.card_Iic]

theorem threshold_forms_agree (n : ℕ) :
    s.R * sin ((2 * ((n : ℝ) + 1) - 1) * π / (4 * ((n : ℝ) + 1) + 2)) =
      s.R * cos (π / (2 * ((n : ℝ) + 1) + 1)) := by
  have hd : (0:ℝ) < 2 * ((n : ℝ) + 1) + 1 := by positivity
  have hdne : (2 : ℝ) * ((n : ℝ) + 1) + 1 ≠ 0 := ne_of_gt hd
  have hkey : (2 * ((n : ℝ) + 1) - 1) * π / (4 * ((n : ℝ) + 1) + 2) =
      π / 2 - π / (2 * ((n : ℝ) + 1) + 1) := by
    have hden : (4 : ℝ) * ((n : ℝ) + 1) + 2 = 2 * (2 * ((n : ℝ) + 1) + 1) := by ring
    rw [hden, mul_div_assoc]
    field_simp
    ring
  rw [hkey, sin_pi_div_two_sub]

/-- The cut set is finite (bounded by any `K` with `(2K+1) α > π`). -/
theorem cut_finite {α : ℝ} (hα : 0 < α) :
    {k : ℕ | (2 * (k : ℝ) + 1) * α ≤ π}.Finite := by
  obtain ⟨K, hK⟩ := exists_nat_gt (π / α)
  have hαmul : π / α * α = π := div_mul_cancel₀ π (ne_of_gt hα)
  have hbig : π < (K : ℝ) * α := by
    have := mul_lt_mul_of_pos_right hK hα
    rwa [hαmul] at this
  have hsub : {k : ℕ | (2 * (k : ℝ) + 1) * α ≤ π} ⊆ Finset.Iio K := by
    intro k hk
    rw [Set.mem_setOf_eq] at hk
    rw [Finset.mem_coe, Finset.mem_Iio]
    by_contra hcon
    push_neg at hcon
    have hKk : (K : ℝ) ≤ (k : ℝ) := by exact_mod_cast hcon
    have h2 : (K : ℝ) * α ≤ (2 * (K : ℝ) + 1) * α := by
      apply mul_le_mul_of_nonneg_right _ (le_of_lt hα)
      have hK0 : (0:ℝ) ≤ (K : ℝ) := Nat.cast_nonneg K
      nlinarith
    have h3 : (2 * (K : ℝ) + 1) * α ≤ (2 * (k : ℝ) + 1) * α := by
      apply mul_le_mul_of_nonneg_right _ (le_of_lt hα)
      nlinarith
    linarith
  exact Set.Finite.subset (Finset.finite_toSet _) hsub

/-- The cut set has card at most `m` when the `m`-th odd multiple exceeds `π`. -/
theorem ncard_clip_le {m : ℕ} {α : ℝ} (hα : 0 < α)
    (hm : π < (2 * (m : ℝ) + 1) * α) :
    Set.ncard {k : ℕ | (2 * (k : ℝ) + 1) * α ≤ π} ≤ m := by
  have hsub : {k : ℕ | (2 * (k : ℝ) + 1) * α ≤ π} ⊆ Finset.Iio m := by
    intro k hk
    rw [Set.mem_setOf_eq] at hk
    rw [Finset.mem_coe, Finset.mem_Iio]
    by_contra hknot
    push_neg at hknot
    have hkm : (m : ℝ) ≤ (k : ℝ) := by exact_mod_cast hknot
    have hmono : (2 * (m : ℝ) + 1) * α ≤ (2 * (k : ℝ) + 1) * α := by
      apply mul_le_mul_of_nonneg_right _ (le_of_lt hα)
      nlinarith
    exact absurd (le_trans hmono hk) (not_le.mpr hm)
  have hfin : ((Finset.Iio m : Finset ℕ) : Set ℕ).Finite := Finset.finite_toSet _
  calc Set.ncard {k : ℕ | (2 * (k : ℝ) + 1) * α ≤ π}
      ≤ Set.ncard ((Finset.Iio m : Finset ℕ) : Set ℕ) :=
        Set.ncard_le_ncard hsub hfin
    _ = m := by rw [Set.ncard_coe_finset, Nat.card_Iio]

/-- The cut set has card at least `m + 1` when the `m`-th odd multiple is
strictly below `π`. -/
theorem ncard_clip_ge {m : ℕ} {α : ℝ} (hα : 0 < α)
    (hm : (2 * (m : ℝ) + 1) * α < π) :
    m + 1 ≤ Set.ncard {k : ℕ | (2 * (k : ℝ) + 1) * α ≤ π} := by
  have hsub : ((Finset.Iic m : Finset ℕ) : Set ℕ) ⊆
      {k : ℕ | (2 * (k : ℝ) + 1) * α ≤ π} := by
    intro k hk
    rw [Finset.mem_coe, Finset.mem_Iic] at hk
    rw [Set.mem_setOf_eq]
    have hkm : (k : ℝ) ≤ (m : ℝ) := by exact_mod_cast hk
    have hmono : (2 * (k : ℝ) + 1) * α ≤ (2 * (m : ℝ) + 1) * α := by
      apply mul_le_mul_of_nonneg_right _ (le_of_lt hα)
      nlinarith
    linarith
  have hfin : {k : ℕ | (2 * (k : ℝ) + 1) * α ≤ π}.Finite := cut_finite hα
  have hcard := Set.ncard_le_ncard hsub hfin
  rw [Set.ncard_coe_finset, Nat.card_Iic] at hcard
  exact hcard

/-- Contrapositive readout: if the `m`-th odd multiple exceeds `π`, the
reflection count is at most `m`. -/
theorem reflection_count_le_of_exceeds (s : HalfCylindricalMirror) {α : ℝ}
    (hα : α ∈ Set.Ioc 0 (π / 2)) {m : ℕ}
    (hm : π < (2 * (m : ℝ) + 1) * α) :
    s.N_refl (s.R * cos α) ≤ m := by
  rw [s.reflection_count_law α hα]
  exact ncard_clip_le hα.1 hm

/-- The entry polar angle `arccos (y / R)` of the ray at transverse coordinate
`y ∈ (0, R)` lies in `(0, π / 2]`. -/
theorem arccos_Ioc_of_mem (s : HalfCylindricalMirror) {y : ℝ} (hy0 : 0 < y)
    (hyR : y < s.R) : Real.arccos (y / s.R) ∈ Set.Ioc 0 (π / 2) := by
  have hyR0 : 0 ≤ y / s.R := div_nonneg (le_of_lt hy0) (le_of_lt s.R_pos)
  have hyR1 : y / s.R < 1 := by
    rw [div_lt_one s.R_pos]
    exact hyR
  constructor
  · have h2 : Real.arccos (y / s.R) > Real.arccos 1 :=
      arccos_lt_arccos (by linarith) hyR1 (le_refl 1)
    rw [arccos_one] at h2
    exact h2
  · have h3 : Real.arccos (y / s.R) ≤ Real.arccos 0 :=
      arccos_le_arccos hyR0
    rw [arccos_zero] at h3
    exact h3

theorem threshold_x_N_cos (n : ℕ) :
    s.x_NAt n = s.R * cos (π / (2 * ((n : ℝ) + 1) + 1)) := by
  have hd_pos : (0:ℝ) < 2 * ((n : ℝ) + 1) + 1 := by positivity
  have hone : (1:ℝ) ≤ 2 * ((n : ℝ) + 1) + 1 := by
    have : (0:ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n
    linarith
  have hαpos : 0 < π / (2 * ((n : ℝ) + 1) + 1) := div_pos pi_pos hd_pos
  have hαleπ : π / (2 * ((n : ℝ) + 1) + 1) ≤ π :=
    calc π / (2 * ((n : ℝ) + 1) + 1) ≤ π / 1 :=
          div_le_div_of_nonneg_left (le_of_lt pi_pos) zero_lt_one hone
      _ = π := div_one π
  set xstar : ℝ := s.R * cos (π / (2 * ((n : ℝ) + 1) + 1)) with hxstar
  have hxstarn : s.N_refl xstar = n + 2 := s.limiting_ray_reflection_count n
  have hcos_pos : 0 < cos (π / (2 * ((n : ℝ) + 1) + 1)) := by
    apply cos_pos_of_mem_Ioo
    constructor
    · linarith [hαpos, pi_pos]
    · rw [div_lt_iff₀ hd_pos]
      have htwo : (2:ℝ) < 2 * ((n : ℝ) + 1) + 1 := by
        have : (0:ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n
        linarith
      calc π = π / 2 * 2 := by ring
      _ < π / 2 * (2 * ((n : ℝ) + 1) + 1) :=
          mul_lt_mul_of_pos_left (by linarith [pi_pos, htwo] : (2:ℝ) < 2 * ((n : ℝ) + 1) + 1) (by positivity)
  have hxstar_pos : 0 < xstar := mul_pos s.R_pos hcos_pos
  have hcos_lt_one : cos (π / (2 * ((n : ℝ) + 1) + 1)) < 1 := by
    have h3 : cos (π / (2 * ((n : ℝ) + 1) + 1)) < cos 0 :=
      cos_lt_cos_of_nonneg_of_le_pi (le_refl 0) hαleπ hαpos
    rwa [cos_zero] at h3
  have hxstar_lt_R : xstar < s.R := by
    calc xstar = s.R * cos (π / (2 * ((n : ℝ) + 1) + 1)) := hxstar
    _ < s.R * 1 := mul_lt_mul_of_pos_left hcos_lt_one s.R_pos
    _ = s.R := mul_one s.R
  by_contra hne
  rcases lt_or_gt_of_ne hne with hlt | hgt
  · -- x_NAt n < xstar: take y ∈ (x_NAt n, xstar); prop(b) gives n+1 < N_refl y,
    -- geometry (y < xstar) gives N_refl y ≤ n+1.
    set y := (s.x_NAt n + xstar) / 2 with hy
    have hy0 : 0 < y := by
      have h1 := s.x_NAt_pos n
      linarith
    have hy1 : s.x_NAt n < y := by linarith
    have hy2 : y < xstar := by linarith
    have hyR : y < s.R := lt_trans hy2 hxstar_lt_R
    have hineq2 : n + 1 < s.N_refl y := (s.x_NAt_is_threshold n).2 y (by
      rw [abs_of_pos hy0]
      exact le_of_lt hy1) (by
      rw [abs_of_pos hy0]
      exact hyR)
    set αy := Real.arccos (y / s.R) with hαy
    have hαy_Ioc : αy ∈ Set.Ioc 0 (π / 2) := s.arccos_Ioc_of_mem hy0 hyR
    have hyR0 : 0 ≤ y / s.R := div_nonneg (le_of_lt hy0) (le_of_lt s.R_pos)
    have hyR1 : y / s.R ≤ 1 := by
      rw [div_le_one s.R_pos]
      exact le_of_lt hyR
    have hcos_y : s.R * cos αy = y := by
      rw [hαy, cos_arccos (by linarith) hyR1]
      field_simp [ne_of_gt s.R_pos]
    rw [← hcos_y] at hineq2
    rw [s.reflection_count_law αy hαy_Ioc] at hineq2
    have hxlt : cos αy < cos (π / (2 * ((n : ℝ) + 1) + 1)) := by
      rw [hαy, cos_arccos (by linarith) hyR1]
      have hstep : y / s.R < cos (π / (2 * ((n : ℝ) + 1) + 1)) := by
        rw [div_lt_iff₀ s.R_pos, mul_comm]
        calc y < xstar := hy2
        _ = s.R * cos (π / (2 * ((n : ℝ) + 1) + 1)) := hxstar
      exact hstep
    have hαy_leπ : αy ≤ π := by
      have h1 := hαy_Ioc.1
      have h2 := hαy_Ioc.2
      linarith [pi_pos]
    have hltα : π / (2 * ((n : ℝ) + 1) + 1) < αy := by
      by_contra hc
      push_neg at hc
      have hle := cos_le_cos_of_nonneg_of_le_pi (le_of_lt hαy_Ioc.1) hαleπ hc
      linarith [hxlt]
    have hcut : π < (2 * ((n : ℝ) + 1) + 1) * αy := by
      have := (div_lt_iff₀ hd_pos).mp hltα
      calc π < αy * (2 * ((n : ℝ) + 1) + 1) := this
      _ = (2 * ((n : ℝ) + 1) + 1) * αy := mul_comm _ _
    have hle2 : Set.ncard {k : ℕ | (2 * (k : ℝ) + 1) * αy ≤ π} ≤ n + 1 := by
      have hcast : (2 : ℝ) * ((n + 1 : ℕ) : ℝ) + 1 = 2 * ((n : ℝ) + 1) + 1 := by push_cast; ring
      have hcut' : π < (2 * ((n + 1 : ℕ) : ℝ) + 1) * αy := by rwa [hcast]
      exact ncard_clip_le hαy_Ioc.1 hcut'
    omega
  · -- xstar < x_NAt n: take y ∈ (xstar, x_NAt n); prop(a) gives N_refl y ≤ n+1,
    -- geometry (y > xstar) gives n+2 ≤ N_refl y.
    set y := (xstar + s.x_NAt n) / 2 with hy
    have hy0 : 0 < y := by linarith [hxstar_pos, s.x_NAt_pos n]
    have hy1 : xstar < y := by linarith
    have hy2 : y < s.x_NAt n := by linarith
    have hyR : y < s.R := lt_trans hy2 (s.x_NAt_lt_R n)
    have hineq1 : s.N_refl y ≤ n + 1 := (s.x_NAt_is_threshold n).1 y (by
      rw [abs_of_pos hy0]
      exact hy2)
    set αy := Real.arccos (y / s.R) with hαy
    have hαy_Ioc : αy ∈ Set.Ioc 0 (π / 2) := s.arccos_Ioc_of_mem hy0 hyR
    have hyR0 : 0 ≤ y / s.R := div_nonneg (le_of_lt hy0) (le_of_lt s.R_pos)
    have hyR1 : y / s.R ≤ 1 := by
      rw [div_le_one s.R_pos]
      exact le_of_lt hyR
    have hcos_y : s.R * cos αy = y := by
      rw [hαy, cos_arccos (by linarith) hyR1]
      field_simp [ne_of_gt s.R_pos]
    rw [← hcos_y] at hineq1
    rw [s.reflection_count_law αy hαy_Ioc] at hineq1
    have hxgt : cos (π / (2 * ((n : ℝ) + 1) + 1)) < cos αy := by
      rw [hαy, cos_arccos (by linarith) hyR1]
      have hstep : cos (π / (2 * ((n : ℝ) + 1) + 1)) < y / s.R := by
        rw [lt_div_iff₀ s.R_pos]
        calc cos (π / (2 * ((n : ℝ) + 1) + 1)) * s.R = xstar := by rw [hxstar]; ring
        _ < y := hy1
      exact hstep
    have hαy_leπ : αy ≤ π := by
      have h1 := hαy_Ioc.1
      have h2 := hαy_Ioc.2
      linarith [pi_pos]
    have hltα : αy < π / (2 * ((n : ℝ) + 1) + 1) := by
      by_contra hc
      push_neg at hc
      have hle := cos_le_cos_of_nonneg_of_le_pi (le_of_lt hαpos) hαy_leπ hc
      linarith [hxgt]
    have hcut : (2 * ((n : ℝ) + 1) + 1) * αy < π := by
      have hmul : αy * (2 * ((n : ℝ) + 1) + 1) < π := (lt_div_iff₀ hd_pos).mp hltα
      calc (2 * ((n : ℝ) + 1) + 1) * αy = αy * (2 * ((n : ℝ) + 1) + 1) := mul_comm _ _
      _ < π := hmul
    have hge2 : n + 2 ≤ Set.ncard {k : ℕ | (2 * (k : ℝ) + 1) * αy ≤ π} := by
      have hcast : (2 : ℝ) * ((n + 1 : ℕ) : ℝ) + 1 = 2 * ((n : ℝ) + 1) + 1 := by push_cast; ring
      have hcut' : (2 * ((n + 1 : ℕ) : ℝ) + 1) * αy < π := by rwa [hcast]
      have h := ncard_clip_ge hαy_Ioc.1 hcut'
      exact h
    omega

theorem threshold_x_N_sin (n : ℕ) :
    s.x_NAt n =
      s.R * sin ((2 * ((n : ℝ) + 1) - 1) * π / (4 * ((n : ℝ) + 1) + 2)) := by
  rw [s.threshold_x_N_cos n, s.threshold_forms_agree n]

theorem threshold_x_N (n : ℕ) :
    s.x_NAt n =
        s.R * sin ((2 * ((n : ℝ) + 1) - 1) * π / (4 * ((n : ℝ) + 1) + 2)) ∧
      s.x_NAt n = s.R * cos (π / (2 * ((n : ℝ) + 1) + 1)) :=
  ⟨s.threshold_x_N_sin n, s.threshold_x_N_cos n⟩

end HalfCylindricalMirror

end IPhO2026_2_A_1
