import Mathlib

open Real Filter InnerProductGeometry
open scoped InnerProductSpace RealInnerProductSpace Topology

namespace IPhO2026.T1B2

abbrev Plane : Type := EuclideanSpace ℝ (Fin 2)

/-- frozen-like statement whose `2 • v` elaboration we probe -/
theorem frozen_like (f g : ℝ → Plane) : f 0 - g 0 = 2 • g 0 := by
  rw [sub_eq_self]; exact zero_smul _ _

-- Q1a: is it nsmul?
example (f g : ℝ → Plane) (h : f 0 - g 0 = 2 • g 0) : True := by
  guard_hyp h : f 0 - g 0 = (2 : ℕ) • g 0
  trivial

-- Q2a: does real_inner_smul_right match directly after rw [h]?
example (f g : ℝ → Plane) (x : Plane) (h : f 0 - g 0 = 2 • g 0) :
    ⟪x, f 0 - g 0⟫_ℝ = 0 := by
  rw [h]
  rw [real_inner_smul_right]
  sorry

-- Q2b: nsmul → cast-smul fix path
example (f g : ℝ → Plane) (x : Plane) (h : f 0 - g 0 = 2 • g 0) :
    ⟪x, f 0 - g 0⟫_ℝ = 0 := by
  rw [h, ← Nat.cast_smul_eq_nsmul ℝ 2 (g 0), Nat.cast_ofNat, real_inner_smul_right]
  sorry

-- Q3: norm chain after cast fix
example (f g : ℝ → Plane) (h : f 0 - g 0 = 2 • g 0) :
    ‖f 0 - g 0‖ ^ 2 = 4 * ‖g 0‖ ^ 2 := by
  rw [h, ← Nat.cast_smul_eq_nsmul ℝ 2 (g 0), Nat.cast_ofNat, norm_smul, mul_pow,
    norm_ofNat]
  ring

-- Q3b: norm_ofNat as standalone
example : ‖(2 : ℝ)‖ = 2 := by simp

-- Q3c: norm_num on ‖(2:ℝ)‖
example : ‖(2 : ℝ)‖ = 2 := by norm_num

-- Q4a: sub_zero after rw-produced 0 under a binder (the 1197 shape)
example (g : ℝ → ℝ) (h0 : g 0 = 0)
    (h : Tendsto (fun t => t⁻¹ • (g t - g 0)) atTop (𝓝 (1 : ℝ))) :
    Tendsto (fun t => t⁻¹ • g t) atTop (𝓝 1) := by
  rw [h0] at h
  rw [sub_zero] at h
  exact h

-- Q4b: sin_zero then sub_zero (sin_lower shape)
example (x : ℝ) : Real.sin x - Real.sin 0 ≤ Real.sin x := by
  rw [Real.sin_zero, sub_zero]

-- Q4c: mul_zero then sub_zero (hww shape)
example (a : ℝ) : (0 : ℝ) - a * 0 = 0 := by
  rw [mul_zero, sub_zero]

-- Q5a: ContDiff.differentiable with plain decide
example (f : ℝ → Plane) (hf : ContDiff ℝ 2 f) : Differentiable ℝ f :=
  hf.differentiable (by decide)

-- Q5b: ContDiff.continuous_deriv with plain decide
example (f : ℝ → Plane) (hf : ContDiff ℝ 2 f) : Continuous (deriv f) :=
  hf.continuous_deriv (by decide)

-- Q6: smul_ne_zero with real scalar 2
example (v : Plane) (hv : v ≠ 0) : (2 : ℝ) • v ≠ 0 :=
  smul_ne_zero (by norm_num) hv

-- Q7: hdr-style convert
example (a ε : ℝ) (r : ℝ → Plane) (u0 ax : Plane) (hr : HasDerivAt r u0 0) :
    HasDerivAt (fun t => (a + ε * ⟪ax, r t⟫_ℝ) ^ 2)
      (2 * (a + ε * ⟪ax, r 0⟫_ℝ) * (ε * ⟪ax, u0⟫_ℝ)) 0 := by
  have hinner : HasDerivAt (fun t => ⟪ax, r t⟫_ℝ) ⟪ax, u0⟫_ℝ 0 := by
    have h := HasDerivAt.inner (𝕜 := ℝ) (hasDerivAt_const (0 : ℝ) ax) hr
    simpa using h
  have h := ((hasDerivAt_const (0 : ℝ) a).add (hinner.const_mul ε)).pow 2
  convert h using 1
  · ext t
    simp only [Pi.pow_apply, Pi.add_apply]
  · simp only [Pi.add_apply, Nat.cast_ofNat, show (2 : ℕ) - 1 = 1 from rfl, pow_one,
      zero_add]

-- Q8a: int_one_sub_sq_div_two shape
example (x : ℝ) : ∫ t in (0 : ℝ)..x, (1 - t ^ 2 / 2) = x - x ^ 3 / 6 := by
  rw [intervalIntegral.integral_sub intervalIntegrable_const
      (((continuous_pow 2).div_const 2).intervalIntegrable _ _),
    intervalIntegral.integral_const, intervalIntegral.integral_div, integral_pow]
  simp only [smul_eq_mul, sub_zero]
  ring

-- Q8b: int_id_sub_cube_div_six shape
example (x : ℝ) : ∫ s in (0 : ℝ)..x, (s - s ^ 3 / 6) = x ^ 2 / 2 - x ^ 4 / 24 := by
  rw [intervalIntegral.integral_sub intervalIntegral.intervalIntegrable_id
      (((continuous_pow 3).div_const 6).intervalIntegrable _ _),
    intervalIntegral.integral_div, integral_pow, integral_id]
  simp only [smul_eq_mul, sub_zero]
  ring

-- Q9: eventually_gt fix (vsub_eq_sub)
example {g : ℝ → ℝ} {a c : ℝ} (hg : HasDerivAt g c a) (hc : 0 < c) :
    ∀ᶠ t in 𝓝[>] a, g a < g t := by
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
      div_mul_cancel₀ _ hsub, vsub_eq_sub]
  have hmulpos : 0 < slope g a t * (t - a) := mul_pos (by linarith [ht]) hpos
  linarith [hmul, hmulpos]

-- Q10: parenthesized HasDerivAt statement parses
example (F : ℝ → ℝ) (d : ℝ) : HasDerivAt F (d ^ 2) 0 := by
  sorry

-- Q11: rw [two_smul] on the frozen-like 2 • v (what happened at line 625)
example (f g : ℝ → Plane) (h : f 0 - g 0 = 2 • g 0) :
    f 0 - g 0 = g 0 + g 0 := by
  rw [h, two_smul]

end IPhO2026.T1B2
