import Mathlib

open Real Filter
open scoped Topology BigOperators

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
