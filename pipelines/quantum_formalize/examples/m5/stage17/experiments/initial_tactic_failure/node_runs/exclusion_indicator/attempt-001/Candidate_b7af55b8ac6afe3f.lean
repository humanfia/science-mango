import FrozenTarget_b7af55b8ac6afe3f
theorem M5.FiniteExclusion.exclusion_indicator : QuantumHarnessFrozenTarget := by
  classical
  change ∀ (S : Finset M5.BinaryPolynomial) (bad : M5.BinaryPolynomial → Bool), M5.FiniteExclusion.exclusionSum S bad = if ∀ p ∈ S, bad p = false then 1 else 0
  intro S bad
  change (∑ H ∈ S.powerset, (-1 : ℤ) ^ H.card * (if ∀ p ∈ H, bad p = true then 1 else 0)) = _
  simp only [mul_ite, mul_one, mul_zero]
  rw [← Finset.sum_filter, M5.FiniteExclusion.filtered_powerset, M5.FiniteExclusion.alternating_subsets]
  have h : S.filter (fun p => bad p = true) = ∅ ↔ ∀ p ∈ S, bad p = false := by
    simp only [Finset.filter_eq_empty_iff]
    constructor
    · intro hn p hp
      have hb := hn p hp
      cases bad p <;> simp_all
    · intro hf p hp
      rw [hf p hp]
      decide
  rw [h]
