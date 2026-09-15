import FrozenTarget_a9f55c9cced6f5bc
theorem M5.FiniteExclusion.exclusion_indicator : QuantumHarnessFrozenTarget := by
  classical
  change ∀ (S : Finset M5.BinaryPolynomial) (bad : M5.BinaryPolynomial → Bool), M5.FiniteExclusion.exclusionSum S bad = if ∀ p ∈ S, bad p = false then 1 else 0
  intro S bad
  have hempty : S.filter (fun p => bad p = true) = ∅ ↔ ∀ p ∈ S, bad p = false := by
    constructor
    · intro h p hp
      have hn : bad p ≠ true := by
        intro hb
        have hm := Finset.mem_filter.mpr ⟨hp, hb⟩
        rw [h] at hm
        simpa using hm
      cases hb : bad p <;> simp_all
    · intro h
      apply Finset.ext
      intro p
      constructor
      · intro hp
        obtain ⟨hp, hb⟩ := Finset.mem_filter.mp hp
        have hf := h p hp
        simp_all
      · intro hp
        simpa using hp
  change (∑ H ∈ S.powerset, (-1 : ℤ) ^ H.card * (if ∀ p ∈ H, bad p = true then 1 else 0)) = _
  simp only [mul_ite, mul_one, mul_zero]
  rw [← Finset.sum_filter, M5.FiniteExclusion.filtered_powerset, M5.FiniteExclusion.alternating_subsets]
  simp only [hempty]
