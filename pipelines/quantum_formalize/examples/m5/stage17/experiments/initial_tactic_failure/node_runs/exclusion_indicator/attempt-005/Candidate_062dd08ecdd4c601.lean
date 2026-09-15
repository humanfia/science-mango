import FrozenTarget_062dd08ecdd4c601
theorem M5.FiniteExclusion.exclusion_indicator : QuantumHarnessFrozenTarget := by
  classical
  change ∀ (S : Finset M5.BinaryPolynomial) (bad : M5.BinaryPolynomial → Bool), M5.FiniteExclusion.exclusionSum S bad = if ∀ p ∈ S, bad p = false then 1 else 0
  intro S bad
  have he : S.filter (fun p => bad p = true) = ∅ ↔ ∀ p ∈ S, bad p = false := by
    constructor
    · intro h p hp
      cases hb : bad p with
      | false => rfl
      | true =>
        have hm : p ∈ S.filter (fun p => bad p = true) := Finset.mem_filter.mpr ⟨hp, hb⟩
        rw [h] at hm
        simp at hm
    · intro h
      apply Finset.ext
      intro p
      simp only [Finset.mem_filter, Finset.not_mem_empty, iff_false]
      rintro ⟨hp, hb⟩
      have hf := h p hp
      rw [hf] at hb
      cases hb
  change (∑ H ∈ S.powerset, (-1 : ℤ) ^ H.card * (if ∀ p ∈ H, bad p = true then 1 else 0)) = _
  simp only [mul_ite, mul_one, mul_zero]
  rw [← Finset.sum_filter, M5.FiniteExclusion.filtered_powerset, M5.FiniteExclusion.alternating_subsets]
  simp only [he]
