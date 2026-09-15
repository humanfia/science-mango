import FrozenTarget_bce8d3dadb00f709
theorem M7.Supports.coefficient : QuantumHarnessFrozenTarget := by
  classical
  intro N inst A n
  unfold M7.Supports.polynomial
  rw [Polynomial.finsetSum_coeff]
  by_cases h : ∃ i ∈ A, i.val = n
  · rw [if_pos h]
    obtain ⟨i, hiA, hin⟩ := h
    rw [Finset.sum_eq_single i]
    · simp [Polynomial.coeff_X_pow, hin]
    · intro j hjA hji
      have hjn : j.val ≠ n := by
        intro heq
        exact hji (ZMod.val_injective N (heq.trans hin.symm))
      simp [Polynomial.coeff_X_pow, hjn, Ne.symm hjn]
    · intro hi
      exact (hi hiA).elim
  · rw [if_neg h]
    apply Finset.sum_eq_zero
    intro i hiA
    have hin : i.val ≠ n := by
      intro heq
      exact h ⟨i, hiA, heq⟩
    simp [Polynomial.coeff_X_pow, hin, Ne.symm hin]
