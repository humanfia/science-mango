import M7Supports

theorem M7.Supports.coefficient : ∀ (N : ℕ) [NeZero N] (A : M7.Supports.Support N), ∀ n : ℕ, (M7.Supports.polynomial A).coeff n = if ∃ i ∈ A, i.val = n then 1 else 0 := by
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

theorem M7.Supports.support : ∀ (N : ℕ) [NeZero N] (A : M7.Supports.Support N), (M7.Supports.polynomial A).support = M7.Supports.natSupport A := by
  classical
  change ∀ (N : ℕ) [NeZero N] (A : M7.Supports.Support N), (M7.Supports.polynomial A).support = M7.Supports.natSupport A
  intro N inst A
  ext n
  rw [Polynomial.mem_support_iff, M7.Supports.coefficient N A n]
  simp only [M7.Supports.natSupport, Finset.mem_image]
  by_cases h : ∃ i ∈ A, i.val = n
  · simp [h]
  · simp [h]
def QuantumHarnessFrozenTarget : Prop :=
  ∀ (N : ℕ) [NeZero N] (A : M7.Supports.Support N), (M7.Supports.polynomial A).support.card = A.card
