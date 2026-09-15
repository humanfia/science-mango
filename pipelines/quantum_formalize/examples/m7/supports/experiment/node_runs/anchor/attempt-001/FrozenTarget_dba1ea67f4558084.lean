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

theorem M7.Supports.indicator_coefficient : ∀ (N : ℕ) [NeZero N] (A : M7.Supports.Support N), ∀ i : ZMod N, (M7.Supports.polynomial A).coeff i.val = M7.Supports.indicator A i := by
  classical
  intro N inst A i
  rw [M7.Supports.coefficient]
  unfold M7.Supports.indicator
  by_cases hi : i ∈ A
  · have hex : ∃ j ∈ A, j.val = i.val := ⟨i, hi, rfl⟩
    simp only [if_pos hex, if_pos hi]
  · have hnex : ¬ ∃ j ∈ A, j.val = i.val := by
      rintro ⟨j, hj, hval⟩
      have hji : j = i := ZMod.val_injective N hval
      exact hi (hji ▸ hj)
    simp only [if_neg hnex, if_neg hi]
def QuantumHarnessFrozenTarget : Prop :=
  ∀ (N : ℕ) [NeZero N] (A : M7.Supports.Support N), ((M7.Supports.polynomial A).coeff 0 = 1 ↔ (0 : ZMod N) ∈ A)
