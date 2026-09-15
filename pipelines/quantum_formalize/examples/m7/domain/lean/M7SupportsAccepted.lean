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

theorem M7.Supports.anchor : ∀ (N : ℕ) [NeZero N] (A : M7.Supports.Support N), ((M7.Supports.polynomial A).coeff 0 = 1 ↔ (0 : ZMod N) ∈ A) := by
  change ∀ (N : ℕ) [NeZero N] (A : M7.Supports.Support N), ((M7.Supports.polynomial A).coeff 0 = 1 ↔ (0 : ZMod N) ∈ A)
  classical
  intro N inst A
  have h : (M7.Supports.polynomial A).coeff 0 = M7.Supports.indicator A (0 : ZMod N) := by
    simpa using M7.Supports.indicator_coefficient N A (0 : ZMod N)
  rw [h]
  by_cases hz : (0 : ZMod N) ∈ A <;> simp [M7.Supports.indicator, hz]

theorem M7.Supports.degree_lt : ∀ (N : ℕ) [NeZero N] (A : M7.Supports.Support N), (M7.Supports.polynomial A).natDegree < N := by
  classical
  change ∀ (N : ℕ) [NeZero N] (A : M7.Supports.Support N), (M7.Supports.polynomial A).natDegree < N
  intro N inst A
  by_cases h : M7.Supports.polynomial A = 0
  · simpa [h] using (Nat.pos_of_ne_zero (NeZero.ne N))
  · have hm := Polynomial.natDegree_mem_support_of_nonzero h
    rw [M7.Supports.support N A] at hm
    change (M7.Supports.polynomial A).natDegree ∈ A.image ZMod.val at hm
    obtain ⟨i, hi, heq⟩ := Finset.mem_image.mp hm
    rw [← heq]
    exact ZMod.val_lt i

theorem M7.Supports.support_card : ∀ (N : ℕ) [NeZero N] (A : M7.Supports.Support N), (M7.Supports.polynomial A).support.card = A.card := by
  classical
  change ∀ (N : ℕ) [NeZero N] (A : M7.Supports.Support N), (M7.Supports.polynomial A).support.card = A.card
  intro N inst A
  rw [M7.Supports.support N A]
  unfold M7.Supports.natSupport
  exact Finset.card_image_of_injective A (ZMod.val_injective N)
#print axioms M7.Supports.coefficient
#print axioms M7.Supports.indicator_coefficient
#print axioms M7.Supports.anchor
#print axioms M7.Supports.support
#print axioms M7.Supports.degree_lt
#print axioms M7.Supports.support_card
