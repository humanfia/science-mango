import M7PrefixSector

theorem M7.PrefixSector.completion_membership : ∀ (N w : ℕ) (E : Finset M5.BinaryPolynomial) (A B WA WB : Finset ℕ), ∀ x, x ∈ M7.PrefixSector.completions N w E A B WA WB ↔ ∃ F ∈ E, x ∈ M5.ConditionalCount.validCompletions N w F A B WA WB := by
  classical
  intro N w E A B WA WB x
  simp only [M7.PrefixSector.completions, Finset.mem_biUnion]

theorem M7.PrefixSector.count_nonnegative : ∀ (N w : ℕ) (E : Finset M5.BinaryPolynomial) (A B WA WB : Finset ℕ), 0 < N → M7.PrefixSector.ValidSector N E → M5.ConditionalCount.PrefixOK N w A B WA WB → 0 ≤ M7.PrefixSector.count N w E A B WA WB := by
  intro N w E A B WA WB hN hE hPrefix
  classical
  unfold M7.PrefixSector.count
  apply Finset.sum_nonneg
  intro F hF
  exact (M5.ConditionalCount.completion_nonnegative_and_exists
    N w F A B WA WB hN (hE F hF).1 (hE F hF).2 hPrefix).1

theorem M7.PrefixSector.disjoint_sector_sum : ∀ (N w : ℕ) (E H : Finset M5.BinaryPolynomial) (A B WA WB : Finset ℕ), Disjoint E H → M7.PrefixSector.count N w (E ∪ H) A B WA WB = M7.PrefixSector.count N w E A B WA WB + M7.PrefixSector.count N w H A B WA WB := by
  classical
  intro N w E H A B WA WB hEH
  unfold M7.PrefixSector.count
  exact Finset.sum_union hEH

theorem M7.PrefixSector.disjoint_signatures : ∀ (N w : ℕ) (F G : M5.BinaryPolynomial) (A B WA WB : Finset ℕ), F ≠ G → Disjoint (M5.ConditionalCount.validCompletions N w F A B WA WB) (M5.ConditionalCount.validCompletions N w G A B WA WB) := by
  classical
  intro N w F G A B WA WB hFG
  apply Finset.disjoint_left.mpr
  intro p hpF hpG
  simp only [M5.ConditionalCount.validCompletions, Finset.mem_filter] at hpF hpG
  aesop

theorem M7.PrefixSector.empty_sector : ∀ (N w : ℕ) (A B WA WB : Finset ℕ), M7.PrefixSector.count N w ∅ A B WA WB = 0 ∧ M7.PrefixSector.completions N w ∅ A B WA WB = ∅ := by
  change ∀ (N w : ℕ) (A B WA WB : Finset ℕ), M7.PrefixSector.count N w ∅ A B WA WB = 0 ∧ M7.PrefixSector.completions N w ∅ A B WA WB = ∅
  intro N w A B WA WB
  classical
  simp [M7.PrefixSector.count, M7.PrefixSector.completions]

theorem M7.PrefixSector.overfull_zero : ∀ (N w : ℕ) (E : Finset M5.BinaryPolynomial) (A B WA WB : Finset ℕ), (w < A.card ∨ w < B.card) → M7.PrefixSector.count N w E A B WA WB = 0 := by
  intro N w E A B WA WB h
  classical
  change M7.PrefixSector.count N w E A B WA WB = 0
  rcases h with hA | hB
  · simp [M7.PrefixSector.count, M5.ConditionalCount.completionC, hA, Nat.not_le_of_lt hA]
  · simp [M7.PrefixSector.count, M5.ConditionalCount.completionC, hB, Nat.not_le_of_lt hB]

theorem M7.PrefixSector.exact_sector_count : ∀ (N w : ℕ) (E : Finset M5.BinaryPolynomial) (A B WA WB : Finset ℕ), 0 < N → M7.PrefixSector.ValidSector N E → M5.ConditionalCount.PrefixOK N w A B WA WB → M7.PrefixSector.count N w E A B WA WB = (M7.PrefixSector.completions N w E A B WA WB).card := by
  classical
  intro N w E A B WA WB hN hE hPrefix
  unfold M7.PrefixSector.count M7.PrefixSector.completions
  rw [Finset.card_biUnion]
  · rw [Nat.cast_sum]
    apply Finset.sum_congr rfl
    intro F hF
    exact M5.ConditionalCount.exact_completion_C N w F A B WA WB
      hN (hE F hF).1 (hE F hF).2 hPrefix
  · intro F hF G hG hFG
    exact M7.PrefixSector.disjoint_signatures N w F G A B WA WB hFG

theorem M7.PrefixSector.leaf_zero_one : ∀ (N w : ℕ) (E : Finset M5.BinaryPolynomial) (A B : Finset ℕ), 0 < N → M7.PrefixSector.ValidSector N E → M5.ConditionalCount.PrefixOK N w A B ∅ ∅ → M7.PrefixSector.count N w E A B ∅ ∅ = (if A.card = w ∧ B.card = w ∧ M5.Connectivity.supportGcd N A B = 1 ∧ M5.completeSignature (M5.SupportPolynomial.ofSupport A) (M5.SupportPolynomial.ofSupport B) N ∈ E then (1 : ℤ) else 0) := by
  classical
  intro N w E A B hN hE hPrefix
  rw [M7.PrefixSector.exact_sector_count N w E A B ∅ ∅ hN hE hPrefix]
  have hleaf : M7.PrefixSector.completions N w E A B ∅ ∅ =
      ({(∅, ∅)} : Finset (Finset ℕ × Finset ℕ)).filter (fun _ =>
        A.card = w ∧ B.card = w ∧
        M5.Connectivity.supportGcd N A B = 1 ∧
        M5.completeSignature (M5.SupportPolynomial.ofSupport A)
          (M5.SupportPolynomial.ofSupport B) N ∈ E) := by
    have hp := hPrefix
    unfold M5.ConditionalCount.PrefixOK at hp
    ext ⟨U, V⟩
    simp [M7.PrefixSector.completions, M5.ConditionalCount.validCompletions,
      Finset.mem_powersetCard, Finset.mem_product, and_assoc]
    <;> aesop (config := { terminal := false })
    <;> omega
  rw [hleaf]
  by_cases h : A.card = w ∧ B.card = w ∧
      M5.Connectivity.supportGcd N A B = 1 ∧
      M5.completeSignature (M5.SupportPolynomial.ofSupport A)
        (M5.SupportPolynomial.ofSupport B) N ∈ E
  <;> simp [h]

theorem M7.PrefixSector.positive_iff : ∀ (N w : ℕ) (E : Finset M5.BinaryPolynomial) (A B WA WB : Finset ℕ), 0 < N → M7.PrefixSector.ValidSector N E → M5.ConditionalCount.PrefixOK N w A B WA WB → (0 < M7.PrefixSector.count N w E A B WA WB ↔ (M7.PrefixSector.completions N w E A B WA WB).Nonempty) := by
  intro N w E A B WA WB hN hE hPrefix
  rw [M7.PrefixSector.exact_sector_count N w E A B WA WB hN hE hPrefix]
  exact_mod_cast (Finset.card_pos : 0 < (M7.PrefixSector.completions N w E A B WA WB).card ↔ (M7.PrefixSector.completions N w E A B WA WB).Nonempty)
#print axioms M7.PrefixSector.completion_membership
#print axioms M7.PrefixSector.count_nonnegative
#print axioms M7.PrefixSector.disjoint_sector_sum
#print axioms M7.PrefixSector.disjoint_signatures
#print axioms M7.PrefixSector.empty_sector
#print axioms M7.PrefixSector.exact_sector_count
#print axioms M7.PrefixSector.leaf_zero_one
#print axioms M7.PrefixSector.overfull_zero
#print axioms M7.PrefixSector.positive_iff
