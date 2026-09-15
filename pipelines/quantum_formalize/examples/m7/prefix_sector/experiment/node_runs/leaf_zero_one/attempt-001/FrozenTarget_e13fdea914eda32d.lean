import M7PrefixSector

theorem M7.PrefixSector.disjoint_signatures : ∀ (N w : ℕ) (F G : M5.BinaryPolynomial) (A B WA WB : Finset ℕ), F ≠ G → Disjoint (M5.ConditionalCount.validCompletions N w F A B WA WB) (M5.ConditionalCount.validCompletions N w G A B WA WB) := by
  classical
  intro N w F G A B WA WB hFG
  apply Finset.disjoint_left.mpr
  intro p hpF hpG
  simp only [M5.ConditionalCount.validCompletions, Finset.mem_filter] at hpF hpG
  aesop

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
def QuantumHarnessFrozenTarget : Prop :=
  ∀ (N w : ℕ) (E : Finset M5.BinaryPolynomial) (A B : Finset ℕ), 0 < N → M7.PrefixSector.ValidSector N E → M5.ConditionalCount.PrefixOK N w A B ∅ ∅ → M7.PrefixSector.count N w E A B ∅ ∅ = (if A.card = w ∧ B.card = w ∧ M5.Connectivity.supportGcd N A B = 1 ∧ M5.completeSignature (M5.SupportPolynomial.ofSupport A) (M5.SupportPolynomial.ofSupport B) N ∈ E then (1 : ℤ) else 0)
