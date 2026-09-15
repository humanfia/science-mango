import M7PrefixSector

theorem M7.PrefixSector.disjoint_signatures : ∀ (N w : ℕ) (F G : M5.BinaryPolynomial) (A B WA WB : Finset ℕ), F ≠ G → Disjoint (M5.ConditionalCount.validCompletions N w F A B WA WB) (M5.ConditionalCount.validCompletions N w G A B WA WB) := by
  classical
  intro N w F G A B WA WB hFG
  apply Finset.disjoint_left.mpr
  intro p hpF hpG
  simp only [M5.ConditionalCount.validCompletions, Finset.mem_filter] at hpF hpG
  aesop
def QuantumHarnessFrozenTarget : Prop :=
  ∀ (N w : ℕ) (E : Finset M5.BinaryPolynomial) (A B WA WB : Finset ℕ), 0 < N → M7.PrefixSector.ValidSector N E → M5.ConditionalCount.PrefixOK N w A B WA WB → M7.PrefixSector.count N w E A B WA WB = (M7.PrefixSector.completions N w E A B WA WB).card
