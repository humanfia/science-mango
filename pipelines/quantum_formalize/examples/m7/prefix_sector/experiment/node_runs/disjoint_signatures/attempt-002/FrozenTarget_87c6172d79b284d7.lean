import M7PrefixSector


def QuantumHarnessFrozenTarget : Prop :=
  ∀ (N w : ℕ) (F G : M5.BinaryPolynomial) (A B WA WB : Finset ℕ), F ≠ G → Disjoint (M5.ConditionalCount.validCompletions N w F A B WA WB) (M5.ConditionalCount.validCompletions N w G A B WA WB)
