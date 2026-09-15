import M7PrefixSector


def QuantumHarnessFrozenTarget : Prop :=
  ∀ (N w : ℕ) (E : Finset M5.BinaryPolynomial) (A B WA WB : Finset ℕ), ∀ x, x ∈ M7.PrefixSector.completions N w E A B WA WB ↔ ∃ F ∈ E, x ∈ M5.ConditionalCount.validCompletions N w F A B WA WB
