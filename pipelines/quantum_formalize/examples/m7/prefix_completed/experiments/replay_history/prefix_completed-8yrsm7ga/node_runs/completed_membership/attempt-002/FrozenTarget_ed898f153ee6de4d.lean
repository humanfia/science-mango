import M7PrefixCompleted


def QuantumHarnessFrozenTarget : Prop :=
  ∀ (N w : ℕ) (E : Finset M5.BinaryPolynomial) (A B WA WB : Finset ℕ), Disjoint A WA → Disjoint B WB → ∀ x, x ∈ M7.PrefixCompleted.completed N w E A B WA WB ↔ M7.PrefixCompleted.Within A B WA WB x ∧ M7.PrefixCompleted.Valid N w E x
