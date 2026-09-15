import M7ResiduePrefix


def QuantumHarnessFrozenTarget : Prop :=
  ∀ (N : ℕ) [NeZero N], ∀ (w : ℕ) (E : Finset M5.BinaryPolynomial) (A B WA WB : Finset ℕ), M7.PrefixCompleted.Base N A B WA WB → ∀ x ∈ M7.PrefixCompleted.completed N w E A B WA WB, x.1 ⊆ Finset.range N ∧ x.2 ⊆ Finset.range N
