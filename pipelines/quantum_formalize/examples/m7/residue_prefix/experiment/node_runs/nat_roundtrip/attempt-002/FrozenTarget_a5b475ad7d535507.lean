import M7ResiduePrefix


def QuantumHarnessFrozenTarget : Prop :=
  ∀ (N : ℕ) [NeZero N], ∀ A : Finset ℕ, A ⊆ Finset.range N → M7.ResiduePrefix.encode (M7.ResiduePrefix.decode N A) = A
