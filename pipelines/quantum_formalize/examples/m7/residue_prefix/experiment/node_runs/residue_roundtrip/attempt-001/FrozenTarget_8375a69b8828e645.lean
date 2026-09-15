import M7ResiduePrefix


def QuantumHarnessFrozenTarget : Prop :=
  ∀ (N : ℕ) [NeZero N], ∀ A : Finset (ZMod N), M7.ResiduePrefix.decode N (M7.ResiduePrefix.encode A) = A
