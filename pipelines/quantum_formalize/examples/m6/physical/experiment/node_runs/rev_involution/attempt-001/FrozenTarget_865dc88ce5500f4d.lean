import M6Physical


def QuantumHarnessFrozenTarget : Prop :=
  ∀ (N : ℕ) (a : M6.Physical.Block N), M6.Physical.rev N (M6.Physical.rev N a) = a
