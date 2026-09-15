import M6Physical


def QuantumHarnessFrozenTarget : Prop :=
  ∀ (N : ℕ) [NeZero N] (a h u : M6.Physical.Block N), M6.Physical.dot N (M6.Physical.rev N (M6.Physical.conv N a h)) u = M6.Physical.dot N (M6.Physical.rev N h) (M6.Physical.conv N a u)
