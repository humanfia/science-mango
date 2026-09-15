import M6Physical


def QuantumHarnessFrozenTarget : Prop :=
  ∀ (N : ℕ) [NeZero N] (a : M6.Physical.Block N), M6.Physical.weight N (M6.Physical.rev N a) = M6.Physical.weight N a
