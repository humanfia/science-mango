import M6Physical


def QuantumHarnessFrozenTarget : Prop :=
  ∀ (N : ℕ) [NeZero N] (a b : M6.Physical.Block N), M6.Physical.conv N a b = M6.Physical.conv N b a
