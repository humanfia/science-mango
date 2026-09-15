import M6Physical


def QuantumHarnessFrozenTarget : Prop :=
  ∀ (N : ℕ) [NeZero N] (a u v : M6.Physical.Block N), M6.Physical.conv N a (u+v) = M6.Physical.conv N a u + M6.Physical.conv N a v
