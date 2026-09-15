import M6Physical


def QuantumHarnessFrozenTarget : Prop :=
  ∀ (N : ℕ) [NeZero N] (a b c : M6.Physical.Block N), M6.Physical.conv N a (M6.Physical.conv N b c) = M6.Physical.conv N (M6.Physical.conv N a b) c
