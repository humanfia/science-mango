import M7Action


def QuantumHarnessFrozenTarget : Prop :=
  ∀ (N : ℕ) [NeZero N], ∀ g h k : M7.Action.Record N, M7.Action.compose (M7.Action.compose g h) k = M7.Action.compose g (M7.Action.compose h k)
