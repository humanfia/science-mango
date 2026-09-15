import M7Action


def QuantumHarnessFrozenTarget : Prop :=
  ∀ (N : ℕ) [NeZero N], ∀ (g h : M7.Action.Record N) (c : M7.Action.Recipe N), M7.Action.act (M7.Action.compose g h) c = M7.Action.act g (M7.Action.act h c)
