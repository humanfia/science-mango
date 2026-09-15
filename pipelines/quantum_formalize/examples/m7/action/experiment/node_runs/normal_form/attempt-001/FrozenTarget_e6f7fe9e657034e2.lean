import M7Action


def QuantumHarnessFrozenTarget : Prop :=
  ∀ (N : ℕ) [NeZero N], ∀ g : M7.Action.Record N, M7.Action.compose (M7.Action.translate g.leftShift g.rightShift) (M7.Action.compose (M7.Action.multiplier g.unit) (if g.exchange then M7.Action.exchange N else M7.Action.identity N)) = g
