import M7Action


def QuantumHarnessFrozenTarget : Prop :=
  ∀ (N : ℕ) [NeZero N], ∀ g : M7.Action.Record N, M7.Action.compose (M7.Action.identity N) g = g
