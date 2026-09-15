import M7ActualFactorizedReady


def QuantumHarnessFrozenTarget : Prop :=
  ∀ (N : ℕ) [NeZero N], ∀ c : M7.Action.Recipe N, ∀ g : M7.Action.Record N, M7.Action.act g c = M7.Action.act (M7.Action.translate g.leftShift g.rightShift) (M7.ActualFactorized.outerImage c (g.unit,g.exchange))
