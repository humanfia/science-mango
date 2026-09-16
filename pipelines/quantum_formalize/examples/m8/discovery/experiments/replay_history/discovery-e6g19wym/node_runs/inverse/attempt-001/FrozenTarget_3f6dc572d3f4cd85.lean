import M8Discovery


def QuantumHarnessFrozenTarget : Prop :=
  ∀ (N : ℕ) [NeZero N] (c : M7.Action.Recipe N), ∀ k : M8.Discovery.Choice N, M7.Action.act (M7.Action.inverse (M8.Discovery.action k)) (M8.Discovery.transformed c k) = c
