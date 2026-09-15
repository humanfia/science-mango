import M6SpacesReady


def QuantumHarnessFrozenTarget : Prop :=
  ∀ (N : ℕ) [NeZero N], Nat.card (M6.Physical.Block N) = 2^N
