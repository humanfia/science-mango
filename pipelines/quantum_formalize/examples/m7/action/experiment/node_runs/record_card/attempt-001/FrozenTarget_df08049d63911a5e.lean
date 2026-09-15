import M7Action


def QuantumHarnessFrozenTarget : Prop :=
  ∀ (N : ℕ) [NeZero N], Fintype.card (M7.Action.Record N) = Nat.totient N * 2 * N * N
