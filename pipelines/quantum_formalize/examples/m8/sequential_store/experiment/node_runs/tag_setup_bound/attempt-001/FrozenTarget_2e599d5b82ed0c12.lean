import M8SequentialStore


def QuantumHarnessFrozenTarget : Prop :=
  ∀ (N : ℕ) [NeZero N], M8.SequentialStore.tagSetupCharge N ≤ 11000000*(N+1)^6
