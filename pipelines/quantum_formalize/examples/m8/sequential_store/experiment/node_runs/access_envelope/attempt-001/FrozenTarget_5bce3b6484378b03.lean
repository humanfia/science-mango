import M8SequentialStore


def QuantumHarnessFrozenTarget : Prop :=
  ∀ (N : ℕ) [NeZero N], M8.SequentialStore.accessCharge N ≤ 3000000*(N+1)^6
