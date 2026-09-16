import M8SequentialStore


def QuantumHarnessFrozenTarget : Prop :=
  ∀ (N : ℕ) [NeZero N], ∀ mem : List Bool, mem.length = M8.SequentialStore.slots N → M8.SequentialStore.storeSpace N mem ≤ 2000000*(N+1)^4
