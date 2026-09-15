import M6TransferResources


def QuantumHarnessFrozenTarget : Prop :=
  ∀ R N : ℕ, R < N → M6.Transfer.traceStorageModel R N ≤ 128 * N^2 * 2^R
