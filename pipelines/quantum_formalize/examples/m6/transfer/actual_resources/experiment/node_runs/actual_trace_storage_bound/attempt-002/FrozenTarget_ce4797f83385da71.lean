import M6TransferActualResources


def QuantumHarnessFrozenTarget : Prop :=
  ∀ R N : ℕ, R < N → M6.Transfer.actualTraceStorage R N ≤ 4096 * N^2 * 2^R
