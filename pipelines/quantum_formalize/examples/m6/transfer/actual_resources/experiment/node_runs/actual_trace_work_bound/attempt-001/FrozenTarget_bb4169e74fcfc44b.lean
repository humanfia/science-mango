import M6TransferActualResources


def QuantumHarnessFrozenTarget : Prop :=
  ∀ R N : ℕ, R < N → M6.Transfer.actualTraceWork R N ≤ 16384 * N^3 * 4^R
