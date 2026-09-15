import M6TransferActualResources


def QuantumHarnessFrozenTarget : Prop :=
  ∀ R N : ℕ, 2^R * 8^N < 2^(M6.Transfer.coefficientBits R N - 1)
