import M6TransferResources


def QuantumHarnessFrozenTarget : Prop :=
  ∀ R N : ℕ, 0 < N → M6.Transfer.addressLocations R N ≤ 2^(M6.Transfer.addressBits R N)
