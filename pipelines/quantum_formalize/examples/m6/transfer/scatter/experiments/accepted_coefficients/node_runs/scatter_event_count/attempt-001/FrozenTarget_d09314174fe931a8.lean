import M6TransferScatter


def QuantumHarnessFrozenTarget : Prop :=
  ∀ R N : ℕ, Fintype.card (M6.Transfer.Memory R) * N * (M6.Transfer.scatterEventList R N).length = M6.Transfer.traceCoefficientOps R N
