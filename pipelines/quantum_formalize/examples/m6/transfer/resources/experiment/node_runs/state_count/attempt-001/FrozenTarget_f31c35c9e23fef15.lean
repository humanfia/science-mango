import M6TransferResources


def QuantumHarnessFrozenTarget : Prop :=
  ∀ R : ℕ, Fintype.card (M6.Transfer.Memory R) = 2^R
