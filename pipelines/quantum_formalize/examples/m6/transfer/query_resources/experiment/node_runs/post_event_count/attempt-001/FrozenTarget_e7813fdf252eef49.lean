import M6QueryResources


def QuantumHarnessFrozenTarget : Prop :=
  ∀ N : ℕ, Fintype.card (M6.Transfer.PostEvent N) = 4*(2*N+1)
