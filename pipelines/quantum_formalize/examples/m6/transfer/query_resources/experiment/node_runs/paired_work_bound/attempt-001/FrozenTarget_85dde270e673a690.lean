import M6QueryResources


def QuantumHarnessFrozenTarget : Prop :=
  ∀ R N : ℕ, R < N → M6.Transfer.pairedQueryWork R N ≤ 40000*N^3*4^R
