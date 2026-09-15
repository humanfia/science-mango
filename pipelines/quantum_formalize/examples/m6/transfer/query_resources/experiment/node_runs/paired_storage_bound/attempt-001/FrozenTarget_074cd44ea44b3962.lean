import M6QueryResources


def QuantumHarnessFrozenTarget : Prop :=
  ∀ R N : ℕ, R < N → M6.Transfer.pairedQueryStorage R N ≤ 8192*N^2*2^R
