import M6ZeroSpan


def QuantumHarnessFrozenTarget : Prop :=
  ∀ N : ℕ, M6.Cyclic.signature 1 1 (M6.Cyclic.modulus N) = 1
