import M6FixedSpan


def QuantumHarnessFrozenTarget : Prop :=
  ∀ N : ℕ, 3 ∣ N → M6.FixedSpan.recipe ∣ M6.Cyclic.modulus N
