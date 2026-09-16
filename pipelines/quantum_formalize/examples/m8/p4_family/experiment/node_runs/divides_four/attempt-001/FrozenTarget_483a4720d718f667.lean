import M8P4Family


def QuantumHarnessFrozenTarget : Prop :=
  ∀ N : ℕ, 4 ∣ N → M8.P4Family.polynomial ∣ M6.Cyclic.modulus N
