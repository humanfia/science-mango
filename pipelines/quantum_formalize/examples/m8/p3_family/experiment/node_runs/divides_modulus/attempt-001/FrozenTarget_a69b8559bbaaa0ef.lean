import M8P3Family


def QuantumHarnessFrozenTarget : Prop :=
  ∀ N : ℕ, 3 ∣ N → M8.P3Family.polynomial ∣ M6.Cyclic.modulus N
