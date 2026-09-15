import M7SignatureIdeal


def QuantumHarnessFrozenTarget : Prop :=
  ∀ (N : ℕ) [NeZero N], ∀ F p : M6.Cyclic.BinaryPolynomial, F ∣ M6.Cyclic.modulus N → (M6.Cyclic.image N p ∈ M7.SignatureIdeal.principal N F ↔ F ∣ p)
