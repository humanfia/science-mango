import M8DiagonalPolynomial


def QuantumHarnessFrozenTarget : Prop :=
  ∀ (N : ℕ) [NeZero N], ∀ (p F q : M8.DiagonalPolynomial.BP), F.Monic → F ∣ p → F ∣ M6.Cyclic.modulus N → M6.Cyclic.image N p * M6.Cyclic.image N q = 1 → F = 1
