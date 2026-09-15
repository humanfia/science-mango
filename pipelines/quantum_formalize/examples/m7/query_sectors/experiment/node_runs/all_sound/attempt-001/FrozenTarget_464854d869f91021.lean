import M7QuerySectors


def QuantumHarnessFrozenTarget : Prop :=
  ∀ (N : ℕ) [NeZero N], ∀ (F : M6.Cyclic.BinaryPolynomial), F ∈ M7.QuerySectors.allSectors N → F.Monic ∧ F ∣ M6.Cyclic.modulus N
