import M7CompactStorage


def QuantumHarnessFrozenTarget : Prop :=
  ∀ (N : ℕ) (F G : M5.BinaryPolynomial), F.natDegree ≤ N → G.natDegree ≤ N → M7.CompactStorage.polynomialBits N F = M7.CompactStorage.polynomialBits N G → F = G
