import M6Normalize


def QuantumHarnessFrozenTarget : Prop :=
  ∀ (k : ℤ) (p : Polynomial ℤ) (d : ℕ), (M6.Normalize.divide k p).coeff d = p.coeff d / k
