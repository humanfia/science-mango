import M6Normalize


def QuantumHarnessFrozenTarget : Prop :=
  ∀ (k : ℤ) (p : Polynomial ℤ) (d : ℕ), k ∣ (Polynomial.C k * p).coeff d
