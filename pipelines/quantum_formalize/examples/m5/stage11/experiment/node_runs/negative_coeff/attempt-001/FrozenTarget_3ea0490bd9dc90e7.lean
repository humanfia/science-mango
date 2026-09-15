import M5Binomial


def QuantumHarnessFrozenTarget : Prop :=
  ∀ m j : ℕ, (((1 : Polynomial ℤ) - Polynomial.X) ^ m).coeff j = (-1 : ℤ) ^ j * (m.choose j : ℤ)
