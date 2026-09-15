import M5Binomial


def QuantumHarnessFrozenTarget : Prop :=
  ∀ (S : Finset ℕ) (f : ℕ → ℤ), (∀ s ∈ S, f s = 1 ∨ f s = -1) → M5.Binomial.signedProduct S f = (1 - Polynomial.X) ^ M5.Binomial.negativeCount S f * (1 + Polynomial.X) ^ (S.card - M5.Binomial.negativeCount S f)
