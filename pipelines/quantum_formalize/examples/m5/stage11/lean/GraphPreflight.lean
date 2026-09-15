import M5Binomial
#check (∀ m j : ℕ, (((1 : Polynomial ℤ) - Polynomial.X) ^ m).coeff j = (-1 : ℤ) ^ j * (m.choose j : ℤ))
#check (∀ (S : Finset ℕ) (f : ℕ → ℤ), (∀ s ∈ S, f s = 1 ∨ f s = -1) → M5.Binomial.signedProduct S f = (1 - Polynomial.X) ^ M5.Binomial.negativeCount S f * (1 + Polynomial.X) ^ (S.card - M5.Binomial.negativeCount S f))
#check (∀ m n k : ℕ, (((1 - Polynomial.X : Polynomial ℤ) ^ m) * (1 + Polynomial.X) ^ n).coeff k = ∑ j ∈ Finset.range (k + 1), (-1 : ℤ) ^ j * (m.choose j : ℤ) * (n.choose (k-j) : ℤ))
#check (∀ (S : Finset ℕ) (f : ℕ → ℤ) (k : ℕ), (∀ s ∈ S, f s = 1 ∨ f s = -1) → (M5.Binomial.signedProduct S f).coeff k = ∑ j ∈ Finset.range (k + 1), (-1 : ℤ) ^ j * ((M5.Binomial.negativeCount S f).choose j : ℤ) * ((S.card - M5.Binomial.negativeCount S f).choose (k-j) : ℤ))
