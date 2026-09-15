import M5FactorProduct
#check (∀ p q : M5.BinaryPolynomial, p.Monic → q.Monic → Irreducible p → Irreducible q → p ≠ q → IsCoprime p q)
#check (∀ (S : Finset M5.BinaryPolynomial) (A : M5.BinaryPolynomial), (∀ p ∈ S, p.Monic ∧ Irreducible p) → ((∏ p ∈ S, p) ∣ A ↔ ∀ p ∈ S, p ∣ A))
#check (∀ F H A : M5.BinaryPolynomial, F ≠ 0 → F ∣ A → (F * H ∣ A ↔ H ∣ A / F))
#check (∀ (S : Finset M5.BinaryPolynomial) (F A : M5.BinaryPolynomial), F ≠ 0 → F ∣ A → (∀ p ∈ S, p.Monic ∧ Irreducible p) → (F * (∏ p ∈ S, p) ∣ A ↔ ∀ p ∈ S, F * p ∣ A))
#check (∀ (S : Finset M5.BinaryPolynomial) (F : M5.BinaryPolynomial) (N : ℕ), 0 < N → F.Monic → F ∣ M5.cyclicModulus N → S ⊆ M5.FactorProduct.residualFactors (M5.cyclicModulus N) F → F * (∏ p ∈ S, p) ∣ M5.cyclicModulus N)
