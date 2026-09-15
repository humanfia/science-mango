import FrozenTarget_a2249828ffe9b1cc
theorem M5.FactorProduct.irreducible_product_dvd : QuantumHarnessFrozenTarget := by
  classical
  change ∀ (S : Finset M5.BinaryPolynomial) (A : M5.BinaryPolynomial), (∀ p ∈ S, p.Monic ∧ Irreducible p) → ((∏ p ∈ S, p) ∣ A ↔ ∀ p ∈ S, p ∣ A)
  intro S A hS
  constructor
  · intro h p hp
    exact (Finset.dvd_prod_of_mem (fun q : M5.BinaryPolynomial => q) hp).trans h
  · intro h
    refine Finset.prod_dvd_of_coprime ?_ h
    intro p hp q hq hpq
    exact M5.FactorProduct.distinct_irreducibles_coprime p q
      (hS p hp).1 (hS q hq).1 (hS p hp).2 (hS q hq).2 hpq
