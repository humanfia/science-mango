import FrozenTarget_31eae788c998edf2
theorem M5.FactorProduct.cyclic_cap : QuantumHarnessFrozenTarget := by
  classical
  change ∀ (S : Finset M5.BinaryPolynomial) (F : M5.BinaryPolynomial) (N : ℕ), 0 < N → F.Monic → F ∣ M5.cyclicModulus N → S ⊆ M5.FactorProduct.residualFactors (M5.cyclicModulus N) F → F * (∏ p ∈ S, p) ∣ M5.cyclicModulus N
  intro S F N hN hF hFdvd hS
  apply (M5.FactorProduct.common_factor_dvd F (∏ p ∈ S, p) (M5.cyclicModulus N) hF.ne_zero hFdvd).mpr
  apply (M5.FactorProduct.irreducible_product_dvd S (M5.cyclicModulus N / F) ?_).mpr
  · intro p hp
    have hp' := hS hp
    simp only [M5.FactorProduct.residualFactors, Multiset.mem_toFinset] at hp'
    have hirr := UniqueFactorizationMonoid.irreducible_of_mem_normalizedFactors hp'
    refine ⟨?_, hirr⟩
    apply M5.Signature.binary_monic
    exact hirr.ne_zero
  · intro p hp
    have hp' := hS hp
    simp only [M5.FactorProduct.residualFactors, Multiset.mem_toFinset] at hp'
    exact UniqueFactorizationMonoid.dvd_of_mem_normalizedFactors hp'
