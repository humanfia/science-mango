import FrozenTarget_6794dde71cc55ac3
theorem M7.ArithmeticLoops.factor_card : QuantumHarnessFrozenTarget := by
  classical
  intro N hN F hF hdiv
  change (UniqueFactorizationMonoid.normalizedFactors (M5.cyclicModulus N / F)).toFinset.card ≤ (UniqueFactorizationMonoid.normalizedFactors (M5.cyclicModulus N)).toFinset.card
  have hQ := M5.PolynomialExclusion.cyclic_quotient_nonzero F N hN hF hdiv
  have hM : M5.cyclicModulus N ≠ 0 := by
    intro h
    apply hQ
    simp [h]
  have hQD : M5.cyclicModulus N / F ∣ M5.cyclicModulus N := by
    refine ⟨F, ?_⟩
    exact (EuclideanDomain.div_mul_cancel hdiv).symm
  apply Finset.card_le_card
  apply Multiset.toFinset_mono
  first
  | exact UniqueFactorizationMonoid.normalizedFactors_mono hM hQD
  | exact UniqueFactorizationMonoid.normalizedFactors_le_of_dvd hM hQD
  | exact (UniqueFactorizationMonoid.normalizedFactors_le_iff_dvd hQ hM).2 hQD
  | exact (UniqueFactorizationMonoid.normalizedFactors_le_iff_dvd hM).2 hQD
  | exact?
