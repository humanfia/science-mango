import FrozenTarget_ab5288e6513542f0
theorem M7.ArithmeticLoops.factor_card : QuantumHarnessFrozenTarget := by
  classical
  intro N hN F hF hFM
  have hq := M5.PolynomialExclusion.cyclic_quotient_nonzero F N hN hF hFM
  have hM : M5.cyclicModulus N ≠ 0 := by
    intro h
    apply hq
    simp [h]
  have hd : M5.cyclicModulus N / F ∣ M5.cyclicModulus N := by
    have hm := (M5.PolynomialExclusion.factor_dvd_quotient F
      (M5.cyclicModulus N) (M5.cyclicModulus N / F) hF.ne_zero hFM).mp (dvd_refl _)
    exact dvd_trans (dvd_mul_left _ _) hm
  change (UniqueFactorizationMonoid.normalizedFactors (M5.cyclicModulus N / F)).toFinset.card ≤
    (UniqueFactorizationMonoid.normalizedFactors (M5.cyclicModulus N)).toFinset.card
  have hfactors : UniqueFactorizationMonoid.normalizedFactors (M5.cyclicModulus N / F) ≤
      UniqueFactorizationMonoid.normalizedFactors (M5.cyclicModulus N) := by
    first
    | exact UniqueFactorizationMonoid.normalizedFactors_le_of_dvd hM hd
    | exact UniqueFactorizationMonoid.normalizedFactors_le_of_dvd hd hM
    | exact (UniqueFactorizationMonoid.normalizedFactors_le_normalizedFactors hq hM).mpr hd
    | exact (UniqueFactorizationMonoid.normalizedFactors_le_normalizedFactors hM).mpr hd
  apply Finset.card_le_card
  intro p hp
  have hp' : p ∈ UniqueFactorizationMonoid.normalizedFactors (M5.cyclicModulus N / F) := by
    simpa only [Multiset.mem_toFinset] using hp
  have hpM := Multiset.mem_of_le hfactors hp'
  simpa only [Multiset.mem_toFinset] using hpM
