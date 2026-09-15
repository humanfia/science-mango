import FrozenTarget_abe2efa2a57f8d02
theorem M7.ArithmeticLoops.factor_card : QuantumHarnessFrozenTarget := by
  classical
  intro N hN F hF hdiv
  have hq : M5.cyclicModulus N / F ≠ 0 :=
    M5.PolynomialExclusion.cyclic_quotient_nonzero F N hN hF hdiv
  have heq : F * (M5.cyclicModulus N / F) = M5.cyclicModulus N :=
    EuclideanDomain.mul_div_cancel' hF.ne_zero hdiv
  have hM : M5.cyclicModulus N ≠ 0 := by
    rw [← heq]
    exact mul_ne_zero hF.ne_zero hq
  have hd : M5.cyclicModulus N / F ∣ M5.cyclicModulus N := by
    refine ⟨F, ?_⟩
    simpa only [mul_comm] using heq.symm
  change (UniqueFactorizationMonoid.normalizedFactors (M5.cyclicModulus N / F)).toFinset.card ≤
    (UniqueFactorizationMonoid.normalizedFactors (M5.cyclicModulus N)).toFinset.card
  have hle : UniqueFactorizationMonoid.normalizedFactors (M5.cyclicModulus N / F) ≤
      UniqueFactorizationMonoid.normalizedFactors (M5.cyclicModulus N) := by
    first
    | exact (UniqueFactorizationMonoid.normalizedFactors_le_normalizedFactors hq hM).2 hd
    | exact (UniqueFactorizationMonoid.normalizedFactors_le_normalizedFactors hM).2 hd
    | exact UniqueFactorizationMonoid.normalizedFactors_le_normalizedFactors hd hM
    | exact UniqueFactorizationMonoid.normalizedFactors_le_normalizedFactors hM hd
  apply Finset.card_le_card
  intro p hp
  exact Multiset.mem_toFinset.mpr (Multiset.mem_of_le hle (Multiset.mem_toFinset.mp hp))
