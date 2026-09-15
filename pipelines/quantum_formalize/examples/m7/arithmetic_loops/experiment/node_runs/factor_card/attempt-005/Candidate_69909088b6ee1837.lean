import FrozenTarget_69909088b6ee1837
theorem M7.ArithmeticLoops.factor_card : QuantumHarnessFrozenTarget := by
  classical
  intro N hN F hF hdiv
  have hq : M5.cyclicModulus N / F ≠ 0 :=
    M5.PolynomialExclusion.cyclic_quotient_nonzero F N hN hF hdiv
  have hM : M5.cyclicModulus N ≠ 0 := by
    intro h
    apply hq
    simp [h]
  have hprod : F * (M5.cyclicModulus N / F) ∣ M5.cyclicModulus N :=
    (M5.PolynomialExclusion.factor_dvd_quotient F (M5.cyclicModulus N)
      (M5.cyclicModulus N / F) hF.ne_zero hdiv).mp (dvd_refl _)
  have hd : M5.cyclicModulus N / F ∣ M5.cyclicModulus N :=
    dvd_trans ⟨F, mul_comm _ _⟩ hprod
  have hle :=
    (UniqueFactorizationMonoid.dvd_iff_normalizedFactors_le_normalizedFactors hq hM).mp hd
  change (UniqueFactorizationMonoid.normalizedFactors (M5.cyclicModulus N / F)).toFinset.card ≤
    (UniqueFactorizationMonoid.normalizedFactors (M5.cyclicModulus N)).toFinset.card
  apply Finset.card_le_card
  intro p hp
  simp only [Multiset.mem_toFinset] at hp ⊢
  exact Multiset.mem_of_le hle hp
