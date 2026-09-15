import FrozenTarget_458d6608557728a6
theorem M7.ArithmeticLoops.factor_card : QuantumHarnessFrozenTarget := by
  classical
  intro N hN F hF hdiv
  have hq : M5.cyclicModulus N / F ≠ 0 :=
    M5.PolynomialExclusion.cyclic_quotient_nonzero F N hN hF hdiv
  have hM : M5.cyclicModulus N ≠ 0 := by
    intro hz
    apply hq
    simp [hz]
  have heq : F * (M5.cyclicModulus N / F) = M5.cyclicModulus N := by
    first
    | exact EuclideanDomain.mul_div_cancel' hdiv
    | exact (EuclideanDomain.div_mul_cancel hdiv).symm.trans (mul_comm _ _)
    | simpa [mul_comm] using (EuclideanDomain.div_mul_cancel hdiv)
  have hqdvd : M5.cyclicModulus N / F ∣ M5.cyclicModulus N := by
    exact ⟨F, by simpa [mul_comm] using heq.symm⟩
  have hle :=
    (UniqueFactorizationMonoid.dvd_iff_normalizedFactors_le_normalizedFactors hq hM).mp hqdvd
  change (UniqueFactorizationMonoid.normalizedFactors (M5.cyclicModulus N / F)).toFinset.card ≤
    (UniqueFactorizationMonoid.normalizedFactors (M5.cyclicModulus N)).toFinset.card
  apply Finset.card_le_card
  intro p hp
  apply Multiset.mem_toFinset.mpr
  exact Multiset.mem_of_le hle (Multiset.mem_toFinset.mp hp)
