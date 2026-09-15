import FrozenTarget_bfc17a9c1c32d9e1
theorem M5.OrderCount.arithmetic_indicator_expansion : QuantumHarnessFrozenTarget := by
  classical
  intro N w F hN hw hF hFd
  have hmonic : ∀ H ∈ (M5.PolynomialExclusion.residualFactors (M5.cyclicModulus N) F).powerset, (F * ∏ p ∈ H, p).Monic := by
    intro H hH
    apply hF.mul
    apply Polynomial.monic_prod_of_monic
    intro p hp
    exact (M5.PolynomialIndicator.residual_factors_regular F N hN hF hFd p ((Finset.mem_powerset.mp hH) hp)).1
  have hzero : ∀ d, 0 ∉ M5.OrderCount.divisorPositions N d := by
    intro d
    simp [M5.OrderCount.divisorPositions, M5.OrderCount.positivePositions]
  have hcount : ∀ H ∈ (M5.PolynomialExclusion.residualFactors (M5.cyclicModulus N) F).powerset, ∀ d, M5.OrderCount.nOne (F * ∏ p ∈ H, p) (M5.OrderCount.divisorPositions N d) (w - 1) ^ 2 = M5.OrderCount.twoBlockIndicatorSum (F * ∏ p ∈ H, p) (M5.OrderCount.divisorPositions N d) (w - 1) := by
    intro H hH d
    exact M5.OrderCount.two_block_divisibility_count _ _ _ (hmonic H hH) (hzero d)
  unfold M5.OrderCount.rawC
  simp (disch := assumption) only [hcount]
  unfold M5.OrderCount.twoBlockIndicatorSum M5.OrderCount.pairIndicator M5.PolynomialIndicator.factorExclusionSum
  simp only [M5.OrderCount.divisor_subset_domain, Finset.sum_filter, Finset.forall_mem_insert, dvd_zero, true_and]
  simp only [Finset.mul_sum, Finset.sum_mul, ite_mul, mul_ite, zero_mul, mul_zero]
