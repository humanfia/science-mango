import FrozenTarget_50735ae450afb6bf
theorem M5.OrderCount.arithmetic_indicator_expansion : QuantumHarnessFrozenTarget := by
  change ∀ (N w : ℕ) (F : M5.BinaryPolynomial), 0 < N → 0 < w → F.Monic → F ∣ M5.cyclicModulus N → _
  intro N w F hN hw hF hFN
  classical
  have hcount (d : ℕ) (H : Finset M5.BinaryPolynomial)
      (hH : H ∈ (M5.PolynomialExclusion.residualFactors (M5.cyclicModulus N) F).powerset) :
      M5.OrderCount.nOne (F * ∏ p ∈ H, p) (M5.OrderCount.divisorPositions N d) (w - 1) ^ 2 =
        M5.OrderCount.twoBlockIndicatorSum (F * ∏ p ∈ H, p)
          (M5.OrderCount.divisorPositions N d) (w - 1) := by
    apply M5.OrderCount.two_block_divisibility_count
    · apply hF.mul
      apply Polynomial.monic_prod_of_monic
      intro p hp
      exact (M5.PolynomialIndicator.residual_factors_regular F N hN hF hFN p
        ((Finset.mem_powerset.mp hH) hp)).1
    · simp [M5.OrderCount.divisorPositions, M5.OrderCount.positivePositions]
  have hsum (p : Prop) (s : Finset (Finset ℕ)) (f : Finset ℕ → ℤ) :
      (if p then ∑ x ∈ s, f x else 0) = ∑ x ∈ s, if p then f x else 0 := by
    by_cases hp : p <;> simp [hp]
  simp only [M5.OrderCount.rawC, hcount]
  unfold M5.OrderCount.twoBlockIndicatorSum M5.OrderCount.pairIndicator
    M5.PolynomialIndicator.factorExclusionSum
  simp only [M5.OrderCount.divisor_subset_domain, Finset.sum_filter,
    Finset.forall_mem_insert, dvd_zero, true_and]
  simp only [Finset.mul_sum, Finset.sum_mul, mul_ite, ite_mul,
    mul_zero, zero_mul, hsum]
  simp [Finset.sum_comm, mul_assoc, mul_left_comm, mul_comm,
    ite_and, and_assoc, and_left_comm, and_comm]
