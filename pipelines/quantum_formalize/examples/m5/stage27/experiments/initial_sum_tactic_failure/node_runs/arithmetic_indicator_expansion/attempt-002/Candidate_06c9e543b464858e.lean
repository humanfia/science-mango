import FrozenTarget_06c9e543b464858e
theorem M5.OrderCount.arithmetic_indicator_expansion : QuantumHarnessFrozenTarget := by
  classical
  change ∀ (N w : ℕ) (F : M5.BinaryPolynomial), 0 < N → 0 < w → F.Monic → F ∣ M5.cyclicModulus N → _
  intro N w F hN hw hF hFN
  have hcount (d : ℕ) (H : Finset M5.BinaryPolynomial)
      (hH : H ∈ (M5.PolynomialExclusion.residualFactors (M5.cyclicModulus N) F).powerset) :
      M5.OrderCount.nOne (F * ∏ p ∈ H, p)
          (M5.OrderCount.divisorPositions N d) (w - 1) ^ 2 =
        M5.OrderCount.twoBlockIndicatorSum (F * ∏ p ∈ H, p)
          (M5.OrderCount.divisorPositions N d) (w - 1) := by
    apply M5.OrderCount.two_block_divisibility_count
    · apply hF.mul
      apply Polynomial.monic_prod_of_monic
      intro p hp
      exact (M5.PolynomialIndicator.residual_factors_regular F N hN hF hFN p
        (Finset.mem_powerset.mp hH hp)).1
    · simp [M5.OrderCount.divisorPositions, M5.OrderCount.positivePositions]
  have hite {α : Type*} (s : Finset α) (p : Prop) [Decidable p] (f : α → ℤ) :
      (if p then ∑ x ∈ s, f x else 0) = ∑ x ∈ s, if p then f x else 0 := by
    by_cases hp : p <;> simp [hp]
  simp only [M5.OrderCount.rawC, hcount]
  simp only [M5.OrderCount.twoBlockIndicatorSum,
    M5.OrderCount.divisor_subset_domain, Finset.sum_filter]
  simp only [M5.OrderCount.pairIndicator,
    M5.PolynomialIndicator.factorExclusionSum]
  simp only [Finset.forall_mem_insert, dvd_zero, true_and,
    Finset.mul_sum, Finset.sum_mul, ite_mul, mul_ite,
    zero_mul, mul_zero, one_mul, mul_one, hite, ite_and]
  simp only [Finset.sum_comm, mul_assoc, mul_left_comm, mul_comm]
