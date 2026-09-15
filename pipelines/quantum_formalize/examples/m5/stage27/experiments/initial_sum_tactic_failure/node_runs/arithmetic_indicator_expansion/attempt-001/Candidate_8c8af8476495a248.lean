import FrozenTarget_8c8af8476495a248
theorem M5.OrderCount.arithmetic_indicator_expansion : QuantumHarnessFrozenTarget := by
  change ∀ (N w : ℕ) (F : M5.BinaryPolynomial), 0 < N → 0 < w → F.Monic → F ∣ M5.cyclicModulus N → _
  intro N w F hN hw hF hFN
  classical
  have hprod : ∀ S : Finset M5.BinaryPolynomial,
      S ⊆ M5.PolynomialExclusion.residualFactors (M5.cyclicModulus N) F →
      (∏ p ∈ S, p).Monic := by
    intro S
    induction S using Finset.induction_on with
    | empty => simp
    | @insert p S hp ih =>
        intro hS
        rw [Finset.prod_insert hp]
        apply Polynomial.Monic.mul
        · exact (M5.PolynomialIndicator.residual_factors_regular F N hN hF hFN p
            (hS (Finset.mem_insert_self p S))).1
        · exact ih (fun q hq => hS (Finset.mem_insert_of_mem hq))
  have hcount : ∀ S ∈ (M5.PolynomialExclusion.residualFactors
      (M5.cyclicModulus N) F).powerset, ∀ d : ℕ,
      M5.OrderCount.nOne (F * ∏ p ∈ S, p)
        (M5.OrderCount.divisorPositions N d) (w - 1) ^ 2 =
      M5.OrderCount.twoBlockIndicatorSum (F * ∏ p ∈ S, p)
        (M5.OrderCount.divisorPositions N d) (w - 1) := by
    intro S hS d
    apply M5.OrderCount.two_block_divisibility_count
    · exact hF.mul (hprod S (Finset.mem_powerset.mp hS))
    · simp [M5.OrderCount.divisorPositions, M5.OrderCount.positivePositions]
  unfold M5.OrderCount.rawC
  simp only [hcount]
  unfold M5.OrderCount.twoBlockIndicatorSum M5.OrderCount.pairIndicator
    M5.PolynomialIndicator.factorExclusionSum
  simp only [M5.OrderCount.divisor_subset_domain]
  simp [Finset.sum_filter, Finset.mul_sum, Finset.sum_mul,
    Finset.sum_ite_irrel, Finset.sum_comm, ite_mul, mul_ite,
    mul_assoc, mul_comm, mul_left_comm, and_assoc, and_comm, and_left_comm]
