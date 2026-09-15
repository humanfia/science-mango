import FrozenTarget_1e89fdacebe10775
theorem M5.OrderCount.arithmetic_indicator_expansion : QuantumHarnessFrozenTarget := by
  change ∀ (N w : ℕ) (F : M5.BinaryPolynomial), 0 < N → 0 < w → F.Monic → F ∣ M5.cyclicModulus N → _
  intro N w F hN hw hF hFN
  classical
  have hprod : ∀ S : Finset M5.BinaryPolynomial, (∀ p ∈ S, p.Monic) → (∏ p ∈ S, p).Monic := by
    intro S
    induction S using Finset.induction_on with
    | empty =>
        intro h
        simpa using (Polynomial.monic_one : (1 : M5.BinaryPolynomial).Monic)
    | @insert p S hp ih =>
        intro h
        rw [Finset.prod_insert hp]
        exact (h p (Finset.mem_insert_self p S)).mul
          (ih (fun q hq => h q (Finset.mem_insert_of_mem hq)))
  have hexpand (d : ℕ) :
      (∑ S ∈ (M5.PolynomialExclusion.residualFactors (M5.cyclicModulus N) F).powerset,
        (-1 : ℤ) ^ S.card * M5.OrderCount.nOne (F * ∏ p ∈ S, p)
          (M5.OrderCount.divisorPositions N d) (w - 1) ^ 2) =
      ∑ S ∈ (M5.PolynomialExclusion.residualFactors (M5.cyclicModulus N) F).powerset,
        (-1 : ℤ) ^ S.card * M5.OrderCount.twoBlockIndicatorSum (F * ∏ p ∈ S, p)
          (M5.OrderCount.divisorPositions N d) (w - 1) := by
    apply Finset.sum_congr rfl
    intro S hS
    congr 1
    apply M5.OrderCount.two_block_divisibility_count
    · apply hF.mul
      apply hprod
      intro p hp
      exact (M5.PolynomialIndicator.residual_factors_regular F N hN hF hFN p
        (Finset.mem_powerset.mp hS hp)).1
    · simp [M5.OrderCount.divisorPositions, M5.OrderCount.positivePositions]
  unfold M5.OrderCount.rawC
  simp_rw [hexpand]
  unfold M5.OrderCount.twoBlockIndicatorSum M5.OrderCount.pairIndicator
  unfold M5.PolynomialIndicator.factorExclusionSum
  simp_rw [M5.OrderCount.divisor_subset_domain]
  simp only [Finset.sum_filter, Finset.forall_mem_insert, dvd_zero, true_and]
  simp only [Finset.mul_sum, Finset.sum_mul, Finset.ite_sum_zero,
    ite_mul, mul_ite, mul_zero, zero_mul]
  conv_lhs =>
    rw [Finset.sum_comm]
    arg 2
    ext S
    rw [Finset.sum_comm]
    arg 2
    ext U
    rw [Finset.sum_comm]
  conv_lhs =>
    rw [Finset.sum_comm]
    arg 2
    ext U
    rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro U hU
  apply Finset.sum_congr rfl
  intro V hV
  apply Finset.sum_congr rfl
  intro S hS
  apply Finset.sum_congr rfl
  intro d hd
  simp only [mul_one]
  split_ifs <;> simp_all
