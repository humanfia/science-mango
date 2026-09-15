import M5OrderCount

theorem M5.OrderCount.divisor_subset_domain : ∀ (N d k : ℕ), (M5.OrderCount.divisorPositions N d).powersetCard k = ((M5.OrderCount.positivePositions N).powersetCard k).filter (fun U => ∀ s ∈ U, d ∣ s) := by
  change ∀ (N d k : ℕ), (M5.OrderCount.divisorPositions N d).powersetCard k = ((M5.OrderCount.positivePositions N).powersetCard k).filter (fun U => ∀ s ∈ U, d ∣ s)
  intro N d k
  classical
  ext U
  simp [M5.OrderCount.divisorPositions, Finset.mem_powersetCard, Finset.subset_iff, forall_and, and_assoc, and_left_comm, and_comm]

theorem M5.OrderCount.two_block_divisibility_count : ∀ (P : M5.BinaryPolynomial) (W : Finset ℕ) (k : ℕ), P.Monic → 0 ∉ W → M5.OrderCount.nOne P W k ^ 2 = M5.OrderCount.twoBlockIndicatorSum P W k := by
  classical
  intro P W k hP hW
  simp only [M5.OrderCount.nOne, dif_pos hP]
  rw [M5.AnchoredCount.anchored_single_block_count P hP W k hW]
  unfold M5.AnchoredCount.count M5.OrderCount.twoBlockIndicatorSum
  simp only [pow_two, Finset.card_eq_sum_ones, Nat.cast_sum, Finset.sum_filter]
  simp [Finset.sum_mul, Finset.mul_sum, ite_mul, mul_ite, ite_and]
  rw [← Finset.sum_filter]
  simp [nsmul_eq_mul]

theorem M5.OrderCount.arithmetic_indicator_expansion : ∀ (N w : ℕ) (F : M5.BinaryPolynomial), 0 < N → 0 < w → F.Monic → F ∣ M5.cyclicModulus N → M5.OrderCount.rawC N w F = ∑ U ∈ (M5.OrderCount.positivePositions N).powersetCard (w-1), ∑ V ∈ (M5.OrderCount.positivePositions N).powersetCard (w-1), M5.OrderCount.pairIndicator N F U V := by
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
def QuantumHarnessFrozenTarget : Prop :=
  ∀ (N w : ℕ) (F : M5.BinaryPolynomial), 0 < N → 0 < w → F.Monic → F ∣ M5.cyclicModulus N → M5.OrderCount.C N w F = (M5.OrderCount.validPairs N w F).card
