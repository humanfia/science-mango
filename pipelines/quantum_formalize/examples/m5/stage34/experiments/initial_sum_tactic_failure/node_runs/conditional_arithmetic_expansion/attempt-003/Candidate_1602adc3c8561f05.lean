import FrozenTarget_1602adc3c8561f05
theorem M5.ConditionalCount.conditional_arithmetic_expansion : QuantumHarnessFrozenTarget := by
  classical
  intro N w F A B WA WB hN hF hFN hprefix
  have hA : Disjoint A WA := by
    unfold M5.ConditionalCount.PrefixOK at hprefix
    tauto
  have hB : Disjoint B WB := by
    unfold M5.ConditionalCount.PrefixOK at hprefix
    tauto
  have hAr (d : ℕ) : Disjoint A (M5.ConditionalCount.restricted WA d) := by
    exact hA.mono_right (Finset.filter_subset _ _)
  have hBr (d : ℕ) : Disjoint B (M5.ConditionalCount.restricted WB d) := by
    exact hB.mono_right (Finset.filter_subset _ _)
  have hprod (H : Finset M5.BinaryPolynomial)
      (hH : ∀ p ∈ H, p.Monic) : (∏ p ∈ H, p).Monic := by
    induction H using Finset.induction_on with
    | empty => simp
    | @insert p H hp ih =>
        rw [Finset.prod_insert hp]
        exact (hH p (Finset.mem_insert_self p H)).mul
          (ih (fun q hq => hH q (Finset.mem_insert_of_mem hq)))
  have hblock (d : ℕ) (H : Finset M5.BinaryPolynomial)
      (hH : H ∈ (M5.PolynomialExclusion.residualFactors (M5.cyclicModulus N) F).powerset) :
      M5.ConditionalCount.nSelected (F * ∏ p ∈ H, p) A
          (M5.ConditionalCount.restricted WA d) (w - A.card) *
        M5.ConditionalCount.nSelected (F * ∏ p ∈ H, p) B
          (M5.ConditionalCount.restricted WB d) (w - B.card) =
        M5.ConditionalCount.twoBlockIndicatorSum (F * ∏ p ∈ H, p) A B
          (M5.ConditionalCount.restricted WA d)
          (M5.ConditionalCount.restricted WB d) (w - A.card) (w - B.card) := by
    apply M5.ConditionalCount.two_block_completion_count
    · apply hF.mul
      apply hprod
      intro p hp
      exact (M5.PolynomialIndicator.residual_factors_regular F N hN hF hFN p
        ((Finset.mem_powerset.mp hH) hp)).1
    · exact hAr d
    · exact hBr d
  unfold M5.ConditionalCount.rawCompletion M5.ConditionalCount.pairIndicator
    M5.ConditionalCount.selectedDivisorSum M5.PolynomialIndicator.factorExclusionSum
  simp only [mul_assoc]
  simp only [hblock]
  simp only [M5.ConditionalCount.twoBlockIndicatorSum,
    M5.ConditionalCount.restricted_subset_domain, Finset.sum_filter]
  simp only [Finset.mul_sum, Finset.sum_mul]
  simp_rw [Finset.sum_comm (s := WB.powersetCard (w - B.card)) (t := N.divisors)]
  simp_rw [Finset.sum_comm (s := WA.powersetCard (w - A.card)) (t := N.divisors)]
  simp_rw [Finset.sum_comm (s := WB.powersetCard (w - B.card))
    (t := (M5.PolynomialExclusion.residualFactors (M5.cyclicModulus N) F).powerset)]
  simp_rw [Finset.sum_comm (s := WA.powersetCard (w - A.card))
    (t := (M5.PolynomialExclusion.residualFactors (M5.cyclicModulus N) F).powerset)]
  apply Finset.sum_congr rfl
  intro d hd
  by_cases hAB : (∀ a ∈ A, d ∣ a) ∧ (∀ b ∈ B, d ∣ b)
  · simp only [hAB, if_true]
    simp only [Finset.mul_sum, Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro H hH
    simp only [Finset.mul_sum, Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro U hU
    apply Finset.sum_congr rfl
    intro V hV
    simp only [Finset.mem_union, forall_eq_or_imp, hAB.1, hAB.2, true_and]
    split_ifs <;> ring
  · simp [Finset.mem_union, forall_eq_or_imp, hAB, mul_ite, ite_mul,
      and_assoc, and_left_comm, and_comm]
