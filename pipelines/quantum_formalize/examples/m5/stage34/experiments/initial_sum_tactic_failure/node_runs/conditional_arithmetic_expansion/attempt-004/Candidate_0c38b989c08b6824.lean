import FrozenTarget_0c38b989c08b6824
theorem M5.ConditionalCount.conditional_arithmetic_expansion : QuantumHarnessFrozenTarget := by
  classical
  intro N w F A B WA WB hN hF hFd hOK
  have hA : Disjoint A WA := by
    unfold M5.ConditionalCount.PrefixOK at hOK
    tauto
  have hB : Disjoint B WB := by
    unfold M5.ConditionalCount.PrefixOK at hOK
    tauto
  have hAr (d : ℕ) : Disjoint A (M5.ConditionalCount.restricted WA d) :=
    hA.mono_right (Finset.filter_subset _ _)
  have hBr (d : ℕ) : Disjoint B (M5.ConditionalCount.restricted WB d) :=
    hB.mono_right (Finset.filter_subset _ _)
  have hmonic (S : Finset M5.BinaryPolynomial)
      (hS : S ∈ (M5.PolynomialExclusion.residualFactors (M5.cyclicModulus N) F).powerset) :
      (F * ∏ p ∈ S, p).Monic := by
    apply hF.mul
    apply Polynomial.monic_prod_of_monic
    intro p hp
    exact (M5.PolynomialIndicator.residual_factors_regular F N hN hF hFd p
      (Finset.mem_powerset.mp hS hp)).1
  change M5.ConditionalCount.rawCompletion N w F A B WA WB = _
  calc
    _ = ∑ d ∈ (M5.Connectivity.supportGcd N A B).divisors,
        ∑ S ∈ (M5.PolynomialExclusion.residualFactors (M5.cyclicModulus N) F).powerset,
        ∑ U ∈ WA.powersetCard (w - A.card),
        ∑ V ∈ WB.powersetCard (w - B.card),
          (if (∀ s ∈ U, d ∣ s) ∧ (∀ s ∈ V, d ∣ s)
            then ArithmeticFunction.moebius d else 0) *
          (if (F * ∏ p ∈ S, p) ∣ M5.SupportPolynomial.ofSupport (A ∪ U) ∧
              (F * ∏ p ∈ S, p) ∣ M5.SupportPolynomial.ofSupport (B ∪ V)
            then (-1 : ℤ) ^ S.card else 0) := by
      unfold M5.ConditionalCount.rawCompletion
      apply Finset.sum_congr rfl
      intro d hd
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro S hS
      rw [mul_assoc ((-1 : ℤ) ^ S.card),
        M5.ConditionalCount.two_block_completion_count
          (F * ∏ p ∈ S, p) A B
          (M5.ConditionalCount.restricted WA d)
          (M5.ConditionalCount.restricted WB d)
          (w - A.card) (w - B.card) (hmonic S hS) (hAr d) (hBr d)]
      unfold M5.ConditionalCount.twoBlockIndicatorSum
      rw [M5.ConditionalCount.restricted_subset_domain,
        M5.ConditionalCount.restricted_subset_domain]
      simp only [Finset.sum_filter, Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro U hU
      by_cases hu : ∀ s ∈ U, d ∣ s
      · simp only [hu, if_true, true_and, Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro V hV
        by_cases hv : ∀ s ∈ V, d ∣ s <;>
          by_cases hp : (F * ∏ p ∈ S, p) ∣ M5.SupportPolynomial.ofSupport (A ∪ U) ∧
            (F * ∏ p ∈ S, p) ∣ M5.SupportPolynomial.ofSupport (B ∪ V) <;>
          simp [hv, hp, mul_assoc]
      · simp [hu]
    _ = _ := by
      simp only [M5.ConditionalCount.pairIndicator,
        M5.ConditionalCount.selectedDivisorSum,
        M5.PolynomialIndicator.factorExclusionSum,
        Finset.sum_mul, Finset.mul_sum]
      simp_rw [Finset.sum_comm
        (s := (M5.PolynomialExclusion.residualFactors (M5.cyclicModulus N) F).powerset)
        (t := WA.powersetCard (w - A.card))]
      rw [Finset.sum_comm]
      simp_rw [Finset.sum_comm
        (s := (M5.PolynomialExclusion.residualFactors (M5.cyclicModulus N) F).powerset)
        (t := WB.powersetCard (w - B.card))]
      simp_rw [Finset.sum_comm
        (s := (M5.Connectivity.supportGcd N A B).divisors)
        (t := WB.powersetCard (w - B.card))]
      apply Finset.sum_congr rfl
      intro U hU
      apply Finset.sum_congr rfl
      intro V hV
      apply Finset.sum_congr rfl
      intro d hd
      apply Finset.sum_congr rfl
      intro S hS
      split_ifs <;> simp_all <;> ring
