import FrozenTarget_8d07017d1d9c4e1e
theorem M5.ConditionalCount.conditional_arithmetic_expansion : QuantumHarnessFrozenTarget := by
  classical
  intro N w F A B WA WB hN hF hFN hOK
  have hA : Disjoint A WA := by
    unfold M5.ConditionalCount.PrefixOK at hOK
    tauto
  have hB : Disjoint B WB := by
    unfold M5.ConditionalCount.PrefixOK at hOK
    tauto
  have hcount (H : Finset M5.BinaryPolynomial)
      (hH : H ∈ (M5.PolynomialExclusion.residualFactors (M5.cyclicModulus N) F).powerset)
      (d : ℕ) :
      M5.ConditionalCount.nSelected (F * ∏ p ∈ H, p) A
          (M5.ConditionalCount.restricted WA d) (w - A.card) *
        M5.ConditionalCount.nSelected (F * ∏ p ∈ H, p) B
          (M5.ConditionalCount.restricted WB d) (w - B.card) =
      M5.ConditionalCount.twoBlockIndicatorSum (F * ∏ p ∈ H, p) A B
        (M5.ConditionalCount.restricted WA d)
        (M5.ConditionalCount.restricted WB d) (w - A.card) (w - B.card) := by
    apply M5.ConditionalCount.two_block_completion_count
    · apply hF.mul
      apply Polynomial.monic_prod_of_monic
      intro p hp
      exact (M5.PolynomialIndicator.residual_factors_regular F N hN hF hFN p
        ((Finset.mem_powerset.mp hH) hp)).1
    · exact hA.mono_right (Finset.filter_subset _ _)
    · exact hB.mono_right (Finset.filter_subset _ _)
  have ite_sum {ι : Type*} (s : Finset ι) (p : Prop) [Decidable p]
      (f : ι → ℤ) :
      (if p then ∑ i ∈ s, f i else 0) =
        ∑ i ∈ s, if p then f i else 0 := by
    by_cases hp : p <;> simp [hp]
  unfold M5.ConditionalCount.rawCompletion
  simp only [mul_assoc]
  simp only [hcount]
  unfold M5.ConditionalCount.twoBlockIndicatorSum
  simp only [M5.ConditionalCount.restricted_subset_domain, Finset.sum_filter]
  unfold M5.ConditionalCount.pairIndicator
  unfold M5.ConditionalCount.selectedDivisorSum M5.PolynomialIndicator.factorExclusionSum
  simp only [Finset.mem_union, or_imp, forall_and]
  simp only [Finset.mul_sum, Finset.sum_mul, mul_ite, ite_mul,
    mul_zero, zero_mul, ite_sum]
  simp only [Finset.sum_comm (s := N.divisors) (t := WA.powersetCard (w - A.card)),
    Finset.sum_comm (s := N.divisors) (t := WB.powersetCard (w - B.card)),
    Finset.sum_comm
      (s := (M5.PolynomialExclusion.residualFactors (M5.cyclicModulus N) F).powerset)
      (t := WA.powersetCard (w - A.card)),
    Finset.sum_comm
      (s := (M5.PolynomialExclusion.residualFactors (M5.cyclicModulus N) F).powerset)
      (t := WB.powersetCard (w - B.card)),
    Finset.sum_comm
      (s := (M5.PolynomialExclusion.residualFactors (M5.cyclicModulus N) F).powerset)
      (t := N.divisors)]
  repeat' (apply Finset.sum_congr rfl; intro x hx)
  split_ifs <;> simp_all [mul_comm, mul_left_comm, mul_assoc]
