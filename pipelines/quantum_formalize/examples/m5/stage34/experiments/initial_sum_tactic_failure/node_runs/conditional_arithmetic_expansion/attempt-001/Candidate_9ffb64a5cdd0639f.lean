import FrozenTarget_9ffb64a5cdd0639f
theorem M5.ConditionalCount.conditional_arithmetic_expansion : QuantumHarnessFrozenTarget := by
  classical
  intro N w F A B WA WB hN hF hFN hPrefix
  have hA : Disjoint A WA := by
    unfold M5.ConditionalCount.PrefixOK at hPrefix
    aesop
  have hB : Disjoint B WB := by
    unfold M5.ConditionalCount.PrefixOK at hPrefix
    aesop
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
        (Finset.mem_powerset.mp hH hp)).1
    · exact hA.mono_right (Finset.filter_subset _ _)
    · exact hB.mono_right (Finset.filter_subset _ _)
  have hite {ι : Type*} (s : Finset ι) (p : Prop) [Decidable p]
      (f : ι → ℤ) :
      (if p then ∑ i ∈ s, f i else 0) = ∑ i ∈ s, if p then f i else 0 := by
    by_cases hp : p <;> simp [hp]
  have hshuffle {ι κ υ ν : Type*} (s : Finset ι) (t : Finset κ)
      (u : Finset υ) (v : Finset ν) (f : ι → κ → υ → ν → ℤ) :
      (∑ i ∈ s, ∑ j ∈ t, ∑ a ∈ u, ∑ b ∈ v, f i j a b) =
        ∑ a ∈ u, ∑ b ∈ v, ∑ i ∈ s, ∑ j ∈ t, f i j a b := by
    simp_rw [Finset.sum_comm (s := t) (t := u)]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro a ha
    simp_rw [Finset.sum_comm (s := t) (t := v)]
    rw [Finset.sum_comm]
  unfold M5.ConditionalCount.rawCompletion
  simp only [mul_assoc]
  simp only [hcount]
  unfold M5.ConditionalCount.twoBlockIndicatorSum
  simp_rw [M5.ConditionalCount.restricted_subset_domain]
  simp only [Finset.sum_filter]
  simp only [Finset.mul_sum, Finset.sum_mul, hite]
  rw [hshuffle]
  apply Finset.sum_congr rfl
  intro U hU
  apply Finset.sum_congr rfl
  intro V hV
  unfold M5.ConditionalCount.pairIndicator
  unfold M5.ConditionalCount.selectedDivisorSum M5.PolynomialIndicator.factorExclusionSum
  simp only [Finset.mul_sum, Finset.sum_mul, hite]
  first
  | apply Finset.sum_congr rfl
    intro d hd
    apply Finset.sum_congr rfl
    intro H hH
    simp only [Finset.mem_union, forall_mem_or]
    split_ifs <;> simp_all <;> ring
  | rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro H hH
    apply Finset.sum_congr rfl
    intro d hd
    simp only [Finset.mem_union, forall_mem_or]
    split_ifs <;> simp_all <;> ring
