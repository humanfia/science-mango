import FrozenTarget_67e994e2fe91626a
theorem M5.ConditionalCount.exact_completion_C : QuantumHarnessFrozenTarget := by
  classical
  intro N w F A B WA WB hN hF hFN hprefix
  have hp := hprefix
  unfold M5.ConditionalCount.PrefixOK at hp
  have hAw : A.card ≤ w := by tauto
  have hBw : B.card ≤ w := by tauto
  have hA : Disjoint A WA := by tauto
  have hB : Disjoint B WB := by tauto
  have hc : M5.ConditionalCount.completionC N w F A B WA WB =
      M5.ConditionalCount.rawCompletion N w F A B WA WB := by
    simp [M5.ConditionalCount.completionC, hAw, hBw,
      not_lt_of_ge hAw, not_lt_of_ge hBw]
  rw [hc, M5.ConditionalCount.conditional_arithmetic_expansion N w F A B WA WB hN hF hFN hprefix]
  unfold M5.ConditionalCount.validCompletions
  rw [Finset.card_filter]
  simp only [Nat.cast_sum]
  simp only [Finset.product_eq_sprod, Finset.sum_product]
  apply Finset.sum_congr rfl
  intro U hU
  apply Finset.sum_congr rfl
  intro V hV
  have hU' := Finset.mem_powersetCard.mp hU
  have hV' := Finset.mem_powersetCard.mp hV
  have hAU : (A ∪ U).card = w := by
    rw [Finset.card_union_of_disjoint (hA.mono_right hU'.1), hU'.2]
    exact Nat.add_sub_of_le hAw
  have hBV : (B ∪ V).card = w := by
    rw [Finset.card_union_of_disjoint (hB.mono_right hV'.1), hV'.2]
    exact Nat.add_sub_of_le hBw
  change M5.ConditionalCount.selectedDivisorSum N A B U V *
    M5.PolynomialIndicator.factorExclusionSum
      (M5.SupportPolynomial.ofSupport (A ∪ U))
      (M5.SupportPolynomial.ofSupport (B ∪ V)) F N = _
  rw [M5.ConditionalCount.selected_divisor_indicator N A B U V hN,
    M5.PolynomialIndicator.exact_signature_indicator
      (M5.SupportPolynomial.ofSupport (A ∪ U))
      (M5.SupportPolynomial.ofSupport (B ∪ V)) F N hN hF hFN]
  by_cases hg : M5.Connectivity.supportGcd N (A ∪ U) (B ∪ V) = 1 <;>
    by_cases hs : M5.completeSignature
      (M5.SupportPolynomial.ofSupport (A ∪ U))
      (M5.SupportPolynomial.ofSupport (B ∪ V)) N = F <;>
    simp [hAU, hBV, hg, hs]
