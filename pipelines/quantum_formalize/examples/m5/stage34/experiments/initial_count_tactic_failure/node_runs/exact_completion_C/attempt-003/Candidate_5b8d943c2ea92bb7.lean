import FrozenTarget_5b8d943c2ea92bb7
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
    simp [M5.ConditionalCount.completionC, hAw, hBw]
  rw [hc, M5.ConditionalCount.conditional_arithmetic_expansion N w F A B WA WB hN hF hFN hprefix]
  unfold M5.ConditionalCount.validCompletions
  simp only [Finset.card_eq_sum_ones, Finset.sum_filter, Nat.cast_sum, Finset.sum_product]
  apply Finset.sum_congr rfl
  intro U hU
  apply Finset.sum_congr rfl
  intro V hV
  have hUs := Finset.mem_powersetCard.mp hU
  have hVs := Finset.mem_powersetCard.mp hV
  have hAU : (A ∪ U).card = w := by
    rw [Finset.card_union_of_disjoint (hA.mono_right hUs.1), hUs.2]
    omega
  have hBV : (B ∪ V).card = w := by
    rw [Finset.card_union_of_disjoint (hB.mono_right hVs.1), hVs.2]
    omega
  unfold M5.ConditionalCount.pairIndicator
  rw [M5.ConditionalCount.selected_divisor_indicator N A B U V hN,
    M5.PolynomialIndicator.exact_signature_indicator
      (M5.SupportPolynomial.ofSupport (A ∪ U))
      (M5.SupportPolynomial.ofSupport (B ∪ V)) F N hN hF hFN]
  by_cases hg : M5.Connectivity.supportGcd N (A ∪ U) (B ∪ V) = 1 <;>
    by_cases hs : M5.completeSignature
      (M5.SupportPolynomial.ofSupport (A ∪ U))
      (M5.SupportPolynomial.ofSupport (B ∪ V)) N = F <;>
    simp [hAU, hBV, hg, hs]
