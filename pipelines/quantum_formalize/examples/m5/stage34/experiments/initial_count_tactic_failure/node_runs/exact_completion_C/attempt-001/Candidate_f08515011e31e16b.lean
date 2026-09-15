import FrozenTarget_f08515011e31e16b
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
    unfold M5.ConditionalCount.completionC
    split_ifs <;> omega
  rw [hc, M5.ConditionalCount.conditional_arithmetic_expansion N w F A B WA WB hN hF hFN hprefix]
  unfold M5.ConditionalCount.validCompletions
  simp only [Finset.card_eq_sum_ones, Nat.cast_sum, Nat.cast_one,
    Finset.sum_filter, Finset.sum_product]
  apply Finset.sum_congr rfl
  intro U hU
  apply Finset.sum_congr rfl
  intro V hV
  obtain ⟨hUsub, hUcard⟩ := Finset.mem_powersetCard.mp hU
  obtain ⟨hVsub, hVcard⟩ := Finset.mem_powersetCard.mp hV
  have hAU : (A ∪ U).card = w := by
    rw [Finset.card_union_of_disjoint (hA.mono_right hUsub), hUcard,
      Nat.add_sub_of_le hAw]
  have hBV : (B ∪ V).card = w := by
    rw [Finset.card_union_of_disjoint (hB.mono_right hVsub), hVcard,
      Nat.add_sub_of_le hBw]
  unfold M5.ConditionalCount.pairIndicator
  rw [M5.ConditionalCount.selected_divisor_indicator N A B U V hN,
    M5.PolynomialIndicator.exact_signature_indicator
      (M5.SupportPolynomial.ofSupport (A ∪ U))
      (M5.SupportPolynomial.ofSupport (B ∪ V)) F N hN hF hFN]
  split_ifs <;>
    simp_all [Finset.subset_iff, Finset.mem_union, or_imp, forall_and] <;>
    aesop
