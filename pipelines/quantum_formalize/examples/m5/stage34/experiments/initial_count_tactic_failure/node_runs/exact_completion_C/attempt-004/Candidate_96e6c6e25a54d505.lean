import FrozenTarget_96e6c6e25a54d505
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
      Nat.not_lt.mpr hAw, Nat.not_lt.mpr hBw]
  rw [hc, M5.ConditionalCount.conditional_arithmetic_expansion N w F A B WA WB hN hF hFN hprefix]
  unfold M5.ConditionalCount.validCompletions
  conv_rhs => rw [Finset.card_eq_sum_ones]
  simp only [Finset.sum_filter, Nat.cast_sum]
  conv_rhs => rw [Finset.sum_product']
  apply Finset.sum_congr rfl
  intro U hU
  apply Finset.sum_congr rfl
  intro V hV
  have hu := Finset.mem_powersetCard.mp hU
  have hv := Finset.mem_powersetCard.mp hV
  have hAU : (A ∪ U).card = w := by
    rw [Finset.card_union_of_disjoint (hA.mono_right hu.1), hu.2]
    exact Nat.add_sub_of_le hAw
  have hBV : (B ∪ V).card = w := by
    rw [Finset.card_union_of_disjoint (hB.mono_right hv.1), hv.2]
    exact Nat.add_sub_of_le hBw
  simp only [M5.ConditionalCount.pairIndicator,
    M5.ConditionalCount.selected_divisor_indicator N A B U V hN,
    M5.PolynomialIndicator.exact_signature_indicator _ _ F N hN hF hFN,
    hAU, hBV]
  split_ifs <;> simp_all
