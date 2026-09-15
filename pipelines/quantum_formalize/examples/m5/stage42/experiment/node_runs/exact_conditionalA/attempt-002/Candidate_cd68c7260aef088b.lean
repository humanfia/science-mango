import FrozenTarget_cd68c7260aef088b
theorem M5.ConditionalResidueCount.exact_conditionalA : QuantumHarnessFrozenTarget := by
  classical
  change ∀ (T w : ℕ) (F : M5.BinaryPolynomial) (p q : List (Fin T)), _
  intro T w F p q hT hw hF hFT
  by_cases hf : M5.ConditionalResidueCount.fits w p q
  · simp only [M5.ConditionalResidueCount.conditionalAAt, if_pos hf]
    rw [M5.ConditionalResidueCount.arithmetic_indicator_expansion T w F p q hT hw hF hFT]
    simp_rw [M5.ConditionalResidueCount.pair_indicator_exact T w F p q _ _ hT hF hFT]
    simp only [M5.ConditionalResidueCount.validCompletions, if_pos hf]
    simp only [Finset.card_eq_sum_ones, Nat.cast_sum, Nat.cast_one,
      Finset.sum_filter, Fintype.sum_prod_type, Finset.sum_product]
    simp [M5.ConditionalResidueCount.feasibleIndicator, hf]
  · simp [M5.ConditionalResidueCount.conditionalAAt,
      M5.ConditionalResidueCount.validCompletions, hf]
