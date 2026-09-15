import FrozenTarget_c66c070862111ac2
theorem M5.ConditionalResidueCount.exact_conditionalA : QuantumHarnessFrozenTarget := by
  classical
  change ∀ (T w : ℕ) (F : M5.BinaryPolynomial) (p q : List (Fin T)), _
  intro T w F p q hT hw hF hFT
  by_cases hf : M5.ConditionalResidueCount.fits w p q
  · simp only [M5.ConditionalResidueCount.conditionalAAt, if_pos hf]
    rw [M5.ConditionalResidueCount.arithmetic_indicator_expansion T w F p q hT hw hF hFT]
    simp_rw [M5.ConditionalResidueCount.pair_indicator_exact T w F p q _ _ hT hF hFT]
    simp [M5.ConditionalResidueCount.validCompletions,
      M5.ConditionalResidueCount.feasibleIndicator, hf,
      Finset.card_eq_sum_ones, Finset.sum_filter, Nat.cast_sum,
      Finset.sum_product, Fintype.sum_prod_type, apply_ite]
  · simp [M5.ConditionalResidueCount.conditionalAAt,
      M5.ConditionalResidueCount.validCompletions, hf]
