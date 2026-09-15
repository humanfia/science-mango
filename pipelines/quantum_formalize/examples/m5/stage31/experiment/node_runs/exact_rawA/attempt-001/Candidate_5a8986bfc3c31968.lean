import FrozenTarget_5a8986bfc3c31968
theorem M5.ResidueCount.exact_rawA : QuantumHarnessFrozenTarget := by
  classical
  intro T w F hT hw hF hFT
  rw [M5.ResidueCount.arithmetic_indicator_expansion T w F hT hw hF hFT]
  simp_rw [M5.ResidueCount.pair_indicator_exact T (w - 1) F _ _ hT hF hFT]
  simp [M5.ResidueCount.validTailPairs, Finset.card_eq_sum_ones,
    Finset.sum_filter, Nat.cast_sum, Fintype.sum_prod_type,
    Finset.sum_product]
