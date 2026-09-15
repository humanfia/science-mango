import FrozenTarget_2150c36f749d5f61
theorem M5.Binomial.signed_coefficient_eval : QuantumHarnessFrozenTarget := by
  unfold QuantumHarnessFrozenTarget
  intro S f k hf
  rw [M5.Binomial.signed_product_split S f hf]
  exact M5.Binomial.binomial_convolution (M5.Binomial.negativeCount S f) (S.card - M5.Binomial.negativeCount S f) k
