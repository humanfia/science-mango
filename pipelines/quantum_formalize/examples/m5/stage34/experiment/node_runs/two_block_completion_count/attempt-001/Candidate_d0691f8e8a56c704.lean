import FrozenTarget_d0691f8e8a56c704
theorem M5.ConditionalCount.two_block_completion_count : QuantumHarnessFrozenTarget := by
  classical
  intro P A B WA WB kA kB hP hA hB
  simp only [M5.ConditionalCount.nSelected, dif_pos hP]
  rw [M5.CompletionBlock.completion_count P hP A WA kA hA,
    M5.CompletionBlock.completion_count P hP B WB kB hB]
  unfold M5.CompletionBlock.count M5.ConditionalCount.twoBlockIndicatorSum
  simp only [Finset.card_eq_sum_ones, Nat.cast_sum, Nat.cast_one, Finset.sum_filter]
  rw [Finset.sum_mul]
  simp_rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro U hU
  apply Finset.sum_congr rfl
  intro V hV
  by_cases hUA : P ∣ M5.SupportPolynomial.ofSupport (A ∪ U) <;>
    by_cases hVB : P ∣ M5.SupportPolynomial.ofSupport (B ∪ V) <;>
    simp [hUA, hVB]
