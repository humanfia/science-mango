import FrozenTarget_6b9cd7dec99fc293
theorem M5.ConditionalCount.two_block_completion_count : QuantumHarnessFrozenTarget := by
  classical
  intro P A B WA WB kA kB hP hA hB
  simp only [M5.ConditionalCount.nSelected, dif_pos hP, if_pos hP]
  rw [M5.CompletionBlock.completion_count P hP A WA kA hA,
      M5.CompletionBlock.completion_count P hP B WB kB hB]
  unfold M5.CompletionBlock.count M5.ConditionalCount.twoBlockIndicatorSum
  simp only [Finset.card_eq_sum_ones, Finset.sum_filter, Nat.cast_sum,
    apply_ite, Nat.cast_one, Nat.cast_zero, Finset.sum_mul, Finset.mul_sum]
  all_goals
    apply Finset.sum_congr rfl
    intro U hU
    apply Finset.sum_congr rfl
    intro V hV
    split_ifs <;> simp_all
