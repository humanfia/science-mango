import FrozenTarget_6006c696be4a3fbd
theorem M5.OrderCount.two_block_divisibility_count : QuantumHarnessFrozenTarget := by
  classical
  intro P W k hP hW
  simp only [M5.OrderCount.nOne, dif_pos hP]
  rw [M5.AnchoredCount.anchored_single_block_count P hP W k hW]
  unfold M5.AnchoredCount.count M5.OrderCount.twoBlockIndicatorSum
  simp only [pow_two, Finset.card_eq_sum_ones, Nat.cast_sum, Nat.cast_one,
    Finset.sum_filter]
  simp [Finset.sum_mul, Finset.mul_sum, ite_mul, mul_ite, ite_and]
