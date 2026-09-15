import FrozenTarget_3bf6643f8d7040cb
theorem M5.ConditionalResidueCount.selected_R_pair_count : QuantumHarnessFrozenTarget := by
  classical
  intro P ZA ZB T d k l hP hT hd
  simp only [M5.ConditionalResidueCount.RSelected, dif_pos hP]
  rw [M5.TupleCompletion.restricted_completion_R P hP ZA T d k hT hd,
    M5.TupleCompletion.restricted_completion_R P hP ZB T d l hT hd]
  unfold M5.TupleCompletion.restrictedCount
  unfold M5.ConditionalResidueCount.divisibilityIndicator
  simp only [Finset.card_eq_sum_ones, Nat.cast_sum, Nat.cast_one,
    Finset.sum_filter]
  simp_rw [Finset.sum_mul, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro a ha
  apply Finset.sum_congr rfl
  intro b hb
  simp only [M5.ConditionalResidueCount.completedPolynomial]
  split_ifs <;> simp_all
