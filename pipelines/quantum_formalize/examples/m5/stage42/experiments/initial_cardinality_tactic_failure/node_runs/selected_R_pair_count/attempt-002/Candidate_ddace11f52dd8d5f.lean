import FrozenTarget_ddace11f52dd8d5f
theorem M5.ConditionalResidueCount.selected_R_pair_count : QuantumHarnessFrozenTarget := by
  classical
  intro P ZA ZB T d k l hP hT hd
  simp only [M5.ConditionalResidueCount.RSelected, dif_pos hP]
  rw [M5.TupleCompletion.restricted_completion_R P hP ZA T d k hT hd,
    M5.TupleCompletion.restricted_completion_R P hP ZB T d l hT hd]
  unfold M5.TupleCompletion.restrictedCount
  unfold M5.ConditionalResidueCount.divisibilityIndicator M5.ConditionalResidueCount.completedPolynomial
  simp only [Finset.card_eq_sum_ones, Nat.cast_sum, Finset.sum_filter,
    Nat.cast_one, Finset.sum_mul, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro a ha
  apply Finset.sum_congr rfl
  intro b hb
  by_cases haD : ∀ i : Fin k, d ∣ (a i).val <;>
    by_cases haP : P ∣ ZA + ∑ i : Fin k, (Polynomial.X : M5.BinaryPolynomial) ^ (a i).val <;>
    by_cases hbD : ∀ i : Fin l, d ∣ (b i).val <;>
    by_cases hbP : P ∣ ZB + ∑ i : Fin l, (Polynomial.X : M5.BinaryPolynomial) ^ (b i).val <;>
    simp only [haD, haP, hbD, hbP, and_true, and_false, true_and, false_and,
      ite_true, ite_false, Nat.cast_one, Nat.cast_zero, one_mul, zero_mul, mul_zero]
