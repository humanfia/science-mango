import FrozenTarget_68b2509600ccf2ad
theorem M5.ConditionalResidueCount.selected_R_pair_count : QuantumHarnessFrozenTarget := by
  unfold QuantumHarnessFrozenTarget
  intro P ZA ZB T d k l hP hT hd
  classical
  simp only [M5.ConditionalResidueCount.RSelected, dif_pos hP]
  rw [M5.TupleCompletion.restricted_completion_R P hP ZA T d k hT hd,
    M5.TupleCompletion.restricted_completion_R P hP ZB T d l hT hd]
  simp only [M5.TupleCompletion.restrictedCount,
    M5.ConditionalResidueCount.divisibilityIndicator,
    M5.ConditionalResidueCount.completedPolynomial,
    Finset.card_eq_sum_ones, Nat.cast_sum, Finset.sum_filter]
  rw [Finset.sum_mul]
  simp_rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro a ha
  apply Finset.sum_congr rfl
  intro b hb
  by_cases hda : ∀ i : Fin k, d ∣ (a i).val <;>
    by_cases hpa : P ∣ ZA + ∑ i : Fin k, (Polynomial.X : M5.BinaryPolynomial) ^ (a i).val <;>
    by_cases hdb : ∀ i : Fin l, d ∣ (b i).val <;>
    by_cases hpb : P ∣ ZB + ∑ i : Fin l, (Polynomial.X : M5.BinaryPolynomial) ^ (b i).val <;>
    simp only [hda, hpa, hdb, hpb, and_true, and_false, true_and, false_and,
      if_true, if_false, Nat.cast_one, Nat.cast_zero, one_mul, zero_mul, mul_zero]
