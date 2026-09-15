import FrozenTarget_5a13fa517bd6485c
theorem M5.ConditionalResidueCount.selected_R_pair_count : QuantumHarnessFrozenTarget := by
  classical
  intro P ZA ZB T d k l hP hT hd
  simp only [M5.ConditionalResidueCount.RSelected, dif_pos hP]
  rw [M5.TupleCompletion.restricted_completion_R P hP ZA T d k hT hd,
    M5.TupleCompletion.restricted_completion_R P hP ZB T d l hT hd]
  unfold M5.TupleCompletion.restrictedCount M5.ConditionalResidueCount.divisibilityIndicator M5.ConditionalResidueCount.completedPolynomial
  simp only [Finset.card_eq_sum_ones, Nat.cast_sum, Nat.cast_one, Finset.sum_filter]
  rw [Finset.sum_mul]
  simp_rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro a ha
  apply Finset.sum_congr rfl
  intro b hb
  by_cases hqa : (∀ i : Fin k, d ∣ (a i).val) ∧ P ∣ ZA + ∑ i : Fin k, (Polynomial.X : M5.BinaryPolynomial) ^ (a i).val
  <;> by_cases hqb : (∀ i : Fin l, d ∣ (b i).val) ∧ P ∣ ZB + ∑ i : Fin l, (Polynomial.X : M5.BinaryPolynomial) ^ (b i).val
  <;> simp [hqa, hqb]
