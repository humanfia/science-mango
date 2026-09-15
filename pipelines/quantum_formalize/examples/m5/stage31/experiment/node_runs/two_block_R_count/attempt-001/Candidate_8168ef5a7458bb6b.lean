import FrozenTarget_8168ef5a7458bb6b
theorem M5.ResidueCount.two_block_R_count : QuantumHarnessFrozenTarget := by
  classical
  intro P T d k hP hT hd
  simp only [M5.ResidueCount.ROne, dif_pos hP]
  rw [M5.AnchoredTupleCount.restricted_R_count P hP T d k hT hd]
  unfold M5.AnchoredTupleCount.restrictedCount
  simp only [pow_two, Finset.card_eq_sum_ones, Nat.cast_sum, Nat.cast_one, Finset.sum_filter]
  rw [Finset.sum_mul]
  simp_rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro a ha
  apply Finset.sum_congr rfl
  intro b hb
  by_cases hqa : (∀ i : Fin k, d ∣ (a i).val) ∧ P ∣ 1 + ∑ i : Fin k, (Polynomial.X : M5.BinaryPolynomial) ^ (a i).val
  <;> by_cases hqb : (∀ i : Fin k, d ∣ (b i).val) ∧ P ∣ 1 + ∑ i : Fin k, (Polynomial.X : M5.BinaryPolynomial) ^ (b i).val
  <;> simp [M5.ResidueCount.tailPolynomial, hqa, hqb]
