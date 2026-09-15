import FrozenTarget_40289c87f3f58dc7
theorem M7.Factorized.numerator_record_card : QuantumHarnessFrozenTarget := by
  intro U S T instU instS instT sector left right
  classical
  unfold M7.Factorized.numerator M7.Factorized.records M7.Factorized.count
  rw [Finset.card_eq_sum_ones]
  simp only [Finset.sum_filter, Fintype.sum_prod_type]
  apply Finset.sum_congr rfl
  intro u hu
  by_cases h : sector u <;> simp [h, ite_and]
  all_goals simp [← Finset.sum_filter, Nat.mul_comm]
