import FrozenTarget_1ce5c074621ff315
theorem M7.Factorized.left_partition : QuantumHarnessFrozenTarget := by
  intro U S T instU instS instT sector left right test
  classical
  simp only [M7.Factorized.numerator_record_card]
  unfold M7.Factorized.records
  simp only [Finset.card_eq_sum_ones, Finset.sum_filter]
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro p hp
  rcases p with ⟨u, s, t⟩
  cases h : test u s <;> simp [h]
