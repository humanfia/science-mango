import FrozenTarget_f4a2b9da9983a0d8
theorem M7.Factorized.numerator_record_card : QuantumHarnessFrozenTarget := by
  change ∀ (U S T : Type) [Fintype U] [Fintype S] [Fintype T] (sector : U → Prop) (left : U → S → Prop) (right : U → T → Prop), M7.Factorized.numerator sector left right = (M7.Factorized.records sector left right).card
  intro U S T instU instS instT sector left right
  classical
  unfold M7.Factorized.numerator M7.Factorized.records M7.Factorized.count
  simp only [Finset.card_eq_sum_ones, Finset.sum_filter, Fintype.sum_prod_type]
  apply Finset.sum_congr rfl
  intro u hu
  by_cases h : sector u <;>
    simp [h, Finset.sum_mul, Finset.mul_sum, ite_and, mul_ite, ite_mul]
