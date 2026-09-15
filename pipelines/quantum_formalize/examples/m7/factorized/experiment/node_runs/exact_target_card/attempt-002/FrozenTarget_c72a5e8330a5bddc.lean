import M7Factorized

theorem M7.Factorized.pair_count : ∀ (S T : Type) [Fintype S] [Fintype T] (left : S → Prop) (right : T → Prop), M7.Factorized.count (fun p : S × T => left p.1 ∧ right p.2) = M7.Factorized.count left * M7.Factorized.count right := by
  intro S T instS instT left right
  classical
  unfold M7.Factorized.count
  rw [← Finset.card_product]
  apply congrArg Finset.card
  apply Finset.ext
  intro p
  simp only [Finset.mem_filter, Finset.mem_product, Finset.mem_univ, true_and]

theorem M7.Factorized.numerator_record_card : ∀ (U S T : Type) [Fintype U] [Fintype S] [Fintype T] (sector : U → Prop) (left : U → S → Prop) (right : U → T → Prop), M7.Factorized.numerator sector left right = (M7.Factorized.records sector left right).card := by
  intro U S T instU instS instT sector left right
  classical
  unfold M7.Factorized.numerator M7.Factorized.records M7.Factorized.count
  rw [Finset.card_eq_sum_ones]
  simp only [Finset.sum_filter, Fintype.sum_prod_type]
  apply Finset.sum_congr rfl
  intro u hu
  by_cases h : sector u <;> simp [h, ite_and]
  all_goals simp [← Finset.sum_filter, Nat.mul_comm]
def QuantumHarnessFrozenTarget : Prop :=
  ∀ (U S T : Type) [Fintype U] [Fintype S] [Fintype T], ∀ (X Y : Type) (leftImage : U → S → X) (rightImage : U → T → Y) (x : X) (y : Y), M7.Factorized.exactTargetNumerator leftImage rightImage x y = M7.Factorized.count (fun r : U × S × T => leftImage r.1 r.2.1 = x ∧ rightImage r.1 r.2.2 = y)
