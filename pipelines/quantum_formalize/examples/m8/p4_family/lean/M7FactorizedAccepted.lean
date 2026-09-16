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

theorem M7.Factorized.exact_target_card : ∀ (U S T : Type) [Fintype U] [Fintype S] [Fintype T], ∀ (X Y : Type) (leftImage : U → S → X) (rightImage : U → T → Y) (x : X) (y : Y), M7.Factorized.exactTargetNumerator leftImage rightImage x y = M7.Factorized.count (fun r : U × S × T => leftImage r.1 r.2.1 = x ∧ rightImage r.1 r.2.2 = y) := by
  intro U S T instU instS instT X Y leftImage rightImage x y
  classical
  unfold M7.Factorized.exactTargetNumerator
  rw [M7.Factorized.numerator_record_card]
  unfold M7.Factorized.records M7.Factorized.count
  apply congrArg Finset.card
  ext r
  simp

theorem M7.Factorized.left_partition : ∀ (U S T : Type) [Fintype U] [Fintype S] [Fintype T] (sector : U → Prop) (left : U → S → Prop) (right : U → T → Prop), ∀ test : U → S → Bool, M7.Factorized.numerator sector left right = M7.Factorized.numerator sector (fun u s => left u s ∧ test u s = false) right + M7.Factorized.numerator sector (fun u s => left u s ∧ test u s = true) right := by
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

theorem M7.Factorized.right_partition : ∀ (U S T : Type) [Fintype U] [Fintype S] [Fintype T] (sector : U → Prop) (left : U → S → Prop) (right : U → T → Prop), ∀ test : U → T → Bool, M7.Factorized.numerator sector left right = M7.Factorized.numerator sector left (fun u t => right u t ∧ test u t = false) + M7.Factorized.numerator sector left (fun u t => right u t ∧ test u t = true) := by
  intro U S T instU instS instT sector left right test
  classical
  simp only [M7.Factorized.numerator_record_card]
  unfold M7.Factorized.records
  simp only [Finset.card_eq_sum_ones, Finset.sum_filter]
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro p hp
  rcases p with ⟨u, s, t⟩
  cases h : test u t <;> simp [h]

theorem M7.Factorized.exact_target_positive : ∀ (U S T : Type) [Fintype U] [Fintype S] [Fintype T], ∀ (X Y : Type) (leftImage : U → S → X) (rightImage : U → T → Y) (x : X) (y : Y), (0 < M7.Factorized.exactTargetNumerator leftImage rightImage x y ↔ ∃ (u : U) (s : S) (t : T), leftImage u s = x ∧ rightImage u t = y) := by
  intro U S T instU instS instT X Y leftImage rightImage x y
  classical
  have count_pos : ∀ {α : Type} [Fintype α] (P : α → Prop),
      0 < M7.Factorized.count P ↔ ∃ a, P a := by
    intro α instα P
    unfold M7.Factorized.count
    simp only [Finset.card_pos, Finset.nonempty_def, Finset.mem_filter,
      Finset.mem_univ, true_and]
  rw [M7.Factorized.exact_target_card, count_pos]
  constructor
  · rintro ⟨⟨u, s, t⟩, hl, hr⟩
    exact ⟨u, s, t, hl, hr⟩
  · rintro ⟨u, s, t, hl, hr⟩
    exact ⟨(u, s, t), hl, hr⟩
#print axioms M7.Factorized.pair_count
#print axioms M7.Factorized.numerator_record_card
#print axioms M7.Factorized.exact_target_card
#print axioms M7.Factorized.exact_target_positive
#print axioms M7.Factorized.left_partition
#print axioms M7.Factorized.right_partition
