import FrozenTarget_e5acdbe1e6faac93
theorem M7.Factorized.exact_target_positive : QuantumHarnessFrozenTarget := by
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
