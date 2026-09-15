import FrozenTarget_bac5f10f1d3f1167
theorem M7.Factorized.exact_target_positive : QuantumHarnessFrozenTarget := by
  intro U S T instU instS instT X Y leftImage rightImage x y
  classical
  rw [M7.Factorized.exact_target_card U S T X Y leftImage rightImage x y]
  unfold M7.Factorized.count
  rw [Finset.card_pos]
  constructor
  · rintro ⟨r, hr⟩
    have h := (Finset.mem_filter.mp hr).2
    exact ⟨r.1, r.2.1, r.2.2, h⟩
  · rintro ⟨u, s, t, h⟩
    exact ⟨(u, s, t), Finset.mem_filter.mpr ⟨Finset.mem_univ _, h⟩⟩
