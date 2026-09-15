import FrozenTarget_b82ff52bac1aaf55
theorem M7.QueryRebase.sector_base : QuantumHarnessFrozenTarget := by
  intro N inst q base placed g
  cases hmode : q.sectorMode <;> simp only [M7.DefaultQuery.sectorTest, hmode]
  all_goals
    first
    | exact Iff.rfl
    | constructor
      · rintro ⟨h, hh⟩
        refine ⟨M7.Action.compose h g, ?_⟩
        simpa only [M7.Action.act_compose] using hh
      · rintro ⟨h, hh⟩
        refine ⟨M7.Action.compose h (M7.Action.inverse g), ?_⟩
        simpa only [M7.Action.act_compose, M7.Action.act_inverse] using hh
