import FrozenTarget_0ece5b59c99325e2
theorem M7.GlobalQuery.winning_classes : QuantumHarnessFrozenTarget := by
  unfold QuantumHarnessFrozenTarget
  intro H N inst q bases i
  classical
  unfold M7.GlobalQuery.winningClasses
  rw [Finset.mem_image]
  constructor
  · rintro ⟨⟨j, g⟩, h, hj⟩
    change j = i at hj
    subst j
    exact ⟨g, h⟩
  · rintro ⟨g, hg⟩
    exact ⟨(i, g), hg, rfl⟩
