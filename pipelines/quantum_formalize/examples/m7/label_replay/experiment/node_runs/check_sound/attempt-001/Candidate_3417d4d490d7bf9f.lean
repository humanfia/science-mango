import FrozenTarget_3417d4d490d7bf9f
theorem M7.LabelReplay.check_sound : QuantumHarnessFrozenTarget := by
  intro N inst c r h
  unfold M7.LabelReplay.check at h
  have hEq := of_decide_eq_true h
  subst r
  exact ⟨rfl, fun i => rfl, rfl, rfl⟩
