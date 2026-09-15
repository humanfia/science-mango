import FrozenTarget_1f7b1d1c201eb18e
theorem M7.DefaultQuery.literal_fiber : QuantumHarnessFrozenTarget := by
  unfold QuantumHarnessFrozenTarget
  intro N inst q base g h heq
  rw [heq]
  exact ⟨Iff.rfl, rfl⟩
