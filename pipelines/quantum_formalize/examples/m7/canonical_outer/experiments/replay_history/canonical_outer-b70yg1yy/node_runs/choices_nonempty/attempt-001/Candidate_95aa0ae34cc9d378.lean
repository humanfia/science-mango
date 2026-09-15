import FrozenTarget_95aa0ae34cc9d378
theorem M7.CanonicalOuter.choices_nonempty : QuantumHarnessFrozenTarget := by
  classical
  change ∀ (N : ℕ) [NeZero N], ∀ c : M7.Action.Recipe N, (M7.CanonicalOuter.choices c).Nonempty
  intro N inst c
  obtain ⟨i, hi⟩ := M7.CanonicalOuter.indices_nonempty N
  unfold M7.CanonicalOuter.choices
  exact ⟨_, Finset.mem_image.mpr ⟨i, hi, rfl⟩⟩
