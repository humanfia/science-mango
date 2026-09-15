import FrozenTarget_89faf5243e77205f
theorem M7.GenerationReplay.replay_terminal_fold : QuantumHarnessFrozenTarget := by
  classical
  intro N inst w E bases final es
  induction es generalizing bases final with
  | nil =>
      intro h
      unfold M7.GenerationReplay.replay at h
      split at h
      · rename_i hz
        have heq : bases = final := Option.some.inj h
        subst final
        exact ⟨hz, rfl⟩
      · simp at h
  | cons e es ih =>
      intro h
      unfold M7.GenerationReplay.replay at h
      split at h
      · exact ih (insert e.representative bases) final h
      · simp at h
