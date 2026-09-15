import FrozenTarget_58c61973e683231c
theorem M7.CanonicalOuter.chosen_outer_member : QuantumHarnessFrozenTarget := by
  classical
  change ∀ (N : ℕ) [NeZero N], ∀ c : M7.Action.Recipe N, M7.CanonicalOuter.chosenOuter c ∈ M7.CanonicalOuter.indices N
  intro N inst c
  have h := M7.CanonicalOuter.choices_nonempty N c
  have hb : M7.CanonicalOuter.best c ∈ M7.CanonicalOuter.choices c := by
    simpa only [M7.CanonicalOuter.best, dif_pos h] using (M7.CanonicalOuter.choices c).min'_mem h
  unfold M7.CanonicalOuter.choices at hb
  obtain ⟨i, hi, he⟩ := Finset.mem_image.mp hb
  unfold M7.CanonicalOuter.chosenOuter
  rw [← he]
  exact hi
