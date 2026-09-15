import FrozenTarget_de5a08a621ee800c
theorem M7.StreamingIndices.all_records : QuantumHarnessFrozenTarget := by
  change ∀ (N : ℕ) [NeZero N], ∀ p : M7.Action.Record N → Bool, M7.StreamingIndices.allRecords N p = true ↔ ∀ g : M7.Action.Record N, p g = true
  intro N inst p
  unfold M7.StreamingIndices.allRecords
  simp only [M7.StreamingIndices.all_fin]
  constructor
  · intro h g
    rcases M7.StreamingIndices.record_surjective N g with ⟨u, e, s, t, hg⟩
    rw [← hg]
    exact h u e s t
  · intro h u e s t
    exact h (M7.StreamingIndices.decodeRecord N u e s t)
