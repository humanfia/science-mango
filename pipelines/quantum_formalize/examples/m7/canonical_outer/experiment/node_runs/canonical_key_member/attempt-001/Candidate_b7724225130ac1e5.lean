import FrozenTarget_b7724225130ac1e5
theorem M7.CanonicalOuter.canonical_key_member : QuantumHarnessFrozenTarget := by
  classical
  change ∀ (N : ℕ) [NeZero N], ∀ c : M7.Action.Recipe N, M7.CanonicalOuter.pairKey (M7.CanonicalOuter.canonical c) ∈ M7.CanonicalOuter.keyset c
  intro N inst c
  unfold M7.CanonicalOuter.keyset M7.CanonicalOuter.canonical
  exact Finset.mem_image.mpr ⟨M7.CanonicalOuter.chosenOuter c, M7.CanonicalOuter.chosen_outer_member N c, rfl⟩
