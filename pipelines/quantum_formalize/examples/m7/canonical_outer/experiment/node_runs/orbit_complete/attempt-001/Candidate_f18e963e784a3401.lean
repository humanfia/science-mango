import FrozenTarget_f18e963e784a3401
theorem M7.CanonicalOuter.orbit_complete : QuantumHarnessFrozenTarget := by
  change ∀ (N : ℕ) [NeZero N], ∀ c d : M7.Action.Recipe N, (∃ g : M7.Action.Record N, M7.Action.act g c = d) ↔ M7.CanonicalOuter.canonical c = M7.CanonicalOuter.canonical d
  intro N inst c d
  constructor
  · rintro ⟨g, rfl⟩
    exact (M7.CanonicalOuter.canonical_invariant N g c).symm
  · intro h
    refine ⟨M7.Action.compose (M7.Action.inverse (M7.CanonicalOuter.realizer d)) (M7.CanonicalOuter.realizer c), ?_⟩
    rw [M7.Action.act_compose N, M7.CanonicalOuter.realizer_correct N c, h]
    exact M7.CanonicalOuter.realizer_inverse N d
