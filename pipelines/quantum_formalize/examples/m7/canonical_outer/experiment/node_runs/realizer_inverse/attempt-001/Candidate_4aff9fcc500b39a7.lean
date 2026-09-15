import FrozenTarget_4aff9fcc500b39a7
theorem M7.CanonicalOuter.realizer_inverse : QuantumHarnessFrozenTarget := by
  change ∀ (N : ℕ) [NeZero N], ∀ c : M7.Action.Recipe N, M7.Action.act (M7.Action.inverse (M7.CanonicalOuter.realizer c)) (M7.CanonicalOuter.canonical c) = c
  intro N _ c
  rw [← M7.CanonicalOuter.realizer_correct N c]
  exact M7.Action.act_inverse N (M7.CanonicalOuter.realizer c) c
