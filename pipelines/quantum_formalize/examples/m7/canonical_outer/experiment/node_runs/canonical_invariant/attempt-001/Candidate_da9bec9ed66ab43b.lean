import FrozenTarget_da9bec9ed66ab43b
theorem M7.CanonicalOuter.canonical_invariant : QuantumHarnessFrozenTarget := by
  change ∀ (N : ℕ) [NeZero N], ∀ (g : M7.Action.Record N) (c : M7.Action.Recipe N), M7.CanonicalOuter.canonical (M7.Action.act g c) = M7.CanonicalOuter.canonical c
  intro N inst g c
  apply M7.CanonicalOuter.pair_key_injective N
  apply le_antisymm
  · apply M7.CanonicalOuter.canonical_minimal N (M7.Action.act g c)
    rw [M7.CanonicalOuter.keyset_action N g c]
    exact M7.CanonicalOuter.canonical_key_member N c
  · apply M7.CanonicalOuter.canonical_minimal N c
    rw [← M7.CanonicalOuter.keyset_action N g c]
    exact M7.CanonicalOuter.canonical_key_member N (M7.Action.act g c)
