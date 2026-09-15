import M7CanonicalClasses

theorem M7.CanonicalClasses.idempotent : ∀ (N : ℕ) [NeZero N], ∀ c : M7.Action.Recipe N, M7.CanonicalOuter.canonical (M7.CanonicalOuter.canonical c) = M7.CanonicalOuter.canonical c := by
  intro N inst c
  simpa only [M7.CanonicalOuter.realizer_correct N c] using
    M7.CanonicalOuter.canonical_invariant N (M7.CanonicalOuter.realizer c) c
def QuantumHarnessFrozenTarget : Prop :=
  ∀ (N : ℕ) [NeZero N], ∀ (bases : Finset (M7.Action.Recipe N)) (y : M7.Action.Recipe N), M7.CanonicalClasses.Normalized bases → M7.CanonicalClasses.Normalized (insert (M7.CanonicalOuter.canonical y) bases)
