import FrozenTarget_ac85751cca734a79
theorem M7.Final.canonical : QuantumHarnessFrozenTarget := by
  change M7.Final.Canonical
  unfold M7.Final.Canonical
  exact ⟨M7.CanonicalOuter.canonical_minimal,
    M7.CanonicalOuter.realizer_correct,
    M7.CanonicalOuter.realizer_inverse,
    M7.CanonicalOuter.canonical_invariant,
    M7.CanonicalOuter.orbit_complete,
    M7.CanonicalClasses.idempotent⟩
