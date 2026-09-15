import FrozenTarget_77c9b31f2af588f9
theorem M7.CanonicalClasses.idempotent : QuantumHarnessFrozenTarget := by
  intro N inst c
  simpa only [M7.CanonicalOuter.realizer_correct N c] using
    M7.CanonicalOuter.canonical_invariant N (M7.CanonicalOuter.realizer c) c
