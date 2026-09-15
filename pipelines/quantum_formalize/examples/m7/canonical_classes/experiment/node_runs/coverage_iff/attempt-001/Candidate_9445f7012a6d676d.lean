import FrozenTarget_9445f7012a6d676d
theorem M7.CanonicalClasses.coverage_iff : QuantumHarnessFrozenTarget := by
  change ∀ (N : ℕ) [NeZero N], ∀ (bases : Finset (M7.Action.Recipe N)) (y : M7.Action.Recipe N), M7.CanonicalClasses.Normalized bases → (y ∈ M7.OrbitResidual.covered bases ↔ M7.CanonicalOuter.canonical y ∈ bases)
  intro N inst bases y hn
  classical
  simp only [M7.OrbitResidual.covered, Finset.mem_biUnion]
  constructor
  · rintro ⟨c, hc, hy⟩
    have he : M7.CanonicalOuter.canonical y = c :=
      ((M7.CanonicalClasses.orbit_membership N c y).mp hy).trans (hn c hc)
    rw [he]
    exact hc
  · intro hy
    refine ⟨M7.CanonicalOuter.canonical y, hy, ?_⟩
    apply (M7.CanonicalClasses.orbit_membership N (M7.CanonicalOuter.canonical y) y).mpr
    exact (hn (M7.CanonicalOuter.canonical y) hy).symm
