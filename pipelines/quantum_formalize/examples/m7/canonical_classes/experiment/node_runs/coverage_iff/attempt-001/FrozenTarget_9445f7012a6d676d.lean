import M7CanonicalClasses

theorem M7.CanonicalClasses.idempotent : ∀ (N : ℕ) [NeZero N], ∀ c : M7.Action.Recipe N, M7.CanonicalOuter.canonical (M7.CanonicalOuter.canonical c) = M7.CanonicalOuter.canonical c := by
  intro N inst c
  simpa only [M7.CanonicalOuter.realizer_correct N c] using
    M7.CanonicalOuter.canonical_invariant N (M7.CanonicalOuter.realizer c) c

theorem M7.CanonicalClasses.orbit_membership : ∀ (N : ℕ) [NeZero N], ∀ c y : M7.Action.Recipe N, y ∈ M7.ActualOrbit.orbit c ↔ M7.CanonicalOuter.canonical y = M7.CanonicalOuter.canonical c := by
  change ∀ (N : ℕ) [NeZero N], ∀ c y : M7.Action.Recipe N, y ∈ M7.ActualOrbit.orbit c ↔ M7.CanonicalOuter.canonical y = M7.CanonicalOuter.canonical c
  intro N _ c y
  classical
  simp only [M7.ActualOrbit.orbit, Finset.mem_image, Finset.mem_univ, true_and]
  exact (M7.CanonicalOuter.orbit_complete N c y).trans eq_comm
def QuantumHarnessFrozenTarget : Prop :=
  ∀ (N : ℕ) [NeZero N], ∀ (bases : Finset (M7.Action.Recipe N)) (y : M7.Action.Recipe N), M7.CanonicalClasses.Normalized bases → (y ∈ M7.OrbitResidual.covered bases ↔ M7.CanonicalOuter.canonical y ∈ bases)
