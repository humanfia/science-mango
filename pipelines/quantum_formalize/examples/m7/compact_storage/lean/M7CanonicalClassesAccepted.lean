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

theorem M7.CanonicalClasses.coverage_iff : ∀ (N : ℕ) [NeZero N], ∀ (bases : Finset (M7.Action.Recipe N)) (y : M7.Action.Recipe N), M7.CanonicalClasses.Normalized bases → (y ∈ M7.OrbitResidual.covered bases ↔ M7.CanonicalOuter.canonical y ∈ bases) := by
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

theorem M7.CanonicalClasses.insert_normalized : ∀ (N : ℕ) [NeZero N], ∀ (bases : Finset (M7.Action.Recipe N)) (y : M7.Action.Recipe N), M7.CanonicalClasses.Normalized bases → M7.CanonicalClasses.Normalized (insert (M7.CanonicalOuter.canonical y) bases) := by
  classical
  intro N inst bases y h
  change ∀ c ∈ insert (M7.CanonicalOuter.canonical y) bases, M7.CanonicalOuter.canonical c = c
  intro c hc
  rcases Finset.mem_insert.mp hc with rfl | hc
  · exact M7.CanonicalClasses.idempotent N y
  · exact h c hc

theorem M7.CanonicalClasses.normalized_separated : ∀ (N : ℕ) [NeZero N], ∀ bases : Finset (M7.Action.Recipe N), M7.CanonicalClasses.Normalized bases → M7.OrbitResidual.Separated bases := by
  change ∀ (N : ℕ) [NeZero N], ∀ bases : Finset (M7.Action.Recipe N), M7.CanonicalClasses.Normalized bases → M7.OrbitResidual.Separated bases
  intro N _ bases hnorm
  classical
  unfold M7.OrbitResidual.Separated
  intro c hc d hd hcd
  apply Finset.disjoint_left.mpr
  intro y hyc hyd
  apply hcd
  calc
    c = M7.CanonicalOuter.canonical c := (hnorm c hc).symm
    _ = M7.CanonicalOuter.canonical y := ((M7.CanonicalClasses.orbit_membership N c y).mp hyc).symm
    _ = M7.CanonicalOuter.canonical d := (M7.CanonicalClasses.orbit_membership N d y).mp hyd
    _ = d := hnorm d hd

theorem M7.CanonicalClasses.fresh_representative : ∀ (N : ℕ) [NeZero N], ∀ (bases : Finset (M7.Action.Recipe N)) (y : M7.Action.Recipe N), M7.CanonicalClasses.Normalized bases → y ∉ M7.OrbitResidual.covered bases → M7.CanonicalOuter.canonical y ∉ bases := by
  change ∀ (N : ℕ) [NeZero N], ∀ (bases : Finset (M7.Action.Recipe N)) (y : M7.Action.Recipe N), M7.CanonicalClasses.Normalized bases → y ∉ M7.OrbitResidual.covered bases → M7.CanonicalOuter.canonical y ∉ bases
  intro N inst bases y hn hy hc
  exact hy ((M7.CanonicalClasses.coverage_iff N bases y hn).mpr hc)
#print axioms M7.CanonicalClasses.idempotent
#print axioms M7.CanonicalClasses.insert_normalized
#print axioms M7.CanonicalClasses.orbit_membership
#print axioms M7.CanonicalClasses.coverage_iff
#print axioms M7.CanonicalClasses.fresh_representative
#print axioms M7.CanonicalClasses.normalized_separated
