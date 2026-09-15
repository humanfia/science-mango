import FrozenTarget_ea72ad6e33c8de75
theorem M7.QuerySectors.effective_valid : QuantumHarnessFrozenTarget := by
  change ∀ (N : ℕ) [NeZero N], ∀ q : M7.DefaultQuery.Query, M7.DefaultQuery.valid N q → M7.PrefixSector.ValidSector N (M7.QuerySectors.effective N q)
  intro N inst q hq
  change ∀ F ∈ M7.QuerySectors.effective N q, F.Monic ∧ F ∣ M6.Cyclic.modulus N
  cases hs : q.signatures with
  | none =>
      simp only [M7.QuerySectors.effective, hs]
      intro F hF
      exact (M7.QuerySectors.all_membership N F).mp hF
  | some E =>
      simp only [M7.QuerySectors.effective, hs]
      simpa only [M7.DefaultQuery.valid, hs] using hq
