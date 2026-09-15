import FrozenTarget_6d4243873e992e84
theorem M7.QuerySectors.effective_valid : QuantumHarnessFrozenTarget := by
  change ∀ (N : ℕ) [NeZero N], ∀ q : M7.DefaultQuery.Query, M7.DefaultQuery.valid N q → M7.PrefixSector.ValidSector N (M7.QuerySectors.effective N q)
  intro N inst q hq
  cases hs : q.signatures with
  | none =>
      simp only [M7.QuerySectors.effective, hs, M7.PrefixSector.ValidSector]
      intro F hF
      exact (M7.QuerySectors.all_membership N F).mp hF
  | some E =>
      simpa only [M7.DefaultQuery.valid, M7.QuerySectors.effective,
        M7.PrefixSector.ValidSector, hs] using hq
