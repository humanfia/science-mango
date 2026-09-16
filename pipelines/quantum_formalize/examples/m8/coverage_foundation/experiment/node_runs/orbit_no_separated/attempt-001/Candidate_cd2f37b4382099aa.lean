import FrozenTarget_cd2f37b4382099aa
theorem M8.CoverageFoundation.orbit_no_separated : QuantumHarnessFrozenTarget := by
  change ∀ (N : ℕ) [NeZero N], ∀ (c : M7.Action.Recipe N) (g : M7.Action.Record N), (M8.CoverageFoundation.FullDirection c.1 ∨ M8.CoverageFoundation.FullDirection c.2) → ¬ M8.CoverageFoundation.Separated (M7.Action.act g c)
  intro N inst c g hfull
  apply M8.CoverageFoundation.no_separated N (M7.Action.act g c)
  rcases g with ⟨u, exchange, s, t⟩
  cases exchange <;>
    simpa [M7.Action.act, M8.CoverageFoundation.affine_full, or_comm] using hfull
