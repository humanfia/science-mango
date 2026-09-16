import FrozenTarget_abd083fb5dcd9a73
theorem M8.ExclusionGeometry.antipodal_exclusion : QuantumHarnessFrozenTarget := by
  change ∀ (N : ℕ) [NeZero N], ∀ (h L : ℕ) (c : M7.Action.Recipe N), N = 2 * h → (M8.ExclusionGeometry.Antipodal h c.1 ∨ M8.ExclusionGeometry.Antipodal h c.2) → L < h → ∀ g : M7.Action.Record N, L < M8.Anchor.span (M7.Action.act g c)
  intro N _ h L c hN hc hL g
  exact lt_of_lt_of_le hL (M8.ExclusionGeometry.orbit_span N h c g hN hc)
