import FrozenTarget_29b5f29c1d6f6db8
theorem M7.OrbitResidual.fresh_separated : QuantumHarnessFrozenTarget := by
  change ∀ (N : ℕ) [NeZero N], ∀ (bases : Finset (M7.Action.Recipe N)) (y : M7.Action.Recipe N) (g : M7.Action.Record N), M7.OrbitResidual.Separated bases → y ∉ M7.OrbitResidual.covered bases → M7.OrbitResidual.Separated (insert (M7.Action.act g y) bases)
  intro N inst bases y g hsep hfresh
  classical
  have hnew : ∀ c ∈ bases, Disjoint (M7.ActualOrbit.orbit c) (M7.ActualOrbit.orbit (M7.Action.act g y)) := by
    intro c hc
    rw [M7.OrbitResidual.orbit_action N y g]
    apply (M7.OrbitResidual.orbit_disjoint N c y).mpr
    intro hy
    exact hfresh ((M7.OrbitResidual.covered_membership N bases y).mpr ⟨c, hc, hy⟩)
  unfold M7.OrbitResidual.Separated at hsep ⊢
  intro c hc d hd hcd
  rcases Finset.mem_insert.mp hc with rfl | hc
  · rcases Finset.mem_insert.mp hd with rfl | hd
    · exact (hcd rfl).elim
    · exact (hnew d hd).symm
  · rcases Finset.mem_insert.mp hd with rfl | hd
    · exact hnew c hc
    · exact hsep c hc d hd hcd
