import FrozenTarget_3e91a74a05881cfb
theorem M8.Solver.discovery_span : QuantumHarnessFrozenTarget := by
  intro N inst c w hw hv
  have hleft : c.1.Nonempty := Finset.card_pos.mp (by
    rw [hv.1]
    exact hw)
  have hright : c.2.Nonempty := Finset.card_pos.mp (by
    rw [hv.2.1]
    exact hw)
  exact (M8.Discovery.complete N c).trans
    (M8.OrbitSpan.small_iff N c hleft hright (M8.Cutoff.limit N)).symm
