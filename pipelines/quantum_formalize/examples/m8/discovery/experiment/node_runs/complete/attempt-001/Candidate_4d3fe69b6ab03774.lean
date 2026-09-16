import FrozenTarget_4d3fe69b6ab03774
theorem M8.Discovery.complete : QuantumHarnessFrozenTarget := by
  classical
  intro N inst c
  change (¬ M8.Discovery.discover c = none) ↔ _
  rw [M8.Discovery.none_iff N c]
  simp only [not_forall, not_not]
  exact (M8.Discovery.good_presentations N c).trans
    (M8.Anchor.passing_presentations N c (M8.Cutoff.limit N))
