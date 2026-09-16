import FrozenTarget_c09212b9df4e9aa2
theorem M8.OrbitSpan.anchor_minimum : QuantumHarnessFrozenTarget := by
  intro N inst c hc₁ hc₂ L
  exact (M8.OrbitSpan.small_iff N c hc₁ hc₂ L).trans (M8.Anchor.passing_presentations N c L).symm
