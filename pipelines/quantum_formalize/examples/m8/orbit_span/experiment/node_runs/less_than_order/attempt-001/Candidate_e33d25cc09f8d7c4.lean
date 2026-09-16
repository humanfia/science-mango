import FrozenTarget_e33d25cc09f8d7c4
theorem M8.OrbitSpan.less_than_order : QuantumHarnessFrozenTarget := by
  intro N inst c hc₁ hc₂
  rcases M8.OrbitSpan.attained N c hc₁ hc₂ with ⟨g, hg, heq⟩
  rw [← heq]
  exact M8.Anchor.span_lt_order N (M7.Action.act g c)
