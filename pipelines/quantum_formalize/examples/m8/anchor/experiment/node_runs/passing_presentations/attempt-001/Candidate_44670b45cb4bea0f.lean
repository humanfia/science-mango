import FrozenTarget_44670b45cb4bea0f
theorem M8.Anchor.passing_presentations : QuantumHarnessFrozenTarget := by
  intro N inst c L
  constructor
  · rintro ⟨e, u, a, b, hEligible, hSpan⟩
    refine ⟨M8.Anchor.record e u a b, ?_, hSpan⟩
    exact M8.Anchor.anchored N c e u a b hEligible
  · rintro ⟨g, hAnchored, hSpan⟩
    rcases M8.Anchor.translation_reconstruction N c g hAnchored with ⟨a, b, hEligible, hRecord⟩
    refine ⟨g.exchange, g.unit, a, b, hEligible, ?_⟩
    simpa only [M8.Anchor.trial, hRecord] using hSpan
