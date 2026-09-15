import FrozenTarget_d4d28d6027b1b71a
theorem M7.QuotientDegree.span_containment : QuantumHarnessFrozenTarget := by
  intro N _ F hF
  apply Ideal.span_le.mpr
  intro p hp
  rcases Set.mem_singleton_iff.mp hp with rfl
  exact Ideal.mem_span_singleton.mpr hF
