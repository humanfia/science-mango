import FrozenTarget_92c4d88327144e9b
theorem M6.ActualCounts.boundary_eq_iff : QuantumHarnessFrozenTarget := by
  intro N inst a b ha hb h h₀
  have hf : Function.Injective (M6.Flatten.flatten N) := by
    intro z w e
    have e' := congrArg (M6.Flatten.unflatten N) e
    simpa only [M6.Flatten.flatten_left] using e'
  rw [← M6.ActualCounts.encoded_boundary N a b ha hb h,
      ← M6.ActualCounts.encoded_boundary N a b ha hb h₀]
  simp only [M6.Spaces.boundary_eval, hf.eq_iff,
    M6.Physical.boundary, Prod.mk.injEq,
    (M6.Coordinates.encode_injective N).eq_iff]
