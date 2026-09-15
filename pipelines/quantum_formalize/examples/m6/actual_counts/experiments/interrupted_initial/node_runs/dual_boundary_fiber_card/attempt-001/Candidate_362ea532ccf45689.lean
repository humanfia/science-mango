import FrozenTarget_362ea532ccf45689
theorem M6.ActualCounts.dual_boundary_fiber_card : QuantumHarnessFrozenTarget := by
  intro N inst a b ha hb h₀
  have hf : Function.Injective (M6.Flatten.flatten N) := by
    intro z w e
    have e' := congrArg (M6.Flatten.unflatten N) e
    simpa only [M6.Flatten.flatten_left] using e'
  have hj : Function.Injective (M6.Physical.J N) := by
    intro z w e
    have e' := congrArg (M6.Physical.J N) e
    simpa only [M6.Physical.J_involution] using e'
  simpa only [M6.Spaces.dual_boundary_eval, M6.Spaces.boundary_eval,
    hf.eq_iff, hj.eq_iff] using
    (M6.ActualCounts.boundary_fiber_card N a b ha hb h₀)
