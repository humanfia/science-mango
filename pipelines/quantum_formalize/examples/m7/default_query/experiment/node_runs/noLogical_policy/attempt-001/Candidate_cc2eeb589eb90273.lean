import FrozenTarget_cc2eeb589eb90273
theorem M7.DefaultQuery.noLogical_policy : QuantumHarnessFrozenTarget := by
  unfold QuantumHarnessFrozenTarget
  intro N inst q base placed
  constructor
  · intro hneed hnone hfeasible
    simpa [M7.DefaultQuery.feasible, hneed, hnone] using hfeasible
  · intro hfloor hobjectives
    simp [M7.DefaultQuery.feasible, M7.DefaultQuery.needsDistance,
      M7.DefaultQuery.floorTest, hfloor, hobjectives]
