import FrozenTarget_43210a7fa3fdb5e7
theorem M7.DefaultQuery.noLogical_policy : QuantumHarnessFrozenTarget := by
  unfold QuantumHarnessFrozenTarget
  intro N inst q base placed
  constructor
  · intro hneed hdist hfeasible
    simp [M7.DefaultQuery.feasible, hneed, hdist] at hfeasible
  · intro hfloor hobjectives
    cases hlocality : q.localityCap <;>
      cases hradius : q.radiusCap <;>
      simp [M7.DefaultQuery.feasible, M7.DefaultQuery.needsDistance,
        M7.DefaultQuery.floorTest, hfloor, hobjectives, hlocality, hradius]
