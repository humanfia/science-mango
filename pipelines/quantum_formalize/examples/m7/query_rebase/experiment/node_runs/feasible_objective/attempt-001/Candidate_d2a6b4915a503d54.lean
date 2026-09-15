import FrozenTarget_d2a6b4915a503d54
theorem M7.QueryRebase.feasible_objective : QuantumHarnessFrozenTarget := by
  unfold QuantumHarnessFrozenTarget
  intro H N inst q bases moves x
  constructor
  · unfold M7.GlobalQuery.feasible
    rw [M7.QueryRebase.realize_reparam]
    simp only [M7.DefaultQuery.feasible, M7.QueryRebase.rebase,
      M7.QueryRebase.reparam, M7.QueryRebase.sector_base]
  · unfold M7.GlobalQuery.objective
    rw [M7.QueryRebase.realize_reparam]
