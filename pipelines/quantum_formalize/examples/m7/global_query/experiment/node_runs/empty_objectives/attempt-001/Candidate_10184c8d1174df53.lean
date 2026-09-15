import FrozenTarget_10184c8d1174df53
theorem M7.GlobalQuery.empty_objectives : QuantumHarnessFrozenTarget := by
  intro H N inst q bases h
  cases q
  dsimp only at h
  subst_vars
  unfold M7.GlobalQuery.winners
  exact M7.Selection.empty_objectives _ _ _ _ _
