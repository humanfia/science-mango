import FrozenTarget_ed80d39350d48cda
theorem M7.DefaultQuery.empty_objectives : QuantumHarnessFrozenTarget := by
  intro N inst q base h
  cases q
  dsimp only at h
  cases h
  unfold M7.DefaultQuery.winners
  change M7.Selection.select _ _ _ _ = _
  exact M7.Selection.empty_objectives _ _ _ _ _
