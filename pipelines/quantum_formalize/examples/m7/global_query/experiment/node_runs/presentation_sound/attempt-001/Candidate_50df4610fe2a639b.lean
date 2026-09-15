import FrozenTarget_50df4610fe2a639b
theorem M7.GlobalQuery.presentation_sound : QuantumHarnessFrozenTarget := by
  unfold QuantumHarnessFrozenTarget
  intro H N inst q bases x hx
  unfold M7.GlobalQuery.present at hx
  refine ⟨hx.1, ?_⟩
  exact (((M7.ActualPresentation.leastAction_spec N (bases x.1)
    (M7.GlobalQuery.realize bases x)).1 x.2).mp hx.2).2
