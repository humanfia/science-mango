import FrozenTarget_79334d24010d8950
theorem M7.DefaultQuery.presentation_exact : QuantumHarnessFrozenTarget := by
  intro N inst q base
  constructor
  · intro g hg
    exact M7.ActualPresentation.presentation_exact N base q.objectives.length
      (M7.DefaultQuery.feasible q base) (M7.DefaultQuery.objective q) _ g hg
  · intro g hg
    exact M7.ActualPresentation.presentation_sound N base q.objectives.length
      (M7.DefaultQuery.feasible q base) (M7.DefaultQuery.objective q) _ g hg
