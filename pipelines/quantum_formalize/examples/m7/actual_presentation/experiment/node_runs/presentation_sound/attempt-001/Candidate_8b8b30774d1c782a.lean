import FrozenTarget_8b8b30774d1c782a
theorem M7.ActualPresentation.presentation_sound : QuantumHarnessFrozenTarget := by
  unfold QuantumHarnessFrozenTarget
  intro N inst c m feasible objective mode g hg
  unfold M7.ActualPresentation.present at hg
  refine ⟨hg.1, ?_⟩
  exact (((M7.ActualPresentation.leastAction_spec N c (M7.Action.act g c)).1 g).mp hg.2).2
