import FrozenTarget_ec033d8d49d69e7f
theorem M7.FinalReplay.raw_presentations : QuantumHarnessFrozenTarget := by
  unfold QuantumHarnessFrozenTarget
  classical
  intro N w inst q hw hwN c hc y
  have hv := ((M7.FinalReplay.parts N w q c).mp hc).1
  have hp := (M7.FinalReplay.checked_sets N w q hw hwN c hc).2
  rw [hp]
  have h := M7.FinalSelector.presentation_exact N w q hw hwN hv y
  simpa [M7.FinalSelector.present, M7.FinalSelector.realize, M7.QueryCertificate.allPresentations, M7.QueryCertificate.isLeast, M7.GlobalQuery.present] using h
