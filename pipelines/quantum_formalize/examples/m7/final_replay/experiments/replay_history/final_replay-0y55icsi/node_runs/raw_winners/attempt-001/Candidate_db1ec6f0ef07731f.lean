import FrozenTarget_db1ec6f0ef07731f
theorem M7.FinalReplay.raw_winners : QuantumHarnessFrozenTarget := by
  unfold QuantumHarnessFrozenTarget
  intro N w inst q hw hwN c hc y
  have hv := ((M7.FinalReplay.parts N w q c).mp hc).1
  have hW := (M7.FinalReplay.checked_sets N w q hw hwN c hc).1
  rw [hW]
  simpa [M7.FinalSelector.win, M7.StreamingIndices.stream_winners] using
    (M7.FinalSelector.raw_output N w q hw hwN hv y)
