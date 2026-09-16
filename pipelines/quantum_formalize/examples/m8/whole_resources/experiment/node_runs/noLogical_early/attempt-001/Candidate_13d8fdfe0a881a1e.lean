import FrozenTarget_13d8fdfe0a881a1e
theorem M8.WholeResources.noLogical_early : QuantumHarnessFrozenTarget := by
  unfold QuantumHarnessFrozenTarget
  intro N inst c h
  simp [M8.WholeResources.run, h]
