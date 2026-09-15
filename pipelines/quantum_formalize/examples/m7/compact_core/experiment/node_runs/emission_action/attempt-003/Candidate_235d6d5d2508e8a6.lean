import FrozenTarget_235d6d5d2508e8a6
theorem M7.CompactGeneration.emission_action : QuantumHarnessFrozenTarget := by
  unfold QuantumHarnessFrozenTarget
  intro N hN w E bases
  dsimp only [M7.CompactGeneration.emission]
  constructor <;> exact?
