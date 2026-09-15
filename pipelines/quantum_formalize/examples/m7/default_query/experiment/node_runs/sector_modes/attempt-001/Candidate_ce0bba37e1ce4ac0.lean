import FrozenTarget_ce0bba37e1ce4ac0
theorem M7.DefaultQuery.sector_modes : QuantumHarnessFrozenTarget := by
  unfold QuantumHarnessFrozenTarget
  intro N inst q base placed
  constructor
  · intro h
    simp [M7.DefaultQuery.sectorTest, h]
  · intro h
    simp [M7.DefaultQuery.sectorTest, h]
