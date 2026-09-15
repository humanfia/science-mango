import FrozenTarget_ab0de5afa534dcb4
theorem M7.FinalResources.storage : QuantumHarnessFrozenTarget := by
  unfold QuantumHarnessFrozenTarget
  intro N w inst E hw hwN hE
  exact (M7.CompactStorage.storage_bounds N (M7.GeneratedFamily.size N w E)).2.2.2
