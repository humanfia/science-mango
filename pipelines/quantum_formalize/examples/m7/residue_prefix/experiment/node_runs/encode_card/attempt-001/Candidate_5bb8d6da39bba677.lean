import FrozenTarget_5bb8d6da39bba677
theorem M7.ResiduePrefix.encode_card : QuantumHarnessFrozenTarget := by
  intro N inst A
  change (M7.Supports.natSupport A).card = A.card
  rw [← M7.Supports.support N A]
  exact M7.Supports.support_card N A
