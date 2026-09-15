import FrozenTarget_84c883555fbf30e6
theorem M5.SubsetCharacter.value_zero : QuantumHarnessFrozenTarget := by
  change ∀ (D : ℕ) (lam : M5.Character.BinaryVector D), M5.Character.value lam 0 = 1
  intro D lam
  simp [M5.Character.value, M5.Character.bitSign]
