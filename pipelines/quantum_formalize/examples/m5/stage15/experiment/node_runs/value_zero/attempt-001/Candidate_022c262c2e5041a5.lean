import FrozenTarget_022c262c2e5041a5
theorem M5.TupleCharacter.value_zero : QuantumHarnessFrozenTarget := by
  change ∀ (D : ℕ) (lam : M5.Character.BinaryVector D), M5.Character.value lam 0 = 1
  intro D lam
  simp [M5.Character.value, M5.Character.bitSign]
