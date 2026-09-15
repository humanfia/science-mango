import M5SubsetCharacter

theorem M5.SubsetCharacter.value_zero : ∀ (D : ℕ) (lam : M5.Character.BinaryVector D), M5.Character.value lam 0 = 1 := by
  change ∀ (D : ℕ) (lam : M5.Character.BinaryVector D), M5.Character.value lam 0 = 1
  intro D lam
  simp [M5.Character.value, M5.Character.bitSign]
def QuantumHarnessFrozenTarget : Prop :=
  ∀ (D : ℕ) (U : Finset ℕ) (f : ℕ → M5.Character.BinaryVector D) (lam : M5.Character.BinaryVector D), M5.Character.value lam (M5.SubsetCharacter.vectorSum U f) = ∏ s ∈ U, M5.Character.value lam (f s)
