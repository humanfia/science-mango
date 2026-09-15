import M5TupleCharacter

theorem M5.TupleCharacter.value_zero : ∀ (D : ℕ) (lam : M5.Character.BinaryVector D), M5.Character.value lam 0 = 1 := by
  change ∀ (D : ℕ) (lam : M5.Character.BinaryVector D), M5.Character.value lam 0 = 1
  intro D lam
  simp [M5.Character.value, M5.Character.bitSign]
def QuantumHarnessFrozenTarget : Prop :=
  ∀ (D n k : ℕ) (f : Fin n → M5.Character.BinaryVector D) (t : Fin k → Fin n) (lam : M5.Character.BinaryVector D), M5.Character.value lam (M5.TupleCharacter.vectorSum f t) = ∏ i : Fin k, M5.Character.value lam (f (t i))
