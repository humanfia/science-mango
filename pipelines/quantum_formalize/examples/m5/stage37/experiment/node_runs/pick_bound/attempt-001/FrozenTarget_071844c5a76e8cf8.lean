import M5ResidueRecovery


def QuantumHarnessFrozenTarget : Prop :=
  ∀ (T : ℕ) (f : Fin T → ℤ) (xs : List (Fin T)), (M5.ResidueRecovery.pick f xs).2 ≤ xs.length
