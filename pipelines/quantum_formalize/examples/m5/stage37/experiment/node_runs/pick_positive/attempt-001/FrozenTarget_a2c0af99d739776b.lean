import M5ResidueRecovery


def QuantumHarnessFrozenTarget : Prop :=
  ∀ (T : ℕ) (f : Fin T → ℤ) (xs : List (Fin T)), (∃ a ∈ xs, 0 < f a) → ∃ a ∈ xs, (M5.ResidueRecovery.pick f xs).1 = some a ∧ 0 < f a
