import M7ObjectiveComparison


def QuantumHarnessFrozenTarget : Prop :=
  ∀ (m : ℕ) (a b : Fin m → ℤ) (i fuel : ℕ), (M7.ObjectiveComparison.lexFrom a b i fuel).2 ≤ 2*fuel
