import M7ObjectiveComparison


def QuantumHarnessFrozenTarget : Prop :=
  ∀ (m : ℕ) (a b : Fin m → ℤ) (i fuel : ℕ) (seen : Bool), (M7.ObjectiveComparison.paretoFrom a b i fuel seen).2 ≤ 2*fuel
