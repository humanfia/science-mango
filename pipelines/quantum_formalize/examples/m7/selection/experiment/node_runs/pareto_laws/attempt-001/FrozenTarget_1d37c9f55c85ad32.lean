import M7Selection


def QuantumHarnessFrozenTarget : Prop :=
  ∀ (m : ℕ), (∀ a : Fin m → ℤ, ¬ M7.Selection.pareto a a) ∧ (∀ a b c : Fin m → ℤ, M7.Selection.pareto a b → M7.Selection.pareto b c → M7.Selection.pareto a c)
