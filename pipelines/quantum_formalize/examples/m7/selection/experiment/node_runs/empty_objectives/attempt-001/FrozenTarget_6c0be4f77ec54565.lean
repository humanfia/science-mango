import M7Selection


def QuantumHarnessFrozenTarget : Prop :=
  ∀ (α : Type) (T : Finset α) (feasible : α → Prop) (objective : α → Fin 0 → ℤ) (mode : M7.Selection.Mode), M7.Selection.select T feasible objective mode = M7.Selection.feasibleSet T feasible
