import M7ObjectiveComparison


def QuantumHarnessFrozenTarget : Prop :=
  ∀ (m : ℕ) (a b : Fin m → ℤ) (i fuel : ℕ) (seen : Bool), (M7.ObjectiveComparison.paretoFrom a b i fuel seen).1 = true ↔ (∀ j : Fin m, i ≤ j.val ∧ j.val < i+fuel → a j ≤ b j) ∧ (seen = true ∨ ∃ j : Fin m, (i ≤ j.val ∧ j.val < i+fuel) ∧ a j < b j)
