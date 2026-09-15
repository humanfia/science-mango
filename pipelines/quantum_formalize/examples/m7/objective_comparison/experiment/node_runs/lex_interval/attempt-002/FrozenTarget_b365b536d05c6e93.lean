import M7ObjectiveComparison


def QuantumHarnessFrozenTarget : Prop :=
  ∀ (m : ℕ) (a b : Fin m → ℤ) (i fuel : ℕ), (M7.ObjectiveComparison.lexFrom a b i fuel).1 = true ↔ ∃ j : Fin m, (i ≤ j.val ∧ j.val < i+fuel) ∧ (∀ k : Fin m, i ≤ k.val → k < j → a k = b k) ∧ a j < b j
