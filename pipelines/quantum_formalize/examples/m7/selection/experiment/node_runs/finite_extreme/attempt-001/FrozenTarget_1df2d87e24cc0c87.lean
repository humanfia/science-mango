import M7Selection


def QuantumHarnessFrozenTarget : Prop :=
  ∀ (α : Type) (T : Finset α) (R : α → α → Prop), (∀ x, ¬ R x x) → (∀ x y z, R x y → R y z → R x z) → ∀ x ∈ T, ∃ y ∈ T, (∀ z ∈ T, ¬ R z y) ∧ (y = x ∨ R y x)
