import M5ResidueNecessity


def QuantumHarnessFrozenTarget : Prop :=
  ∀ (A : Finset ℕ) (w : ℕ), 0 < w → A.card = w → 0 ∈ A → ∃ u : Fin w → ℕ, Function.Injective u ∧ Finset.univ.image u = A ∧ ∀ i : Fin w, i.val = 0 → u i = 0
