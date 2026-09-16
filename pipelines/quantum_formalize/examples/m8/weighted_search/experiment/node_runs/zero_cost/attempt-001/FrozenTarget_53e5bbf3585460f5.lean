import M8WeightedSearch


def QuantumHarnessFrozenTarget : Prop :=
  ∀ (n : ℕ) (α : Type) (test : Fin n → Option α × ℕ) (start fuel : ℕ), (∀ i, (test i).2 = 0) → (M8.WeightedSearch.walk test start fuel).work = 0
