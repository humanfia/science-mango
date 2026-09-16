import M8WeightedSearch


def QuantumHarnessFrozenTarget : Prop :=
  ∀ (n : ℕ) (α : Type) (test : Fin n → Option α × ℕ) (start fuel : ℕ), ∀ C : ℕ, (∀ i, (test i).2 ≤ C) → (M8.WeightedSearch.walk test start fuel).work ≤ (M8.WeightedSearch.walk test start fuel).calls*C
