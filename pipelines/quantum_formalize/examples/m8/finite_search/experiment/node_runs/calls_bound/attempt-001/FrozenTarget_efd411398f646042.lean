import M8FiniteSearch


def QuantumHarnessFrozenTarget : Prop :=
  ∀ (n : ℕ) (α : Type) (test : Fin n → Option α) (start fuel : ℕ), (M8.FiniteSearch.walk test start fuel).2 ≤ fuel
