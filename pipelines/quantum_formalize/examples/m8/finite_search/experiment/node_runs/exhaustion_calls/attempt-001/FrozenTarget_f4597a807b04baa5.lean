import M8FiniteSearch


def QuantumHarnessFrozenTarget : Prop :=
  ∀ (n : ℕ) (α : Type) (test : Fin n → Option α) (start fuel : ℕ), start+fuel ≤ n → (M8.FiniteSearch.walk test start fuel).1 = none → (M8.FiniteSearch.walk test start fuel).2 = fuel
