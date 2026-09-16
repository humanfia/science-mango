import M8WeightedSearch


def QuantumHarnessFrozenTarget : Prop :=
  ∀ (n : ℕ) (α : Type) (test : Fin n → Option α × ℕ) (start fuel : ℕ), ((M8.WeightedSearch.walk test start fuel).selected, (M8.WeightedSearch.walk test start fuel).calls) = M8.FiniteSearch.walk (fun i => (test i).1) start fuel
