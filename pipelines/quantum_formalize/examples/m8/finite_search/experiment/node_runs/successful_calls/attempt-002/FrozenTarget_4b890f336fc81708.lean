import M8FiniteSearch


def QuantumHarnessFrozenTarget : Prop :=
  ∀ (n : ℕ) (α : Type) (test : Fin n → Option α) (start fuel : ℕ), ∀ (i : Fin n) (a : α), (M8.FiniteSearch.walk test start fuel).1 = some (i,a) → (M8.FiniteSearch.walk test start fuel).2 = i.val-start+1
