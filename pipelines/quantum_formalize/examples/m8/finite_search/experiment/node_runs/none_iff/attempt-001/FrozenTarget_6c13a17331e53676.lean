import M8FiniteSearch


def QuantumHarnessFrozenTarget : Prop :=
  ∀ (n : ℕ) (α : Type) (test : Fin n → Option α) (start fuel : ℕ), ((M8.FiniteSearch.walk test start fuel).1 = none ↔ ∀ i : Fin n, start ≤ i.val → i.val < start+fuel → test i = none)
