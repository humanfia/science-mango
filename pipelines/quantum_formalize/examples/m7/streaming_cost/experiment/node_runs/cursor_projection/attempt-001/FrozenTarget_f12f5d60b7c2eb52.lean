import M7StreamingCost


def QuantumHarnessFrozenTarget : Prop :=
  ∀ (n : ℕ) (p : Fin n → M7.StreamingCost.Eval) (i fuel : ℕ), (M7.StreamingCost.allFinFrom n p i fuel).result = M7.StreamingIndices.allFinFrom n (fun j => (p j).result) i fuel
