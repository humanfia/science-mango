import M7StreamingCost


def QuantumHarnessFrozenTarget : Prop :=
  ∀ (n : ℕ) (p : Fin n → M7.StreamingCost.Eval) (i fuel a b : ℕ), (∀ j, (p j).outer ≤ a ∧ (p j).inner ≤ b) → (M7.StreamingCost.allFinFrom n p i fuel).outer ≤ fuel*a ∧ (M7.StreamingCost.allFinFrom n p i fuel).inner ≤ fuel*b
