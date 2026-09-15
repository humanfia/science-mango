import M7StreamingIndices


def QuantumHarnessFrozenTarget : Prop :=
  ∀ (n : ℕ) (p : Fin n → Bool) (i fuel : ℕ), M7.StreamingIndices.allFinFrom n p i fuel = true ↔ ∀ j : Fin n, i ≤ j.val → j.val < i + fuel → p j = true
