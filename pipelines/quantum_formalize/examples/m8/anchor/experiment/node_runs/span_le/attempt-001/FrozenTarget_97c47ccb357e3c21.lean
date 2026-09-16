import M8Anchor


def QuantumHarnessFrozenTarget : Prop :=
  ∀ (N : ℕ) [NeZero N] (c : M8.Anchor.Recipe N) (L : ℕ), M8.Anchor.span c ≤ L ↔ (∀ i ∈ c.1, i.val ≤ L) ∧ (∀ i ∈ c.2, i.val ≤ L)
