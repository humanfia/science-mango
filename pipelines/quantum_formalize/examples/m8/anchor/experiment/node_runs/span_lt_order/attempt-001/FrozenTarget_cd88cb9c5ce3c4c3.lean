import M8Anchor


def QuantumHarnessFrozenTarget : Prop :=
  ∀ (N : ℕ) [NeZero N] (c : M8.Anchor.Recipe N), M8.Anchor.span c < N
