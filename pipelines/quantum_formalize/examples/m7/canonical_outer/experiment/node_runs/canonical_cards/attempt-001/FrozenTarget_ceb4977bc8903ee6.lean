import M7CanonicalOuter


def QuantumHarnessFrozenTarget : Prop :=
  ∀ (N : ℕ) [NeZero N], ∀ (c : M7.Action.Recipe N) (w : ℕ), c.1.card = w → c.2.card = w → (M7.CanonicalOuter.canonical c).1.card = w ∧ (M7.CanonicalOuter.canonical c).2.card = w
