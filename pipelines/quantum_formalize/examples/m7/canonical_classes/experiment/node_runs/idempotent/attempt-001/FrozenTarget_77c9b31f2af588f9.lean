import M7CanonicalClasses


def QuantumHarnessFrozenTarget : Prop :=
  ∀ (N : ℕ) [NeZero N], ∀ c : M7.Action.Recipe N, M7.CanonicalOuter.canonical (M7.CanonicalOuter.canonical c) = M7.CanonicalOuter.canonical c
