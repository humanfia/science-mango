import M7CanonicalOuter


def QuantumHarnessFrozenTarget : Prop :=
  ∀ (N : ℕ) [NeZero N], ∀ c : M7.Action.Recipe N, M7.Action.act (M7.CanonicalOuter.realizer c) c = M7.CanonicalOuter.canonical c
