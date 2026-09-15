import M7CanonicalOuter


def QuantumHarnessFrozenTarget : Prop :=
  ∀ (N : ℕ) [NeZero N], ∀ c : M7.Action.Recipe N, c.1.Nonempty → c.2.Nonempty → 0 ∈ (M7.CanonicalOuter.canonical c).1 ∧ 0 ∈ (M7.CanonicalOuter.canonical c).2
