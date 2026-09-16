import M8OrbitSpan


def QuantumHarnessFrozenTarget : Prop :=
  ∀ (N : ℕ) [NeZero N] (c : M7.Action.Recipe N), c.1.Nonempty → c.2.Nonempty → (M8.OrbitSpan.spans c).Nonempty
