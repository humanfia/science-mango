import M7CanonicalClasses


def QuantumHarnessFrozenTarget : Prop :=
  ∀ (N : ℕ) [NeZero N], ∀ c y : M7.Action.Recipe N, y ∈ M7.ActualOrbit.orbit c ↔ M7.CanonicalOuter.canonical y = M7.CanonicalOuter.canonical c
