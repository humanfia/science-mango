import M6ZeroSpan


def QuantumHarnessFrozenTarget : Prop :=
  ∀ N : ℕ, M6.Final.Admissible N 1 1 → N = 1
