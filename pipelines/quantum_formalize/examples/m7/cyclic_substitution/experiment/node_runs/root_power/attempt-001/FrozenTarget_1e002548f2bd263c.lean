import M7CyclicSubstitution


def QuantumHarnessFrozenTarget : Prop :=
  ∀ (N : ℕ) [NeZero N], M7.CyclicSubstitution.rho N ^ N = 1
