import M8P4Family


def QuantumHarnessFrozenTarget : Prop :=
  ∀ (N : ℕ) [NeZero N], 8 ≤ N → M7.Supports.polynomial (M8.P4Family.support N) = M8.P4Family.polynomial
