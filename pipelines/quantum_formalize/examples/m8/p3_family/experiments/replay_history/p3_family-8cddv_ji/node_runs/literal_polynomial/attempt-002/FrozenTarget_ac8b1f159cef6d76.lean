import M8P3Family


def QuantumHarnessFrozenTarget : Prop :=
  ∀ (N : ℕ) [NeZero N], 3 ≤ N → M7.Supports.polynomial (M8.P3Family.support N) = M8.P3Family.polynomial
