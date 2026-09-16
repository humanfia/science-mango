import M8AntipodalFamily


def QuantumHarnessFrozenTarget : Prop :=
  ∀ (N : ℕ) [NeZero N], 8 ≤ N → Even N → M7.Supports.polynomial (M8.AntipodalFamily.support N) = M8.AntipodalFamily.polynomial N
