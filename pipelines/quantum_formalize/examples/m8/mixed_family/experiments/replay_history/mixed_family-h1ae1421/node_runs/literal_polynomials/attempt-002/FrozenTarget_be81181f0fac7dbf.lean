import M8MixedFamily


def QuantumHarnessFrozenTarget : Prop :=
  ∀ (N : ℕ) [NeZero N], 7 ≤ N → M7.Supports.polynomial (M8.MixedFamily.left N) = M8.MixedFamily.a ∧ M7.Supports.polynomial (M8.MixedFamily.right N) = M8.MixedFamily.b
