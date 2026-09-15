import M7CanonicalBlock


def QuantumHarnessFrozenTarget : Prop :=
  ∀ (N : ℕ) [NeZero N], ∀ A : M7.CanonicalBlock.Support N, M7.CanonicalBlock.shift 0 A = A
