import M7CanonicalBlock


def QuantumHarnessFrozenTarget : Prop :=
  ∀ (N : ℕ) [NeZero N], ∀ (s t : ZMod N) (A : M7.CanonicalBlock.Support N), M7.CanonicalBlock.shift s (M7.CanonicalBlock.shift t A) = M7.CanonicalBlock.shift (s+t) A
