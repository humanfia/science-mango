import M7CanonicalBlock


def QuantumHarnessFrozenTarget : Prop :=
  ∀ (N : ℕ) [NeZero N], ∀ A : M7.CanonicalBlock.Support N, A.Nonempty → (ofLex (M7.CanonicalBlock.bestKey A)).1 = M7.CanonicalBlock.key (M7.CanonicalBlock.normalize A)
