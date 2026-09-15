import M7CanonicalBlock


def QuantumHarnessFrozenTarget : Prop :=
  ∀ (N : ℕ) [NeZero N], ∀ (s : ZMod N) (A : M7.CanonicalBlock.Support N), (M7.CanonicalBlock.shift s A).card = A.card
