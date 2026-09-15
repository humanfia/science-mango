import M7Domain


def QuantumHarnessFrozenTarget : Prop :=
  ∀ (N : ℕ) [NeZero N] (A : M7.Domain.Support N), ∀ r : ZMod N, (M7.Domain.shift A r).card = A.card
