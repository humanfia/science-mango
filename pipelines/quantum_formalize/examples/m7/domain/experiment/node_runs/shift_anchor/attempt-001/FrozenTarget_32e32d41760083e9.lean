import M7Domain


def QuantumHarnessFrozenTarget : Prop :=
  ∀ (N : ℕ) [NeZero N] (A : M7.Domain.Support N), ∀ q : ZMod N, q ∈ A → (0 : ZMod N) ∈ M7.Domain.shift A (-q)
