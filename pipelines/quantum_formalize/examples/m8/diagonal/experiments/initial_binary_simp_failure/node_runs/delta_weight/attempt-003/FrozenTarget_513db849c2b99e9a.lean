import M8Diagonal


def QuantumHarnessFrozenTarget : Prop :=
  ∀ (N : ℕ) [NeZero N], ∀ j : ZMod N, M6.Physical.weight N (M6.Physical.delta N j) = 1
