import M6Physical


def QuantumHarnessFrozenTarget : Prop :=
  ∀ (N : ℕ) [NeZero N] (a : M6.Physical.Block N) (i : ZMod N), M6.Physical.dot N (M6.Physical.delta N i) a = a i
