import M6Coordinates


def QuantumHarnessFrozenTarget : Prop :=
  ∀ (N : ℕ) [NeZero N], (AdjoinRoot.root (M6.Cyclic.modulus N))^N = 1
