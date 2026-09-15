import M6Coordinates


def QuantumHarnessFrozenTarget : Prop :=
  ∀ (N : ℕ) [NeZero N] (h : M6.Physical.Block N), (M6.Coordinates.blockPolynomial N h).degree < (N : WithBot ℕ)
