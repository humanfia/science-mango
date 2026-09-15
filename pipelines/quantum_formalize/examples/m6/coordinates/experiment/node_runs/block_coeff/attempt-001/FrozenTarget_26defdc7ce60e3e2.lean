import M6Coordinates


def QuantumHarnessFrozenTarget : Prop :=
  ∀ (N : ℕ) [NeZero N] (h : M6.Physical.Block N) (i : Fin N), (M6.Coordinates.blockPolynomial N h).coeff i.val = h (i.val : ZMod N)
