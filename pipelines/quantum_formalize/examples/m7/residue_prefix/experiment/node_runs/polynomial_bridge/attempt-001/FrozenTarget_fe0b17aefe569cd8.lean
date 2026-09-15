import M7ResiduePrefix


def QuantumHarnessFrozenTarget : Prop :=
  ∀ (N : ℕ) [NeZero N], ∀ A : Finset (ZMod N), M5.SupportPolynomial.ofSupport (M7.ResiduePrefix.encode A) = M7.Supports.polynomial A
