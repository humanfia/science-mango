import M7AffinePolynomial


def QuantumHarnessFrozenTarget : Prop :=
  ∀ (N : ℕ) [NeZero N], ∀ s : ZMod N, IsUnit (M7.CyclicSubstitution.rho N ^ s.val)
