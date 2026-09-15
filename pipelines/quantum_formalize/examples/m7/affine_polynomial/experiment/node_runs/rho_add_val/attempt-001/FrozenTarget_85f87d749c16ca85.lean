import M7AffinePolynomial


def QuantumHarnessFrozenTarget : Prop :=
  ∀ (N : ℕ) [NeZero N], ∀ x y : ZMod N, M7.CyclicSubstitution.rho N ^ (x+y).val = M7.CyclicSubstitution.rho N ^ x.val * M7.CyclicSubstitution.rho N ^ y.val
