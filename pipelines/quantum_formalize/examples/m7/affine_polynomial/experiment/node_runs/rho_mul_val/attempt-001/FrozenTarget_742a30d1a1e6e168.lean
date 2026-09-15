import M7AffinePolynomial


def QuantumHarnessFrozenTarget : Prop :=
  ∀ (N : ℕ) [NeZero N], ∀ (u : (ZMod N)ˣ) (x : ZMod N), M7.CyclicSubstitution.rho N ^ ((u : ZMod N)*x).val = M7.CyclicSubstitution.point u ^ x.val
