import M7AffinePolynomial


def QuantumHarnessFrozenTarget : Prop :=
  ∀ (N : ℕ) [NeZero N], ∀ A : M7.Supports.Support N, M7.AffinePolynomial.image A = ∑ i ∈ A, M7.CyclicSubstitution.rho N ^ i.val
