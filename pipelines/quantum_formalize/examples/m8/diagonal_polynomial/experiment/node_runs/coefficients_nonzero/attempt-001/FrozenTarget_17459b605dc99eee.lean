import M8DiagonalPolynomial


def QuantumHarnessFrozenTarget : Prop :=
  ∀ (N : ℕ) [NeZero N], ∀ p : M8.DiagonalPolynomial.BP, p ≠ 0 → p.degree < (N : WithBot ℕ) → M6.Coordinates.coefficients N p ≠ 0
