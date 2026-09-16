import M8DiagonalPolynomial


def QuantumHarnessFrozenTarget : Prop :=
  ∀ (N : ℕ) [NeZero N], M6.Coordinates.encode N (M6.Physical.delta N 0) = 1
