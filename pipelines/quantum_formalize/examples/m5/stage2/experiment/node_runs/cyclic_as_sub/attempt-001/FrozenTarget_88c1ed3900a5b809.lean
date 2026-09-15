import M5Lift


def QuantumHarnessFrozenTarget : Prop :=
  ∀ N : ℕ, M5.cyclicModulus N = (Polynomial.X : M5.BinaryPolynomial) ^ N - 1
