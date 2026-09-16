import M8MixedFamily


def QuantumHarnessFrozenTarget : Prop :=
  M8.MixedFamily.b = M8.MixedFamily.a^2 ∧ M8.MixedFamily.a*M8.MixedFamily.b = 1+Polynomial.X+Polynomial.X^2+Polynomial.X^3
