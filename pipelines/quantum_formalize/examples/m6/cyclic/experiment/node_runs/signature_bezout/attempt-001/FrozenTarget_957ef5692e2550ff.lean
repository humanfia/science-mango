import M6Cyclic


def QuantumHarnessFrozenTarget : Prop :=
  ∀ a b M : M6.Cyclic.BinaryPolynomial, ∃ p q r : M6.Cyclic.BinaryPolynomial, M6.Cyclic.signature a b M = p*a + q*b + r*M
