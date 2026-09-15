import M6TransferCoefficients


def QuantumHarnessFrozenTarget : Prop :=
  ∀ p q : Polynomial ℤ, M6.Transfer.polynomialMass (p+q) ≤ M6.Transfer.polynomialMass p + M6.Transfer.polynomialMass q
