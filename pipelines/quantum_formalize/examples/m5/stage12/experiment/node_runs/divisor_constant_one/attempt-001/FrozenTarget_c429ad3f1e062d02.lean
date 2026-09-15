import M5Signature


def QuantumHarnessFrozenTarget : Prop :=
  ∀ P a : M5.BinaryPolynomial, P ∣ a → a.coeff 0 = 1 → P.coeff 0 = 1
