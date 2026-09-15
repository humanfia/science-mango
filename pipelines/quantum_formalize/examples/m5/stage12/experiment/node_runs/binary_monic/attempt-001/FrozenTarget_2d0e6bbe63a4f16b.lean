import M5Signature


def QuantumHarnessFrozenTarget : Prop :=
  ∀ P : M5.BinaryPolynomial, P ≠ 0 → P.Monic
