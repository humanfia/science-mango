import M5Period


def QuantumHarnessFrozenTarget : Prop :=
  ∀ (F : M5.BinaryPolynomial), F.coeff 0 = 1 → IsUnit (AdjoinRoot.root F)
