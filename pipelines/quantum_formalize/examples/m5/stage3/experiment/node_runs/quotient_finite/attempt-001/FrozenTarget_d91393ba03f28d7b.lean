import M5Period


def QuantumHarnessFrozenTarget : Prop :=
  ∀ (F : M5.BinaryPolynomial), F.Monic → Finite (AdjoinRoot F)
