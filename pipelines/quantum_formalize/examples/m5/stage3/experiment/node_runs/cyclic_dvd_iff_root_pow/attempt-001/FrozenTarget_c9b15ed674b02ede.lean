import M5Period


def QuantumHarnessFrozenTarget : Prop :=
  ∀ (F : M5.BinaryPolynomial) (N : ℕ), F ∣ M5.cyclicModulus N ↔ (AdjoinRoot.root F) ^ N = 1
