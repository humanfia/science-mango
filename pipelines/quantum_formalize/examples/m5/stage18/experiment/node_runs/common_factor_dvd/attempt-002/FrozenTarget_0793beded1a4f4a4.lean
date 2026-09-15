import M5FactorProduct


def QuantumHarnessFrozenTarget : Prop :=
  ∀ F H A : M5.BinaryPolynomial, F ≠ 0 → F ∣ A → (F * H ∣ A ↔ H ∣ A / F)
