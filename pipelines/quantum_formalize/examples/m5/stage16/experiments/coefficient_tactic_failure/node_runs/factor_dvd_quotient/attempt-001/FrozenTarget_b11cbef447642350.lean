import M5BinaryDivisibility
import M5PolynomialExclusion


def QuantumHarnessFrozenTarget : Prop :=
  ∀ F P p : M5.BinaryPolynomial, F ≠ 0 → F ∣ P → (p ∣ P / F ↔ F * p ∣ P)
