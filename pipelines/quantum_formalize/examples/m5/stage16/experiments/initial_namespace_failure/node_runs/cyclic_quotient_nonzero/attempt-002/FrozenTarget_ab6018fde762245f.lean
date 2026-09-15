import M5BinaryDivisibility
import M5PolynomialExclusion


def QuantumHarnessFrozenTarget : Prop :=
  ∀ (F : M5.BinaryPolynomial) (N : ℕ), 0 < N → F.Monic → F ∣ M5.cyclicModulus N → M5.cyclicModulus N / F ≠ 0
