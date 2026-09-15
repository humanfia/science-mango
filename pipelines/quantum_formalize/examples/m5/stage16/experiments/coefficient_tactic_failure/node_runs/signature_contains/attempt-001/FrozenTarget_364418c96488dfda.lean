import M5BinaryDivisibility
import M5PolynomialExclusion


def QuantumHarnessFrozenTarget : Prop :=
  ∀ (a b F : M5.BinaryPolynomial) (N : ℕ), F ∣ a → F ∣ b → F ∣ M5.cyclicModulus N → F ∣ M5.completeSignature a b N
