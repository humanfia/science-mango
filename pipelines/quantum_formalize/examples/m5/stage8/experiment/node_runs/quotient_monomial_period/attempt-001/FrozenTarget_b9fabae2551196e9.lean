import M5PackingInjective
import M5SupportPolynomial


def QuantumHarnessFrozenTarget : Prop :=
  ∀ T a j : ℕ, AdjoinRoot.mk (M5.cyclicModulus T) ((Polynomial.X : M5.BinaryPolynomial) ^ (a + j * T)) = AdjoinRoot.mk (M5.cyclicModulus T) ((Polynomial.X : M5.BinaryPolynomial) ^ a)
