import M7QuotientDegree


def QuantumHarnessFrozenTarget : Prop :=
  ∀ (N : ℕ) [NeZero N], ∀ F : M6.Cyclic.BinaryPolynomial, F ∣ M6.Cyclic.modulus N → Ideal.span ({M6.Cyclic.modulus N} : Set M6.Cyclic.BinaryPolynomial) ≤ Ideal.span ({F} : Set M6.Cyclic.BinaryPolynomial)
