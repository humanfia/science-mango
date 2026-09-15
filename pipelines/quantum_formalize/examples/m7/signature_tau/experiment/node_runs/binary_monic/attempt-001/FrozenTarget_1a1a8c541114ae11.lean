import M7SignatureTau


def QuantumHarnessFrozenTarget : Prop :=
  ∀ F : M6.Cyclic.BinaryPolynomial, F ≠ 0 → F.Monic
