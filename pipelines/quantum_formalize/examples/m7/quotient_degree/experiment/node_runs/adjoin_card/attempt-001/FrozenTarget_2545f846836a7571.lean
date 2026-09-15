import M7QuotientDegree


def QuantumHarnessFrozenTarget : Prop :=
  ∀ F : M6.Cyclic.BinaryPolynomial, F.Monic → Nat.card (AdjoinRoot F) = 2 ^ F.natDegree
