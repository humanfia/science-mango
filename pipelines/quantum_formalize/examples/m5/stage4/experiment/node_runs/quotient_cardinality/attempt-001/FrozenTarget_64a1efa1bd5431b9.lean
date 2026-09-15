import M5Cardinality


def QuantumHarnessFrozenTarget : Prop :=
  ∀ F : M5.BinaryPolynomial, F.Monic → Nat.card (AdjoinRoot F) = 2 ^ F.natDegree
