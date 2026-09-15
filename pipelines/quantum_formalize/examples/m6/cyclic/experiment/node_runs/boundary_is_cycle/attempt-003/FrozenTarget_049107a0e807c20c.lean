import M6Cyclic


def QuantumHarnessFrozenTarget : Prop :=
  ∀ (N : ℕ) (a b : M6.Cyclic.BinaryPolynomial) (h : M6.Cyclic.CycleRing N), M6.Cyclic.syndrome N a b (M6.Cyclic.boundary N a b h) = 0
