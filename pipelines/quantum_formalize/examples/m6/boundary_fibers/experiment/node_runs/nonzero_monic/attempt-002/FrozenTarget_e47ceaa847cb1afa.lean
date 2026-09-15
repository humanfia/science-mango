import M6BoundaryFibers


def QuantumHarnessFrozenTarget : Prop :=
  ∀ p : M6.BoundaryFibers.BP, p ≠ 0 → p.Monic
