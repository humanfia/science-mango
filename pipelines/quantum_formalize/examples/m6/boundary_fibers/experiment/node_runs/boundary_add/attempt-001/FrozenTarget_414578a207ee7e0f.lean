import M6BoundaryFibers


def QuantumHarnessFrozenTarget : Prop :=
  ∀ (a b M : M6.BoundaryFibers.BP) (h k : AdjoinRoot M), M6.BoundaryFibers.boundary a b M (h+k) = M6.BoundaryFibers.boundary a b M h + M6.BoundaryFibers.boundary a b M k
