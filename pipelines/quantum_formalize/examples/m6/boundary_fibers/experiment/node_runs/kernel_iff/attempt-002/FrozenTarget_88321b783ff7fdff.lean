import M6BoundaryFibers


def QuantumHarnessFrozenTarget : Prop :=
  ∀ (a b M : M6.BoundaryFibers.BP) (h : AdjoinRoot M), M6.BoundaryFibers.boundary a b M h = (0,0) ↔ AdjoinRoot.mk M (M6.Cyclic.signature a b M) * h = 0
