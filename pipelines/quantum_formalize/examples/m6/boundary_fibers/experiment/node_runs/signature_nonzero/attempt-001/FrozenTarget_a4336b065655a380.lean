import M6BoundaryFibers


def QuantumHarnessFrozenTarget : Prop :=
  ∀ a b M : M6.BoundaryFibers.BP, M ≠ 0 → M6.Cyclic.signature a b M ≠ 0
