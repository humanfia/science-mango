import FrozenTarget_05a9715f49a6f6cc
theorem M6.BoundaryFibers.kernel_iff : QuantumHarnessFrozenTarget := by
  intro a b M h
  refine AdjoinRoot.induction_on h ?_
  intro p
  simpa only [M6.BoundaryFibers.boundary, Prod.mk.injEq, ← map_mul,
    AdjoinRoot.mk_eq_zero, and_comm] using
    (M6.Cyclic.kernel_divisibility a b M p)
