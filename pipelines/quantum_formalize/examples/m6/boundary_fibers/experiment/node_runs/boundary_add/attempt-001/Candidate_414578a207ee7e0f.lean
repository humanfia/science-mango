import FrozenTarget_414578a207ee7e0f
theorem M6.BoundaryFibers.boundary_add : QuantumHarnessFrozenTarget := by
  intro a b M h k
  unfold M6.BoundaryFibers.boundary
  apply Prod.ext <;> exact mul_add _ _ _
