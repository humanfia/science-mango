import FrozenTarget_2468ec1945f047b3
theorem M6.Cyclic.boundary_is_cycle : QuantumHarnessFrozenTarget := by
  change ∀ (N : ℕ) (a b : M6.Cyclic.BinaryPolynomial) (h : M6.Cyclic.CycleRing N), M6.Cyclic.syndrome N a b (M6.Cyclic.boundary N a b h) = 0
  intro N a b h
  simp [M6.Cyclic.syndrome, M6.Cyclic.boundary, mul_assoc, mul_left_comm, mul_comm, CharTwo.add_self_eq_zero]
