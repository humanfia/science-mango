import FrozenTarget_cc5e22d86e4b83c5
theorem M6.Cyclic.boundary_is_cycle : QuantumHarnessFrozenTarget := by
  change ∀ (N : ℕ) (a b : M6.Cyclic.BinaryPolynomial) (h : M6.Cyclic.CycleRing N), M6.Cyclic.syndrome N a b (M6.Cyclic.boundary N a b h) = 0
  intro N a b h
  have htwo : (2 : M6.Cyclic.CycleRing N) = 0 := by
    have hp : (2 : M6.Cyclic.BinaryPolynomial) = 0 := CharTwo.two_eq_zero
    simpa using congrArg (AdjoinRoot.mk (M6.Cyclic.modulus N)) hp
  simp only [M6.Cyclic.syndrome, M6.Cyclic.boundary, mul_assoc, mul_left_comm, mul_comm, Prod.fst, Prod.snd]
  rw [← two_mul, htwo, zero_mul]
