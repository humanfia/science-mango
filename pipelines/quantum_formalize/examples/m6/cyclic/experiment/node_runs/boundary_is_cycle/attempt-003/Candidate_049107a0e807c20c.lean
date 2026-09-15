import FrozenTarget_049107a0e807c20c
theorem M6.Cyclic.boundary_is_cycle : QuantumHarnessFrozenTarget := by
  intro N a b h
  have hp : (2 : M6.Cyclic.BinaryPolynomial) = 0 :=
    CharP.cast_eq_zero M6.Cyclic.BinaryPolynomial 2
  have htwo : (2 : M6.Cyclic.CycleRing N) = 0 := by
    simpa only [map_ofNat, map_zero] using
      congrArg (AdjoinRoot.mk (M6.Cyclic.modulus N)) hp
  simp only [M6.Cyclic.syndrome, M6.Cyclic.boundary, mul_left_comm, mul_comm]
  rw [← two_mul, htwo, zero_mul]
