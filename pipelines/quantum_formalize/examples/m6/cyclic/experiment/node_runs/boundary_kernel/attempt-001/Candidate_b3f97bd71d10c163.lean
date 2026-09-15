import FrozenTarget_b3f97bd71d10c163
theorem M6.Cyclic.boundary_kernel : QuantumHarnessFrozenTarget := by
  change ∀ (N : ℕ) (a b h : M6.Cyclic.BinaryPolynomial), M6.Cyclic.boundary N a b (M6.Cyclic.image N h) = (0, 0) ↔ M6.Cyclic.modulus N ∣ M6.Cyclic.signature a b (M6.Cyclic.modulus N) * h
  intro N a b h
  rw [← M6.Cyclic.kernel_divisibility]
  simp only [M6.Cyclic.boundary, M6.Cyclic.image, Prod.mk.injEq, ← map_mul, AdjoinRoot.mk_eq_zero, and_comm]
