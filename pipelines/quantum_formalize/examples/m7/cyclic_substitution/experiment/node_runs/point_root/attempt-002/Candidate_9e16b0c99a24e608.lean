import FrozenTarget_9e16b0c99a24e608
theorem M7.CyclicSubstitution.point_root : QuantumHarnessFrozenTarget := by
  change ∀ (N : ℕ) [NeZero N], ∀ u : (ZMod N)ˣ, M7.CyclicSubstitution.RootCondition u
  intro N _ u
  change (Polynomial.X ^ N + 1 : M6.Cyclic.BinaryPolynomial).eval₂
    (AdjoinRoot.of (M6.Cyclic.modulus N))
    (M7.CyclicSubstitution.rho N ^ (u : ZMod N).val) = 0
  rw [Polynomial.eval₂_add, Polynomial.eval₂_X_pow, Polynomial.eval₂_one]
  have hp : (M7.CyclicSubstitution.rho N ^ (u : ZMod N).val) ^ N = 1 := by
    rw [← pow_mul, Nat.mul_comm, pow_mul, M7.CyclicSubstitution.root_power, one_pow]
  rw [hp]
  have h := congrArg (AdjoinRoot.of (M6.Cyclic.modulus N))
    (show (1 : ZMod 2) + 1 = 0 by decide)
  simpa only [map_add, map_one, map_zero] using h
