import FrozenTarget_c037baa1de3ec0fd
theorem M7.CyclicSubstitution.root_power : QuantumHarnessFrozenTarget := by
  change ∀ (N : ℕ) [NeZero N], M7.CyclicSubstitution.rho N ^ N = 1
  intro N inst
  have hroot : M7.CyclicSubstitution.rho N ^ N + 1 = 0 := by
    simpa only [M7.CyclicSubstitution.rho, M6.Cyclic.modulus,
      Polynomial.eval₂_add, Polynomial.eval₂_pow,
      Polynomial.eval₂_X, Polynomial.eval₂_one] using
      (AdjoinRoot.eval₂_root (M6.Cyclic.modulus N))
  have htwo : (1 : M6.Cyclic.CycleRing N) + 1 = 0 := by
    have h : (1 : ZMod 2) + 1 = 0 := by decide
    have hm := congrArg (AdjoinRoot.of (M6.Cyclic.modulus N)) h
    simpa only [map_add, map_one, map_zero] using hm
  apply add_right_cancel (b := (1 : M6.Cyclic.CycleRing N))
  exact hroot.trans htwo.symm
