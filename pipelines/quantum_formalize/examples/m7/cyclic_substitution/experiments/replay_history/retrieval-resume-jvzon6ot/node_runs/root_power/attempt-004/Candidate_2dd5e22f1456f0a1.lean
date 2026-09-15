import FrozenTarget_2dd5e22f1456f0a1
theorem M7.CyclicSubstitution.root_power : QuantumHarnessFrozenTarget := by
  change ∀ (N : ℕ) [NeZero N], M7.CyclicSubstitution.rho N ^ N = 1
  intro N hN
  have h : M7.CyclicSubstitution.rho N ^ N + 1 = 0 := by
    simpa only [M7.CyclicSubstitution.rho, M6.Cyclic.modulus,
      Polynomial.eval₂_add, Polynomial.eval₂_pow, Polynomial.eval₂_X,
      Polynomial.eval₂_one] using AdjoinRoot.eval₂_root (M6.Cyclic.modulus N)
  have htwo : (1 : M6.Cyclic.CycleRing N) + 1 = 0 := by
    have hbase : (1 : ZMod 2) + 1 = 0 := by decide
    have hm := congrArg (AdjoinRoot.of (M6.Cyclic.modulus N)) hbase
    simpa only [map_add, map_one, map_zero] using hm
  exact add_right_cancel (h.trans htwo.symm)
