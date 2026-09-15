import FrozenTarget_7e7839d5138e973e
theorem M7.CyclicSubstitution.root_power : QuantumHarnessFrozenTarget := by
  change ∀ (N : ℕ) [NeZero N], M7.CyclicSubstitution.rho N ^ N = 1
  intro N inst
  have hroot : M7.CyclicSubstitution.rho N ^ N + 1 = 0 := by
    simpa only [M7.CyclicSubstitution.rho, M6.Cyclic.modulus,
      Polynomial.eval₂_add, Polynomial.eval₂_pow, Polynomial.eval₂_X,
      Polynomial.eval₂_one] using
      (AdjoinRoot.eval₂_root (M6.Cyclic.modulus N))
  have htwo : (1 : M6.Cyclic.CycleRing N) + 1 = 0 := by
    have h := congrArg (AdjoinRoot.of (M6.Cyclic.modulus N))
      (show (1 : ZMod 2) + 1 = 0 by decide)
    simpa only [map_add, map_one, map_zero] using h
  exact add_right_cancel (hroot.trans htwo.symm)
