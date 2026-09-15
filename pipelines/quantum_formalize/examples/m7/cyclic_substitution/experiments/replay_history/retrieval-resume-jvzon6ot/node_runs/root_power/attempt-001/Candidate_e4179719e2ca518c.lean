import FrozenTarget_e4179719e2ca518c
theorem M7.CyclicSubstitution.root_power : QuantumHarnessFrozenTarget := by
  change ∀ (N : ℕ) [NeZero N], M7.CyclicSubstitution.rho N ^ N = 1
  intro N inst
  have hroot := AdjoinRoot.eval₂_root (M6.Cyclic.modulus N)
  have h : M7.CyclicSubstitution.rho N ^ N + 1 = 0 := by
    simpa [M6.Cyclic.modulus, M7.CyclicSubstitution.rho] using hroot
  have htwo : (1 : M6.Cyclic.CycleRing N) + 1 = 0 := by
    have hz : (1 : ZMod 2) + 1 = 0 := by decide
    have hm := congrArg (AdjoinRoot.of (M6.Cyclic.modulus N)) hz
    simpa using hm
  exact add_right_cancel (h.trans htwo.symm)
