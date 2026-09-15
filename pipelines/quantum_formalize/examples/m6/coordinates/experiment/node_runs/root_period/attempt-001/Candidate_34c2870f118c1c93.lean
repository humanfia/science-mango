import FrozenTarget_34c2870f118c1c93
theorem M6.Coordinates.root_period : QuantumHarnessFrozenTarget := by
  change ∀ (N : ℕ) [NeZero N], (AdjoinRoot.root (M6.Cyclic.modulus N)) ^ N = 1
  intro N _
  have h : (AdjoinRoot.root (M6.Cyclic.modulus N)) ^ N + 1 = 0 := by
    simpa [M6.Cyclic.modulus] using
      (AdjoinRoot.eval₂_root (M6.Cyclic.modulus N))
  have htwo : (1 : AdjoinRoot (M6.Cyclic.modulus N)) + 1 = 0 := by
    have hbase : (1 : ZMod 2) + 1 = 0 := by decide
    have hm := congrArg
      (algebraMap (ZMod 2) (AdjoinRoot (M6.Cyclic.modulus N))) hbase
    simpa only [map_add, map_one, map_zero] using hm
  exact add_right_cancel (h.trans htwo.symm)
