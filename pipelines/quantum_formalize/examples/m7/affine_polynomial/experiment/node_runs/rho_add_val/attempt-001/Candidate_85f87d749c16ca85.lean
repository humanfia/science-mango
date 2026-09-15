import FrozenTarget_85f87d749c16ca85
theorem M7.AffinePolynomial.rho_add_val : QuantumHarnessFrozenTarget := by
  intro N inst x y
  rw [ZMod.val_add, ← M7.CyclicSubstitution.power_mod N (x.val + y.val), pow_add]
