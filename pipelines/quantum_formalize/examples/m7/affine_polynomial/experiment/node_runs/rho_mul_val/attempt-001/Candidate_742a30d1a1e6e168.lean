import FrozenTarget_742a30d1a1e6e168
theorem M7.AffinePolynomial.rho_mul_val : QuantumHarnessFrozenTarget := by
  intro N inst u x
  change M7.CyclicSubstitution.rho N ^ ((u : ZMod N) * x).val =
    (M7.CyclicSubstitution.rho N ^ (u : ZMod N).val) ^ x.val
  rw [← pow_mul, ZMod.val_mul]
  exact (M7.CyclicSubstitution.power_mod N ((u : ZMod N).val * x.val)).symm
