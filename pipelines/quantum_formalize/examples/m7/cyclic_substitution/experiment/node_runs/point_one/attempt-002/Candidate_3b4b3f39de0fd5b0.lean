import FrozenTarget_3b4b3f39de0fd5b0
theorem M7.CyclicSubstitution.point_one : QuantumHarnessFrozenTarget := by
  change ∀ (N : ℕ) [NeZero N], M7.CyclicSubstitution.point (1 : (ZMod N)ˣ) = M7.CyclicSubstitution.rho N
  intro N _
  unfold M7.CyclicSubstitution.point
  change M7.CyclicSubstitution.rho N ^ ((1 : ℕ) : ZMod N).val = M7.CyclicSubstitution.rho N
  rw [ZMod.val_natCast]
  simpa only [pow_one] using (M7.CyclicSubstitution.power_mod N 1).symm
