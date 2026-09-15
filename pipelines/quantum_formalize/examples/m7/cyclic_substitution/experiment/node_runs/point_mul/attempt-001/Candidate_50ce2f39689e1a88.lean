import FrozenTarget_50ce2f39689e1a88
theorem M7.CyclicSubstitution.point_mul : QuantumHarnessFrozenTarget := by
  change ∀ (N : ℕ) [NeZero N], ∀ u v : (ZMod N)ˣ, M7.CyclicSubstitution.point u ^ (v : ZMod N).val = M7.CyclicSubstitution.point (v * u)
  intro N _ u v
  change (M7.CyclicSubstitution.rho N ^ (u : ZMod N).val) ^ (v : ZMod N).val = M7.CyclicSubstitution.rho N ^ ((v : ZMod N) * (u : ZMod N)).val
  rw [← pow_mul, ZMod.val_mul]
  simpa only [Nat.mul_comm] using M7.CyclicSubstitution.power_mod N ((u : ZMod N).val * (v : ZMod N).val)
