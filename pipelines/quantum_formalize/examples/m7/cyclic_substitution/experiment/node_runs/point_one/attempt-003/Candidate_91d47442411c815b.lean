import FrozenTarget_91d47442411c815b
theorem M7.CyclicSubstitution.point_one : QuantumHarnessFrozenTarget := by
  change ∀ (N : ℕ) [NeZero N], M7.CyclicSubstitution.point (1 : (ZMod N)ˣ) = M7.CyclicSubstitution.rho N
  intro N _
  unfold M7.CyclicSubstitution.point
  simp only [Units.val_one]
  have h : (1 : ZMod N).val = 1 % N := by
    simpa only [Nat.cast_one] using (ZMod.val_natCast N 1)
  rw [h]
  exact (M7.CyclicSubstitution.power_mod N 1).symm.trans (pow_one _)
