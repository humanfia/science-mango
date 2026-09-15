import FrozenTarget_855843b27ee10aae
theorem M7.CyclicSubstitution.point_inverse : QuantumHarnessFrozenTarget := by
  change ∀ (N : ℕ) [NeZero N], ∀ u : (ZMod N)ˣ, M7.CyclicSubstitution.point u ^ ((u⁻¹ : (ZMod N)ˣ) : ZMod N).val = M7.CyclicSubstitution.rho N
  intro N _ u
  rw [M7.CyclicSubstitution.point_mul N u u⁻¹, inv_mul_cancel, M7.CyclicSubstitution.point_one N]
