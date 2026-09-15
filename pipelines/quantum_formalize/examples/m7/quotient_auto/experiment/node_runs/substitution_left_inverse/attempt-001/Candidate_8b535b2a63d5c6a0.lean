import FrozenTarget_8b535b2a63d5c6a0
theorem M7.QuotientAuto.substitution_left_inverse : QuantumHarnessFrozenTarget := by
  intro N inst u x
  change ((M7.QuotientAuto.substitution (u⁻¹)).comp (M7.QuotientAuto.substitution u)) x = x
  rw [M7.QuotientAuto.substitution_comp N u (u⁻¹), inv_mul_cancel, M7.QuotientAuto.substitution_one N]
  rfl
