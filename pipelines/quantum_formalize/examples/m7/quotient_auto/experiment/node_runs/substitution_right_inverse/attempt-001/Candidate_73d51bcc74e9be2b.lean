import FrozenTarget_73d51bcc74e9be2b
theorem M7.QuotientAuto.substitution_right_inverse : QuantumHarnessFrozenTarget := by
  intro N inst u x
  change ((M7.QuotientAuto.substitution u).comp (M7.QuotientAuto.substitution (u⁻¹))) x = x
  rw [M7.QuotientAuto.substitution_comp N (u⁻¹) u, mul_inv_cancel, M7.QuotientAuto.substitution_one N]
  rfl
