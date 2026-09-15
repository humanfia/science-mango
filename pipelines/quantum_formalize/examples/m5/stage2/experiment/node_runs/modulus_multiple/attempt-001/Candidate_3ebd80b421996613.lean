import FrozenTarget_3ebd80b421996613
theorem M5.Lift.modulus_multiple : QuantumHarnessFrozenTarget := by
  change ∀ E N : ℕ, E ∣ N → M5.cyclicModulus E ∣ M5.cyclicModulus N
  intro E N h
  rw [M5.Lift.cyclic_as_sub E, M5.Lift.cyclic_as_sub N]
  apply pow_sub_one_dvd_pow_sub_one <;> assumption
