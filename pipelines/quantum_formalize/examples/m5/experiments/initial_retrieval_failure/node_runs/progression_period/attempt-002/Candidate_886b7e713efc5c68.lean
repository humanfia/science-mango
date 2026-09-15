import FrozenTarget_886b7e713efc5c68
theorem M5.progression_period : QuantumHarnessFrozenTarget := by
  change ∀ (T E j : ℕ), T ∣ E → T ∣ T + j * E
  intro T E j h
  exact dvd_add (dvd_refl T) (dvd_mul_of_dvd_right h j)
