import FrozenTarget_54d6f20fcd01d97a
theorem M5.progression_period : QuantumHarnessFrozenTarget := by
  by
    change ∀ (T E j : ℕ), T ∣ E → T ∣ T + j * E
    intro T E j h
    exact dvd_add (dvd_refl T) (dvd_mul_of_dvd_right h j)
