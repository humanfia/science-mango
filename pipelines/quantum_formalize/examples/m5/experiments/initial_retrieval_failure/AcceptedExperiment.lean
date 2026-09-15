import M5Foundation

theorem M5.progression_period : ∀ (T E j : ℕ), T ∣ E → T ∣ T + j * E := by
  change ∀ (T E j : ℕ), T ∣ E → T ∣ T + j * E
  intro T E j h
  exact dvd_add (dvd_refl T) (dvd_mul_of_dvd_right h j)

theorem M5.recovery_inclusion_positive : ∀ (total excluded included : ℕ), total = excluded + included → 0 < total → excluded = 0 → 0 < included := by
  change ∀ (total excluded included : ℕ), total = excluded + included → 0 < total → excluded = 0 → 0 < included
  intro total excluded included hpartition hpositive hexcluded
  rw [hpartition, hexcluded, Nat.zero_add] at hpositive
  exact hpositive
#print axioms M5.progression_period
#print axioms M5.recovery_inclusion_positive
