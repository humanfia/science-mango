import FrozenTarget_d242783f8f91e4b3
theorem M5.Lift.common_divisors_lift : QuantumHarnessFrozenTarget := by
  change ∀ (G D : M5.BinaryPolynomial) (T E j : ℕ), G ∣ M5.cyclicModulus E → D ∣ G → (D ∣ M5.cyclicModulus (T + j * E) ↔ D ∣ M5.cyclicModulus T)
  intro G D T E j hG hD
  have hd : D ∣ M5.cyclicModulus (T + j * E) - M5.cyclicModulus T :=
    dvd_trans hD (M5.Lift.progression_congruence G T E j hG)
  constructor
  · intro h
    simpa only [sub_sub_cancel] using dvd_sub h hd
  · intro h
    simpa only [sub_add_cancel] using dvd_add hd h
