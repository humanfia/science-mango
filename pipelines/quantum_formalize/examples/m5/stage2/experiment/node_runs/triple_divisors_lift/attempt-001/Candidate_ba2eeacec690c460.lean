import FrozenTarget_ba2eeacec690c460
theorem M5.Lift.triple_divisors_lift : QuantumHarnessFrozenTarget := by
  change ∀ (a b D : M5.BinaryPolynomial) (T E j : ℕ), EuclideanDomain.gcd a b ∣ M5.cyclicModulus E → ((D ∣ a ∧ D ∣ b ∧ D ∣ M5.cyclicModulus (T + j * E)) ↔ (D ∣ a ∧ D ∣ b ∧ D ∣ M5.cyclicModulus T))
  intro a b D T E j hG
  constructor
  · rintro ⟨ha, hb, h⟩
    have hD : D ∣ EuclideanDomain.gcd a b := EuclideanDomain.dvd_gcd ha hb
    exact ⟨ha, hb, (M5.Lift.common_divisors_lift (EuclideanDomain.gcd a b) D T E j hG hD).mp h⟩
  · rintro ⟨ha, hb, h⟩
    have hD : D ∣ EuclideanDomain.gcd a b := EuclideanDomain.dvd_gcd ha hb
    exact ⟨ha, hb, (M5.Lift.common_divisors_lift (EuclideanDomain.gcd a b) D T E j hG hD).mpr h⟩
