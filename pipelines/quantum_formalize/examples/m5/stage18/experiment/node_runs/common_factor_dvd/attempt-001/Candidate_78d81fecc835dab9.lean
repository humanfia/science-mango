import FrozenTarget_78d81fecc835dab9
theorem M5.FactorProduct.common_factor_dvd : QuantumHarnessFrozenTarget := by
  change ∀ F H A : M5.BinaryPolynomial, F ≠ 0 → F ∣ A → (F * H ∣ A ↔ H ∣ A / F)
  intro F H A hF hFA
  constructor
  · intro h
    apply EuclideanDomain.dvd_div_of_mul_dvd <;>
      first | assumption | simpa only [mul_comm] using h
  · rintro ⟨k, hk⟩
    refine ⟨k, ?_⟩
    calc
      A = F * (A / F) := (EuclideanDomain.mul_div_cancel' hFA).symm
      _ = (F * H) * k := by rw [hk, mul_assoc]
