import FrozenTarget_a0bedadcf13bdae0
theorem M5.PolynomialExclusion.factor_dvd_quotient : QuantumHarnessFrozenTarget := by
  change ∀ F P p : M5.BinaryPolynomial, F ≠ 0 → F ∣ P → (p ∣ P / F ↔ F * p ∣ P)
  intro F P p hF hFP
  have hcancel : F * (P / F) = P := EuclideanDomain.mul_div_cancel' hFP
  constructor
  · rintro ⟨q, hq⟩
    refine ⟨q, ?_⟩
    calc
      P = F * (P / F) := hcancel.symm
      _ = (F * p) * q := by rw [hq, mul_assoc]
  · rintro ⟨q, hq⟩
    refine ⟨q, ?_⟩
    apply mul_left_cancel₀ hF
    calc
      F * (P / F) = P := hcancel
      _ = F * (p * q) := by rw [hq, mul_assoc]
