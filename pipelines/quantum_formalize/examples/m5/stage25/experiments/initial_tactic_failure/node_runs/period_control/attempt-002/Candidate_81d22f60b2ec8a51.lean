import FrozenTarget_81d22f60b2ec8a51
theorem M5.PhysicalOrder.period_control : QuantumHarnessFrozenTarget := by
  intro A B w T hw hT hA hB hBbound
  have hAc : (M5.SupportPolynomial.ofSupport A).coeff 0 = 1 := by
    simpa [hA] using M5.SupportPolynomial.support_coeff_zero A
  have hBc : (M5.SupportPolynomial.ofSupport B).coeff 0 = 1 := by
    simpa [hB] using M5.SupportPolynomial.support_coeff_zero B
  have hAn : (M5.SupportPolynomial.ofSupport A).coeff 0 ≠ 0 := by
    rw [hAc]
    exact one_ne_zero
  have hBn : (M5.SupportPolynomial.ofSupport B).coeff 0 ≠ 0 := by
    rw [hBc]
    exact one_ne_zero
  have hwT : 0 < w * T := Nat.mul_pos (by omega) hT
  have hdeg : (M5.SupportPolynomial.ofSupport B).natDegree ≤ w * T := by
    first
    | apply M5.SupportPolynomial.support_degree_bound <;> assumption
    | apply Nat.le_of_lt
      apply M5.SupportPolynomial.support_degree_bound <;> assumption
  have hpow : 2 ^ (M5.SupportPolynomial.ofSupport B).natDegree ≤ 2 ^ (w * T) :=
    Nat.pow_le_pow_right (by decide) hdeg
  unfold M5.PhysicalOrder.supportPeriod
   aesop (add safe forward M5.Signature.ordinary_gcd_period_bound)
     (add safe forward M5.Signature.ordinary_gcd_properties)
     (add safe apply M5.Period.period_law)
     (add safe apply le_trans)
