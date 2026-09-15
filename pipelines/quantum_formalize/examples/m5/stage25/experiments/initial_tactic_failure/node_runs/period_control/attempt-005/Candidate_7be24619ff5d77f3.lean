import FrozenTarget_7be24619ff5d77f3
theorem M5.PhysicalOrder.period_control : QuantumHarnessFrozenTarget := by
  intro A B w T hw hT hA hB hBbound
  have hA0 : (M5.SupportPolynomial.ofSupport A).coeff 0 = 1 := by
    apply M5.SupportPolynomial.support_coeff_zero
    exact hA
  have hB0 : (M5.SupportPolynomial.ofSupport B).coeff 0 = 1 := by
    apply M5.SupportPolynomial.support_coeff_zero
    exact hB
  have hA0' : (M5.SupportPolynomial.ofSupport A).coeff 0 ≠ 0 := by
    rw [hA0]
    exact one_ne_zero
  have hB0' : (M5.SupportPolynomial.ofSupport B).coeff 0 ≠ 0 := by
    rw [hB0]
    exact one_ne_zero
  have hwT : 0 < w * T := Nat.mul_pos (by omega) hT
  have hdeg : (M5.SupportPolynomial.ofSupport B).natDegree < w * T := by
    apply M5.SupportPolynomial.support_degree_bound <;> assumption
  have hcontrol : 0 < M5.PhysicalOrder.supportPeriod A B ∧
      M5.PhysicalOrder.supportPeriod A B ≤ 2 ^ (M5.SupportPolynomial.ofSupport B).natDegree := by
    unfold M5.PhysicalOrder.supportPeriod
    apply M5.Signature.ordinary_gcd_period_bound <;> assumption
  refine ⟨hcontrol.1, hcontrol.2.trans ?_, ?_⟩
  · exact Nat.pow_le_pow_right (by decide) (Nat.le_of_lt hdeg)
  · unfold M5.PhysicalOrder.supportPeriod
    aesop (add safe apply M5.Period.period_law)
      (add safe forward M5.Signature.ordinary_gcd_properties)
