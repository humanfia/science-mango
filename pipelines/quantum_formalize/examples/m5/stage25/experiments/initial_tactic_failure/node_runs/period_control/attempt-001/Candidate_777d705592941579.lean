import FrozenTarget_777d705592941579
theorem M5.PhysicalOrder.period_control : QuantumHarnessFrozenTarget := by
  intro A B w T hw hT hA hB hBbound
  have hA0 := M5.SupportPolynomial.support_coeff_zero A hA
  have hB0 := M5.SupportPolynomial.support_coeff_zero B hB
  have hdegree : (M5.SupportPolynomial.ofSupport B).natDegree < w * T := by
    apply M5.SupportPolynomial.support_degree_bound <;> assumption
  have hperiod : 0 < M5.PhysicalOrder.supportPeriod A B ∧
      M5.PhysicalOrder.supportPeriod A B ≤ 2 ^ (M5.SupportPolynomial.ofSupport B).natDegree := by
    unfold M5.PhysicalOrder.supportPeriod
    apply M5.Signature.ordinary_gcd_period_bound <;> assumption
  refine ⟨hperiod.1, hperiod.2.trans ?_, ?_⟩
  · exact Nat.pow_le_pow_right (by decide) (Nat.le_of_lt hdegree)
  · unfold M5.PhysicalOrder.supportPeriod
    have hprops := M5.Signature.ordinary_gcd_properties
    aesop (add safe apply [M5.Period.period_law])
